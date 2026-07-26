#!/usr/bin/env python3
"""Rank, deduplicate, and deeply audit a pool of qLDPC candidates."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
import uuid
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Iterable, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.bb_code import build_bb_code
from evaluation.certificate_dispatch import build_certificate, verify_certificate
from evaluation.proof_triage import (
    candidate_identity,
    deduplicate_ranked,
)
from evaluation.registry import check_code_novelty
from scripts.screen_frontier_xor import (
    TERMINAL_STATUSES,
    load_replayable_sectors,
    solve_sector,
    verify_bb_translation_symmetry,
    write_artifact,
)


PROJECT = Path(__file__).resolve().parent.parent
DEFAULT_KNOWN_ANSWER = PROJECT / "results" / "known_answer_gate.json"


@dataclass(frozen=True)
class AuditConfig:
    """Serializable configuration for one candidate-audit worker."""

    state_dir: Path
    solver_timeout_s: float = 300
    solver_workers: int = 4
    seed: int = 0
    resume: bool = True
    certify: bool = True
    known_answer_artifact: Path = DEFAULT_KNOWN_ANSWER
    certificate_timeout_per_logical_s: float = 300
    certificate_total_timeout_s: float = 7200
    verification_timeout_per_logical_s: float = 300


def _atomic_write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(
        f".{path.name}.{os.getpid()}.{uuid.uuid4().hex}.tmp",
    )
    try:
        temporary.write_text(text)
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def atomic_write_json(path: Path, value: Mapping[str, Any]) -> None:
    """Atomically write one JSON object."""

    _atomic_write_text(path, json.dumps(value, indent=2) + "\n")


def atomic_write_jsonl(
    path: Path,
    rows: Iterable[Mapping[str, Any]],
) -> None:
    """Atomically write JSONL without exposing a partially written ranking."""

    _atomic_write_text(
        path,
        "".join(json.dumps(dict(row), sort_keys=True) + "\n" for row in rows),
    )


def read_candidate_jsonl(
    paths: Iterable[Path],
) -> tuple[list[dict[str, Any]], list[str]]:
    """Read candidate objects and retain a source path for every input row."""

    records: list[dict[str, Any]] = []
    sources: list[str] = []
    for path in paths:
        with path.open() as stream:
            for line_number, line in enumerate(stream, start=1):
                if not line.strip():
                    continue
                try:
                    value = json.loads(line)
                except json.JSONDecodeError as exc:
                    # A live search writer may be between writes when this
                    # reader reaches EOF. Ignore only that unterminated final
                    # fragment; malformed completed lines still fail closed.
                    if not line.endswith(("\n", "\r")):
                        continue
                    raise ValueError(
                        f"{path}:{line_number}: invalid JSON: {exc.msg}",
                    ) from exc
                if not isinstance(value, dict):
                    raise ValueError(
                        f"{path}:{line_number}: candidate must be an object",
                    )
                records.append(value)
                sources.append(str(path))
    return records, sources


def rank_candidate_files(
    paths: Iterable[Path],
) -> tuple[list[dict[str, Any]], dict[str, int]]:
    """Load, proof-rank, and canonical-deduplicate all candidate files."""

    records, sources = read_candidate_jsonl(paths)
    ranked = deduplicate_ranked(records, sources)
    eligible = [
        row for row in ranked
        if row["proof_score"].get("rejected") is not True
        and row["proof_score"].get("status") != "REJECTED"
    ]
    return ranked, {
        "input_records": len(records),
        "unique_candidates": len(ranked),
        "duplicate_records": len(records) - len(ranked),
        "rejected_candidates": len(ranked) - len(eligible),
        "eligible_candidates": len(eligible),
    }


def validate_worker_budget(
    candidate_workers: int,
    solver_workers: int,
    max_total_workers: int,
) -> None:
    """Reject configurations that can oversubscribe the solver budget."""

    if candidate_workers < 1:
        raise ValueError("candidate_workers must be positive")
    if not 1 <= solver_workers <= 8:
        raise ValueError("solver_workers must be between 1 and 8")
    if max_total_workers < 1:
        raise ValueError("max_total_workers must be positive")
    requested = candidate_workers * solver_workers
    if requested > max_total_workers:
        raise ValueError(
            "candidate_workers * solver_workers exceeds max_total_workers "
            f"({candidate_workers} * {solver_workers} = {requested} > "
            f"{max_total_workers})",
        )


def safe_digest(canonical_digest: str) -> str:
    """Map an opaque canonical digest to a path-safe, fixed-width token."""

    return hashlib.sha256(str(canonical_digest).encode()).hexdigest()


def state_paths(
    state_dir: Path,
    canonical_digest: str,
) -> dict[str, Path]:
    token = safe_digest(canonical_digest)
    return {
        "audit": state_dir / "xor" / f"{token}.json",
        "certificate": state_dir / "certificates" / f"{token}.json",
        "verification": state_dir / "certificates" / f"{token}.verify.json",
    }


def _construction_candidate(
    ranked: Mapping[str, Any],
    canonical_digest: str,
) -> dict[str, Any]:
    """Remove triage-only evidence while retaining construction provenance."""

    required = ("ell", "m", "A_terms", "B_terms", "required_distance")
    missing = [name for name in required if ranked.get(name) is None]
    if missing:
        raise ValueError(
            "XOR audit requires BB construction fields: "
            + ", ".join(missing),
        )
    retained = (
        "source",
        "trial",
        "ansatz",
        "ell",
        "m",
        "A_terms",
        "B_terms",
        "C_terms",
        "D_terms",
        "n",
        "k",
        "required_distance",
        "max_row_weight",
        "max_qubit_degree",
        "tanner_components",
        "novelty",
        "canonical_digest",
    )
    candidate = {
        name: ranked[name]
        for name in retained
        if name in ranked and ranked[name] is not None
    }
    candidate.setdefault("canonical_digest", canonical_digest)
    return candidate


def _load_json_object(path: Path) -> dict[str, Any] | None:
    try:
        value = json.loads(path.read_text())
    except (OSError, TypeError, ValueError):
        return None
    return value if isinstance(value, dict) else None


def canonicalize_for_audit(
    ranked: Mapping[str, Any],
    *,
    code_builder: Callable[..., Any] | None = None,
    novelty_checker: Callable[..., dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Bind one selected historical row to the real registry digest.

    Older expanded-search rows did not compute canonical novelty unless their
    short MILP screen finished. Proof triage uses an exact-claim hash as a safe
    fallback, but before expensive XOR work we reconstruct the BB code and
    replace that fallback with the registry's canonical graph digest.
    """

    code_builder = build_bb_code if code_builder is None else code_builder
    novelty_checker = (
        check_code_novelty if novelty_checker is None else novelty_checker
    )
    updated = dict(ranked)
    identity = updated.get("triage_identity")
    if not isinstance(identity, Mapping):
        identity = candidate_identity(updated)
    identity = dict(identity)
    existing_novelty = updated.get("novelty")
    has_checked_novelty = (
        isinstance(existing_novelty, Mapping)
        and existing_novelty.get("checked") is True
        and existing_novelty.get("canonical_digest")
    )
    if has_checked_novelty:
        actual_digest = str(existing_novelty["canonical_digest"])
    else:
        candidate = _construction_candidate(
            updated, str(identity["canonical_digest"]),
        )
        if candidate.get("C_terms") or candidate.get("D_terms"):
            raise ValueError("XOR audit canonicalization supports CSS BB only")
        code = code_builder(
            int(candidate["ell"]),
            int(candidate["m"]),
            candidate["A_terms"],
            candidate["B_terms"],
        )
        existing_novelty = novelty_checker(code, code_type="css")
        actual_digest = str(existing_novelty["canonical_digest"])

    digest_kind = str(identity.get("digest_kind", ""))
    claimed_digest = str(identity.get("canonical_digest", ""))
    if (
        digest_kind in {"canonical", "registry-canonical"}
        and claimed_digest
        and claimed_digest != actual_digest
    ):
        raise ValueError(
            "stored canonical digest does not match reconstructed BB code",
        )
    identity["precanonical_digest"] = claimed_digest
    identity["canonical_digest"] = actual_digest
    identity["digest_kind"] = "registry-canonical"
    updated["triage_identity"] = identity
    updated["canonical_digest"] = actual_digest
    updated["novelty"] = dict(existing_novelty)
    return updated


def select_audit_candidates(
    ranked: list[dict[str, Any]],
    top: int,
    *,
    canonicalizer: Callable[[Mapping[str, Any]], dict[str, Any]] | None = None,
) -> tuple[list[dict[str, Any]], dict[str, int]]:
    """Fill the audit queue with unique, registry-novel CSS candidates."""

    if top < 0:
        raise ValueError("top must be non-negative")
    canonicalizer = (
        canonicalize_for_audit if canonicalizer is None else canonicalizer
    )
    selected: list[dict[str, Any]] = []
    seen_digests: set[str] = set()
    stats = {
        "canonicalized_candidates": 0,
        "canonical_duplicates_skipped": 0,
        "known_codes_skipped": 0,
        "unsupported_candidates_skipped": 0,
        "canonicalization_errors": 0,
    }
    if top == 0:
        return selected, stats

    for index, row in enumerate(ranked):
        if (
            row["proof_score"].get("rejected") is True
            or row["proof_score"].get("status") == "REJECTED"
        ):
            continue
        if row.get("C_terms") or row.get("D_terms"):
            row["campaign_skip_reason"] = "UNSUPPORTED_NONCSS"
            stats["unsupported_candidates_skipped"] += 1
            continue
        try:
            updated = canonicalizer(row)
        except (KeyError, TypeError, ValueError) as exc:
            row["campaign_skip_reason"] = "CANONICALIZATION_ERROR"
            row["campaign_skip_error"] = str(exc)
            stats["canonicalization_errors"] += 1
            continue
        ranked[index] = updated
        stats["canonicalized_candidates"] += 1
        novelty = updated.get("novelty")
        if (
            isinstance(novelty, Mapping)
            and novelty.get("novel") is not True
        ):
            updated["campaign_skip_reason"] = "KNOWN_CODE"
            stats["known_codes_skipped"] += 1
            continue
        digest = str(updated["triage_identity"]["canonical_digest"])
        if digest in seen_digests:
            updated["campaign_skip_reason"] = "CANONICAL_DUPLICATE"
            stats["canonical_duplicates_skipped"] += 1
            continue
        seen_digests.add(digest)
        selected.append(updated)
        if len(selected) == top:
            break
    return selected, stats


def certify_candidate(
    candidate: dict[str, Any],
    canonical_digest: str,
    config: AuditConfig,
    *,
    builder: Callable[..., dict[str, Any]] | None = None,
    verifier: Callable[..., dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Build and independently verify a durable exact certificate.

    A completed build and verification sidecar are reusable.  This matters
    because each operation may itself contain many long-running MILP solves.
    """

    builder = build_certificate if builder is None else builder
    verifier = verify_certificate if verifier is None else verifier
    paths = state_paths(config.state_dir, canonical_digest)

    certificate = (
        _load_json_object(paths["certificate"]) if config.resume else None
    )
    certificate_resumed = certificate is not None
    if certificate is None:
        certificate = builder(
            candidate,
            known_answer_artifact=config.known_answer_artifact,
            timeout_per_logical=config.certificate_timeout_per_logical_s,
            total_timeout=config.certificate_total_timeout_s,
        )
        atomic_write_json(paths["certificate"], certificate)

    certificate_sha256 = certificate.get("certificate_sha256")
    verification_envelope = (
        _load_json_object(paths["verification"]) if config.resume else None
    )
    verification = None
    verification_resumed = False
    if (
        verification_envelope is not None
        and verification_envelope.get("schema_version") == 1
        and verification_envelope.get("canonical_digest")
        == canonical_digest
        and certificate_sha256 is not None
        and verification_envelope.get("certificate_sha256")
        == certificate_sha256
        and isinstance(verification_envelope.get("verification"), dict)
    ):
        verification = verification_envelope["verification"]
        verification_resumed = True
    if verification is None:
        if certificate.get("passed") is True:
            verification = verifier(
                certificate,
                known_answer_artifact=config.known_answer_artifact,
                rerun_milp=True,
                timeout_per_logical=config.verification_timeout_per_logical_s,
            )
        else:
            verification = {
                "passed": False,
                "skipped": True,
                "reason": (
                    "certificate build did not pass the exact challenge gate"
                ),
            }
        atomic_write_json(
            paths["verification"],
            {
                "schema_version": 1,
                "canonical_digest": canonical_digest,
                "certificate_sha256": certificate_sha256,
                "verification": verification,
            },
        )

    return {
        "attempted": True,
        "certificate_path": str(paths["certificate"]),
        "verification_path": str(paths["verification"]),
        "certificate_passed": certificate.get("passed") is True,
        "verification_passed": verification.get("passed") is True,
        "verification_attempted": verification.get("skipped") is not True,
        "certificate_resumed": certificate_resumed,
        "verification_resumed": verification_resumed,
    }


def audit_candidate(
    ranked: Mapping[str, Any],
    config: AuditConfig,
    *,
    symmetry_checker: Callable[[dict[str, Any]], dict[str, Any]] | None = None,
    replay_loader: Callable[..., list[dict[str, Any]]] | None = None,
    sector_solver: Callable[[tuple[Any, ...]], dict[str, Any]] | None = None,
    artifact_writer: Callable[..., dict[str, Any]] | None = None,
    certificate_builder: Callable[..., dict[str, Any]] | None = None,
    certificate_verifier: Callable[..., dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Run a resumable two-sector threshold audit for one ranked candidate."""

    symmetry_checker = (
        verify_bb_translation_symmetry
        if symmetry_checker is None else symmetry_checker
    )
    replay_loader = (
        load_replayable_sectors if replay_loader is None else replay_loader
    )
    sector_solver = solve_sector if sector_solver is None else sector_solver
    artifact_writer = write_artifact if artifact_writer is None else artifact_writer

    identity = ranked.get("triage_identity")
    if not isinstance(identity, Mapping):
        identity = candidate_identity(ranked)
    canonical_digest = str(identity["canonical_digest"])
    paths = state_paths(config.state_dir, canonical_digest)

    try:
        candidate = _construction_candidate(ranked, canonical_digest)
    except (KeyError, TypeError, ValueError) as exc:
        return {
            "canonical_digest": canonical_digest,
            "status": "UNSUPPORTED",
            "error": str(exc),
        }
    if candidate.get("C_terms") or candidate.get("D_terms"):
        return {
            "canonical_digest": canonical_digest,
            "status": "UNSUPPORTED",
            "error": "XOR sector audit currently supports CSS candidates only",
        }

    symmetry = symmetry_checker(candidate)
    if symmetry.get("verified") is not True:
        artifact = artifact_writer(
            paths["audit"],
            candidate,
            [],
            threshold_only=True,
            translation_symmetry=symmetry,
        )
        return {
            "canonical_digest": canonical_digest,
            "status": artifact["status"],
            "audit_path": str(paths["audit"]),
            "error": "BB translation symmetry audit failed",
        }

    sectors = (
        replay_loader(
            paths["audit"],
            candidate,
            threshold_only=True,
            translation_symmetry=symmetry,
        )
        if config.resume else []
    )
    artifact = artifact_writer(
        paths["audit"],
        candidate,
        sectors,
        threshold_only=True,
        translation_symmetry=symmetry,
    )
    resumed_sectors = len(sectors)
    completed = {str(item.get("sector")) for item in sectors}
    anchors = tuple(int(value) for value in symmetry["orbit_representatives"])
    max_weight = int(candidate["required_distance"]) - 1

    for sector in ("X", "Z"):
        if artifact["status"] in TERMINAL_STATUSES:
            break
        if sector in completed:
            continue
        result = sector_solver((
            candidate,
            sector,
            config.solver_timeout_s,
            max_weight,
            config.solver_workers,
            config.seed,
            anchors,
        ))
        sectors = [
            item for item in sectors
            if str(item.get("sector")) != sector
        ]
        sectors.append(result)
        artifact = artifact_writer(
            paths["audit"],
            candidate,
            sectors,
            threshold_only=True,
            translation_symmetry=symmetry,
        )

    result: dict[str, Any] = {
        "canonical_digest": canonical_digest,
        "status": artifact["status"],
        "audit_path": str(paths["audit"]),
        "completed_sectors": artifact["completed_sectors"],
        "resumed_sectors": resumed_sectors,
    }
    if artifact["status"] == "THRESHOLD_PROVEN" and config.certify:
        try:
            result["certificate"] = certify_candidate(
                candidate,
                canonical_digest,
                config,
                builder=certificate_builder,
                verifier=certificate_verifier,
            )
        except Exception as exc:  # preserve the completed threshold proof
            result["certificate"] = {
                "attempted": True,
                "certificate_passed": False,
                "verification_passed": False,
                "error": f"{type(exc).__name__}: {exc}",
            }
    elif artifact["status"] == "THRESHOLD_PROVEN":
        result["certificate"] = {"attempted": False}
    return result


def _audit_worker(
    payload: tuple[dict[str, Any], AuditConfig],
) -> dict[str, Any]:
    ranked, config = payload
    return audit_candidate(ranked, config)


def audit_selected_candidates(
    selected: list[dict[str, Any]],
    config: AuditConfig,
    *,
    candidate_workers: int,
) -> list[dict[str, Any]]:
    """Audit selected candidates and isolate per-candidate failures."""

    if candidate_workers == 1:
        results = []
        for candidate in selected:
            try:
                results.append(audit_candidate(candidate, config))
            except Exception as exc:
                identity = candidate_identity(candidate)
                results.append({
                    "canonical_digest": identity["canonical_digest"],
                    "status": "ERROR",
                    "error": f"{type(exc).__name__}: {exc}",
                })
        return results

    results = []
    with ProcessPoolExecutor(max_workers=candidate_workers) as executor:
        futures = {
            executor.submit(_audit_worker, (candidate, config)):
            str(candidate["triage_identity"]["canonical_digest"])
            for candidate in selected
        }
        for future in as_completed(futures):
            digest = futures[future]
            try:
                results.append(future.result())
            except Exception as exc:
                results.append({
                    "canonical_digest": digest,
                    "status": "ERROR",
                    "error": f"{type(exc).__name__}: {exc}",
                })
    order = {
        str(candidate["triage_identity"]["canonical_digest"]): index
        for index, candidate in enumerate(selected)
    }
    return sorted(results, key=lambda item: order[item["canonical_digest"]])


def _annotate_ranked(
    ranked: list[dict[str, Any]],
    selected_digests: set[str],
    results: Iterable[Mapping[str, Any]] = (),
) -> list[dict[str, Any]]:
    by_digest = {
        str(result["canonical_digest"]): dict(result)
        for result in results
    }
    annotated = []
    for row in ranked:
        updated = dict(row)
        digest = str(row["triage_identity"]["canonical_digest"])
        updated["campaign_selected"] = digest in selected_digests
        if digest in by_digest:
            updated["campaign_audit"] = by_digest[digest]
        annotated.append(updated)
    return annotated


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inputs", nargs="+", type=Path)
    parser.add_argument("--top", type=int, default=20)
    parser.add_argument("--state-dir", type=Path, required=True)
    parser.add_argument("--ranked-output", type=Path, required=True)
    parser.add_argument("--summary-output", type=Path, required=True)
    parser.add_argument("--timeout", type=float, default=300)
    parser.add_argument("--candidate-workers", type=int, default=2)
    parser.add_argument("--solver-workers", type=int, default=4)
    parser.add_argument("--max-total-workers", type=int, default=8)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument(
        "--resume",
        action=argparse.BooleanOptionalAction,
        default=True,
    )
    parser.add_argument(
        "--certify",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="build and independently rerun an exact certificate after proof",
    )
    parser.add_argument(
        "--known-answer-artifact",
        type=Path,
        default=DEFAULT_KNOWN_ANSWER,
    )
    parser.add_argument(
        "--certificate-timeout-per-logical",
        type=float,
        default=300,
    )
    parser.add_argument(
        "--certificate-total-timeout",
        type=float,
        default=7200,
    )
    parser.add_argument(
        "--verification-timeout-per-logical",
        type=float,
        default=300,
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    if args.top < 0:
        parser.error("top must be non-negative")
    for name in (
        "timeout",
        "certificate_timeout_per_logical",
        "certificate_total_timeout",
        "verification_timeout_per_logical",
    ):
        if getattr(args, name) <= 0:
            parser.error(f"{name.replace('_', '-')} must be positive")
    try:
        validate_worker_budget(
            args.candidate_workers,
            args.solver_workers,
            args.max_total_workers,
        )
        ranked, counts = rank_candidate_files(args.inputs)
    except (OSError, TypeError, ValueError) as exc:
        parser.error(str(exc))

    selected, selection_counts = select_audit_candidates(
        ranked, args.top,
    )
    selected_digests = {
        str(row["triage_identity"]["canonical_digest"])
        for row in selected
    }
    atomic_write_jsonl(
        args.ranked_output,
        _annotate_ranked(ranked, selected_digests),
    )

    config = AuditConfig(
        state_dir=args.state_dir,
        solver_timeout_s=args.timeout,
        solver_workers=args.solver_workers,
        seed=args.seed,
        resume=args.resume,
        certify=args.certify,
        known_answer_artifact=args.known_answer_artifact,
        certificate_timeout_per_logical_s=(
            args.certificate_timeout_per_logical
        ),
        certificate_total_timeout_s=args.certificate_total_timeout,
        verification_timeout_per_logical_s=(
            args.verification_timeout_per_logical
        ),
    )
    results = audit_selected_candidates(
        selected,
        config,
        candidate_workers=args.candidate_workers,
    )
    annotated = _annotate_ranked(ranked, selected_digests, results)
    atomic_write_jsonl(args.ranked_output, annotated)

    status_counts: dict[str, int] = {}
    for result in results:
        status = str(result["status"])
        status_counts[status] = status_counts.get(status, 0) + 1
    certified = sum(
        result.get("certificate", {}).get("certificate_passed") is True
        and result.get("certificate", {}).get("verification_passed") is True
        for result in results
    )
    summary = {
        "schema_version": 1,
        "gate": "qldpc-proof-oriented-candidate-pool",
        "inputs": [str(path) for path in args.inputs],
        **counts,
        **selection_counts,
        "selected_candidates": len(selected),
        "top": args.top,
        "worker_budget": {
            "candidate_workers": args.candidate_workers,
            "solver_workers": args.solver_workers,
            "max_total_workers": args.max_total_workers,
            "configured_solver_workers": (
                args.candidate_workers * args.solver_workers
            ),
        },
        "certify": args.certify,
        "status_counts": status_counts,
        "certified_wins": certified,
        "ranked_output": str(args.ranked_output),
        "state_dir": str(args.state_dir),
        "results": results,
    }
    atomic_write_json(args.summary_output, summary)
    print(json.dumps(summary, indent=2))
    return 0 if not any(
        result["status"] == "ERROR" for result in results
    ) else 2


if __name__ == "__main__":
    raise SystemExit(main())
