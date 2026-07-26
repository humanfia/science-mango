#!/usr/bin/env python3
"""Search sparse CSS/BB codes with proof-oriented, resumable screening.

The wide lane can mix uniform supports with bounded mutations of algebraic
frontier templates. Canonical structures are claimed in a shared SQLite
registry before any logical MILP, so equivalent candidates from different
shards are proved only once. Search evidence is explicit about upper versus
lower distance bounds; a large timeout incumbent is never reported as an exact
FOM.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from pathlib import Path
from typing import Any

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.bb_code import build_bb_code
from evaluation.campaign_dedup import CampaignDedup
from evaluation.certificate import (
    _direction_specs,
    pack_vector,
    solve_css_below_threshold,
    solve_css_direction,
    solve_css_sector_xor,
    verify_css_sector_witness,
    verify_css_witness,
)
from evaluation.certificate_dispatch import build_certificate, verify_certificate
from evaluation.distance_milp import get_code_matrices
from evaluation.final_gate import _connected, minimum_winning_distance
from evaluation.registry import check_code_novelty
from evaluation.search_sampling import sample_bb_supports


DEFAULT_SPLITS = ((2, 2), (2, 3), (3, 2), (2, 4), (4, 2), (3, 3))
STATE_SCHEMA_VERSION = 1


def parse_term_splits(value: str) -> tuple[tuple[int, int], ...]:
    try:
        splits = tuple(
            tuple(int(part) for part in item.split("+"))
            for item in value.split(",")
        )
    except ValueError as exc:
        raise argparse.ArgumentTypeError(
            "term splits must look like 2+2,3+3",
        ) from exc
    if (
        not splits
        or any(len(item) != 2 for item in splits)
        or any(a < 2 or b < 2 or a + b > 6 for a, b in splits)
    ):
        raise argparse.ArgumentTypeError(
            "each BB support needs at least two terms and total weight at most 6",
        )
    return splits


def parse_shapes(value: str) -> tuple[tuple[int, int], ...]:
    try:
        shapes = tuple(
            tuple(int(part) for part in item.lower().split("x"))
            for item in value.split(",")
        )
    except ValueError as exc:
        raise argparse.ArgumentTypeError(
            "shapes must look like 6x6,9x6",
        ) from exc
    if (
        not shapes
        or any(len(item) != 2 for item in shapes)
        or any(ell < 2 or m < 2 for ell, m in shapes)
    ):
        raise argparse.ArgumentTypeError(
            "each lattice shape must be at least 2x2",
        )
    return shapes


def sample_css_claim(
    rng: np.random.Generator,
    shapes: tuple[tuple[int, int], ...],
    splits: tuple[tuple[int, int], ...],
    *,
    seed: int,
    trial: int,
    sampler: str = "uniform",
    structured_probability: float = 0.7,
    structured_max_mutations: int = 1,
    mutation_radius: int = 1,
    template_labels: tuple[str, ...] | None = None,
) -> dict[str, Any]:
    ell, m = shapes[int(rng.integers(len(shapes)))]
    kwargs: dict[str, Any] = {
        "rng": rng,
        "return_metadata": True,
    }
    if sampler == "uniform":
        kwargs["splits"] = splits
    elif sampler == "structured-frontier":
        kwargs.update({
            "template_labels": template_labels,
            "max_mutations": structured_max_mutations,
            "mutation_radius": mutation_radius,
        })
    elif sampler == "mixed":
        kwargs.update({
            "uniform_splits": splits,
            "structured_probability": structured_probability,
            "template_labels": template_labels,
            "max_mutations": structured_max_mutations,
            "mutation_radius": mutation_radius,
        })
    else:
        raise ValueError(f"unsupported sampler: {sampler}")

    a_terms, b_terms, sampling = sample_bb_supports(
        sampler, ell, m, **kwargs,
    )
    return {
        "source": (
            f"expanded-css-{sampler} seed={seed} trial={trial}"
        ),
        "ell": ell,
        "m": m,
        "A_terms": [list(term) for term in a_terms],
        "B_terms": [list(term) for term in b_terms],
        "sampling": sampling,
    }


def candidate_key(claim: dict[str, Any]) -> tuple[Any, ...]:
    return (
        int(claim["ell"]),
        int(claim["m"]),
        tuple(sorted(map(tuple, claim["A_terms"]))),
        tuple(sorted(map(tuple, claim["B_terms"]))),
    )


def _atomic_write_json(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def _resume_config(args: argparse.Namespace) -> dict[str, Any]:
    return {
        "schema_version": STATE_SCHEMA_VERSION,
        "seed": args.seed,
        "shapes": [list(item) for item in args.shapes],
        "term_splits": [list(item) for item in args.term_splits],
        "sampler": args.sampler,
        "structured_probability": args.structured_probability,
        "structured_max_mutations": args.structured_max_mutations,
        "mutation_radius": args.mutation_radius,
        "template_labels": list(args.template_labels or ()),
        "screen_mode": args.screen_mode,
        "shard_count": args.shard_count,
        "shard_index": args.shard_index,
    }


def _load_existing_keys(path: Path) -> set[tuple[Any, ...]]:
    keys: set[tuple[Any, ...]] = set()
    if not path.exists():
        return keys
    with path.open() as stream:
        for line in stream:
            try:
                row = json.loads(line)
                claim = row.get("claim")
                if isinstance(claim, dict):
                    keys.add(candidate_key(claim))
            except (OSError, TypeError, ValueError):
                continue
    return keys


def _load_persisted_digests(path: Path) -> set[str]:
    """Recover digests whose evidence was durable before a crash."""

    digests: set[str] = set()
    if not path.exists():
        return digests
    with path.open() as stream:
        for line in stream:
            try:
                row = json.loads(line)
            except (OSError, TypeError, ValueError):
                continue
            digest = row.get("canonical_digest")
            if digest:
                digests.add(str(digest))
    return digests


def _load_state(
    path: Path,
    *,
    expected_config: dict[str, Any],
) -> tuple[int, dict[str, int]]:
    if not path.exists():
        return 0, {}
    state = json.loads(path.read_text())
    if state.get("schema_version") != STATE_SCHEMA_VERSION:
        raise ValueError("unsupported expanded-search state schema")
    if state.get("config") != expected_config:
        raise ValueError("resume state configuration does not match this run")
    return int(state.get("next_trial", 0)), {
        str(key): int(value)
        for key, value in dict(state.get("stats", {})).items()
    }


def _direction_evidence(
    result: dict[str, Any],
    *,
    logical_type: str,
    index: int,
    check_name: str,
    checks: np.ndarray,
    target: np.ndarray,
) -> dict[str, Any]:
    failures = (
        verify_css_witness(result, checks, target)
        if result.get("operator") is not None else []
    )
    return {
        **result,
        "logical_type": logical_type,
        "logical_index": index,
        "check_matrix": check_name,
        "target_logical": pack_vector(target),
        "witness_verified": (
            result.get("operator") is not None and not failures
        ),
        "witness_failures": failures,
    }


def _xor_prefilter(
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
    *,
    required_distance: int,
    timeout_per_sector: float,
    workers: int,
    seed: int,
) -> tuple[str, list[dict[str, Any]]]:
    """Look for a cheap global-sector counterexample before direction MILPs."""

    sectors: list[dict[str, Any]] = []
    for offset, (sector, checks, targets) in enumerate((
        ("X", hz, lz),
        ("Z", hx, lx),
    )):
        evidence = solve_css_sector_xor(
            checks,
            targets,
            timeout=timeout_per_sector,
            max_weight=required_distance - 1,
            workers=workers,
            seed=seed + offset,
        )
        failures = (
            verify_css_sector_witness(evidence, checks, targets)
            if evidence.get("operator") is not None else []
        )
        evidence = {
            **evidence,
            "sector": sector,
            "logical_count": len(targets),
            "witness_verified": (
                evidence.get("operator") is not None and not failures
            ),
            "witness_failures": failures,
        }
        sectors.append(evidence)
        if (
            evidence["witness_verified"] is True
            and evidence.get("objective") is not None
            and int(evidence["objective"]) < required_distance
        ):
            return "REJECTED", sectors
    if len(sectors) == 2 and all(
        item.get("threshold_infeasible") is True
        and int(item.get("max_weight", -1)) == required_distance - 1
        for item in sectors
    ):
        return "THRESHOLD_PROVEN", sectors
    return "UNRESOLVED", sectors


def _screen_code(
    code: Any,
    *,
    required_distance: int,
    screen_mode: str,
    timeout_per_logical: float,
    total_timeout_per_code: float,
) -> tuple[str, list[dict[str, Any]], bool]:
    directions: list[dict[str, Any]] = []
    specs = _direction_specs(code)
    started = time.monotonic()
    for logical_type, index, check_name, checks, target in specs:
        remaining = total_timeout_per_code - (time.monotonic() - started)
        if remaining <= 0:
            return "UNRESOLVED", directions, False
        timeout = min(timeout_per_logical, remaining)
        if screen_mode == "threshold":
            result = solve_css_below_threshold(
                checks,
                target,
                max_weight=required_distance - 1,
                timeout=timeout,
            )
        else:
            result = solve_css_direction(checks, target, timeout=timeout)
        evidence = _direction_evidence(
            result,
            logical_type=logical_type,
            index=index,
            check_name=check_name,
            checks=checks,
            target=target,
        )
        directions.append(evidence)
        low_witness = (
            evidence["witness_verified"] is True
            and evidence.get("objective") is not None
            and int(evidence["objective"]) < required_distance
        )
        if low_witness:
            return "REJECTED", directions, False
        if screen_mode == "threshold":
            if evidence.get("threshold_infeasible") is not True:
                return "UNRESOLVED", directions, False
        elif not (
            evidence.get("success") is True
            and evidence.get("mip_gap") == 0.0
            and evidence.get("objective") is not None
        ):
            return "UNRESOLVED", directions, False

    if len(directions) != len(specs):
        return "UNRESOLVED", directions, False
    return (
        ("THRESHOLD_PROVEN", directions, False)
        if screen_mode == "threshold"
        else ("EXACT_PROVEN", directions, True)
    )


def _complete_claim(
    dedup: CampaignDedup | None,
    digest: str,
    stats: dict[str, int],
) -> None:
    if dedup is not None and not dedup.complete(digest):
        stats["dedup_completion_lost"] += 1


def _evaluate_claim(
    claim: dict[str, Any],
    *,
    trial: int,
    args: argparse.Namespace,
    seen: set[tuple[Any, ...]],
    dedup: CampaignDedup | None,
    stats: dict[str, int],
) -> tuple[dict[str, Any], Any] | None:
    key = candidate_key(claim)
    if key in seen:
        stats["local_duplicate"] += 1
        return None
    seen.add(key)
    stats["sampled"] += 1
    try:
        code = build_bb_code(
            claim["ell"], claim["m"], claim["A_terms"], claim["B_terms"],
        )
    except (TypeError, ValueError):
        stats["invalid"] += 1
        return None

    n, k = int(code.num_qudits), int(code.dimension)
    if k <= 0:
        stats["nonpositive_k"] += 1
        return None
    hx = np.asarray(code.matrix_x, dtype=np.uint8) & 1
    hz = np.asarray(code.matrix_z, dtype=np.uint8) & 1
    support = np.vstack((hx, hz))
    connected, components = _connected(support)
    max_weight = int(support.sum(axis=1).max(initial=0))
    max_degree = int(support.sum(axis=0).max(initial=0))
    if not connected or max_weight > 6 or max_degree > 6:
        stats["static_rejected"] += 1
        return None
    stats["static_pass"] += 1

    # Canonicalization is intentionally before logical-basis construction and
    # MILP. This is the expensive-work ownership boundary shared by shards.
    novelty = check_code_novelty(code, code_type="css")
    digest = str(novelty["canonical_digest"])
    if novelty.get("novel") is not True:
        stats["registry_known"] += 1
        return None
    if dedup is not None and not dedup.claim(
        digest,
        source=f"seed={args.seed}/shard={args.shard_index}",
        metadata={"trial": trial, "claim": claim},
    ):
        stats["cross_shard_duplicate"] += 1
        return None
    stats["canonical_unique"] += 1

    _, _, lx, lz = (
        np.asarray(value, dtype=np.uint8) & 1
        for value in get_code_matrices(code)
    )
    if len(lx) != k or len(lz) != k:
        stats["logical_basis_rejected"] += 1
        _complete_claim(dedup, digest, stats)
        return None
    required_distance = minimum_winning_distance(n, k)
    basis_weights = [
        int(row.sum()) for row in np.vstack((lx, lz)) if row.any()
    ]
    basis_bound = min(basis_weights, default=0)
    if basis_bound < required_distance:
        stats["basis_bound_rejected"] += 1
        _complete_claim(dedup, digest, stats)
        return None
    stats["basis_bound_pass"] += 1

    sectors: list[dict[str, Any]] = []
    prefilter_status = "DISABLED"
    if args.xor_prefilter_timeout > 0:
        stats["xor_prefilter_attempted"] += 1
        prefilter_status, sectors = _xor_prefilter(
            hx,
            hz,
            lx,
            lz,
            required_distance=required_distance,
            timeout_per_sector=args.xor_prefilter_timeout,
            workers=args.xor_prefilter_workers,
            seed=args.seed + trial * 2,
        )
    if prefilter_status in {"REJECTED", "THRESHOLD_PROVEN"}:
        status, directions, exact = prefilter_status, [], False
        stats[f"xor_prefilter_{prefilter_status.lower()}"] += 1
    else:
        stats["milp_attempted"] += 1
        status, directions, exact = _screen_code(
            code,
            required_distance=required_distance,
            screen_mode=args.screen_mode,
            timeout_per_logical=args.timeout_per_logical,
            total_timeout_per_code=args.total_timeout_per_code,
        )
    stats[status.lower()] += 1
    verified_objectives = [
        int(item["objective"])
        for item in [*sectors, *directions]
        if item.get("witness_verified") is True
        and item.get("objective") is not None
    ]
    distance_upper_bound = min(verified_objectives, default=None)
    exact_distance = (
        distance_upper_bound
        if exact and len(directions) == 2 * k else None
    )
    distance_lower_bound = (
        int(exact_distance)
        if exact_distance is not None
        else required_distance if status == "THRESHOLD_PROVEN" else 0
    )
    fom_exact = (
        k * exact_distance * exact_distance / n
        if exact_distance is not None else None
    )
    fom_upper = (
        k * distance_upper_bound * distance_upper_bound / n
        if distance_upper_bound is not None else None
    )
    fom_lower = k * distance_lower_bound * distance_lower_bound / n
    record = {
        "schema_version": 2,
        "trial": trial,
        "search_seed": args.seed,
        "shard_index": args.shard_index,
        "shard_count": args.shard_count,
        "ansatz": "css-sparse-bb",
        "claim": claim,
        "n": n,
        "k": k,
        "required_distance": required_distance,
        "basis_bound": basis_bound,
        "screen_mode": args.screen_mode,
        "xor_prefilter_status": prefilter_status,
        "status": status,
        "distance": exact_distance if exact_distance is not None else 0,
        "distance_lower_bound": distance_lower_bound,
        "distance_upper_bound": distance_upper_bound,
        "exact": exact_distance is not None,
        "d_is_exact": exact_distance is not None,
        "fom": fom_exact,
        "fom_lower_bound": fom_lower,
        "fom_upper_bound": fom_upper,
        "max_row_weight": max_weight,
        "max_qubit_degree": max_degree,
        "tanner_components": components,
        "novelty": novelty,
        "canonical_digest": digest,
        "witnesses_self_contained": bool(sectors or directions) and all(
            item.get("operator") is None
            or item.get("witness_verified") is True
            for item in [*sectors, *directions]
        ),
        "expected_directions": 2 * k,
        "completed_directions": len(directions),
        "completed_sectors": len(sectors),
        "sectors": sectors,
        "directions": directions,
    }
    return record, code


def _certify(
    record: dict[str, Any],
    *,
    args: argparse.Namespace,
) -> tuple[dict[str, Any], bool]:
    claim = record["claim"]
    certificate_claim = {
        "source": claim["source"],
        "ell": claim["ell"],
        "m": claim["m"],
        "A_terms": claim["A_terms"],
        "B_terms": claim["B_terms"],
    }
    certificate = build_certificate(
        certificate_claim,
        known_answer_artifact=args.known_answer_artifact,
        timeout_per_logical=args.certificate_timeout_per_logical,
        total_timeout=args.certificate_total_timeout,
    )
    digest = str(record["canonical_digest"]).replace(":", "_")
    path = args.certificate_dir / f"{digest}.json"
    _atomic_write_json(path, certificate)
    verification = {"passed": False, "failures": ["exact certificate incomplete"]}
    if certificate.get("passed") is True:
        verification = verify_certificate(
            certificate,
            known_answer_artifact=args.known_answer_artifact,
            rerun_milp=True,
            timeout_per_logical=args.certificate_timeout_per_logical,
        )
    summary = {
        "attempted": True,
        "certificate": str(path),
        "certificate_passed": certificate.get("passed") is True,
        "independently_verified": verification.get("passed") is True,
        "exact_distance": certificate.get("milp", {}).get("distance"),
        "failures": verification.get("failures", []),
    }
    return summary, bool(
        certificate.get("passed") is True
        and verification.get("passed") is True
    )


def _persist_record(stream: Any, record: dict[str, Any]) -> None:
    """Durably append one JSONL record."""

    stream.write(json.dumps(record) + "\n")
    stream.flush()
    os.fsync(stream.fileno())


def _persist_and_complete(
    stream: Any,
    record: dict[str, Any],
    dedup: CampaignDedup | None,
    stats: dict[str, int],
) -> None:
    """Make completion permanent only after its evidence is durable."""

    _persist_record(stream, record)
    _complete_claim(dedup, record["canonical_digest"], stats)


def main() -> int:
    project = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--shapes", type=parse_shapes,
        default=((6, 6), (9, 6), (12, 6)),
    )
    parser.add_argument(
        "--term-splits", type=parse_term_splits, default=DEFAULT_SPLITS,
    )
    parser.add_argument("--trials", type=int, default=2000)
    parser.add_argument("--seed", type=int, default=20260728)
    parser.add_argument(
        "--sampler",
        choices=("uniform", "structured-frontier", "mixed"),
        default="mixed",
    )
    parser.add_argument("--structured-probability", type=float, default=0.7)
    parser.add_argument("--structured-max-mutations", type=int, default=2)
    parser.add_argument("--mutation-radius", type=int, default=1)
    parser.add_argument(
        "--template-labels",
        help="comma-separated structured template labels",
    )
    parser.add_argument(
        "--screen-mode", choices=("exact", "threshold"), default="exact",
    )
    parser.add_argument(
        "--xor-prefilter-timeout",
        type=float,
        default=1.0,
        help="CP-SAT seconds per global sector; zero disables the prefilter",
    )
    parser.add_argument("--xor-prefilter-workers", type=int, default=1)
    parser.add_argument("--timeout-per-logical", type=float, default=20)
    parser.add_argument("--total-timeout-per-code", type=float, default=300)
    parser.add_argument("--shard-count", type=int, default=1)
    parser.add_argument("--shard-index", type=int, default=0)
    parser.add_argument(
        "--dedup-db",
        type=Path,
        help="shared SQLite path used by every shard",
    )
    parser.add_argument(
        "--resume",
        action=argparse.BooleanOptionalAction,
        default=True,
    )
    parser.add_argument("--checkpoint-interval", type=int, default=100)
    parser.add_argument("--state-file", type=Path)
    parser.add_argument(
        "--auto-certify",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="build and independently verify an exact certificate after a threshold proof",
    )
    parser.add_argument(
        "--certificate-timeout-per-logical", type=float, default=300,
    )
    parser.add_argument("--certificate-total-timeout", type=float, default=7200)
    parser.add_argument(
        "--known-answer-artifact",
        type=Path,
        default=project / "results" / "known_answer_gate.json",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=project / "results" / "expanded_ansatz_search.jsonl",
    )
    parser.add_argument(
        "--certificate-dir",
        type=Path,
        default=project / "results" / "expanded_ansatz_certificates",
    )
    args = parser.parse_args()

    if args.trials < 1:
        parser.error("trials must be positive")
    if (
        args.xor_prefilter_timeout < 0
        or args.timeout_per_logical <= 0
        or args.total_timeout_per_code <= 0
        or args.certificate_timeout_per_logical <= 0
        or args.certificate_total_timeout <= 0
    ):
        parser.error(
            "MILP/certificate timeouts must be positive and "
            "xor-prefilter-timeout must be non-negative"
        )
    if not 1 <= args.xor_prefilter_workers <= 8:
        parser.error("xor-prefilter-workers must be between 1 and 8")
    if not 0.0 <= args.structured_probability <= 1.0:
        parser.error("structured-probability must lie in [0, 1]")
    if args.structured_max_mutations < 0 or args.mutation_radius < 1:
        parser.error("structured mutation parameters are invalid")
    if args.shard_count < 1 or not 0 <= args.shard_index < args.shard_count:
        parser.error("shard-index must lie in [0, shard-count)")
    if args.checkpoint_interval < 1:
        parser.error("checkpoint-interval must be positive")
    args.template_labels = (
        tuple(
            item.strip() for item in args.template_labels.split(",")
            if item.strip()
        )
        if args.template_labels else None
    )
    args.state_file = args.state_file or args.output.with_suffix(
        args.output.suffix + ".state.json",
    )
    config = _resume_config(args)
    stats = {
        "sampled": 0,
        "local_duplicate": 0,
        "invalid": 0,
        "nonpositive_k": 0,
        "static_rejected": 0,
        "static_pass": 0,
        "registry_known": 0,
        "cross_shard_duplicate": 0,
        "canonical_unique": 0,
        "dedup_completion_lost": 0,
        "logical_basis_rejected": 0,
        "basis_bound_rejected": 0,
        "basis_bound_pass": 0,
        "xor_prefilter_attempted": 0,
        "xor_prefilter_rejected": 0,
        "xor_prefilter_threshold_proven": 0,
        "milp_attempted": 0,
        "rejected": 0,
        "unresolved": 0,
        "threshold_proven": 0,
        "exact_proven": 0,
        "certificates_attempted": 0,
        "wins": 0,
    }
    start_trial = 0
    if args.resume:
        try:
            start_trial, resumed_stats = _load_state(
                args.state_file, expected_config=config,
            )
        except (OSError, TypeError, ValueError) as exc:
            parser.error(str(exc))
        stats.update(resumed_stats)
    if start_trial > args.trials:
        parser.error(
            "trials cannot be smaller than the saved next_trial; "
            "use --no-resume for a new run"
        )
    if start_trial > 0 and not args.output.exists():
        parser.error(
            "resume state exists but the JSONL output is missing; "
            "restore it or use --no-resume"
        )

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.certificate_dir.mkdir(parents=True, exist_ok=True)
    seen = _load_existing_keys(args.output) if args.resume else set()
    stream_mode = "a" if args.resume and args.output.exists() else "w"
    if stream_mode == "a" and args.output.stat().st_size:
        with args.output.open("rb+") as recovery_stream:
            recovery_stream.seek(-1, 2)
            if recovery_stream.read(1) != b"\n":
                # Preserve an interrupted fragment for audit, but ensure the
                # next complete record starts on its own JSONL line.
                recovery_stream.seek(0, 2)
                recovery_stream.write(b"\n")
    dedup = (
        CampaignDedup(
            args.dedup_db,
            lease_seconds=max(
                60.0,
                args.total_timeout_per_code
                + 2 * args.xor_prefilter_timeout + 60.0,
            ),
            owner_id=(
                f"seed={args.seed}/shards={args.shard_count}"
                f"/shard={args.shard_index}"
            ),
        )
        if args.dedup_db else None
    )
    if dedup is not None and args.resume:
        for persisted_digest in _load_persisted_digests(args.output):
            # The stable shard owner closes the fsync->complete crash window.
            # A digest already completed or reclaimed by another owner is safe.
            dedup.complete(persisted_digest)
    dedup_summary = None
    processed_since_checkpoint = 0
    started = time.monotonic()

    def checkpoint(next_trial: int) -> None:
        _atomic_write_json(args.state_file, {
            "schema_version": STATE_SCHEMA_VERSION,
            "config": config,
            "next_trial": next_trial,
            "stats": stats,
        })

    try:
        with args.output.open(stream_mode) as stream:
            for trial in range(start_trial, args.trials):
                if trial % args.shard_count != args.shard_index:
                    continue
                trial_rng = np.random.default_rng(
                    np.random.SeedSequence([args.seed, trial]),
                )
                claim = sample_css_claim(
                    trial_rng,
                    args.shapes,
                    args.term_splits,
                    seed=args.seed,
                    trial=trial,
                    sampler=args.sampler,
                    structured_probability=args.structured_probability,
                    structured_max_mutations=args.structured_max_mutations,
                    mutation_radius=args.mutation_radius,
                    template_labels=args.template_labels,
                )
                evaluated = _evaluate_claim(
                    claim,
                    trial=trial,
                    args=args,
                    seen=seen,
                    dedup=dedup,
                    stats=stats,
                )
                won = False
                next_trial = trial + 1
                if evaluated is not None:
                    record, _ = evaluated
                    needs_certificate = (
                        args.auto_certify
                        and record["status"] in {
                            "THRESHOLD_PROVEN", "EXACT_PROVEN",
                        }
                        and record["novelty"].get("novel") is True
                        and record["fom_lower_bound"] > 12
                    )
                    claim_completed = False
                    if needs_certificate:
                        # Persist the threshold proof and advance campaign
                        # state before the potentially hours-long exact build.
                        # If certification is interrupted, the audit lane can
                        # resume from this self-contained candidate record.
                        stats["certificates_attempted"] += 1
                        _persist_and_complete(
                            stream, record, dedup, stats,
                        )
                        claim_completed = True
                        checkpoint(next_trial)
                        processed_since_checkpoint = 0
                        record["certification"], won = _certify(
                            record, args=args,
                        )
                    if claim_completed:
                        _persist_record(stream, record)
                    else:
                        _persist_and_complete(
                            stream, record, dedup, stats,
                        )
                    if won:
                        stats["wins"] += 1
                processed_since_checkpoint += 1
                if processed_since_checkpoint >= args.checkpoint_interval or won:
                    checkpoint(next_trial)
                    processed_since_checkpoint = 0
                if won:
                    print(json.dumps({
                        "status": "WIN",
                        "trial": trial,
                        "n": record["n"],
                        "k": record["k"],
                        "certificate": record["certification"]["certificate"],
                        "stats": stats,
                    }, indent=2))
                    return 0
        checkpoint(args.trials)
        if dedup is not None:
            dedup_summary = dedup.stats()
    finally:
        if dedup is not None:
            dedup.close()

    print(json.dumps({
        "status": "NO_WIN",
        "elapsed_s": time.monotonic() - started,
        "ansatz": {
            "family": "css-sparse-bb",
            "sampler": args.sampler,
            "shapes": args.shapes,
            "term_splits": args.term_splits,
            "screen_mode": args.screen_mode,
            "shard": [args.shard_index, args.shard_count],
        },
        "stats": stats,
        "dedup": dedup_summary,
        "output": str(args.output),
        "state": str(args.state_file),
    }, indent=2))
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
