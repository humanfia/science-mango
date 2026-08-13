#!/usr/bin/env python3
"""Seal the realized finite candidate/audit domain of an ansatz-v3 run."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path
from typing import Any


PROJECT = Path(__file__).resolve().parents[1]
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from evaluation.ansatz_v3_contract import load_finite_domain_contract  # noqa: E402
from evaluation.formal_audit_quota import (  # noqa: E402
    candidate_audit_strata,
    load_quota_contract,
    validate_selection_report,
)
from evaluation.search_contract import (  # noqa: E402
    PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID,
)
from humanize.state import code_key  # noqa: E402


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _canonical_sha256(value: Any) -> str:
    return hashlib.sha256(json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")).hexdigest()


def _json_object(path: Path, label: str) -> dict[str, Any]:
    if path.is_symlink() or not path.is_file():
        raise ValueError(f"{label} must be a regular file: {path}")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot read {label}: {exc}") from exc
    if not isinstance(value, dict):
        raise ValueError(f"{label} must contain an object")
    return value


def _jsonl(path: Path, label: str) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    if path.is_symlink() or not path.is_file():
        raise ValueError(f"{label} must be a regular file: {path}")
    payload = path.read_bytes()
    if payload and not payload.endswith(b"\n"):
        raise ValueError(f"{label} ends in a partial row")
    rows = []
    for number, line in enumerate(payload.splitlines(), 1):
        if not line:
            continue
        try:
            row = json.loads(line)
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise ValueError(f"{label}:{number} is invalid: {exc}") from exc
        if not isinstance(row, dict):
            raise ValueError(f"{label}:{number} is not an object")
        rows.append(row)
    return rows, {
        "path": str(path.resolve()),
        "sha256": hashlib.sha256(payload).hexdigest(),
        "bytes": len(payload),
        "rows": len(rows),
    }


def build_manifest(
    run_root: Path,
    *,
    finite_domain_path: Path,
    quota_path: Path,
) -> dict[str, Any]:
    run_root = run_root.resolve()
    state_path = run_root / "state.json"
    state = _json_object(state_path, "Stage-1 state")
    config = state.get("config")
    if not isinstance(config, dict):
        raise ValueError("Stage-1 state has no config")
    finite = load_finite_domain_contract(
        finite_domain_path,
        representation_id=PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID,
        rounds=config.get("max_rounds"),
        iterations_per_round=config.get("iterations_per_round"),
    )
    quota = load_quota_contract(
        quota_path,
        representation_id=PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID,
        rounds=config.get("max_rounds"),
        slots_per_round=config.get("milp_top"),
    )
    if (
        state.get("status") != "search-complete"
        or state.get("current_round") != finite["search_budget"]["rounds"]
        or state.get("pending_round") is not None
        or state.get("round_phase") is not None
        or config.get("search_representation_id")
        != PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID
        or Path(config.get("finite_search_domain_contract", "")).resolve()
        != Path(finite["contract_path"])
        or Path(config.get("formal_audit_quota_contract", "")).resolve()
        != Path(quota["contract_path"])
    ):
        raise ValueError("Stage-1 run is not a sealed compatible ansatz-v3 domain")

    unique: dict[str, dict[str, Any]] = {}
    source_batches = []
    quota_reports = []
    volume_counts: Counter[str] = Counter()
    lattice_q_counts: Counter[str] = Counter()
    mechanism_counts: Counter[str] = Counter()
    split_counts: Counter[str] = Counter()
    audit_volume_counts: Counter[str] = Counter()
    unfilled_slots = 0
    for number in range(1, finite["search_budget"]["rounds"] + 1):
        round_dir = run_root / "rounds" / f"round-{number:03d}"
        transaction = _json_object(
            round_dir / "evolution-transaction.json",
            f"round {number} transaction",
        )
        rows, identity = _jsonl(
            round_dir / "candidate-batch.jsonl",
            f"round {number} candidate batch",
        )
        if (
            transaction.get("status") != "committed"
            or transaction.get("round") != number
            or transaction.get("candidate_batch_identity") != {
                key: identity[key] for key in ("sha256", "bytes", "rows")
            }
        ):
            raise ValueError(f"round {number} batch is not transaction-bound")
        source_batches.append(identity)
        for row in rows:
            if row.get("search_representation_id") != (
                PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID
            ):
                raise ValueError(f"round {number} contains another representation")
            strata = candidate_audit_strata(row)
            if strata is None:
                raise ValueError(f"round {number} contains malformed BB supports")
            key = code_key(row)
            unique.setdefault(key, dict(row))
            volume_counts[str(strata["published_volume"])] += 1
            lattice_q_counts[
                ":".join(map(str, strata["lattice_q"]))
            ] += 1
            mechanism_counts[str(strata["algebraic_mechanism"])] += 1
            split_counts[str(strata["support_split"])] += 1

        report_path = round_dir / "formal-audit-quota-selection.json"
        report = validate_selection_report(
            _json_object(report_path, f"round {number} quota report"),
            contract=quota,
            round_number=number,
        )
        quota_reports.append({
            "path": str(report_path.resolve()),
            "sha256": _sha256(report_path),
            "report_sha256": report["report_sha256"],
        })
        for slot in report["slots"]:
            if slot["status"] == "FILLED":
                audit_volume_counts[str(slot["volume"])] += 1
            else:
                unfilled_slots += 1

    quota_expected = {
        str(row["volume"]): row["quota"] for row in quota["volume_quotas"]
    }
    quota_complete = (
        unfilled_slots == 0
        and dict(audit_volume_counts) == quota_expected
    )
    manifest = {
        "schema_version": 1,
        "kind": "qcode-ansatz-v3-realized-finite-domain",
        "domain_id": finite["domain_id"],
        "representation_id": finite["representation_id"],
        "family_id": finite["family_id"],
        "run_id": state.get("run_id"),
        "state": {
            "path": str(state_path.resolve()),
            "sha256": _sha256(state_path),
            "status": state["status"],
            "rounds_completed": state["current_round"],
            "pending_round": state.get("pending_round"),
        },
        "finite_domain_contract": {
            "path": finite["contract_path"],
            "sha256": finite["contract_sha256"],
        },
        "formal_audit_quota": {
            "path": quota["contract_path"],
            "sha256": quota["contract_sha256"],
            "complete": quota_complete,
            "unfilled_slots": unfilled_slots,
            "volume_counts": dict(sorted(audit_volume_counts.items())),
        },
        "source_batches": source_batches,
        "quota_reports": quota_reports,
        "total_unique_candidates": len(unique),
        "candidate_key_set_sha256": _canonical_sha256(sorted(unique)),
        "coverage": {
            "volume_counts": dict(sorted(volume_counts.items())),
            "lattice_q_counts": dict(sorted(lattice_q_counts.items())),
            "algebraic_mechanism_counts": dict(sorted(mechanism_counts.items())),
            "support_split_counts": dict(sorted(split_counts.items())),
            "mandatory_volumes_observed": all(
                str(volume) in volume_counts
                for volume in finite["mandatory_formal_audit_volumes"]
            ),
        },
        "manifest_complete": True,
        "family_switch_authorized": False,
        "semantics": (
            "realized finite search domain only; Stage-2 trusted upper-bound "
            "exhaustion and zero unresolved remain separately required"
        ),
    }
    return {**manifest, "manifest_sha256": _canonical_sha256(manifest)}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("run_root", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument(
        "--finite-domain",
        type=Path,
        default=PROJECT / "configs/twisted_torus_ansatz_v3.finite_domain.v1.json",
    )
    parser.add_argument(
        "--formal-audit-quota",
        type=Path,
        default=(
            PROJECT
            / "configs/twisted_torus_ansatz_v3.formal_audit_quota.v1.json"
        ),
    )
    args = parser.parse_args(argv)
    manifest = build_manifest(
        args.run_root,
        finite_domain_path=args.finite_domain,
        quota_path=args.formal_audit_quota,
    )
    if args.output.exists() or args.output.is_symlink():
        parser.error("output already exists; finite-domain manifests are immutable")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(manifest, ensure_ascii=False, sort_keys=True, indent=2) + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
