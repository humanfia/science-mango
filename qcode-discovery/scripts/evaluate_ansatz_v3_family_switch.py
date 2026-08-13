#!/usr/bin/env python3
"""Fail-closed CLI for the manual post-ansatz family-transition gate."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


PROJECT = Path(__file__).resolve().parents[1]
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from evaluation.ansatz_v3_contract import (  # noqa: E402
    family_switch_decision,
    load_finite_domain_contract,
)
from evaluation.formal_audit_quota import load_quota_contract  # noqa: E402


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("evidence", type=Path)
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
    finite = load_finite_domain_contract(args.finite_domain)
    quota = load_quota_contract(
        args.formal_audit_quota,
        representation_id=finite["representation_id"],
        rounds=finite["search_budget"]["rounds"],
    )
    evidence = json.loads(args.evidence.read_text(encoding="utf-8"))
    decision = family_switch_decision(
        evidence,
        contract=finite,
        quota_contract=quota,
    )
    if args.output.exists() or args.output.is_symlink():
        parser.error("output already exists; decisions are immutable")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(decision, ensure_ascii=False, sort_keys=True, indent=2) + "\n",
        encoding="utf-8",
    )
    return 0 if decision["eligible_for_manual_family_transition"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
