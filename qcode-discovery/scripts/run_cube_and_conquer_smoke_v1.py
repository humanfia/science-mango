#!/usr/bin/env python3
"""CLI for the TEST_ONLY proof-carrying Cube-and-Conquer smoke test."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from evaluation import cube_and_conquer_smoke_v1 as smoke  # noqa: E402


DEFAULT_CADICAL = Path("/root/cadical-rel-1.9.5-standalone-audit/build/cadical")
DEFAULT_DRAT_TRIM = Path("/root/qcode-proof-tools/bin/drat-trim")
DEFAULT_LRAT_CHECK = Path("/root/qcode-proof-tools/bin/lrat-check")


def _split_variables(value: str) -> tuple[int, ...]:
    try:
        variables = tuple(int(item) for item in value.split(",") if item)
    except ValueError as exc:
        raise argparse.ArgumentTypeError("split variables must be comma-separated integers") from exc
    if not variables:
        raise argparse.ArgumentTypeError("at least one split variable is required")
    return variables


def _tools(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--cadical", type=Path, default=DEFAULT_CADICAL)
    parser.add_argument("--drat-trim", type=Path, default=DEFAULT_DRAT_TRIM)
    parser.add_argument("--lrat-check", type=Path, default=DEFAULT_LRAT_CHECK)
    parser.add_argument("--timeout", type=int, default=30)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="action", required=True)
    run = subparsers.add_parser("run", help="build and solve a fresh smoke bundle")
    run.add_argument("--input", type=Path, required=True)
    run.add_argument("--output", type=Path, required=True)
    run.add_argument("--split-vars", type=_split_variables, required=True)
    run.add_argument("--workers", type=int, default=1)
    _tools(run)
    verify = subparsers.add_parser("verify", help="freshly replay a completed bundle")
    verify.add_argument("--root", type=Path, required=True)
    verify.add_argument("--report", type=Path, default=Path("verification.json"))
    _tools(verify)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        if args.action == "run":
            result = smoke.run_bundle(
                input_cnf=args.input,
                output_root=args.output,
                split_variables=args.split_vars,
                workers=args.workers,
                cadical=args.cadical,
                drat_trim=args.drat_trim,
                lrat_check=args.lrat_check,
                timeout_s=args.timeout,
            )
        else:
            result = smoke.verify_bundle(
                args.root,
                cadical=args.cadical,
                drat_trim=args.drat_trim,
                lrat_check=args.lrat_check,
                timeout_s=args.timeout,
                report_path=args.report,
            )
    except (OSError, ValueError, smoke.CubeAndConquerSmokeError) as exc:
        print(f"UNRESOLVED: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(result, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
