#!/usr/bin/env python3
"""Build or verify a typed DistQLDPC exact CSS BB certificate."""

from __future__ import annotations

import argparse
import json
import os
import sys
import uuid
from pathlib import Path
from typing import Any, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.distance_distqldpc import DEFAULT_DISTQLDPC_EXE
from evaluation.distqldpc_sector_certificate import (
    build_distqldpc_sector_certificate,
    verify_distqldpc_sector_certificate,
)
from evaluation.sector_certificate import (
    REQUEST_FIELD,
    STAGE3_GATE,
    claim_from_sector_sat_artifact,
)


def _load_value(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_claim(path: Path, index: int) -> dict[str, Any]:
    value = _load_value(path)
    if isinstance(value, list):
        if not 0 <= index < len(value) or not isinstance(value[index], Mapping):
            raise ValueError(f"candidate index {index} is unavailable")
        value = value[index]
    if not isinstance(value, Mapping):
        raise ValueError("candidate input must be a JSON object or object list")
    row = dict(value)
    if row.get("gate") == STAGE3_GATE:
        return claim_from_sector_sat_artifact(row)
    if not isinstance(row.get(REQUEST_FIELD), Mapping):
        raise ValueError("build input is not a source-bound Stage-3 claim")
    return row


def _load_certificate(path: Path) -> dict[str, Any]:
    value = _load_value(path)
    if not isinstance(value, Mapping):
        raise ValueError("certificate input must be one JSON object")
    return dict(value)


def _atomic_write_json(path: Path, value: Mapping[str, Any], *, force: bool) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists() and not force:
        raise ValueError(f"output already exists: {path}; pass --force to replace")
    temporary = path.with_name(
        f".{path.name}.{os.getpid()}.{uuid.uuid4().hex}.tmp",
    )
    try:
        with temporary.open("w", encoding="utf-8") as stream:
            json.dump(
                dict(value),
                stream,
                indent=2,
                sort_keys=True,
                ensure_ascii=False,
                allow_nan=False,
            )
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
        try:
            directory_fd = os.open(path.parent, os.O_RDONLY)
        except OSError:
            directory_fd = None
        if directory_fd is not None:
            try:
                os.fsync(directory_fd)
            finally:
                os.close(directory_fd)
    finally:
        temporary.unlink(missing_ok=True)


def _parser() -> argparse.ArgumentParser:
    project = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)

    build = commands.add_parser(
        "build",
        help="statically seal Stage-3 lower evidence and its SAT upper witness",
    )
    build.add_argument("source", type=Path)
    build.add_argument("--index", type=int, default=0)
    build.add_argument("--output", type=Path, required=True)
    build.add_argument(
        "--known-answer-artifact",
        type=Path,
        default=project / "results" / "known_answer_gate.json",
    )
    build.add_argument(
        "--no-rerun",
        action="store_true",
        help="explicitly document that build is static (the only build mode)",
    )
    build.add_argument("--force", action="store_true")

    verify = commands.add_parser(
        "verify",
        help="replay static evidence and run one certificate-bound DistQLDPC lane",
    )
    verify.add_argument("certificate", type=Path)
    verify.add_argument("--output", type=Path, required=True)
    verify.add_argument(
        "--known-answer-artifact",
        type=Path,
        default=project / "results" / "known_answer_gate.json",
    )
    verify.add_argument("--timeout", type=float, default=21600)
    verify.add_argument("--binary", type=Path, default=DEFAULT_DISTQLDPC_EXE)
    verify.add_argument("--checkpoint", type=Path)
    verify.add_argument("--progress", type=Path)
    verify.add_argument(
        "--resume",
        action=argparse.BooleanOptionalAction,
        default=True,
    )
    verify.add_argument(
        "--no-rerun",
        action="store_true",
        help="perform static checks only and return an incomplete replay",
    )
    verify.add_argument("--force", action="store_true")
    return parser


def _build(args: argparse.Namespace) -> int:
    if args.source.resolve() == args.output.resolve():
        raise ValueError("build output must differ from its Stage-3 source")
    claim = _load_claim(args.source, args.index)
    certificate = build_distqldpc_sector_certificate(
        claim,
        known_answer_artifact=args.known_answer_artifact,
    )
    _atomic_write_json(args.output, certificate, force=args.force)
    exact = certificate["distqldpc_exact"]
    print(json.dumps({
        "action": "static-build",
        "passed": certificate["passed"],
        "certificate_sha256": certificate["certificate_sha256"],
        "distance": exact["distance"],
        "fom": certificate["claim"]["fom"],
        "lower_bound_backend": exact["lower_bound_backend"],
        "coverage_mode": exact["coverage_mode"],
        "requested_coverage_mode": exact["requested_coverage_mode"],
        "completed_lower_decisions": exact["completed_lower_decisions"],
        "expected_lower_decisions": exact["expected_lower_decisions"],
        "solver_invocations": 0,
        "independent_replay_required": True,
        "output": str(args.output),
    }, sort_keys=True))
    return 0 if certificate["passed"] else 1


def _verify(args: argparse.Namespace) -> int:
    if args.certificate.resolve() == args.output.resolve():
        raise ValueError("verification output must differ from its certificate")
    certificate = _load_certificate(args.certificate)
    checkpoint = args.checkpoint or args.output.with_suffix(
        args.output.suffix + ".checkpoint.json",
    )
    progress = args.progress or args.output.with_suffix(
        args.output.suffix + ".progress.json",
    )
    report = verify_distqldpc_sector_certificate(
        certificate,
        known_answer_artifact=args.known_answer_artifact,
        rerun=not args.no_rerun,
        timeout=args.timeout,
        binary=args.binary,
        checkpoint_path=checkpoint,
        progress_path=progress,
        resume=args.resume,
    )
    _atomic_write_json(args.output, report, force=args.force)
    print(json.dumps({
        "action": "verify" if not args.no_rerun else "static-verify",
        "passed": report["passed"],
        "replay_complete": report["replay_complete"],
        "distance": report.get("distance"),
        "typed_lower": report.get("typed_lower"),
        "upper": report.get("upper"),
        "novelty": report.get("novelty"),
        "fom_target": report.get("fom_target"),
        "decisions": [
            report.get("distqldpc_decisions_verified"),
            report.get("distqldpc_decisions_total"),
        ],
        "failures": report.get("failures"),
        "output": str(args.output),
    }, sort_keys=True))
    return 0 if report["passed"] else 1


def main() -> int:
    args = _parser().parse_args()
    try:
        return _build(args) if args.command == "build" else _verify(args)
    except (KeyError, OSError, TypeError, ValueError, json.JSONDecodeError) as exc:
        print(f"DISTQLDPC CERTIFICATE {args.command.upper()} FAILED: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
