#!/usr/bin/env python3
"""Export or validate the portable final typed DistQLDPC release."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


# Direct-file bootstrap is intentionally before every project import so that
# ``pinned-python -I -B /absolute/path/to/this/script.py --help`` works.
PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from evaluation.distqldpc_release_replay_v4 import (  # noqa: E402
    DistQLDPCReleaseReplayError,
)
from humanize.distqldpc_release_export_final5 import (  # noqa: E402
    TypedDistQLDPCFinal5ReleaseError,
    export_typed_distqldpc_release,
    validate_typed_distqldpc_release,
)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("export", "validate"):
        command = commands.add_parser(name)
        command.add_argument("--repo-dir", type=Path, required=True)
        command.add_argument("--stage3-artifact", type=Path, required=True)
        command.add_argument("--certificate", type=Path, required=True)
        command.add_argument("--verification", type=Path, required=True)
        command.add_argument("--known-answer-artifact", type=Path, required=True)
        command.add_argument("--known-answer-trust", type=Path, required=True)
        command.add_argument("--known-answer-integrity", type=Path, required=True)
        command.add_argument("--run-id", required=True)
        command.add_argument("--expected-candidate-digest", required=True)
        command.add_argument("--expected-certificate-sha256", required=True)
        command.add_argument("--expected-stage3-artifact-sha256", required=True)
        command.add_argument("--expected-stage3-file-sha256", required=True)
        command.add_argument("--expected-certificate-file-sha256", required=True)
        command.add_argument("--expected-verification-file-sha256", required=True)
        command.add_argument(
            "--expected-known-answer-integrity-file-sha256", required=True,
        )
    commands.choices["export"].add_argument(
        "--output-dir", type=Path, required=True,
    )
    commands.choices["validate"].add_argument(
        "--manifest", type=Path, required=True,
    )
    return parser


def main() -> int:
    args = build_parser().parse_args()
    common = {
        "repo_dir": args.repo_dir,
        "stage3_artifact": args.stage3_artifact,
        "certificate_path": args.certificate,
        "verification_path": args.verification,
        "known_answer_artifact": args.known_answer_artifact,
        "known_answer_trust": args.known_answer_trust,
        "known_answer_integrity": args.known_answer_integrity,
        "expected_candidate_digest": args.expected_candidate_digest,
        "expected_certificate_sha256": args.expected_certificate_sha256,
        "expected_stage3_artifact_sha256": args.expected_stage3_artifact_sha256,
        "expected_stage3_file_sha256": args.expected_stage3_file_sha256,
        "expected_certificate_file_sha256": args.expected_certificate_file_sha256,
        "expected_verification_file_sha256": args.expected_verification_file_sha256,
        "expected_known_answer_integrity_file_sha256": (
            args.expected_known_answer_integrity_file_sha256
        ),
    }
    try:
        if args.command == "export":
            result = export_typed_distqldpc_release(
                output_dir=args.output_dir,
                run_id=args.run_id,
                invocation_argv=list(sys.argv),
                **common,
            )
        else:
            result = validate_typed_distqldpc_release(
                args.manifest,
                expected_run_id=args.run_id,
                **common,
            )
        print(json.dumps(result, sort_keys=True))
        return 0 if result.get("status") == "EXPORTED" or result.get("passed") else 1
    except (
        TypedDistQLDPCFinal5ReleaseError,
        DistQLDPCReleaseReplayError,
        KeyError,
        OSError,
        TypeError,
        ValueError,
    ) as exc:
        print(json.dumps({
            "status": "FAILED",
            "classification": getattr(exc, "classification", "RELEASE_FAILED"),
            "failures": [str(exc)],
        }, sort_keys=True))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())




