#!/usr/bin/env python3
"""Freeze the verified ladder decision into two unlaunched work tracks."""

from __future__ import annotations

import argparse
import json
import os
import sys
import tempfile
from pathlib import Path


PROJECT = Path(__file__).resolve().parents[1]
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from evaluation.ansatz_v3_dual_track import build_dual_track_plan  # noqa: E402


def _create_once(path: Path, payload: bytes) -> None:
    if path.exists() or path.is_symlink():
        raise ValueError("output already exists; dual-track plans are immutable")
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        try:
            os.link(temporary, path, follow_symlinks=False)
        except FileExistsError as exc:
            raise ValueError(
                "output appeared concurrently; refusing to replace it"
            ) from exc
        directory_fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    finally:
        temporary.unlink(missing_ok=True)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("diagnostic_dir", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument(
        "--preregistration",
        type=Path,
        default=(
            PROJECT / "configs/twisted_torus_ansatz_v3.dual_track.v1.json"
        ),
    )
    args = parser.parse_args(argv)
    plan = build_dual_track_plan(
        args.diagnostic_dir,
        repo_dir=PROJECT,
        preregistration_path=args.preregistration,
    )
    payload = (
        json.dumps(plan, ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    ).encode("utf-8")
    try:
        _create_once(args.output.resolve(), payload)
    except ValueError as exc:
        parser.error(str(exc))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
