"""Opt-in production acceptance test for a real five-stage WIN run."""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

import pytest

from humanize.release_export import export_release

_RUN_ID_ENV = "QCODE_PRODUCTION_WIN_RUN_ID"


def test_real_five_stage_win_survives_independent_strict_release_replay():
    """Export a real run and independently rerun every production proof."""

    run_id = os.environ.get(_RUN_ID_ENV)
    if not run_id:
        pytest.skip(
            f"set {_RUN_ID_ENV} to a completed real WIN run id",
        )

    repo = Path(__file__).resolve().parents[1]
    exported = export_release(repo_dir=repo, run_id=run_id)
    manifest = Path(exported["manifest"])
    completed = subprocess.run(
        [
            sys.executable,
            str(repo / "scripts" / "verify_release.py"),
            str(manifest),
            "--run-id",
            run_id,
            "--known-answer-mode",
            "strict",
        ],
        cwd=repo,
        text=True,
        capture_output=True,
        check=False,
    )

    output = "\n".join(part for part in (completed.stdout, completed.stderr) if part)
    assert completed.returncode == 0, output
    assert "RELEASE REPLAY PASSED" in completed.stdout, output
