from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any

import pytest

import humanize.reviewer as reviewer_module
from humanize.reviewer import CodexReviewer, ReviewError


def _valid_review() -> dict[str, Any]:
    return {
        "verdict": "continue",
        "summary": "continue searching",
        "risks": [],
        "recommended_focus": [],
        "lessons": [],
    }


def _output_path(command: list[str]) -> Path:
    return Path(command[command.index("--output-last-message") + 1])


def _reviewer(
    tmp_path: Path,
    *,
    max_attempts: int = 3,
    sleeps: list[float] | None = None,
) -> CodexReviewer:
    recorded_sleeps = sleeps if sleeps is not None else []
    return CodexReviewer(
        repo_dir=tmp_path,
        model="test-model",
        effort="low",
        timeout=5,
        codex_bin="codex-test",
        max_attempts=max_attempts,
        retry_backoff_seconds=0.25,
        sleeper=recorded_sleeps.append,
    )


def test_transient_process_failure_retries_then_succeeds(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls = 0
    sleeps: list[float] = []
    stale_output = tmp_path / "review.json"
    stale_output.write_text(json.dumps({"verdict": "promote"}))

    def fake_run(command: list[str], **_: Any) -> None:
        nonlocal calls
        calls += 1
        output_path = _output_path(command)
        assert not output_path.exists()
        if calls == 1:
            raise subprocess.CalledProcessError(1, command)
        output_path.write_text(json.dumps(_valid_review()))

    monkeypatch.setattr(reviewer_module.subprocess, "run", fake_run)

    result = _reviewer(tmp_path, sleeps=sleeps).review("prompt", tmp_path)

    assert result == _valid_review()
    assert calls == 2
    assert sleeps == [0.25]
    assert "failure=" in (tmp_path / "review-attempt-01.log").read_text()
    assert "status=success" in (tmp_path / "review-attempt-02.log").read_text()


def test_all_process_attempts_fail_closed(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls = 0
    sleeps: list[float] = []

    def fake_run(command: list[str], **_: Any) -> None:
        nonlocal calls
        calls += 1
        if calls == 1:
            raise subprocess.CalledProcessError(1, command)
        if calls == 2:
            raise subprocess.TimeoutExpired(command, timeout=5)
        raise OSError("temporary launch failure")

    monkeypatch.setattr(reviewer_module.subprocess, "run", fake_run)

    with pytest.raises(ReviewError, match="failed after 3 attempts"):
        _reviewer(tmp_path, sleeps=sleeps).review("prompt", tmp_path)

    assert calls == 3
    assert sleeps == [0.25, 0.5]
    for attempt in range(1, 4):
        log = tmp_path / f"review-attempt-{attempt:02d}.log"
        assert log.is_file()
        assert f"attempt={attempt}/3" in log.read_text()
        assert "failure=" in log.read_text()


@pytest.mark.parametrize(
    "first_output",
    [
        "{not-json",
        json.dumps({"verdict": "continue"}),
    ],
)
def test_malformed_or_schema_invalid_output_retries_then_succeeds(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    first_output: str,
) -> None:
    calls = 0
    sleeps: list[float] = []

    def fake_run(command: list[str], **_: Any) -> None:
        nonlocal calls
        calls += 1
        output_path = _output_path(command)
        assert not output_path.exists()
        output_path.write_text(
            first_output if calls == 1 else json.dumps(_valid_review())
        )

    monkeypatch.setattr(reviewer_module.subprocess, "run", fake_run)

    result = _reviewer(tmp_path, sleeps=sleeps).review("prompt", tmp_path)

    assert result["verdict"] == "continue"
    assert calls == 2
    assert sleeps == [0.25]
    assert "failure=" in (tmp_path / "review-attempt-01.log").read_text()


def test_missing_output_retries_then_succeeds(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls = 0

    def fake_run(command: list[str], **_: Any) -> None:
        nonlocal calls
        calls += 1
        if calls == 2:
            _output_path(command).write_text(json.dumps(_valid_review()))

    monkeypatch.setattr(reviewer_module.subprocess, "run", fake_run)

    assert _reviewer(tmp_path).review("prompt", tmp_path) == _valid_review()
    assert calls == 2


@pytest.mark.parametrize("interrupt", [KeyboardInterrupt(), SystemExit(7)])
def test_control_flow_exceptions_are_not_retried(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    interrupt: BaseException,
) -> None:
    calls = 0
    sleeps: list[float] = []

    def fake_run(command: list[str], **_: Any) -> None:
        nonlocal calls
        calls += 1
        raise interrupt

    monkeypatch.setattr(reviewer_module.subprocess, "run", fake_run)

    with pytest.raises(type(interrupt)):
        _reviewer(tmp_path, sleeps=sleeps).review("prompt", tmp_path)

    assert calls == 1
    assert sleeps == []
