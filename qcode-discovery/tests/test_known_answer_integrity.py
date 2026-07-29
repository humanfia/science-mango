"""Tests for pinned known-answer integrity modes."""

import json
import subprocess
import sys
from pathlib import Path

import pytest

import evaluation.known_answer_integrity as integrity_module
from evaluation.known_answer_integrity import (
    check_fast,
    file_sha256,
    semantic_sha256,
)
from evaluation.proof_runtime import (
    SOLVER_RUNTIME_PACKAGES,
    proof_runtime_fingerprint,
)


def test_proof_runtime_fingerprint_is_complete_and_json_serializable():
    runtime = proof_runtime_fingerprint()

    assert runtime["schema_version"] == 2
    assert runtime["python"]["implementation"]
    assert runtime["python"]["version"]
    assert set(runtime["packages"]) == set(SOLVER_RUNTIME_PACKAGES)
    assert set(runtime["package_artifacts"]) == set(
        SOLVER_RUNTIME_PACKAGES
    )
    assert runtime["package_artifacts"]["scipy"]["files_sha256"]
    assert runtime["interpreter"]["realpath"]
    assert runtime["interpreter"]["executable_file"]["sha256"]
    assert json.loads(
        json.dumps(runtime, allow_nan=False),
    ) == runtime


def test_repository_pinned_known_answer_passes_fast_mode():
    result = check_fast(
        "results/known_answer_gate.json",
        "results/known_answer_trust.json",
    )
    assert result["passed"] is True


def test_fast_mode_rejects_tampered_artifact(tmp_path):
    source = json.loads(open("results/known_answer_gate.json").read())
    source["baselines"][0]["observed"]["d"] += 1
    artifact = tmp_path / "known.json"
    artifact.write_text(json.dumps(source))
    result = check_fast(artifact, "results/known_answer_trust.json")
    assert result["passed"] is False
    assert any("SHA-256" in failure for failure in result["failures"])


def test_semantic_hash_ignores_runtime_only_fields():
    artifact = json.loads(open("results/known_answer_gate.json").read())
    changed = json.loads(json.dumps(artifact))
    changed["generated_at"] = "different"
    changed["baselines"][0]["milp"]["time_s"] = 999999
    assert semantic_sha256(artifact) == semantic_sha256(changed)
    assert file_sha256("results/known_answer_gate.json")


def _strict_inputs(tmp_path, monkeypatch):
    artifact = tmp_path / "known.json"
    artifact.write_text("{}")
    trust = tmp_path / "trust.json"
    trust.write_text(json.dumps({"semantic_sha256": "pinned-semantic"}))
    monkeypatch.setattr(
        integrity_module,
        "check_fast",
        lambda *_args, **_kwargs: {
            "passed": True,
            "mode": "fast",
            "artifact_sha256": "artifact",
            "semantic_sha256": "pinned-semantic",
            "environment": {},
            "failures": [],
        },
    )
    monkeypatch.setattr(
        integrity_module,
        "validate_known_answer_artifact",
        lambda _path: {"passed": True, "failures": []},
    )
    monkeypatch.setattr(
        integrity_module,
        "semantic_sha256",
        lambda value: value.get("semantic"),
    )
    return artifact, trust


def _rerun_output_path(command):
    return Path(command[command.index("--output") + 1])


def test_strict_mode_reruns_and_accepts_matching_semantics(
    tmp_path, monkeypatch,
):
    artifact, trust = _strict_inputs(tmp_path, monkeypatch)
    calls = []

    def fake_run(command, **kwargs):
        calls.append((command, kwargs))
        _rerun_output_path(command).write_text(json.dumps({
            "semantic": "pinned-semantic",
        }))
        return integrity_module.subprocess.CompletedProcess(
            command, 0, stdout="three baselines passed",
        )

    monkeypatch.setattr(integrity_module.subprocess, "run", fake_run)
    result = integrity_module.check_strict(
        artifact,
        trust,
        timeout_per_logical=7,
        total_timeout_per_code=20,
    )

    assert result["passed"] is True
    assert result["mode"] == "strict"
    assert result["rerun_semantic_sha256"] == "pinned-semantic"
    assert len(calls) == 1
    command, kwargs = calls[0]
    assert command[command.index("--timeout-per-logical") + 1] == "7"
    assert command[command.index("--total-timeout-per-code") + 1] == "20"
    assert kwargs["timeout"] == 120


def test_strict_mode_skips_rerun_when_fast_integrity_fails(
    tmp_path, monkeypatch,
):
    artifact, trust = _strict_inputs(tmp_path, monkeypatch)
    monkeypatch.setattr(
        integrity_module,
        "check_fast",
        lambda *_args, **_kwargs: {
            "passed": False,
            "mode": "fast",
            "failures": ["artifact SHA mismatch"],
        },
    )

    def should_not_run(*_args, **_kwargs):
        raise AssertionError("strict rerun must not start after fast failure")

    monkeypatch.setattr(integrity_module.subprocess, "run", should_not_run)
    result = integrity_module.check_strict(artifact, trust)

    assert result["passed"] is False
    assert result["mode"] == "strict"
    assert result["rerun_command"] == []
    assert "artifact SHA mismatch" in result["failures"]
    assert any(
        "rerun skipped" in failure for failure in result["failures"]
    )


def test_strict_mode_rejects_nonzero_subprocess(tmp_path, monkeypatch):
    artifact, trust = _strict_inputs(tmp_path, monkeypatch)

    def fake_run(command, **_kwargs):
        return integrity_module.subprocess.CompletedProcess(
            command, 9, stdout="solver failed",
        )

    monkeypatch.setattr(integrity_module.subprocess, "run", fake_run)
    result = integrity_module.check_strict(artifact, trust)

    assert result["passed"] is False
    assert "solver failed" in result["rerun_output_tail"]
    assert any("rerun failed" in failure for failure in result["failures"])


def test_strict_mode_rejects_missing_output(tmp_path, monkeypatch):
    artifact, trust = _strict_inputs(tmp_path, monkeypatch)

    def fake_run(command, **_kwargs):
        return integrity_module.subprocess.CompletedProcess(
            command, 0, stdout="no artifact",
        )

    monkeypatch.setattr(integrity_module.subprocess, "run", fake_run)
    result = integrity_module.check_strict(artifact, trust)

    assert result["passed"] is False
    assert any("rerun failed" in failure for failure in result["failures"])


def test_strict_mode_rejects_bad_rerun_json_structurally(
    tmp_path, monkeypatch,
):
    artifact, trust = _strict_inputs(tmp_path, monkeypatch)

    def fake_run(command, **_kwargs):
        _rerun_output_path(command).write_text("{")
        return integrity_module.subprocess.CompletedProcess(
            command, 0, stdout="bad output",
        )

    monkeypatch.setattr(integrity_module.subprocess, "run", fake_run)
    result = integrity_module.check_strict(artifact, trust)

    assert result["passed"] is False
    assert any("output or trust is invalid" in failure for failure in result["failures"])


def test_strict_mode_rejects_semantic_mismatch(tmp_path, monkeypatch):
    artifact, trust = _strict_inputs(tmp_path, monkeypatch)

    def fake_run(command, **_kwargs):
        _rerun_output_path(command).write_text(json.dumps({
            "semantic": "different",
        }))
        return integrity_module.subprocess.CompletedProcess(
            command, 0, stdout="completed",
        )

    monkeypatch.setattr(integrity_module.subprocess, "run", fake_run)
    result = integrity_module.check_strict(artifact, trust)

    assert result["passed"] is False
    assert any("semantic evidence differs" in failure for failure in result["failures"])


def test_strict_mode_wall_timeout_is_fail_closed(tmp_path, monkeypatch):
    artifact, trust = _strict_inputs(tmp_path, monkeypatch)

    def fake_run(command, **kwargs):
        raise integrity_module.subprocess.TimeoutExpired(
            command,
            kwargs["timeout"],
            output=b"partial solver output",
        )

    monkeypatch.setattr(integrity_module.subprocess, "run", fake_run)
    result = integrity_module.check_strict(
        artifact,
        trust,
        timeout_per_logical=2,
        total_timeout_per_code=3,
    )

    assert result["passed"] is False
    assert result["rerun_wall_timeout_s"] == 69
    assert "partial solver output" in result["rerun_output_tail"]
    assert any("wall timeout" in failure for failure in result["failures"])


def test_strict_mode_spawn_io_error_is_structured(tmp_path, monkeypatch):
    artifact, trust = _strict_inputs(tmp_path, monkeypatch)

    def fake_run(*_args, **_kwargs):
        raise OSError("cannot spawn verifier")

    monkeypatch.setattr(integrity_module.subprocess, "run", fake_run)
    result = integrity_module.check_strict(artifact, trust)

    assert result["passed"] is False
    assert any("could not start" in failure for failure in result["failures"])


@pytest.mark.parametrize("field", ["timeout_per_logical", "total_timeout_per_code"])
@pytest.mark.parametrize("value", [0, -1, float("inf"), float("nan"), 1.5, True])
def test_strict_mode_rejects_invalid_budgets(
    tmp_path, monkeypatch, field, value,
):
    artifact, trust = _strict_inputs(tmp_path, monkeypatch)

    def should_not_run(*_args, **_kwargs):
        raise AssertionError("invalid budget must fail before subprocess")

    monkeypatch.setattr(integrity_module.subprocess, "run", should_not_run)
    kwargs = {field: value}
    with pytest.raises(ValueError, match="positive finite integer"):
        integrity_module.check_strict(artifact, trust, **kwargs)


def test_fast_mode_non_object_json_is_structured_failure(
    tmp_path, monkeypatch,
):
    artifact = tmp_path / "known.json"
    artifact.write_text("[]")
    trust = tmp_path / "trust.json"
    trust.write_text("{}")
    monkeypatch.setattr(
        integrity_module,
        "validate_known_answer_artifact",
        lambda _path: {"passed": False, "failures": ["bad artifact"]},
    )

    result = integrity_module.check_fast(artifact, trust)

    assert result["passed"] is False
    assert any("must be JSON objects" in failure for failure in result["failures"])


@pytest.mark.parametrize(
    "script",
    [
        "scripts/certify_run.py",
        "scripts/run_challenge_pipeline.py",
    ],
)
def test_formal_commands_reject_fast_mode_during_argument_parsing(script):
    project = Path(__file__).resolve().parent.parent
    completed = subprocess.run(
        [
            sys.executable,
            str(project / script),
            "--run-id",
            "strict-mode-cli-test",
            "--known-answer-mode",
            "fast",
        ],
        cwd=project,
        text=True,
        capture_output=True,
        timeout=30,
    )

    assert completed.returncode == 2
    assert "invalid choice" in completed.stderr
    assert "choose from 'strict'" in completed.stderr


@pytest.mark.parametrize(
    "script",
    ["scripts/certify_run.py", "scripts/run_challenge_pipeline.py"],
)
def test_formal_commands_keep_explicit_strict_wrapper_compatibility(script):
    project = Path(__file__).resolve().parent.parent
    completed = subprocess.run(
        [sys.executable, str(project / script), "--known-answer-mode", "strict", "--help"],
        cwd=project, text=True, capture_output=True, timeout=30,
    )
    assert completed.returncode == 0
