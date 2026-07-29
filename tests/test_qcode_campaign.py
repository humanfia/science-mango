from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace

import pytest
from typer.testing import CliRunner

from archon.cli import app
from archon.commands import qcode_campaign

runner = CliRunner()


def _campaign_tree(tmp_path: Path) -> tuple[Path, Path, Path, Path]:
    project = tmp_path / "science-mango"
    repo = project / "qcode-discovery"
    (repo / "humanize").mkdir(parents=True)
    (repo / "humanize" / "pipeline_cli.py").write_text("# test entry point\n")
    (repo / "main.py").write_text("# qcode\n")
    (repo / "pyproject.toml").write_text("[project]\nname='qcode'\n")
    python = repo / ".venv" / "bin" / "python"
    python.parent.mkdir(parents=True)
    python.write_text("#!/bin/sh\n")
    python.chmod(0o755)
    config = project / "campaign.json"
    config.write_text('{"run_id": "config-run"}\n')
    return project, repo.resolve(), python.resolve(), config.resolve()


def _record_subprocess(monkeypatch):
    calls = []

    def fake_run(command, **kwargs):
        calls.append((command, kwargs))
        return SimpleNamespace(returncode=0)

    monkeypatch.setattr(qcode_campaign.subprocess, "run", fake_run)
    return calls


def test_qcode_campaign_help_registers_five_commands():
    result = runner.invoke(app, ["qcode-campaign", "--help"])

    assert result.exit_code == 0, result.output
    for command in ("run", "start", "status", "export-release", "cancel"):
        assert command in result.output


def test_run_forwards_review_overrides_and_resolves_config(tmp_path, monkeypatch):
    project, repo, python, config = _campaign_tree(tmp_path)
    calls = _record_subprocess(monkeypatch)
    monkeypatch.chdir(project)

    result = runner.invoke(
        app,
        [
            "qcode-campaign",
            "run",
            str(project),
            "--config",
            "campaign.json",
            "--run-id",
            "run-one",
            "--stage-review",
            "--reviewer-model",
            "review-model",
            "--reviewer-effort",
            "high",
        ],
    )

    assert result.exit_code == 0, result.output
    assert calls[0][0] == [
        str(python),
        "-m",
        "humanize.pipeline_cli",
        "run",
        "--repo-dir",
        str(repo),
        "--config",
        str(config),
        "--run-id",
        "run-one",
        "--stage-review",
        "--reviewer-model",
        "review-model",
        "--reviewer-effort",
        "high",
    ]
    assert calls[0][1]["cwd"] == str(repo)
    assert calls[0][1]["check"] is False
    assert calls[0][1]["env"]["VIRTUAL_ENV"] == str(repo / ".venv")


def test_start_uses_qcode_python_and_detached_worker_interface(tmp_path, monkeypatch):
    project, repo, python, config = _campaign_tree(tmp_path)
    calls = _record_subprocess(monkeypatch)

    result = runner.invoke(
        app,
        [
            "qcode-campaign",
            "start",
            str(project),
            "--config",
            str(config),
            "--no-stage-review",
        ],
    )

    assert result.exit_code == 0, result.output
    command = calls[0][0]
    assert command == [
        str(python),
        "-m",
        "humanize.pipeline_cli",
        "start",
        "--repo-dir",
        str(repo),
        "--config",
        str(config),
        "--no-stage-review",
        "--python-executable",
        str(python),
    ]
    assert "nohup" not in command
    assert calls[0][1].get("shell", False) is False


def test_status_and_cancel_forward_control_arguments(tmp_path, monkeypatch):
    project, repo, python, _config = _campaign_tree(tmp_path)
    calls = _record_subprocess(monkeypatch)

    status = runner.invoke(
        app,
        [
            "qcode-campaign",
            "status",
            str(project),
            "--run-id",
            "run-two",
        ],
    )
    cancel = runner.invoke(
        app,
        [
            "qcode-campaign",
            "cancel",
            str(project),
            "--run-id",
            "run-two",
            "--grace-seconds",
            "4.5",
        ],
    )

    assert status.exit_code == 0, status.output
    assert cancel.exit_code == 0, cancel.output
    assert calls[0][0] == [
        str(python),
        "-m",
        "humanize.pipeline_cli",
        "status",
        "--repo-dir",
        str(repo),
        "--run-id",
        "run-two",
    ]
    assert calls[1][0] == [
        str(python),
        "-m",
        "humanize.pipeline_cli",
        "cancel",
        "--repo-dir",
        str(repo),
        "--run-id",
        "run-two",
        "--grace-seconds",
        "4.5",
    ]


def test_export_release_forwards_fixed_run_and_repo(tmp_path, monkeypatch):
    project, repo, python, _config = _campaign_tree(tmp_path)
    calls = _record_subprocess(monkeypatch)

    result = runner.invoke(
        app,
        [
            "qcode-campaign",
            "export-release",
            str(project),
            "--run-id",
            "release-run",
        ],
    )

    assert result.exit_code == 0, result.output
    assert calls[0][0] == [
        str(python),
        "-m",
        "humanize.pipeline_cli",
        "export-release",
        "--repo-dir",
        str(repo),
        "--run-id",
        "release-run",
        "--python-executable",
        str(python),
    ]


def test_export_release_forwards_explicit_authorized_worker(
    tmp_path,
    monkeypatch,
):
    project, repo, _python, _config = _campaign_tree(tmp_path)
    worker = tmp_path / "custom-worker" / "bin" / "python"
    worker.parent.mkdir(parents=True)
    worker.write_text("#!/bin/sh\n")
    worker.chmod(0o755)
    calls = _record_subprocess(monkeypatch)

    result = runner.invoke(
        app,
        [
            "qcode-campaign",
            "export-release",
            str(project),
            "--run-id",
            "release-run",
            "--python-executable",
            str(worker),
        ],
    )

    assert result.exit_code == 0, result.output
    assert calls[0][0][-2:] == ["--python-executable", str(worker)]


def test_pipeline_exit_code_is_preserved(tmp_path, monkeypatch):
    project, _repo, _python, _config = _campaign_tree(tmp_path)
    monkeypatch.setattr(
        qcode_campaign.subprocess,
        "run",
        lambda *_args, **_kwargs: SimpleNamespace(returncode=2),
    )

    result = runner.invoke(
        app,
        [
            "qcode-campaign",
            "status",
            str(project),
            "--run-id",
            "unsafe",
        ],
    )

    assert result.exit_code == 2


def test_missing_campaign_entrypoint_fails_before_subprocess(tmp_path, monkeypatch):
    project = tmp_path / "science-mango"
    repo = project / "qcode-discovery"
    repo.mkdir(parents=True)
    monkeypatch.setattr(
        qcode_campaign.subprocess,
        "run",
        lambda *_args, **_kwargs: pytest.fail("must not launch subprocess"),
    )

    result = runner.invoke(
        app,
        [
            "qcode-campaign",
            "status",
            str(project),
            "--repo-dir",
            str(repo),
            "--run-id",
            "missing",
        ],
    )

    assert result.exit_code != 0
    assert "pipeline_cli.py" in result.output
