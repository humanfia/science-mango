"""Archon-owned entry point for the resumable five-stage qcode campaign."""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path
from typing import Optional

import typer

from archon import log
from archon.commands.qcode import _default_repo_dir, _venv_env

app = typer.Typer(
    name="qcode-campaign",
    help="Run and control the resumable five-stage qcode campaign.",
    no_args_is_help=True,
)


def _resolve_repo(project_path: str, repo_dir: Optional[Path]) -> Path:
    project = Path(project_path).expanduser().resolve()
    repo = (repo_dir or _default_repo_dir(project)).expanduser().resolve()
    entrypoint = repo / "humanize" / "pipeline_cli.py"
    if not entrypoint.is_file():
        raise typer.BadParameter(f"qcode campaign entry point not found: {entrypoint}")
    return repo


def _resolve_config(config: Path) -> Path:
    resolved = config.expanduser().resolve()
    if not resolved.is_file():
        raise typer.BadParameter(f"qcode campaign config not found: {resolved}")
    return resolved


def _runtime(repo: Path) -> tuple[Path, dict[str, str]]:
    qcode_python = repo / ".venv" / "bin" / "python"
    if qcode_python.is_file() and os.access(qcode_python, os.X_OK):
        return qcode_python, _venv_env(repo)
    return Path(sys.executable), os.environ.copy()


def _invoke_pipeline_cli(repo: Path, arguments: list[str]) -> None:
    python, env = _runtime(repo)
    command = [str(python), "-m", "humanize.pipeline_cli", *arguments]
    if arguments and arguments[0] == "start":
        command.extend(["--python-executable", str(python)])
    log.step("$ " + " ".join(command))
    completed = subprocess.run(
        command,
        cwd=str(repo),
        env=env,
        check=False,
    )
    if completed.returncode:
        raise typer.Exit(completed.returncode)


def _launch(
    action: str,
    *,
    project_path: str,
    repo_dir: Optional[Path],
    config: Path,
    run_id: Optional[str],
    stage_review: Optional[bool],
    reviewer_model: Optional[str],
    reviewer_effort: Optional[str],
) -> None:
    repo = _resolve_repo(project_path, repo_dir)
    arguments = [
        action,
        "--repo-dir",
        str(repo),
        "--config",
        str(_resolve_config(config)),
    ]
    if run_id is not None:
        arguments.extend(["--run-id", run_id])
    if stage_review is not None:
        arguments.append("--stage-review" if stage_review else "--no-stage-review")
    if reviewer_model is not None:
        arguments.extend(["--reviewer-model", reviewer_model])
    if reviewer_effort is not None:
        arguments.extend(["--reviewer-effort", reviewer_effort])
    _invoke_pipeline_cli(repo, arguments)


@app.command("run")
def run_campaign(
    project_path: str = typer.Argument(".", help="science-mango project path."),
    repo_dir: Optional[Path] = typer.Option(
        None, "--repo-dir", help="Vendored or standalone qcode-discovery path."
    ),
    config: Path = typer.Option(..., "--config", help="Five-stage pipeline JSON."),
    run_id: Optional[str] = typer.Option(
        None, "--run-id", help="Override the run id stored in the config."
    ),
    stage_review: Optional[bool] = typer.Option(
        None,
        "--stage-review/--no-stage-review",
        help="Override advisory reviews between deterministic stages.",
    ),
    reviewer_model: Optional[str] = typer.Option(None, "--reviewer-model"),
    reviewer_effort: Optional[str] = typer.Option(None, "--reviewer-effort"),
) -> None:
    """Run the five-stage campaign in the foreground."""
    _launch(
        "run",
        project_path=project_path,
        repo_dir=repo_dir,
        config=config,
        run_id=run_id,
        stage_review=stage_review,
        reviewer_model=reviewer_model,
        reviewer_effort=reviewer_effort,
    )


@app.command("start")
def start_campaign(
    project_path: str = typer.Argument(".", help="science-mango project path."),
    repo_dir: Optional[Path] = typer.Option(
        None, "--repo-dir", help="Vendored or standalone qcode-discovery path."
    ),
    config: Path = typer.Option(..., "--config", help="Five-stage pipeline JSON."),
    run_id: Optional[str] = typer.Option(
        None, "--run-id", help="Override the run id stored in the config."
    ),
    stage_review: Optional[bool] = typer.Option(
        None,
        "--stage-review/--no-stage-review",
        help="Override advisory reviews between deterministic stages.",
    ),
    reviewer_model: Optional[str] = typer.Option(None, "--reviewer-model"),
    reviewer_effort: Optional[str] = typer.Option(None, "--reviewer-effort"),
) -> None:
    """Start a detached campaign that survives the terminal session."""
    _launch(
        "start",
        project_path=project_path,
        repo_dir=repo_dir,
        config=config,
        run_id=run_id,
        stage_review=stage_review,
        reviewer_model=reviewer_model,
        reviewer_effort=reviewer_effort,
    )


@app.command("status")
def campaign_status(
    project_path: str = typer.Argument(".", help="science-mango project path."),
    repo_dir: Optional[Path] = typer.Option(
        None, "--repo-dir", help="Vendored or standalone qcode-discovery path."
    ),
    run_id: str = typer.Option(..., "--run-id"),
) -> None:
    """Show durable stage state, heartbeat, and verified process identity."""
    repo = _resolve_repo(project_path, repo_dir)
    _invoke_pipeline_cli(
        repo,
        ["status", "--repo-dir", str(repo), "--run-id", run_id],
    )


@app.command("export-release")
def export_campaign_release(
    project_path: str = typer.Argument(".", help="science-mango project path."),
    repo_dir: Optional[Path] = typer.Option(
        None, "--repo-dir", help="Vendored or standalone qcode-discovery path."
    ),
    run_id: str = typer.Option(..., "--run-id"),
) -> None:
    """Export one completed WIN into the immutable release layout."""

    repo = _resolve_repo(project_path, repo_dir)
    _invoke_pipeline_cli(
        repo,
        [
            "export-release",
            "--repo-dir",
            str(repo),
            "--run-id",
            run_id,
        ],
    )


@app.command("cancel")
def cancel_campaign(
    project_path: str = typer.Argument(".", help="science-mango project path."),
    repo_dir: Optional[Path] = typer.Option(
        None, "--repo-dir", help="Vendored or standalone qcode-discovery path."
    ),
    run_id: str = typer.Option(..., "--run-id"),
    grace_seconds: float = typer.Option(30.0, "--grace-seconds"),
) -> None:
    """Safely stop the verified process group for one campaign."""
    if grace_seconds < 0:
        raise typer.BadParameter("--grace-seconds must be non-negative")
    repo = _resolve_repo(project_path, repo_dir)
    _invoke_pipeline_cli(
        repo,
        [
            "cancel",
            "--repo-dir",
            str(repo),
            "--run-id",
            run_id,
            "--grace-seconds",
            str(grace_seconds),
        ],
    )
