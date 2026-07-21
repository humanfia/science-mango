"""Archon entry point for Humanize-style qcode search and Lean promotion."""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Optional

import typer

from archon import log
from archon.commands.qcode import (
    _default_bridge_dir,
    _default_lean_project,
    _default_repo_dir,
    _ensure_repo,
    _new_run_id,
    _run,
    _venv_env,
)


def qcode_humanize(
    project_path: str = typer.Argument(".", help="science-mango project path."),
    repo_dir: Optional[Path] = typer.Option(
        None, "--repo-dir", help="Vendored or standalone qcode-discovery path."
    ),
    run_id: Optional[str] = typer.Option(None, "--run-id"),
    rounds: int = typer.Option(5, "--rounds"),
    iterations_per_round: int = typer.Option(20, "--iterations-per-round"),
    model: str = typer.Option("gpt-5.5", "--model"),
    review_model: str = typer.Option("gpt-5.5", "--review-model"),
    reasoning_effort: str = typer.Option("xhigh", "--reasoning-effort"),
    review_effort: str = typer.Option("xhigh", "--review-effort"),
    api_base: Optional[str] = typer.Option(None, "--api-base"),
    milp_top: int = typer.Option(3, "--milp-top"),
    milp_timeout_per_logical: int = typer.Option(300, "--milp-timeout-per-logical"),
    milp_total_timeout: int = typer.Option(7200, "--milp-total-timeout"),
    milp_early_stop: int = typer.Option(0, "--milp-early-stop"),
    patience: int = typer.Option(3, "--patience"),
    install: bool = typer.Option(True, "--install/--no-install"),
    formalize: bool = typer.Option(True, "--formalize/--no-formalize"),
    prove: bool = typer.Option(False, "--prove/--no-prove"),
    formalize_top: int = typer.Option(3, "--formalize-top"),
    lean_project: Optional[Path] = typer.Option(None, "--lean-project"),
    bridge_dir: Optional[Path] = typer.Option(None, "--bridge-dir"),
    witness_timeout: int = typer.Option(10800, "--witness-timeout"),
    sat_timeout: int = typer.Option(10800, "--sat-timeout"),
    skip_missing_witness: bool = typer.Option(
        True, "--skip-missing-witness/--fail-missing-witness"
    ),
    lean_jobs: int = typer.Option(1, "--lean-jobs"),
    metrics_reference: Optional[Path] = typer.Option(None, "--metrics-reference"),
) -> None:
    """Run OpenEvolve + RLCR review + MILP, then optionally verify in Lean.

    This command is the Humanize-style variant. ``archon qcode`` remains the
    fixed-candidate baseline for direct accuracy and wall-time comparisons.
    """
    if rounds < 1 or iterations_per_round < 1:
        raise typer.BadParameter("--rounds and --iterations-per-round must be positive")
    if milp_top < 0:
        raise typer.BadParameter("--milp-top must be non-negative")
    if prove and not formalize:
        raise typer.BadParameter("--prove requires --formalize")
    if not 1 <= lean_jobs <= 4:
        raise typer.BadParameter("--lean-jobs must be between 1 and 4")

    project = Path(project_path).resolve()
    repo = (repo_dir or _default_repo_dir(project)).resolve()
    selected_run_id = run_id or _new_run_id().replace("archon-", "humanize-")

    log.header("archon qcode-humanize")
    _ensure_repo(repo, "https://github.com/qiskit-community/qcode-discovery.git")
    if install:
        if subprocess.run(
            ["uv", "--version"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
        ).returncode != 0:
            raise typer.BadParameter("uv is required to install the OpenEvolve group")
        _run(["uv", "sync", "--group", "dev", "--group", "evolve"], cwd=repo)
        env = _venv_env(repo)
    else:
        env = _venv_env(repo) if (repo / ".venv" / "bin" / "python").is_file() else os.environ.copy()

    command = [
        "python", "-m", "humanize.cli",
        "--run-id", selected_run_id,
        "--rounds", str(rounds),
        "--iterations-per-round", str(iterations_per_round),
        "--model", model,
        "--review-model", review_model,
        "--reasoning-effort", reasoning_effort,
        "--review-effort", review_effort,
        "--milp-top", str(milp_top),
        "--milp-timeout-per-logical", str(milp_timeout_per_logical),
        "--milp-total-timeout", str(milp_total_timeout),
        "--milp-early-stop", str(milp_early_stop),
        "--patience", str(patience),
    ]
    if api_base:
        command.extend(["--api-base", api_base])
    _run(command, cwd=repo, env=env)

    state_path = repo / "results" / "humanize" / selected_run_id / "state.json"
    state = json.loads(state_path.read_text())
    if state.get("status") != "search-complete":
        raise RuntimeError(f"Humanize search did not complete: {state_path}")

    from archon.commands.qcode_metrics import write_metrics

    reference = (metrics_reference or repo / "results" / "ilp_catalog.json").resolve()
    metric_paths = write_metrics(
        repo_dir=repo,
        run_id=selected_run_id,
        reference_catalog=reference if reference.is_file() else None,
    )
    log.success(f"Humanize qcode metrics: {metric_paths[0]}")

    if formalize:
        from archon.commands.qcode_formalize import formalize_qcode_run, verify_qcode_run

        lean_root = (lean_project or _default_lean_project(project)).resolve()
        bridges = (bridge_dir or _default_bridge_dir(project, lean_root)).resolve()
        python = repo / ".venv" / "bin" / "python"
        run_root = formalize_qcode_run(
            lean_project=lean_root,
            repo_dir=repo,
            bridge_dir=bridges,
            run_id=selected_run_id,
            python=str(python if python.is_file() else sys.executable),
            top=formalize_top,
            witness_timeout=witness_timeout,
            sat_timeout=sat_timeout,
            skip_missing=skip_missing_witness,
        )
        if prove:
            verify_qcode_run(lean_root, run_root, lean_jobs)
        metric_paths = write_metrics(
            repo_dir=repo,
            run_id=selected_run_id,
            reference_catalog=reference if reference.is_file() else None,
            lean_run_root=run_root,
        )
        log.success(f"Lean-aware Humanize metrics: {metric_paths[0]}")
        log.success(f"Humanize/Lean artifacts: {run_root}")
