"""Run the qcode-discovery CLI from Archon."""

from __future__ import annotations

import os
import subprocess
import sys
import tomllib
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional

import typer

from archon import log

QCODE_DISCOVERY_URL = "https://github.com/qiskit-community/qcode-discovery.git"


def _run(cmd: list[str], cwd: Path | None = None, env: dict[str, str] | None = None) -> None:
    log.step("$ " + " ".join(cmd))
    subprocess.run(cmd, cwd=str(cwd) if cwd else None, env=env, check=True)


def _capture(cmd: list[str], cwd: Path | None = None, env: dict[str, str] | None = None) -> str:
    return subprocess.check_output(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=env,
        text=True,
        stderr=subprocess.STDOUT,
    )


def _default_repo_dir(project_path: Path) -> Path:
    project = project_path.resolve()
    vendored = project / "qcode-discovery"
    if (vendored / "main.py").is_file() and (vendored / "pyproject.toml").is_file():
        return vendored
    return project.parent / "qcode-discovery"


def _default_lean_project(project: Path) -> Path:
    if (project / "lakefile.lean").is_file() or (project / "lakefile.toml").is_file():
        return project
    candidate = project / "qcode_lean_bridges" / "qcode_bridge"
    return candidate if candidate.is_dir() else project


def _default_bridge_dir(project: Path, lean_project: Path) -> Path:
    candidates = [project / "qcode_lean_bridges", lean_project.parent,
                  project.parent / "qcode_lean_bridges"]
    for candidate in candidates:
        if (candidate / "bridge_css.py").is_file():
            return candidate
    return candidates[0]


def _new_run_id() -> str:
    return datetime.now(timezone.utc).strftime("archon-%Y%m%d-%H%M%S")


def _ensure_repo(repo_dir: Path, repo_url: str) -> None:
    standalone = (repo_dir / ".git").is_dir()
    vendored = (repo_dir / "main.py").is_file() and (repo_dir / "pyproject.toml").is_file()
    if standalone or vendored:
        kind = "standalone" if standalone else "vendored"
        log.success(f"qcode-discovery {kind} tree found: {repo_dir}")
        return
    if repo_dir.exists() and any(repo_dir.iterdir()):
        raise typer.BadParameter(f"Non-empty path is not qcode-discovery: {repo_dir}")
    repo_dir.parent.mkdir(parents=True, exist_ok=True)
    _run(["git", "clone", repo_url, str(repo_dir)])


def _checkout_branch(repo_dir: Path, branch: str, fallback_default: bool) -> str:
    _run(["git", "fetch", "--all", "--prune"], cwd=repo_dir)
    remote_ref = f"refs/remotes/origin/{branch}"
    local_ref = f"refs/heads/{branch}"
    if subprocess.run(["git", "show-ref", "--verify", "--quiet", remote_ref], cwd=repo_dir).returncode == 0:
        _run(["git", "checkout", "-B", branch, f"origin/{branch}"], cwd=repo_dir)
        return branch
    if subprocess.run(["git", "show-ref", "--verify", "--quiet", local_ref], cwd=repo_dir).returncode == 0:
        _run(["git", "checkout", branch], cwd=repo_dir)
        return branch
    branches = _capture(["git", "branch", "-a", "--no-color"], cwd=repo_dir).strip()
    if not fallback_default:
        raise typer.BadParameter(
            f"Branch {branch!r} was not found in {repo_dir}. Available branches:\n{branches}"
        )
    default_branch = _capture(
        ["git", "symbolic-ref", "--short", "refs/remotes/origin/HEAD"], cwd=repo_dir
    ).strip().removeprefix("origin/")
    log.warn(f"qcode-discovery branch {branch!r} not found; falling back to {default_branch!r}.")
    log.info("Available branches:\n" + branches)
    _run(["git", "checkout", default_branch], cwd=repo_dir)
    return default_branch


def _venv_env(repo_dir: Path) -> dict[str, str]:
    env = os.environ.copy()
    venv_bin = repo_dir / ".venv" / "bin"
    env["PATH"] = str(venv_bin) + ":" + env.get("PATH", "")
    env["VIRTUAL_ENV"] = str(repo_dir / ".venv")
    return env


def _install_deps(repo_dir: Path) -> dict[str, str]:
    if subprocess.run(["uv", "--version"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0:
        if (repo_dir / ".venv" / "bin" / "python").exists():
            venv_dir = repo_dir / ".venv"
            log.success(f"Reusing qcode-discovery virtualenv: {venv_dir}")
        else:
            _run(["uv", "venv", "--python", "python3", ".venv"], cwd=repo_dir)
        env = _venv_env(repo_dir)
        pyproject = repo_dir / "pyproject.toml"
        deps: list[str] = []
        if pyproject.is_file():
            data = tomllib.loads(pyproject.read_text())
            deps = list(data.get("project", {}).get("dependencies", []))
        if deps:
            _run(["uv", "pip", "install", *deps], cwd=repo_dir, env=env)
        elif (repo_dir / "requirements.txt").is_file():
            _run(["uv", "pip", "install", "-r", "requirements.txt"], cwd=repo_dir, env=env)
        return env

    _run([sys.executable, "-m", "venv", ".venv"], cwd=repo_dir)
    env = _venv_env(repo_dir)
    _run(["python", "-m", "pip", "install", "-U", "pip"], cwd=repo_dir, env=env)
    if (repo_dir / "requirements.txt").is_file():
        _run(["python", "-m", "pip", "install", "-r", "requirements.txt"], cwd=repo_dir, env=env)
    return env


def qcode_discovery(
    project_path: str = typer.Argument(
        ".",
        help="Archon/science-mango project path. The qcode-discovery repo defaults to its parent directory.",
    ),
    repo_dir: Optional[Path] = typer.Option(
        None,
        "--repo-dir",
        help="Path for the qcode-discovery checkout. Defaults to <project-parent>/qcode-discovery.",
    ),
    repo_url: str = typer.Option(
        QCODE_DISCOVERY_URL,
        "--repo-url",
        help="Git URL for qcode-discovery.",
    ),
    branch: str = typer.Option(
        "qcode",
        "--branch",
        help="qcode-discovery branch to try first.",
    ),
    fallback_default: bool = typer.Option(
        True,
        "--fallback-default/--no-fallback-default",
        help="Use origin/HEAD if --branch does not exist.",
    ),
    update_repo: bool = typer.Option(
        True,
        "--update-repo/--no-update-repo",
        help="Fetch and check out the requested qcode-discovery branch before running.",
    ),
    install: bool = typer.Option(
        True,
        "--install/--no-install",
        help="Create/update .venv and install qcode-discovery runtime dependencies.",
    ),
    quick: bool = typer.Option(
        True,
        "--quick/--full",
        help="Pass --quick to qcode-discovery; --full enables distance-estimation cascade.",
    ),
    lattices: Optional[list[str]] = typer.Option(
        None,
        "--lattices",
        help="Lattice dimensions as ELL,M. Repeat the option for multiple lattices.",
    ),
    top: int = typer.Option(10, "--top", help="Number of top qcode-discovery results to display."),
    run_id: Optional[str] = typer.Option(None, "--run-id", help="Optional qcode-discovery run id."),
    quick_trials: int = typer.Option(100, "--quick-trials", help="Initial BP-OSD trials per candidate."),
    refine_trials: int = typer.Option(1000, "--refine-trials", help="Refined BP-OSD trials per batch."),
    fom_threshold_refine: float = typer.Option(6.0, "--fom-threshold-refine"),
    fom_threshold_exact: float = typer.Option(8.0, "--fom-threshold-exact"),
    milp_top: int = typer.Option(3, "--milp-top", help="Run HiGHS MILP only on the top N BP-OSD candidates per lattice."),
    milp_timeout_per_logical: int = typer.Option(300, "--milp-timeout-per-logical"),
    milp_total_timeout: int = typer.Option(7200, "--milp-total-timeout"),
    milp_early_stop: int = typer.Option(0, "--milp-early-stop", help="0 checks every logical direction; positive values trade exactness for speed."),
    formalize: bool = typer.Option(False, "--formalize/--no-formalize", help="Generate Lean objectives from selected discovery results."),
    prove: bool = typer.Option(False, "--prove/--no-prove", help="Formalize and compile-check every generated Lean theorem."),
    formalize_top: Optional[int] = typer.Option(None, "--formalize-top", help="Number of ranked codes to send to Lean (default: --top)."),
    metrics_reference: Optional[Path] = typer.Option(
        None, "--metrics-reference",
        help="MILP catalog for paper-style agreement metrics (default: results/ilp_catalog.json).",
    ),
    lean_project: Optional[Path] = typer.Option(None, "--lean-project", help="Lean/Archon project receiving .archon/qcode-runs artifacts."),
    bridge_dir: Optional[Path] = typer.Option(None, "--bridge-dir", help="Directory containing the qcode Lean bridge scripts."),
    witness_timeout: int = typer.Option(10800, "--witness-timeout"),
    sat_timeout: int = typer.Option(10800, "--sat-timeout"),
    skip_missing_witness: bool = typer.Option(True, "--skip-missing-witness/--fail-missing-witness"),
    lean_jobs: int = typer.Option(1, "--lean-jobs"),
    verbose: bool = typer.Option(False, "--verbose", "-v", help="Enable qcode-discovery verbose logging."),
) -> None:
    """Clone/update and run qcode-discovery through its CLI.

    Examples:
      archon qcode . --lattices 6,6 --quick --top 5
      archon qcode . --branch main --full --lattices 12,6 --milp-top 3
      archon qcode . --full --milp-top 3 --formalize --prove
    """
    project = Path(project_path).resolve()
    repo = (repo_dir or _default_repo_dir(project)).resolve()
    if (formalize or prove) and quick:
        raise typer.BadParameter("--formalize/--prove requires --full")
    if milp_top < 0:
        raise typer.BadParameter("--milp-top must be non-negative")
    if not 1 <= lean_jobs <= 4:
        raise typer.BadParameter("--lean-jobs must be between 1 and 4")
    selected_run_id = run_id or (_new_run_id() if (formalize or prove) else None)

    log.header("archon qcode")
    _ensure_repo(repo, repo_url)
    if (repo / ".git").is_dir():
        active_branch = (
            _checkout_branch(repo, branch, fallback_default)
            if update_repo
            else _capture(["git", "branch", "--show-current"], cwd=repo).strip() or "detached"
        )
    else:
        active_branch = "vendored"
    log.success(f"Using qcode-discovery branch: {active_branch}")

    env = (
        _install_deps(repo)
        if install
        else _venv_env(repo) if (repo / ".venv" / "bin" / "python").is_file()
        else os.environ.copy()
    )

    cmd = ["python", "main.py"]
    if lattices:
        cmd.append("--lattices")
        cmd.extend(lattices)
    if quick:
        cmd.append("--quick")
    else:
        cmd.extend([
            "--quick-trials", str(quick_trials), "--refine-trials", str(refine_trials),
            "--fom-threshold-refine", str(fom_threshold_refine),
            "--fom-threshold-exact", str(fom_threshold_exact),
            "--milp-top", str(milp_top),
            "--milp-timeout-per-logical", str(milp_timeout_per_logical),
            "--milp-total-timeout", str(milp_total_timeout),
            "--milp-early-stop", str(milp_early_stop),
        ])
    if top:
        cmd.extend(["--top", str(top)])
    if selected_run_id:
        cmd.extend(["--run-id", selected_run_id])
    if verbose:
        cmd.append("--verbose")

    _run(cmd, cwd=repo, env=env)

    from archon.commands.qcode_metrics import write_metrics
    reference = (metrics_reference or repo / "results" / "ilp_catalog.json").resolve()
    if selected_run_id:
        metric_paths = write_metrics(
            repo_dir=repo, run_id=selected_run_id,
            reference_catalog=reference if reference.is_file() else None,
        )
        log.success(f"Qcode metrics: {metric_paths[0]}")

    if formalize or prove:
        assert selected_run_id is not None
        _run([
            "python", str(repo / "scripts" / "certify_run.py"),
            "--run-id", selected_run_id,
            "--limit", str(formalize_top if formalize_top is not None else top),
            "--known-answer-mode", "strict",
            "--timeout-per-logical", str(milp_timeout_per_logical),
            "--total-timeout", str(milp_total_timeout),
        ], cwd=repo, env=env)
        _run([
            "python", str(repo / "scripts" / "check_release_manifest.py"),
            str(repo / "results" / "runs" / selected_run_id / "challenge_manifest.json"),
            "--run-id", selected_run_id,
        ], cwd=repo, env=env)
        from archon.commands.qcode_formalize import formalize_qcode_run, verify_qcode_run
        lean_root = (lean_project or _default_lean_project(project)).resolve()
        bridges = (bridge_dir or _default_bridge_dir(project, lean_root)).resolve()
        required = [bridges / name for name in ("bridge_css.py", "bridge_distance.py", "bridge_exact.py")]
        missing = [str(path) for path in required if not path.is_file()]
        if missing:
            raise typer.BadParameter("Missing qcode Lean bridges: " + ", ".join(missing))
        if prove and not ((lean_root / "lakefile.lean").is_file()
                          or (lean_root / "lakefile.toml").is_file()):
            raise typer.BadParameter(f"Lean project has no lakefile: {lean_root}")
        qcode_python = repo / ".venv" / "bin" / "python"
        run_root = formalize_qcode_run(
            lean_project=lean_root, repo_dir=repo, bridge_dir=bridges,
            run_id=selected_run_id,
            python=str(qcode_python if qcode_python.is_file() else sys.executable),
            top=formalize_top if formalize_top is not None else top,
            witness_timeout=witness_timeout, sat_timeout=sat_timeout,
            skip_missing=skip_missing_witness,
        )
        if prove:
            verify_qcode_run(lean_root, run_root, lean_jobs)
        metric_paths = write_metrics(
            repo_dir=repo, run_id=selected_run_id,
            reference_catalog=reference if reference.is_file() else None,
            lean_run_root=run_root,
        )
        log.success(f"Updated Lean-aware metrics: {metric_paths[0]}")
        log.success(f"Archon qcode artifacts: {run_root}")
