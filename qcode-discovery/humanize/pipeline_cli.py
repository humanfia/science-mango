"""Run and safely control the resumable five-stage qcode pipeline."""

from __future__ import annotations

import argparse
import json
import signal
import sys
import traceback
from collections.abc import Sequence
from pathlib import Path
from typing import Any

from .pipeline_process import (
    AlreadyRunningError,
    ProcessControlError,
    cancel_run,
    control_paths,
    execute_pipeline,
    pipeline_result_succeeded,
    resolve_config_path,
    resolve_repo_dir,
    run_foreground,
    start_background,
    status_for_run,
    validate_run_id,
)
from .release_export import (
    ReleaseExportError,
    ReleaseNotExportableError,
    export_release,
)


def _default_repo_dir() -> Path:
    return Path(__file__).resolve().parent.parent


def _add_repo_argument(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--repo-dir",
        type=Path,
        default=_default_repo_dir(),
        help="qcode-discovery repository directory",
    )


def _add_review_arguments(parser: argparse.ArgumentParser) -> None:
    review = parser.add_mutually_exclusive_group()
    review.add_argument(
        "--stage-review",
        dest="stage_review",
        action="store_true",
        help="enable advisory Humanize review after machine stages (default)",
    )
    review.add_argument(
        "--no-stage-review",
        dest="stage_review",
        action="store_false",
        help="disable advisory stage reviews; machine gates are unchanged",
    )
    parser.set_defaults(stage_review=None)
    parser.add_argument("--reviewer-model")
    parser.add_argument("--reviewer-effort")


def _add_launch_arguments(parser: argparse.ArgumentParser) -> None:
    _add_repo_argument(parser)
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument(
        "--run-id",
        help="safe run id; defaults to the top-level run_id in the JSON config",
    )
    _add_review_arguments(parser)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    run = subparsers.add_parser("run", help="run in the foreground")
    _add_launch_arguments(run)

    start = subparsers.add_parser(
        "start", help="start a detached, session-independent worker"
    )
    _add_launch_arguments(start)
    start.add_argument(
        "--python-executable",
        default=sys.executable,
        help="Python interpreter used by the detached worker",
    )

    status = subparsers.add_parser(
        "status", help="show core state, heartbeat, and verified process identity"
    )
    _add_repo_argument(status)
    status.add_argument("--run-id", required=True)

    cancel = subparsers.add_parser(
        "cancel", help="terminate a verified worker process group"
    )
    _add_repo_argument(cancel)
    cancel.add_argument("--run-id", required=True)
    cancel.add_argument("--grace-seconds", type=float, default=30.0)

    export = subparsers.add_parser(
        "export-release",
        help="publish a completed strict WIN as an immutable release snapshot",
    )
    _add_repo_argument(export)
    export.add_argument("--run-id", required=True)

    # Private entry point used only by ``start``.  Archon may call the public
    # helpers directly and is not required to route through this CLI.
    worker = subparsers.add_parser("_worker", help=argparse.SUPPRESS)
    _add_launch_arguments(worker)
    worker.add_argument("--lock-fd", type=int, required=True)
    worker.add_argument("--start-fd", type=int, required=True)
    return parser


def _load_run_id(config_path: Path, explicit: str | None) -> str:
    if explicit is not None:
        return validate_run_id(explicit)
    path = resolve_config_path(config_path)
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise ValueError(f"invalid pipeline JSON config: {exc}") from exc
    if not isinstance(payload, dict):
        raise ValueError("pipeline config must be a JSON object")
    run_id = payload.get("run_id")
    if not isinstance(run_id, str):
        raise ValueError("--run-id is required when config has no top-level run_id")
    return validate_run_id(run_id)


def _print_json(value: Any, *, stream: Any = sys.stdout) -> None:
    print(
        json.dumps(value, ensure_ascii=False, indent=2, default=str),
        file=stream,
        flush=True,
    )


def _run_command(args: argparse.Namespace) -> int:
    repo = resolve_repo_dir(args.repo_dir)
    config = resolve_config_path(args.config)
    run_id = _load_run_id(config, args.run_id)
    result = run_foreground(
        repo_dir=repo,
        config_path=config,
        run_id=run_id,
        stage_review=args.stage_review,
        reviewer_model=args.reviewer_model,
        reviewer_effort=args.reviewer_effort,
    )
    _print_json(result)
    return 0 if pipeline_result_succeeded(result) else 1


def _start_command(args: argparse.Namespace) -> int:
    repo = resolve_repo_dir(args.repo_dir)
    config = resolve_config_path(args.config)
    run_id = _load_run_id(config, args.run_id)
    record = start_background(
        repo_dir=repo,
        config_path=config,
        run_id=run_id,
        python_executable=args.python_executable,
        stage_review=args.stage_review,
        reviewer_model=args.reviewer_model,
        reviewer_effort=args.reviewer_effort,
    )
    _print_json(
        {
            "run_id": run_id,
            "status": record["status"],
            "pid": record["pid"],
            "proc_starttime": record["proc_starttime"],
            "process": str(control_paths(repo, run_id).process),
            "state": str(control_paths(repo, run_id).state),
            "log": str(control_paths(repo, run_id).log),
        }
    )
    return 0


def _status_command(args: argparse.Namespace) -> int:
    _print_json(status_for_run(repo_dir=args.repo_dir, run_id=args.run_id))
    return 0


def _cancel_command(args: argparse.Namespace) -> int:
    result = cancel_run(
        repo_dir=args.repo_dir,
        run_id=args.run_id,
        grace_seconds=args.grace_seconds,
    )
    _print_json(result)
    return 0 if result["stopped"] else 1


def _export_release_command(args: argparse.Namespace) -> int:
    result = export_release(
        repo_dir=resolve_repo_dir(args.repo_dir),
        run_id=validate_run_id(args.run_id),
    )
    _print_json(result)
    return 0


def _interrupt_worker_on_sigterm(
    _signum: int,
    _frame: Any,
) -> None:
    """Turn detached-worker cancellation into a normal Python unwind.

    Stage 1 deliberately launches OpenEvolve in its own session so a crashed
    launcher cannot leave solver workers in the pipeline worker's group.
    Consequently, terminating only the outer detached group is insufficient:
    Python must unwind through ``_wait_for_managed_process`` so that it can
    terminate the inner private process group as well.
    """
    # Avoid a second SIGTERM interrupting the cleanup that the first one
    # initiates.  SIGKILL remains available to the process controller.
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    raise KeyboardInterrupt("detached pipeline worker received SIGTERM")


def _worker_command(args: argparse.Namespace) -> int:
    # start_new_session prevents a terminal hangup from reaching the worker;
    # explicitly ignoring SIGHUP also gives nohup-equivalent behaviour.
    signal.signal(signal.SIGHUP, signal.SIG_IGN)
    # SIGTERM must unwind Python rather than applying the default immediate
    # exit, otherwise Stage 1's separately-sessioned OpenEvolve tree survives.
    signal.signal(signal.SIGTERM, _interrupt_worker_on_sigterm)
    repo = resolve_repo_dir(args.repo_dir)
    config = resolve_config_path(args.config)
    run_id = _load_run_id(config, args.run_id)
    paths = control_paths(repo, run_id, create=True)
    try:
        result = execute_pipeline(
            repo_dir=repo,
            config_path=config,
            run_id=run_id,
            paths=paths,
            lock_fd=args.lock_fd,
            start_fd=args.start_fd,
            isolated_session=True,
            command=sys.argv,
            stage_review=args.stage_review,
            reviewer_model=args.reviewer_model,
            reviewer_effort=args.reviewer_effort,
        )
    except BaseException:
        traceback.print_exc()
        return 1
    _print_json(result)
    return 0 if pipeline_result_succeeded(result) else 1


def main(argv: Sequence[str] | None = None) -> int:
    try:
        args = build_parser().parse_args(argv)
        if args.command == "run":
            return _run_command(args)
        if args.command == "start":
            return _start_command(args)
        if args.command == "status":
            return _status_command(args)
        if args.command == "cancel":
            return _cancel_command(args)
        if args.command == "export-release":
            return _export_release_command(args)
        if args.command == "_worker":
            return _worker_command(args)
        raise AssertionError(f"unhandled command: {args.command}")
    except AlreadyRunningError as exc:
        _print_json(
            {"status": "already-running", "error": str(exc)},
            stream=sys.stderr,
        )
        return 2
    except ReleaseNotExportableError as exc:
        _print_json(
            {
                "status": "not-exportable",
                "classification": exc.classification,
                "error": str(exc),
            },
            stream=sys.stderr,
        )
        return 1
    except (ProcessControlError, ReleaseExportError, OSError, ValueError) as exc:
        _print_json(
            {
                "status": "error",
                "classification": getattr(exc, "classification", None),
                "error": f"{type(exc).__name__}: {exc}",
            },
            stream=sys.stderr,
        )
        return 2
    except KeyboardInterrupt:
        _print_json(
            {"status": "interrupted", "error": "KeyboardInterrupt"},
            stream=sys.stderr,
        )
        return 130


if __name__ == "__main__":
    raise SystemExit(main())
