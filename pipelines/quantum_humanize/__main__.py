"""Prepare, test or deliberately launch the pinned local humanize flow."""

import argparse
import json
import os
import shlex
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from . import Agents, Config, prepare, save_new
from ._evidence import _manifest_files, run_baseline_checks
from ._runtime import runtime_pin
from ._tasks import OBLIGATIONS, UPSTREAM_COMMIT


def launch(args):
    """Construct an isolated local launcher; no live process without --live."""
    runtime_pin()
    config = Config(
        repo=str(Path(args.repo).resolve(strict=True)), obligation=args.obligation,
        live=True, attempts=args.attempts, rounds=args.rounds,
        parallelism=args.parallelism, max_calls=args.max_calls,
        output_token_budget=args.output_token_budget,
        turn_timeout_seconds=args.turn_timeout_seconds,
        integrator_timeout_seconds=args.integrator_timeout_seconds,
        timeout_retries=args.timeout_retries,
        audit_continuations=getattr(args, "audit_continuations", 2),
        extra_inputs=args.extra_input,
        integration_baseline=getattr(args, "integration_baseline", ""),
        integration_focus_inputs=getattr(args, "integration_focus_input", []),
        summary_integration=getattr(args, "summary_integration", True),
        integration_batch_size=getattr(args, "integration_batch_size", 3),
        repair_inputs=args.repair_input,
        audit_inputs=getattr(args, "audit_input", []),
        integrate=args.integrate,
        optimize=args.optimize,
        coverage_planning=args.coverage_planning,
        integration_closure=args.integration_closure,
        strategy_review=args.strategy_review,
        strategy_interval=args.strategy_interval,
        dispatch_review=getattr(args, "dispatch_review", True),
        research_task_inputs=getattr(args, "research_task_input", []),
    )
    # model/effort are supplied by the user, never silently replaced by this flow.
    if any(char in args.model + args.effort for char in ",\n\r\0"):
        raise ValueError("model and effort may not contain agent-spec separators")
    hmz = Path(sys.executable).parent / "hmz"
    if not hmz.is_file():
        raise ValueError("use the pinned environment's Python (hmz script missing beside it)")
    area = Path(config.repo) / ".humanize-quantum-runs"
    if area.is_symlink():
        raise ValueError("run area must not be a symlink")
    area.mkdir(mode=0o700, exist_ok=True)
    control = Path(tempfile.mkdtemp(prefix="launcher-", dir=area))
    humanize_home = control / "humanize-home"
    humanize_home.mkdir(mode=0o700)
    save_new(humanize_home / "quantum-launch.json", {"upstream_commit": UPSTREAM_COMMIT})
    settings = control / "config.json"
    save_new(settings, config)
    spec = (
        f"cli=codex,model={args.model},effort={args.effort},"
        "permission=read-only,web_search=false"
    )
    command = [str(hmz), "exec", "-f", str(Path(__file__).parent), "-c", str(settings)]
    for _ in range(len(Agents._fields)):
        command.extend(["-a", spec])
    command.append(args.task)
    print("HUMANIZE_SENTRY=off HUMANIZE_HOME=" + shlex.quote(str(humanize_home)))
    print("cwd=" + str(control))
    print(shlex.join(command))
    if not args.live:
        print("Not launched. Add --live to authorize real model turns and their costs.")
        return 0
    if shutil.which("codex") is None:
        raise ValueError("codex is not available on PATH")
    environment = os.environ.copy()
    environment.update({
        "HUMANIZE_HOME": str(humanize_home), "HUMANIZE_SENTRY": "off",
        "PYTHONDONTWRITEBYTECODE": "1",
    })
    # cwd, not Hmz(workspace=...), determines where the native runner works.
    # No daemon or detach. Parent process waits for this explicitly requested run.
    return subprocess.run(command, cwd=control, env=environment, check=False).returncode


def frontier_check(args):
    """Analyze explicitly supplied JSON offline; never prepare or launch a run."""
    from ._frontier import Frontier, analyze_frontier

    try:
        frontier = Frontier.model_validate_json(Path(args.input).read_bytes(), strict=True)
        manifest = json.loads(Path(args.manifest).read_bytes())
        _manifest_files(manifest)
        report = analyze_frontier(frontier, manifest, args.obligation)
        output = json.dumps(report, ensure_ascii=False, indent=2, allow_nan=False)
    except (OSError, ValueError, TypeError, RecursionError):
        print("frontier-check: invalid or unreadable input.", file=sys.stderr)
        return 2
    print(output)
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="action", required=True)
    commands.add_parser("doctor", help="check the installed upstream pin; no agent calls")
    prepare_parser = commands.add_parser("prepare", help="freeze current evidence, no agents")
    mock_parser = commands.add_parser("mock", help="run deterministic fake-agent scenarios")
    launch_parser = commands.add_parser("launch", help="print a launch command; --live executes")
    frontier_parser = commands.add_parser("frontier-check", help="analyze a frontier JSON offline; no agents or writes")
    frontier_parser.add_argument("input", help="Frontier JSON to validate and analyze")
    frontier_parser.add_argument("--manifest", required=True, help="snapshot manifest JSON")
    frontier_parser.add_argument("--obligation", choices=OBLIGATIONS, default="self_audit")
    for command in (prepare_parser, launch_parser):
        command.add_argument("--repo", default=".")
        command.add_argument("--obligation", choices=OBLIGATIONS, default="self_audit")
        command.add_argument("--extra-input", action="append", default=[],
                             help="explicit research Markdown input under docs/; repeatable")
    prepare_parser.add_argument("--checks", action="store_true", help="execute eight frozen known checkers")
    mock_parser.add_argument("--verbose", action="store_true")
    launch_parser.add_argument("--model", required=True)
    launch_parser.add_argument("--effort", required=True)
    launch_parser.add_argument("--integration-baseline", default="",
                               help="frozen comparison draft; never imports mathematical acceptance")
    launch_parser.add_argument("--integration-focus-input", action="append", default=[],
                               help="prioritize a frozen candidate for compatibility work; at most eight")
    launch_parser.add_argument("--integration-batch-size", type=int, default=3,
                               help="new root drafts per integration, 2 to 4; full invoked dependencies still required")
    launch_parser.add_argument("--no-summary-integration", action="store_false", dest="summary_integration", default=True,
                               help="disable detached summaries and retain all-archive integration accounting")
    launch_parser.add_argument("--repair-input", action="append", default=[],
                               help="explicit repair-queue JSON under .humanize-quantum-runs/ for the mender only; repeatable")
    launch_parser.add_argument("--audit-input", action="append", default=[],
                               help="unchanged candidate audit seeds; no old sessions or review votes")
    launch_parser.add_argument("--audit-continuations", type=int, default=2,
                               help="extra turns in each incomplete reviewer's own session (0 to 4)")
    launch_parser.add_argument("--attempts", type=int, default=8)
    launch_parser.add_argument("--rounds", type=int, default=20)
    launch_parser.add_argument("--parallelism", type=int, default=8)
    launch_parser.add_argument("--max-calls", type=int, default=640)
    launch_parser.add_argument("--output-token-budget", type=int, default=2_000_000)
    launch_parser.add_argument("--turn-timeout-seconds", type=float, default=1800)
    launch_parser.add_argument("--integrator-timeout-seconds", type=float, default=1800)
    launch_parser.add_argument("--timeout-retries", type=int, default=1,
                               help="fresh-session retries per timed-out turn (0 to 2)")
    launch_parser.add_argument("--live", action="store_true")
    launch_parser.add_argument("--no-integrate", action="store_false", dest="integrate", default=True,
                               help="disable automatic integration between research rounds")
    launch_parser.add_argument("--no-optimize", action="store_false", dest="optimize", default=True,
                               help="disable research optimizations and use the legacy flow")
    launch_parser.add_argument("--no-coverage-planning", action="store_false", dest="coverage_planning", default=False,
                               help="disable coverage and parameter planning")
    launch_parser.add_argument("--no-integration-closure", action="store_false", dest="integration_closure", default=True,
                               help="use the previous integration contract and audit/repair routing")
    launch_parser.add_argument("--no-strategy-review", action="store_false", dest="strategy_review", default=True,
                               help="disable high-level route review and cross-obligation exploration")
    launch_parser.add_argument("--strategy-interval", type=int, default=3,
                               help="rounds between route reviews (2 to 20); also triggered by two unsuccessful integrations")
    launch_parser.add_argument("--no-dispatch-review", action="store_false", dest="dispatch_review", default=True,
                               help="disable semantic pre-dispatch review and use the previous task queue")
    launch_parser.add_argument("--research-task-input", action="append", default=[],
                               help="restart task-list JSON in the run area; proposals only, reviewed before dispatch")
    launch_parser.add_argument("--task", default="推进量子码研究交接任务；先独立审计 SELF，保留全部未证缺口。")
    args = parser.parse_args()
    if args.action == "frontier-check":
        return frontier_check(args)
    if args.action == "doctor":
        print(json.dumps(runtime_pin(), indent=2))
        print("No credentials read. No agent or daemon started.")
        return 0
    if args.action == "launch":
        return launch(args)
    if args.action == "mock":
        import unittest
        suite = unittest.defaultTestLoader.discover(str(Path(__file__).parent), pattern="test_*.py")
        return int(not unittest.TextTestRunner(verbosity=2 if args.verbose else 1).run(suite).wasSuccessful())
    _, work, manifest, _ = prepare(Config(
        repo=args.repo, obligation=args.obligation, extra_inputs=args.extra_input,
    ))
    print(f"Frozen evidence: {work}")
    if args.checks:
        checks = run_baseline_checks(work / "snapshot", manifest)
        save_new(work / "baseline-checks.json", checks)
        for check in checks:
            print(("PASS " if check["passed"] else "FAIL ") + check["name"])
        return int(not checks or not all(check["passed"] for check in checks))
    print("No model calls. Use --checks to run only the eight allowlisted baseline scripts.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
