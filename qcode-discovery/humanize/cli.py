"""CLI for the Humanize-style qcode search control loop."""

from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path

from .flow import FlowConfig, HumanizeFlow
from .pipeline_process import validate_run_id


def _default_run_id() -> str:
    return datetime.now(timezone.utc).strftime("humanize-%Y%m%d-%H%M%S")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-id", default=None)
    parser.add_argument("--rounds", type=int, default=5)
    parser.add_argument("--iterations-per-round", type=int, default=20)
    parser.add_argument("--model", default="gpt-5.5")
    parser.add_argument("--reasoning-effort", default="xhigh")
    parser.add_argument("--review-model", default="gpt-5.5")
    parser.add_argument("--review-effort", default="xhigh")
    parser.add_argument("--api-base")
    parser.add_argument(
        "--evolution-config", type=Path,
        help="Explicit OpenEvolve YAML, e.g. evolve/config_ansatz_server.yaml.",
    )
    parser.add_argument(
        "--evolution-seed", type=Path,
        help="Matching seed program, e.g. evolve/seed_solution_ansatz.py.",
    )
    parser.add_argument(
        "--evaluator",
        choices=("default", "coset-two-block"),
        default="default",
        help="Versioned Stage-1 evaluator representation.",
    )
    parser.add_argument(
        "--codex-cli", action="store_true",
        help="Use authenticated Codex CLI instead of an OpenAI-compatible API.",
    )
    parser.add_argument("--milp-top", type=int, default=3)
    parser.add_argument("--milp-timeout-per-logical", type=int, default=300)
    parser.add_argument("--milp-total-timeout", type=int, default=7200)
    parser.add_argument("--milp-early-stop", type=int, default=0)
    parser.add_argument(
        "--max-total-workers", type=int, default=None,
        help="Shared cap for OpenEvolve evaluation lanes and Stage 1 MILP candidates.",
    )
    parser.add_argument("--patience", type=int, default=3)
    parser.add_argument("--min-improvement", type=float, default=0.01)
    parser.add_argument(
        "--candidate-file", type=Path,
        help="Offline/debug JSONL source. When set, skip OpenEvolve but keep MILP and review.",
    )
    return parser


def main() -> None:
    args = build_parser().parse_args()
    repo_dir = Path(__file__).resolve().parent.parent
    run_id = validate_run_id(args.run_id or _default_run_id())
    config = FlowConfig(
        repo_dir=repo_dir,
        run_id=run_id,
        max_rounds=args.rounds,
        iterations_per_round=args.iterations_per_round,
        model=args.model,
        reasoning_effort=args.reasoning_effort,
        review_model=args.review_model,
        review_effort=args.review_effort,
        api_base=args.api_base,
        milp_top=args.milp_top,
        milp_timeout_per_logical=args.milp_timeout_per_logical,
        evolution_config=(
            args.evolution_config.resolve() if args.evolution_config else None
        ),
        evolution_seed=args.evolution_seed.resolve() if args.evolution_seed else None,
        evolution_evaluator=args.evaluator,
        milp_total_timeout=args.milp_total_timeout,
        milp_early_stop=args.milp_early_stop,
        patience=args.patience,
        min_improvement=args.min_improvement,
        candidate_file=args.candidate_file.resolve() if args.candidate_file else None,
        codex_cli=args.codex_cli,
        max_total_workers=args.max_total_workers,
    )
    state = HumanizeFlow(config).run()
    print(json.dumps({
        "run_id": state["run_id"],
        "status": state["status"],
        "rounds": state["current_round"],
        "best_fom": state["best_fom"],
        "state": str(repo_dir / "results" / "humanize" / state["run_id"] / "state.json"),
    }, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
