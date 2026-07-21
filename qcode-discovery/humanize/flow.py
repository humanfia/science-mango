"""Humanize RLCR controller around OpenEvolve, MILP, and qcode artifacts."""

from __future__ import annotations

import json
import subprocess
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable, Protocol

from .reviewer import CodexReviewer, build_review_prompt, validate_review
from .state import (
    EliteArchive,
    RunStore,
    append_jsonl,
    candidate_fom,
    code_key,
    credible_bp_candidate,
    read_jsonl_since,
    utc_now,
)


class Reviewer(Protocol):
    def review(self, prompt: str, round_dir: Path) -> dict[str, Any]: ...


MilpEvaluator = Callable[[dict[str, Any], "FlowConfig"], dict[str, Any]]
EvolutionRunner = Callable[["FlowConfig", dict[str, Any], Path], Path | None]


@dataclass(frozen=True)
class FlowConfig:
    repo_dir: Path
    run_id: str
    max_rounds: int = 5
    iterations_per_round: int = 20
    model: str = "gpt-5.5"
    reasoning_effort: str = "xhigh"
    review_model: str = "gpt-5.5"
    review_effort: str = "xhigh"
    api_base: str | None = None
    milp_top: int = 3
    milp_timeout_per_logical: int = 300
    milp_total_timeout: int = 7200
    milp_early_stop: int = 0
    patience: int = 3
    min_improvement: float = 0.01
    candidate_file: Path | None = None

    def serializable(self) -> dict[str, Any]:
        value = asdict(self)
        value["repo_dir"] = str(self.repo_dir)
        value["candidate_file"] = str(self.candidate_file) if self.candidate_file else None
        return value

    def validate(self) -> None:
        if self.max_rounds < 1:
            raise ValueError("max_rounds must be positive")
        if self.iterations_per_round < 1 and self.candidate_file is None:
            raise ValueError("iterations_per_round must be positive")
        if self.milp_top < 0:
            raise ValueError("milp_top must be non-negative")
        if self.milp_early_stop < 0:
            raise ValueError("milp_early_stop must be non-negative")
        if self.patience < 1:
            raise ValueError("patience must be positive")


def _latest_checkpoint(output_dir: Path) -> Path | None:
    checkpoint_root = output_dir / "checkpoints"
    if not checkpoint_root.is_dir():
        return None

    def number(path: Path) -> int:
        try:
            return int(path.name.rsplit("_", 1)[-1])
        except ValueError:
            return -1

    checkpoints = [path for path in checkpoint_root.glob("checkpoint_*") if path.is_dir()]
    return max(checkpoints, key=number) if checkpoints else None


def run_openevolve(config: FlowConfig, state: dict[str, Any], round_dir: Path) -> Path | None:
    """Run or resume a bounded OpenEvolve slice for one RLCR round."""
    evolution_name = f"humanize_{config.run_id}"
    output_dir = config.repo_dir / "results" / "evolution" / evolution_name
    target_iterations = int(state["current_round"] + 1) * config.iterations_per_round
    memory_path = config.repo_dir / "results" / "humanize" / config.run_id / "bitlesson.md"
    context_parts = [memory_path.read_text()] if memory_path.is_file() else []
    previous_review = round_dir.parent / f"round-{int(state["current_round"]):03d}" / "review.json"
    if previous_review.is_file():
        review = json.loads(previous_review.read_text())
        focus = review.get("recommended_focus", [])
        if focus:
            context_parts.append("Previous independent reviewer focus:\n- " + "\n- ".join(map(str, focus)))
    context_path = round_dir / "search-context.md"
    context_path.write_text("\n\n".join(context_parts) + "\n")
    command = [
        sys.executable,
        "evolve/run_evolution.py",
        "--run-name", evolution_name,
        "--iterations", str(target_iterations),
        "--model", config.model,
        "--reasoning-effort", config.reasoning_effort,
        "--humanize-context", str(context_path),
        "--no-temperature",
    ]
    checkpoint = state.get("last_checkpoint")
    if checkpoint and Path(checkpoint).is_dir():
        command.extend(["--resume", checkpoint])
    if config.api_base:
        command.extend(["--api-base", config.api_base])
    log_path = round_dir / "evolution.log"
    with log_path.open("w", encoding="utf-8") as stream:
        subprocess.run(
            command,
            cwd=config.repo_dir,
            stdout=stream,
            stderr=subprocess.STDOUT,
            check=True,
        )
    return _latest_checkpoint(output_dir)


def _milp_is_fully_exact(row: dict[str, Any]) -> bool:
    if (row.get("stage") == "symplectic_low_d" and row.get("d_is_exact")
            and int(row.get("d", 0) or 0) == 2):
        return True
    if row.get("d_is_exact") and row.get("stage") in {
        "exact", "self_dual_d2", "milp_exact"
    }:
        details = row.get("milp_details")
        if not details:
            return row.get("stage") in {"exact", "self_dual_d2"}
    details = row.get("milp_details") or {}
    total = int(details.get("total_logicals", 0) or 0)
    checked = int(details.get("num_logicals_checked", 0) or 0)
    optimal = int(details.get("logicals_optimal", 0) or 0)
    return bool(details.get("exact")) and total > 0 and checked == total == optimal


def evaluate_with_milp(candidate: dict[str, Any], config: FlowConfig) -> dict[str, Any]:
    """Use qcode's evaluator and preserve the strict partial-MILP semantics."""
    from evaluation.evaluator import evaluate_candidate_milp
    from main import merge_bp_milp_result

    result = evaluate_candidate_milp(
        int(candidate["ell"]),
        int(candidate["m"]),
        [tuple(map(int, term)) for term in candidate["A_terms"]],
        [tuple(map(int, term)) for term in candidate["B_terms"]],
        milp_timeout_per_logical=config.milp_timeout_per_logical,
        milp_total_timeout=config.milp_total_timeout,
        milp_early_stop=(config.milp_early_stop or None),
    )
    merged = merge_bp_milp_result(candidate, result)
    merged["candidate_key"] = code_key(candidate)
    merged["milp_attempted"] = True
    # A reviewer must never be able to alter this machine-derived field.
    merged["d_is_exact"] = _milp_is_fully_exact(merged)
    return merged


def _deduplicate(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    best: dict[str, dict[str, Any]] = {}
    for row in rows:
        key = code_key(row)
        current = best.get(key)
        if current is None or candidate_fom(row) > candidate_fom(current):
            best[key] = row
    return list(best.values())


def select_for_milp(
    new_elites: list[dict[str, Any]],
    archive: EliteArchive,
    audited_keys: set[str],
    limit: int,
) -> list[dict[str, Any]]:
    """Select credible and diverse elites, never re-auditing an existing key."""
    if limit <= 0:
        return []
    pool = _deduplicate(new_elites + archive.ranked())
    pool = [
        row for row in pool
        if code_key(row) not in audited_keys and credible_bp_candidate(row)
    ]
    pool.sort(key=candidate_fom, reverse=True)

    selected: list[dict[str, Any]] = []
    used_cells: set[str] = set()
    for row in pool:
        cell = str(row.get("archive_cell", ""))
        if cell and cell in used_cells:
            continue
        selected.append(row)
        used_cells.add(cell)
        if len(selected) == limit:
            return selected
    for row in pool:
        if row in selected:
            continue
        selected.append(row)
        if len(selected) == limit:
            break
    return selected


class HumanizeFlow:
    """One-build/one-review qcode loop with durable evidence and hard gates."""

    def __init__(
        self,
        config: FlowConfig,
        *,
        reviewer: Reviewer | None = None,
        evolution_runner: EvolutionRunner = run_openevolve,
        milp_evaluator: MilpEvaluator = evaluate_with_milp,
    ):
        config.validate()
        self.config = config
        self.store = RunStore.create(config.repo_dir / "results", config.run_id)
        self.archive = EliteArchive(self.store.archive_path)
        self.reviewer = reviewer or CodexReviewer(
            repo_dir=config.repo_dir,
            model=config.review_model,
            effort=config.review_effort,
        )
        self.evolution_runner = evolution_runner
        self.milp_evaluator = milp_evaluator
        self.run_dir = config.repo_dir / "results" / "runs" / self.store.run_id
        self.run_dir.mkdir(parents=True, exist_ok=True)

    @property
    def evolution_output(self) -> Path:
        return self.config.repo_dir / "results" / "evolution" / f"humanize_{self.store.run_id}"

    @property
    def candidate_log(self) -> Path:
        return self.config.candidate_file or self.evolution_output / "all_codes.jsonl"

    def _write_run_meta(self, state: dict[str, Any]) -> None:
        meta = {
            "run_id": self.store.run_id,
            "status": state["status"],
            "humanize": True,
            "rounds_completed": state["current_round"],
            "total_evaluations": len(state.get("audited_keys", [])),
            "best_fom": state.get("best_fom", 0.0),
            "config": state["config"],
            "state_path": str(self.store.state_path),
            "updated_at": utc_now(),
        }
        path = self.run_dir / "run_meta.json"
        temporary = path.with_suffix(".json.tmp")
        temporary.write_text(json.dumps(meta, ensure_ascii=False, indent=2) + "\n")
        temporary.replace(path)

    def _write_contract(self, round_number: int, round_dir: Path) -> dict[str, Any]:
        contract = {
            "round": round_number,
            "build": {
                "openevolve_target_iterations": round_number * self.config.iterations_per_round,
                "model": self.config.model,
                "reasoning_effort": self.config.reasoning_effort,
            },
            "promotion_gates": {
                "bp_osd": "upper-bound candidate only",
                "milp_top": self.config.milp_top,
                "milp_exact": "all logical directions proven optimal",
                "lean": "performed by archon after search promotion",
            },
            "review": {
                "model": self.config.review_model,
                "reasoning_effort": self.config.review_effort,
                "independent_fresh_session": True,
            },
        }
        (round_dir / "contract.json").write_text(
            json.dumps(contract, ensure_ascii=False, indent=2) + "\n"
        )
        return contract

    def _finish_round(
        self,
        state: dict[str, Any],
        number: int,
        candidates: list[dict[str, Any]],
        audited: list[dict[str, Any]],
        review: dict[str, Any],
        round_dir: Path,
    ) -> None:
        exact = sum(1 for row in audited if row.get("d_is_exact"))
        summary = {
            "round": number,
            "new_candidates": len(candidates),
            "milp_audited": len(audited),
            "milp_exact": exact,
            "best_fom": max((candidate_fom(r) for r in candidates), default=0.0),
            "review_verdict": review["verdict"],
            "review_summary": review["summary"],
        }
        state["rounds"].append(summary)
        state["current_round"] = number
        (round_dir / "summary.md").write_text(
            "\n".join([
                f"# Humanize qcode round {number}", "",
                f"- New candidates: {len(candidates)}",
                f"- MILP audited: {len(audited)}",
                f"- Fully exact MILP: {exact}",
                f"- Reviewer verdict: `{review['verdict']}`", "",
                "## Review", "", review["summary"], "",
                "## BitLesson Delta", "",
                f"- Action: {'add' if review['lessons'] else 'none'}",
                f"- Lesson count: {len(review['lessons'])}",
            ]) + "\n"
        )

    def run(self) -> dict[str, Any]:
        serialized_config = self.config.serializable()
        existing = self.store.load_state()
        if existing is not None and existing.get("config") != serialized_config:
            raise ValueError(
                "Refusing to resume a Humanize run with different configuration"
            )
        state = self.store.initialize(serialized_config)
        if state["status"] in {"completed", "search-complete"}:
            return state
        state["status"] = "running"
        self.store.write_state(state)
        self._write_run_meta(state)

        for number in range(int(state["current_round"]) + 1, self.config.max_rounds + 1):
            round_dir = self.store.round_dir(number)
            contract = self._write_contract(number, round_dir)
            self.store.event("round_started", round_number=number)

            try:
                candidate_path = round_dir / "candidates.jsonl"
                milp_path = round_dir / "milp.jsonl"
                review_path = round_dir / "review.json"
                resume_review = (
                    state.get("pending_round") == number
                    and state.get("round_phase") in {"review", "finalize"}
                    and candidate_path.is_file()
                    and milp_path.is_file()
                )
                if resume_review:
                    candidates = [json.loads(line) for line in candidate_path.read_text().splitlines() if line.strip()]
                    audited = [json.loads(line) for line in milp_path.read_text().splitlines() if line.strip()]
                    self.store.event("round_resumed", round_number=number, phase=state.get("round_phase"))
                else:
                    checkpoint = None
                    if self.config.candidate_file is None:
                        checkpoint = self.evolution_runner(self.config, state, round_dir)
                    if checkpoint:
                        state["last_checkpoint"] = str(checkpoint)

                    candidates, new_offset = read_jsonl_since(
                        self.candidate_log, int(state.get("candidate_offset", 0))
                    )
                    state["candidate_offset"] = new_offset
                    candidates = _deduplicate(candidates)
                    with candidate_path.open("w", encoding="utf-8") as stream:
                        for row in candidates:
                            stream.write(json.dumps(row, ensure_ascii=False, default=str) + "\n")

                    new_elites = self.archive.update(candidates, number)
                    audited_keys = set(state.get("audited_keys", []))
                    selected = select_for_milp(
                        new_elites, self.archive, audited_keys, self.config.milp_top
                    )
                    audited = []
                    for candidate in selected:
                        result = self.milp_evaluator(candidate, self.config)
                        result["candidate_key"] = code_key(candidate)
                        result["milp_attempted"] = True
                        result["d_is_exact"] = _milp_is_fully_exact(result)
                        audited.append(result)
                        audited_keys.add(result["candidate_key"])
                        append_jsonl(self.run_dir / "evaluations.jsonl", result)
                    state["audited_keys"] = sorted(audited_keys)
                    with milp_path.open("w", encoding="utf-8") as stream:
                        for row in audited:
                            stream.write(json.dumps(row, ensure_ascii=False, default=str) + "\n")
                    state["pending_round"] = number
                    state["round_phase"] = "review"
                    self.store.write_state(state)

                memory = self.store.memory_path.read_text() if self.store.memory_path.exists() else ""
                prompt = build_review_prompt(
                    round_number=number,
                    contract=contract,
                    candidates=candidates,
                    audited=audited,
                    archive_top=self.archive.ranked(),
                    memory=memory,
                )
                (round_dir / "review-request.md").write_text(prompt)
                if state.get("round_phase") == "finalize" and review_path.is_file():
                    review = validate_review(json.loads(review_path.read_text()))
                else:
                    review = self.reviewer.review(prompt, round_dir)
                    if not review_path.exists():
                        review_path.write_text(json.dumps(review, ensure_ascii=False, indent=2) + "\n")
                    state["round_phase"] = "finalize"
                    self.store.write_state(state)

                if review["verdict"] != "reject_round":
                    self.store.add_lessons(review["lessons"], number)

                round_best = max((candidate_fom(r) for r in candidates), default=0.0)
                previous_best = float(state.get("best_fom", 0.0))
                if round_best > previous_best + self.config.min_improvement:
                    state["best_fom"] = round_best
                    state["no_improvement_rounds"] = 0
                else:
                    state["no_improvement_rounds"] = int(
                        state.get("no_improvement_rounds", 0)
                    ) + 1

                self._finish_round(state, number, candidates, audited, review, round_dir)
                exact_total = sum(
                    1
                    for path in (self.run_dir / "evaluations.jsonl",)
                    for row in (path.read_text().splitlines() if path.is_file() else [])
                    if row.strip() and _milp_is_fully_exact(json.loads(row))
                )
                should_stop = (
                    review["verdict"] == "stop" and exact_total > 0
                ) or int(state["no_improvement_rounds"]) >= self.config.patience
                self.store.event(
                    "round_completed",
                    round_number=number,
                    reviewer_verdict=review["verdict"],
                    exact_total=exact_total,
                    stop=should_stop,
                )
                state.pop("pending_round", None)
                state.pop("round_phase", None)
                self.store.write_state(state)
                self._write_run_meta(state)
                if should_stop:
                    break
            except (Exception, KeyboardInterrupt) as exc:
                state["status"] = "failed"
                state["failure"] = f"{type(exc).__name__}: {exc}"
                self.store.write_state(state)
                self._write_run_meta(state)
                self.store.event(
                    "round_failed", round_number=number, error=state["failure"]
                )
                raise

        state["status"] = "search-complete"
        self.store.write_state(state)
        self._write_run_meta(state)
        self.store.event("search_completed", rounds=state["current_round"])
        return state
