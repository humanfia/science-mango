"""Humanize RLCR controller around OpenEvolve, MILP, and qcode artifacts."""

from __future__ import annotations

import json
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
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
    evolution_config: Path | None = None
    evolution_seed: Path | None = None
    milp_top: int = 3
    milp_timeout_per_logical: int = 300
    milp_total_timeout: int = 7200
    milp_early_stop: int = 0
    patience: int = 3
    min_improvement: float = 0.01
    candidate_file: Path | None = None
    codex_cli: bool = False

    def serializable(self) -> dict[str, Any]:
        value = asdict(self)
        value["repo_dir"] = str(self.repo_dir)
        value["candidate_file"] = str(self.candidate_file) if self.candidate_file else None
        # Omit unset optional launch fields so pre-fix failed runs retain an
        # identical serialized configuration and can resume their audit.
        for name in ("evolution_config", "evolution_seed"):
            path = value.get(name)
            if path is None:
                value.pop(name, None)
            else:
                value[name] = str(path)
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

        for name in ("evolution_config", "evolution_seed"):
            path = getattr(self, name)
            if path is not None and not path.is_file():
                raise ValueError(f"{name} does not exist: {path}")


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
    if config.evolution_config:
        command.extend(["--config", str(config.evolution_config)])
    if config.evolution_seed:
        command.extend(["--seed", str(config.evolution_seed)])
    if config.api_base:
        command.extend(["--api-base", config.api_base])
    if config.codex_cli:
        command.append("--codex-cli")
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
    # Preserve pre-MILP machine gates when an exact result replaces the BP row;
    # final acceptance requires this replayable evidence.
    for field in ("static_eligibility", "structural_novelty"):
        if field in candidate:
            merged[field] = candidate[field]
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
    audited_digests: set[str] | None = None,
) -> list[dict[str, Any]]:
    """Select diverse elites with one lane for high-upside BP outliers.

    The sqrt(n) credibility heuristic remains useful for budget allocation, but
    it is not a theorem and must not categorically exclude a real breakthrough.
    """
    if limit <= 0:
        return []
    pool = _deduplicate(new_elites + archive.ranked())
    eligible = []
    for row in pool:
        if code_key(row) in audited_keys:
            continue
        static = row.get("static_eligibility") or {}
        novelty = row.get("structural_novelty") or {}
        if static and static.get("eligible") is not True:
            continue
        if novelty and novelty.get("novel") is not True:
            continue
        digest = novelty.get("canonical_digest")
        if audited_digests and digest and digest in audited_digests:
            continue
        eligible.append(row)

    credible = [row for row in eligible if credible_bp_candidate(row)]
    exploratory = [row for row in eligible if not credible_bp_candidate(row)]
    credible.sort(key=candidate_fom, reverse=True)
    exploratory.sort(key=candidate_fom, reverse=True)

    selected: list[dict[str, Any]] = []
    used_cells: set[str] = set()

    def add_from(rows: list[dict[str, Any]], target: int) -> None:
        for require_new_cell in (True, False):
            for row in rows:
                if len(selected) >= target or len(selected) >= limit:
                    return
                if row in selected:
                    continue
                cell = str(row.get("archive_cell", ""))
                if require_new_cell and cell and cell in used_cells:
                    continue
                selected.append(row)
                if cell:
                    used_cells.add(cell)

    reserve_exploration = bool(exploratory) and limit > 1
    add_from(credible, limit - int(reserve_exploration))
    if reserve_exploration:
        add_from(exploratory, len(selected) + 1)
    add_from(credible + exploratory, limit)
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

    @staticmethod
    def _read_jsonl(path: Path) -> list[dict[str, Any]]:
        if not path.is_file():
            return []
        return [
            json.loads(line)
            for line in path.read_text().splitlines()
            if line.strip()
        ]

    @staticmethod
    def _write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
        with path.open("w", encoding="utf-8") as stream:
            for row in rows:
                stream.write(
                    json.dumps(row, ensure_ascii=False, default=str) + "\n"
                )

    def _screen_candidates(
        self, rows: list[dict[str, Any]]
    ) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
        """Apply static and BLISS gates before archive ranking or MILP.

        Existing archive rows participate in the same pass. This both performs
        cross-round structural deduplication and purges polluted archives left
        by runs created before the gate moved to Tier 0.
        """
        from evaluation.structural_dedup import deduplicate_css_results

        current = _deduplicate(rows)
        current.sort(key=candidate_fom, reverse=True)
        current_keys = {code_key(row) for row in current}
        combined = _deduplicate(self.archive.ranked() + current)
        combined.sort(key=candidate_fom, reverse=True)
        kept, rejected = deduplicate_css_results(combined)
        self.archive.replace(kept)
        accepted = [row for row in kept if code_key(row) in current_keys]
        return accepted, rejected

    def _audit_selected(
        self,
        selected: list[dict[str, Any]],
        *,
        state: dict[str, Any],
        milp_path: Path,
    ) -> list[dict[str, Any]]:
        """Audit selected candidates concurrently with durable checkpoints."""
        existing = self._read_jsonl(milp_path)
        by_key = {code_key(row): row for row in existing}
        pending = [row for row in selected if code_key(row) not in by_key]
        audited_keys = set(state.get("audited_keys", []))
        audited_digests = set(state.get("audited_structural_digests", []))
        failures: list[tuple[str, Exception]] = []

        def persist(candidate: dict[str, Any], result: dict[str, Any]) -> None:
            key = code_key(candidate)
            result["candidate_key"] = key
            result["milp_attempted"] = True
            result["d_is_exact"] = _milp_is_fully_exact(result)
            append_jsonl(milp_path, result)
            append_jsonl(self.run_dir / "evaluations.jsonl", result)
            by_key[key] = result
            audited_keys.add(key)
            state["audited_keys"] = sorted(audited_keys)
            novelty = result.get("structural_novelty") or {}
            digest = novelty.get("canonical_digest")
            if digest:
                audited_digests.add(str(digest))
            state["audited_structural_digests"] = sorted(audited_digests)
            state["round_phase"] = "audit"
            self.store.write_state(state)

        if len(pending) == 1:
            candidate = pending[0]
            persist(candidate, self.milp_evaluator(candidate, self.config))
        elif pending:
            # Candidate-level parallelism is intentionally capped at three for
            # the 64 GiB cgroup. HiGHS releases the GIL and is thread-safe, so
            # this also supports non-pickleable test evaluators.
            with ThreadPoolExecutor(max_workers=min(3, len(pending))) as pool:
                futures = {
                    pool.submit(self.milp_evaluator, candidate, self.config): candidate
                    for candidate in pending
                }
                for future in as_completed(futures):
                    candidate = futures[future]
                    try:
                        result = future.result()
                    except Exception as exc:
                        failures.append((code_key(candidate), exc))
                    else:
                        persist(candidate, result)

        if failures:
            key, exc = failures[0]
            raise RuntimeError(
                f"MILP audit failed for {key}: {type(exc).__name__}: {exc}"
            ) from exc

        # Reviewer input follows selection order, independent of worker finish
        # order and append order on disk.
        return [by_key[code_key(row)] for row in selected if code_key(row) in by_key]

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
                "static": "commuting, weight/degree <= 6, connected Tanner graph",
                "novelty": "BLISS match plus explicit H_X/H_Z replay",
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
        state.pop("failure", None)
        state["status"] = "running"
        self.store.write_state(state)
        self._write_run_meta(state)

        for number in range(int(state["current_round"]) + 1, self.config.max_rounds + 1):
            round_dir = self.store.round_dir(number)
            contract = self._write_contract(number, round_dir)
            self.store.event("round_started", round_number=number)

            try:
                rejected_path = round_dir / "rejected-candidates.jsonl"
                selected_path = round_dir / "selected.jsonl"
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
                    candidates = self._read_jsonl(candidate_path)
                    audited = self._read_jsonl(milp_path)
                    self.store.event(
                        "round_resumed", round_number=number,
                        phase=state.get("round_phase"),
                    )
                else:
                    resume_audit = candidate_path.is_file()
                    if resume_audit:
                        candidates = self._read_jsonl(candidate_path)
                        self.store.event(
                            "round_resumed", round_number=number,
                            phase=state.get("round_phase", "audit"),
                        )
                    else:
                        checkpoint = None
                        if self.config.candidate_file is None:
                            checkpoint = self.evolution_runner(
                                self.config, state, round_dir
                            )
                        if checkpoint:
                            state["last_checkpoint"] = str(checkpoint)

                        candidates, new_offset = read_jsonl_since(
                            self.candidate_log,
                            int(state.get("candidate_offset", 0)),
                        )
                        state["candidate_offset"] = new_offset
                        candidates = _deduplicate(candidates)
                        # Persist raw input and offset before any gate or solver
                        # can fail; otherwise a resume starts after these rows.
                        self._write_jsonl(candidate_path, candidates)
                        state["pending_round"] = number
                        state["round_phase"] = "screen"
                        self.store.write_state(state)

                    candidates, rejected = self._screen_candidates(candidates)
                    self._write_jsonl(candidate_path, candidates)
                    self._write_jsonl(rejected_path, rejected)
                    audited_keys = set(state.get("audited_keys", []))
                    audited_digests = set(
                        state.get("audited_structural_digests", [])
                    )
                    selected = self._read_jsonl(selected_path)
                    if not selected:
                        selected = select_for_milp(
                            candidates, self.archive, audited_keys,
                            self.config.milp_top, audited_digests,
                        )
                        self._write_jsonl(selected_path, selected)
                    if not milp_path.exists():
                        milp_path.write_text("")
                    state["pending_round"] = number
                    state["round_phase"] = "audit"
                    self.store.write_state(state)
                    audited = self._audit_selected(
                        selected, state=state, milp_path=milp_path
                    )
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
