"""Bounded route review and exploration policy; never mathematical evidence."""

from typing import Literal

from pydantic import Field

from ._frontier import Data, Evidence


class StrategyTask(Data):
    obligation_id: str = Field(min_length=1, max_length=80)
    objective: str = Field(min_length=1, max_length=4000)
    success_criterion: str = Field(min_length=1, max_length=2000)
    stop_criterion: str = Field(min_length=1, max_length=2000)
    dependencies: list[Evidence] = Field(min_length=1, max_length=30)


class Alternative(Data):
    route: str = Field(min_length=1, max_length=1000)
    expected_gain: str = Field(min_length=1, max_length=2000)
    obstruction: str = Field(min_length=1, max_length=2000)


class StrategyReview(Data):
    assessment: str = Field(min_length=1, max_length=6000)
    necessity: Literal["necessary_for_goal", "route_specific", "unestablished"]
    decision: Literal["continue_local", "explore_alternative", "pause_exploration"]
    alternatives: list[Alternative] = Field(max_length=3)
    tasks: list[StrategyTask] = Field(max_length=2)
    literature_requests: list[str] = Field(max_length=3, description=(
        "Missing primary sources to request for a future frozen input set, not citations "
        "or permission to browse, change assumptions, or import unverified theorems."
    ))


GOAL = """Complete the declared sparse cyclic two-block CSS research roadmap.
First audit SELF without assuming it. Then resolve uniform birth/lift generation,
cross-parameter distance laws and the certified selector, or prove precise scoped
obstructions. Keep finite certificates distinct from uniform symbolic theorems.
Do not broaden recipe equivalence to all quantum codes or weaken the final goal.
""".strip()

PROMPT = """
STRATEGY REVIEW — review the proof ROUTE, not the correctness of one draft.
This is UNVERIFIED planning, never a proof or a mathematical acceptance vote.
Determine whether the current bottleneck is necessary for the final goal, only
necessary for one chosen route, or not known to be necessary. Justify the choice.
Compare at most three concrete routes: non-local septic relations, admissible
infinite counterfamilies, or certified distance reductions. None is assumed valid.
Identify the shortest justified dependency path to the final goal and its still
open bridges. Local lemma counts and positive votes are not global progress.
Use recent outcomes to explain which exploration should continue or pause.
Distinguish mathematical obstructions from incomplete audits and runtime failures.
Return at most two ORDERED, bounded tasks from the available obligation catalog.
Each needs exact frozen dependencies, a checkable success criterion and a stop
criterion. An exploration gets one solver attempt and fresh independent audits;
failure does not trigger unlimited repair. Identical tasks are not run again.
With continue_local or pause_exploration return no tasks. With explore_alternative
return at least one task. Missing literature goes in literature_requests, never
as an invented citation or dependency. Use only the frozen input directory.
Do not certify any route, close any coverage gap, or redefine any obligation.
"""


def available_routes(obligations, manifest):
    names = {entry["path"] for entry in manifest["files"]}
    return {name: {**task, "missing_inputs": sorted(set(task["inputs"]) - names)}
            for name, task in obligations.items()}


def review_errors(review, routes, manifest):
    errors = []
    if bool(review.tasks) != (review.decision == "explore_alternative"):
        errors.append("only explore_alternative may dispatch tasks, and it requires a task")
    known = {entry["path"]: entry["sha256"] for entry in manifest["files"]}
    for task in review.tasks:
        if task.obligation_id not in routes:
            errors.append("unknown strategy obligation: " + task.obligation_id)
        elif routes[task.obligation_id]["missing_inputs"]:
            errors.append("strategy obligation has missing frozen inputs: " + task.obligation_id)
        for ref in task.dependencies:
            if known.get(ref.path) != ref.sha256:
                errors.append("unlocked strategy dependency: " + ref.path)
    return errors


def review_trigger(round_number, last_round, integrations, interval):
    if last_round == 0:
        return "startup"
    recent = [record for record in integrations if record["round"] >= last_round]
    if (len(recent) >= 2 and not any(record.get("mathematical_progress", False) for record in recent[-2:])
            and all("mathematical_progress" in record for record in recent[-2:])):
        return "two_integrations_without_mathematical_progress"
    def assembled(record):
        if "mathematical_progress" in record:
            return record["mathematical_progress"]
        if "assembly_status" in record:
            return record["assembly_status"] == "dual_reviewed_assembly_pending_manual_check"
        return record["status"].startswith("reviewed_")
    if len(recent) >= 2 and not any(assembled(record) for record in recent[-2:]):
        return "two_unsuccessful_integrations"
    if round_number - last_round >= interval:
        return "periodic"
    return ""


def exploration_slots(attempts, round_number):
    # Never increase the epoch's lane count. One-lane runs alternate with local work.
    if attempts == 1:
        return int(round_number % 2 == 1)
    return min(2, max(1, attempts // 4))
