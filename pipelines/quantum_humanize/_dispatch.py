"""Semantic dispatch review; navigation only, with no mathematical matching rules."""

from ._assembly import ledger_view
from ._summaries import view


PROMPT = """
PRE-DISPATCH SEMANTIC REVIEW — organize research, never certify mathematics.
You alone assess semantic duplication, subsumption, useful novelty, task splitting,
merging and priority. The controller does not infer formula/region equivalence.
Review the proposed task pool TOGETHER, against existing drafts, previous attempts,
reserved exploration and audit/repair work. Explicit integrator suggestions,
deferred-piece audits and frontier-generated tasks can describe the SAME work.
Different wording, task IDs or hashes do not make different mathematical goals.

Distinguish existing geometric coverage, a local estimate's exact hypotheses,
an unfinished applicability audit, and a genuinely uncontrolled complement.
'Not read in this integration' does NOT mean 'the old estimate must be reproved'.
Same region alone does NOT imply duplication: source/sign/output, selector class,
cutoffs, constant losses and window quantifiers may differ materially. Preserve
useful weaker hypotheses or stronger bounds when they address a named bottleneck;
do not occupy lanes with arbitrary improvements to already sufficient estimates.
For partial overlaps, merge the common work or split into complementary targets.
Keep any intentionally independent exploration only with an explicit rationale.
Do not cancel or merge the two independent mathematical reviewers or reserved jobs.

Return at most available_solver_slots ordered tasks for THIS round. Each task's
objective/success_criterion must say what differs from the cited existing result,
the exact unresolved step, and what would satisfy it. Reuse established arguments
subject to their actual assumptions; do not ask for an unchanged union or reward
an unrelated strengthening instead of the assigned applicability audit. You may
form a new bounded complement/assembly task if frozen inputs justify the target.
Return fewer tasks, including [], when no useful nonoverlapping work is justified;
never fill idle lanes just to meet a count. Before returning, semantically check
the final tasks against EACH OTHER and against the reserved/prior work again.

retire_task_ids names only supplied proposal IDs that this plan replaces/merges
or recommends shelving as redundant. Explain those decisions and any deferral in
assessment, identifying the original IDs and supporting draft references. Omitted
proposal IDs stay queued; retirement is reversible planning, never gap closure or
proof acceptance. The controller keeps the original task and review artifacts.

Use the supplied cached summaries and compact draft index first; they are NOT
proofs. Read frozen full sources selectively when scope is ambiguous. Do not
re-audit the whole archive or reconstruct unchanged proofs for scheduling. Missing
summary fields and truncated/omitted history are unknowns, not evidence of absence.
Past review status is scheduling context only, never a premise. If uncertain about
duplication, retain a narrowly scoped applicability task or defer it explicitly.
Keep the authoritative obligation, physical constraints and exact frozen citations.
Your assessment/retirements must never become mathematical review evidence.
"""


def navigation(driver, state, proposals, reserved, summary):
    """Bound context size; expose truncation and preserve the full frozen archive."""
    # Fresh drafts already have cached summaries when summary integration is on.
    selected = {ref["path"] for item in proposals for ref in item["task"]["dependencies"]}
    selected.add(summary["latest_integration"] or driver.config.integration_baseline)
    selected.update(list(driver.summary_cache)[-16:])
    history = list(driver.research_tasks.values())
    pending = [job.candidate for job in state["pending"]] + [
        job.candidate for job in driver.pending_audits]
    return {
        "trusted_proof": False,
        "proposals": proposals,
        "queued_tasks_total": len(state["tasks"]),
        "queued_tasks_omitted": max(0, len(state["tasks"]) - len(proposals)),
        "task_history": history[-16:], "task_history_omitted": max(0, len(history) - 16),
        "recent_results": [{"round": item["round"], "candidate_sha256": item.get("sha256", ""),
                            "status": item["status"], "proof_path": item.get("proof_path", "")}
                           for item in summary["candidates"][-16:]],
        "reserved_work": reserved,
        "pending_work": [{"claim": c.claim[:1200], "claim_truncated": len(c.claim) > 1200,
                          "obligation_id": c.obligation_id} for c in pending[:16]],
        "pending_work_omitted": max(0, len(pending) - 16),
        "coverage": ledger_view(driver.frontier_ledger),
        "latest_integration": summary["latest_integration"] or driver.config.integration_baseline,
        "draft_index": [{"reference": record.reference.model_dump(),
                         "claim_excerpt": record.summary.claim,
                         "summary_only": True} for record in driver.summary_cache.values()],
        "draft_summaries": [view(record) for path, record in driver.summary_cache.items() if path in selected],
        "summaries_available": driver.config.summary_integration,
        "previous_dispatch_review": state.get("dispatch_review", None),
    }
