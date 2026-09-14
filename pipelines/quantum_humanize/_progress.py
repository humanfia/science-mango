"""Explicit mathematical deltas and bounded integration work, never proof votes."""

from collections import deque
import re
from typing import Literal

from pydantic import Field

from ._frontier import Data, Evidence


class Progress(Data):
    kind: Literal["initial", "coverage_expansion", "stronger_bound", "weaker_hypotheses", "proof_repair", "none"]
    baseline: Evidence | None
    previous_statement: str = Field(max_length=4000)
    improved_statement: str = Field(max_length=4000)
    justification: str = Field(max_length=6000)


PROMPT = """
INCREMENTAL INTEGRATION: Identify stronger versions and assemble the strongest
justified mathematical claim. First inspect the focused new inputs below and
test a specific replacement or addition to the comparison draft. Inventory
membership and historical votes certify nothing; verify the invoked arguments.
Return progress separately from assembly. Its baseline must be the exact supplied
comparison reference (or null when absent). Use initial only with no comparison.
Otherwise state a coverage_expansion, stronger_bound, weaker_hypotheses or genuine
proof_repair. Copy previous_statement, improved_statement and justification
VERBATIM into Candidate.argument so both new reviewers audit the mathematical
delta itself. Cite the baseline in Candidate.dependencies, read it in full, and
preserve old coverage unless a stated, proved correction requires changing it.
The comparison reference establishes what the old draft stated, not that its
claims are true. Independently verify mathematics actually reused. Historical
controller remarks are not mathematical premises and must not be propagated.
New wording, citations, ledger counts, file bookkeeping and rechecking the same
union are NOT mathematical progress: use none and do not manufacture an advance.
Changing a cutoff schedule must justify its domain and all constant losses.
When a focused input cannot be used, name the precise unverified dependency,
selector condition, overlap or cutoff step in deferred_pieces.reason and propose
a bounded next_task to check it. 'Not audited yet' alone is not a resolution.

CONTROL/MATHEMATICS BOUNDARY: All ledger/cell IDs, counts, frontier attachments,
partition_gaps fields and review/navigation status belong ONLY in planning
attachments. Never copy those bookkeeping assertions into Candidate.claim or
Candidate.argument, even to correct an older draft. Describe actual mathematical
sets and unresolved conditions in the proof without referring to hidden tables.
Reviewers cannot see controller attachments. Correcting stale navigation is not
proof_repair and does not require reconstructing an unchanged theorem.
"""


def navigation_errors(candidate):
    text = candidate.claim + "\n" + candidate.argument
    markers = re.findall(
        r"\b(?:gap|cell)_[a-f0-9]{64}\b|\bpartition_gaps\b|coverage-ledger|"
        r"\bcumulative\s+(?:navigation|accounting|ledger)\b|"
        r"\b(?:supplied|current)\s+navigation\b", text, re.IGNORECASE)
    return (["Move controller-only navigation assertions out of Candidate; preserve the mathematical "
             "partition, assumptions and complement. Unreviewable markers: " + ", ".join(sorted(set(markers)))]
            if markers else [])


def progress_errors(delta, candidate, baseline):
    errors = []
    expected = (baseline["path"], baseline["sha256"]) if baseline else None
    actual = (delta.baseline.path, delta.baseline.sha256) if delta.baseline else None
    if actual != expected:
        errors.append("progress must name the exact frozen comparison draft")
    if delta.kind == "initial" and baseline:
        errors.append("initial is not progress relative to an existing comparison draft")
    if delta.kind not in {"initial", "none"}:
        if not baseline:
            errors.append("a mathematical delta requires a frozen comparison draft")
        elif expected not in {(ref.path, ref.sha256) for ref in candidate.dependencies}:
            errors.append("Candidate.dependencies must include the comparison draft")
        for field in ("previous_statement", "improved_statement", "justification"):
            value = getattr(delta, field)
            if not value.strip() or value not in candidate.argument:
                errors.append("missing mathematical progress argument in Candidate: " + field)
        if " ".join(delta.previous_statement.split()) == " ".join(delta.improved_statement.split()):
            errors.append("identical mathematical statements do not establish a delta")
    return errors


def focused_inputs(candidates, hashes, baseline, new_paths, attempts, preferred):
    """At most eight full-text pointers; excerpts are navigation, not proof."""
    ranks = {path: i for i, path in enumerate(preferred)}
    paths = [p for p in candidates if p != baseline]
    paths.sort(key=lambda p: (attempts.get(p, 0), p not in new_paths,
                              ranks.get(p, len(ranks)), p))
    return [{"reference": {"path": p, "sha256": hashes[p], "section": "Full candidate; verify all invoked arguments"},
             "new_since_last_attempt": p in new_paths,
             "claim_excerpt": candidates[p].claim[:1800],
             "excerpt_truncated": len(candidates[p].claim) > 1800,
             "previous_focus_attempts": attempts.get(p, 0), "trusted_proof": False}
            for p in paths[:8]]


def compatibility_tasks(focus, assembly, baseline, obligation):
    deferred = {item.reference.path: item for item in assembly.deferred_pieces}
    tasks = []
    for item in focus:
        ref = item["reference"]
        if ref["path"] not in deferred:
            continue
        reason = deferred[ref["path"]].reason
        tasks.append({"obligation_id": obligation,
            "objective": "Audit integration of the focused full draft " + ref["path"]
                         + ". Pending applicability issue (UNVERIFIED): " + reason,
            "success_criterion": "Read the full draft and comparison. Prove a replacement/addition with "
                "explicit old/new regions or bounds, all source/sign/output and selector assumptions, "
                "and compatible cutoffs; otherwise identify the exact mathematical step still missing. "
                "Do not merely rewrite the old union or report that the draft has not been audited.",
            "dependencies": [ref] + ([baseline] if baseline else [])})
    return tasks


def interleave(groups):
    """Preserve overflow; explicit, compatibility and generic work share the queue."""
    queues = [deque(group) for group in groups]
    while any(queues):
        for queue in queues:
            if queue:
                yield queue.popleft()


def pending_tasks(entries):
    groups = [[] for _ in range(3)]
    for entry in entries:
        if entry["status"] == "queued":
            groups[entry.get("priority_group", 2)].append(entry["task"])
    return list(interleave(groups))
