"""Assembly contracts and cumulative UNVERIFIED navigation, never proof evidence."""

import hashlib
import json
from typing import Literal

from pydantic import Field

from ._frontier import Data, Evidence


def key(value):
    return hashlib.sha256(json.dumps(value, ensure_ascii=False, sort_keys=True,
                                    separators=(",", ":")).encode()).hexdigest()


class GapUpdate(Data):
    gap_id: str = Field(pattern=r"^gap_[a-f0-9]{64}$")
    justification: str = Field(min_length=1, max_length=3000)


class DeferredPiece(Data):
    reference: Evidence
    reason: str = Field(min_length=1, max_length=2000)


class Assembly(Data):
    kind: Literal["assembly", "new_lemma", "blocked"]
    pieces: list[Evidence] = Field(max_length=256)
    deferred_pieces: list[DeferredPiece] = Field(max_length=256)
    partition_identity: str = Field(min_length=1, max_length=6000)
    uncovered_region: str = Field(min_length=1, max_length=6000)
    overlap_argument: str = Field(min_length=1, max_length=6000)
    cutoff_argument: str = Field(min_length=1, max_length=6000)
    gap_updates: list[GapUpdate] = Field(max_length=32)


PROMPT = """
ASSEMBLY CONTRACT: Your primary job is assembly, not another independent lemma.
Return assembly.kind=assembly only when combining at least TWO distinct full
proof inputs into an explicitly justified union. List those pieces by exact
file-byte hashes and cite each in Candidate.dependencies.
Account for EVERY available full proof: either pieces, or deferred_pieces with
its exact reference and a concrete reason (subsumed, incompatible hypotheses,
unresolved overlap, etc.). Do not silently pick two drafts and ignore the rest.
The CANONICAL FULL PROOF INVENTORY below is the authoritative list for pieces
and deferred_pieces. Other frozen reference documents are bibliography, not
inventory members: cite them in Candidate.dependencies when needed, but do not
list them as used or deferred proof pieces. Inventory membership is not proof
certification; every mathematical dependency must still be independently checked.
Deferred explanations are unverified navigation, not assertions that a lemma is false.
State an exact
partition identity, the exact uncontrolled complement, admissible overlap
allocation and all shared-cutoff conditions. Copy the four assembly argument
strings VERBATIM into Candidate.argument: these are mathematical claims that
the fresh reviewers must audit, not assertions hidden in a planning attachment.
Account for the earlier cumulative cells/gaps in planning attachments only;
never erase them by omission or copy bookkeeping assertions into the proof.
If discovering a stronger single lemma, use new_lemma; it may be independently
reviewed, but it is NOT an assembled union. If no justified claim is ready, use
blocked and give concrete research tasks, not an invented positive result.
gap_updates may reference only stable gap IDs supplied below; copy each proposed
resolution's justification into Candidate.argument. A positive candidate review
does not certify the ledger, its geometry, or global coverage. Never label a
possibly nonzero leading term an o(T^2) error just to make the powers feasible.
"""


def classify_deferred(assembly, proof_hashes, frozen_hashes):
    """Separate uniquely listed, byte-locked bibliography; never repair mathematics.

    Return a copy and the complete moved entries for an explicit audit artifact.
    Invalid hashes, unknown paths, duplicate entries, used pieces and canonical
    proof entries stay untouched so the strict contract/evidence gates reject them.
    """
    counts = {}
    for item in assembly.deferred_pieces:
        path = item.reference.path
        counts[path] = counts.get(path, 0) + 1
    used = {ref.path for ref in assembly.pieces}
    kept, bibliography = [], []
    for item in assembly.deferred_pieces:
        ref = item.reference
        target = (bibliography if ref.path not in proof_hashes and ref.path not in used
                  and counts[ref.path] == 1 and frozen_hashes.get(ref.path) == ref.sha256 else kept)
        target.append(item)
    return assembly.model_copy(update={"deferred_pieces": kept}, deep=True), bibliography


def contract_errors(assembly, candidate, ledger, proof_hashes):
    errors = []
    dependencies = {(ref.path, ref.sha256) for ref in candidate.dependencies}
    pieces = {(ref.path, ref.sha256) for ref in assembly.pieces}
    if len(pieces) != len(assembly.pieces):
        errors.append("duplicate assembly piece")
    if any(proof_hashes.get(path) != sha or (path, sha) not in dependencies for path, sha in pieces):
        errors.append("assembly pieces must cite frozen full proof inputs in Candidate.dependencies")
    deferred = [(item.reference.path, item.reference.sha256) for item in assembly.deferred_pieces]
    if len(set(deferred)) != len(deferred) or set(deferred) & pieces:
        errors.append("duplicate or simultaneously used/deferred proof")
    if any(proof_hashes.get(path) != sha for path, sha in deferred):
        errors.append("unlocked deferred proof reference")
    if {path for path, _ in pieces | set(deferred)} != set(proof_hashes):
        errors.append("every available proof must be used or explicitly deferred")
    if assembly.kind == "assembly":
        if len(pieces) < 2:
            errors.append("assembly requires two distinct proof pieces; classify a single lemma as new_lemma")
        for field in ("partition_identity", "uncovered_region", "overlap_argument", "cutoff_argument"):
            if getattr(assembly, field) not in candidate.argument:
                errors.append("missing assembly argument in Candidate: " + field)
    for update in assembly.gap_updates:
        if update.gap_id not in ledger["gaps"]:
            errors.append("unknown cumulative gap: " + update.gap_id)
        if update.justification not in candidate.argument:
            errors.append("gap resolution must appear in Candidate.argument")
    return errors


def empty_ledger():
    return {"trusted_proof": False, "coverage_complete": False, "cells": {}, "gaps": {}, "rounds": []}


def retain_frontier(ledger, frontier, round_number, candidate_sha, review_status):
    """Stable geometry keys; revisions and omitted gaps never disappear.

    Only structurally/reference-valid tables reach here. Even then every cell,
    loss and proposed partition remains mathematically unverified.
    """
    data = frontier.model_dump()
    revision = {"round": round_number, "candidate_sha256": candidate_sha,
                "candidate_review_status": review_status, "frontier": data}
    ledger["rounds"].append(revision)
    for cell in data["cells"]:
        identity = {k: cell[k] for k in ("placements", "source_labels", "temporal_signs",
                                        "outputs", "region", "localization")}
        identity["placements"] = sorted(identity["placements"])
        stable_id = "cell_" + key(identity)
        entry = ledger["cells"].setdefault(stable_id, {
            "id": stable_id, "identity": identity, "first_round": round_number, "revisions": [],
        })
        entry["revisions"].append({"round": round_number, "local_id": cell["id"],
                                   "candidate_sha256": candidate_sha})
        entry["latest"] = cell
        gaps = [cell["gap"]] if cell["gap"] else []
        for gap in gaps:
            retain_gap(ledger, gap, round_number, stable_id, cell["dependencies"])
    for gap in data["partition_gaps"]:
        retain_gap(ledger, gap, round_number, "partition", data["partition_dependencies"])


def retain_gap(ledger, text, round_number, owner, dependencies):
    stable_id = "gap_" + key({"owner": owner, "text": text.strip()})
    entry = ledger["gaps"].setdefault(stable_id, {
        "id": stable_id, "owner": owner, "text": text.strip(), "first_round": round_number,
        "dependencies": dependencies, "resolution_proposals": [], "status": "open",
    })
    entry["last_seen_round"] = round_number


def ledger_view(ledger):
    """Bound prompt growth; full append-only history stays in controller artifacts."""
    cells = list(ledger["cells"].values())
    gaps = list(ledger["gaps"].values())
    # Never call the displayed subset a complete inventory.
    return {
        "caution": "UNVERIFIED navigation only. Not proof, review feedback, or a complete displayed cover.",
        "coverage_complete": False, "ledger_sha256": key(ledger),
        "total_cells": len(cells), "total_gaps": len(gaps),
        "omitted_cells": max(0, len(cells) - 32), "omitted_gaps": max(0, len(gaps) - 32),
        "cells": [{"id": c["id"], "region": c["identity"]["region"][:700],
                   "local_id": c["latest"]["id"], "status": "unverified_proposal",
                   "summary_only": True} for c in cells[-32:]],
        "gaps": [{"id": g["id"], "text": g["text"][:1000], "status": g["status"],
                  "summary_truncated": len(g["text"]) > 1000} for g in gaps[-32:]],
    }
