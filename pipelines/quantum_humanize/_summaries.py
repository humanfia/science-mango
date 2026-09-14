"""Content-addressed navigation summaries, never substitute proof evidence."""

from pathlib import Path
from typing import Literal

from pydantic import Field

from ._evidence import _directory, _read_regular, _write_new
from ._frontier import Data, Evidence


class Summary(Data):
    claim: str = Field(min_length=1, max_length=600)
    region: str = Field(min_length=1, max_length=600)
    source_sign_output_scope: str = Field(min_length=1, max_length=600)
    assumptions: str = Field(min_length=1, max_length=600)
    selector_requirements: str = Field(min_length=1, max_length=600)
    cutoffs_and_constant_losses: str = Field(min_length=1, max_length=600)
    bound: str = Field(min_length=1, max_length=600)
    uncovered: str = Field(min_length=1, max_length=600)


class Record(Data):
    version: Literal[1]
    reference: Evidence
    dependencies: list[Evidence]
    source: Literal["author_fields", "legacy_excerpt"]
    summary: Summary
    unknown_fields: list[str]
    truncated_fields: list[str]
    trusted_proof: Literal[False]


AUTHOR_PROMPT = """
Return summary alongside the complete candidate, in this SAME call. It is a
bounded navigation attachment, not a replacement argument. Record the precise
claim, region, original source/sign/output scope, assumptions, selector norms,
cutoffs and constant losses, bound, and uncovered complement. Each field is at
most 600 characters. Say explicitly when a detail is unknown or not established;
never omit a restriction to make the summary look stronger. Do not put ledger
counts or historical review claims in it. Two fresh reviewers will check BOTH
the complete candidate and this summary's fidelity. Do not cite summary files
as evidence; dependencies always name full frozen sources.
"""


BATCH_PROMPT = """
BOUNDED INTEGRATION BATCH: Work only on the supplied comparison and selected new
root drafts. First use their structured summaries for orientation, then read
their FULL arguments and EVERY dependency actually invoked. Summaries, especially
legacy excerpts with missing fields, are untrusted indexes, never lemmas or
evidence. Do not scan or re-summarize the complete archive. The full frozen archive
remains accessible for dependency checking; availability is not a reading mandate.
The BATCH ROOT INVENTORY replaces the all-archive inventory for assembly.pieces
and deferred_pieces. Account for every batch root, not every archived draft.
Other full drafts may be cited as supporting dependencies, but are not new root
pieces in this batch. The controller retains all unselected drafts as unassessed
queued work; do not invent mathematical deferral reasons or archive-wide counts.
Preserve all previous mathematical coverage and explicit gaps. No summary or
unchanged registry entry establishes coverage. Prove one concrete, bounded
addition/replacement with compatible parameters. The new full argument and its
mathematical delta still require two fresh independent reviews.
"""


def cache(repo, reference, candidate, authored=None):
    """Immutable per-proof-byte-SHA cache; legacy fields are explicitly incomplete."""
    reference = Evidence.model_validate(reference)
    dependencies = [Evidence.model_validate(ref.model_dump()) for ref in candidate.dependencies]
    directory = Path(repo) / ".humanize-quantum-runs" / "summary-cache-v1"
    _directory(directory.parent)
    directory.mkdir(mode=0o700, exist_ok=True)
    _directory(directory)
    path = directory / (reference.sha256 + ".json")
    if path.exists() or path.is_symlink():
        record = Record.model_validate_json(_read_regular(path))
        if ((record.reference.path, record.reference.sha256) != (reference.path, reference.sha256)
                or record.dependencies != dependencies):
            raise ValueError("summary cache does not match the exact full candidate")
        return record
    unknown, truncated = [], []
    if authored is None:
        values = {field: "Not extracted from this legacy draft; read the full argument."
                  for field in Summary.model_fields}
        unknown = [field for field in values if field not in {"claim", "uncovered"}]
        for field, text in (("claim", candidate.claim),
                            ("uncovered", "\n".join(candidate.remaining_obligations))):
            values[field] = text[:600] or "Not extracted; absence is not a coverage claim."
            if not text:
                unknown.append(field)
            if len(text) > 600:
                truncated.append(field)
        authored = Summary.model_validate(values)
        source = "legacy_excerpt"
    else:
        authored = Summary.model_validate(authored)
        source = "author_fields"
    record = Record(version=1, reference=reference, dependencies=dependencies, source=source,
                    summary=authored, unknown_fields=unknown, truncated_fields=truncated,
                    trusted_proof=False)
    data = (record.model_dump_json() + "\n").encode()
    try:
        _write_new(path, data)
    except FileExistsError:
        # Another writer may have cached the same immutable full draft first.
        return cache(repo, reference.model_dump(), candidate)
    return record


def view(record):
    """Do not expand the dependency graph into every navigation prompt."""
    return {key: value for key, value in record.model_dump().items() if key != "dependencies"} | {
        "dependency_count": len(record.dependencies),
        "dependency_list_location": "Read dependencies in the referenced full candidate.",
    }


def trim_reading_index(context):
    start = "Available required-reading index (including explicitly selected new inputs):\n"
    end = "\n_snapshot.json lists exact hashes."
    if start not in context or end not in context.split(start, 1)[1]:
        return context
    before, rest = context.split(start, 1)
    _, after = rest.split(end, 1)
    return before + "The full archive is indexed in _snapshot.json; select the batch and read invoked dependencies." + end + after


def inventory(proof_hashes, baseline, focus, history):
    """Unselected roots are retained, not model-deferred or mathematically dismissed."""
    selected = {item["reference"]["path"] for item in focus}
    if baseline:
        selected.add(baseline)
    return {"trusted_proof": False, "coverage_complete": False,
            "batch_root_paths": sorted(selected),
            "drafts": [{"path": path, "sha256": sha,
                        "batch_state": "selected" if path in selected else "outside_batch_retained",
                        "latest_assessment": history.get(path, "unassessed_queued")}
                       for path, sha in sorted(proof_hashes.items())]}
