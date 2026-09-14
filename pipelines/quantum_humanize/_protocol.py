"""Conservative metadata recovery; no mathematical claim or proof vote is repaired."""

from pydantic import BaseModel, Field

from ._frontier import Data, RETAINED_HYPOTHESIS


class Confirmation(Data):
    index: int = Field(ge=0)
    path: str
    confirmed: bool
    section: str = Field(min_length=1, max_length=2000)
    explanation: str = Field(min_length=1, max_length=2000)


class ReferenceRepair(Data):
    confirmations: list[Confirmation] = Field(max_length=256)


def references(value, location=()):
    """Visit only typed reference objects, never parse or rewrite mathematical text."""
    if isinstance(value, BaseModel):
        fields = type(value).model_fields
        if set(fields) == {"path", "sha256", "section"}:
            yield location, value
        else:
            for name in fields:
                yield from references(getattr(value, name), (*location, name))
    elif isinstance(value, list):
        for index, item in enumerate(value):
            yield from references(item, (*location, index))


def reference_issues(value, manifest):
    known = {entry["path"]: entry["sha256"] for entry in manifest["files"]}
    return [{"index": index, "location": list(location), "path": ref.path,
             "supplied_sha256": ref.sha256, "canonical_sha256": known.get(ref.path),
             "section": ref.section}
            for index, (location, ref) in enumerate(references(value))
            if known.get(ref.path) != ref.sha256]


def apply_confirmations(value, issues, response):
    """All-or-nothing, explicit source confirmation; only hash/section may change."""
    expected = {item["index"]: item for item in issues}
    answers = response.confirmations
    if len(answers) != len(expected) or {item.index for item in answers} != set(expected):
        return value, ["confirm every mismatched reference exactly once"]
    for answer in answers:
        issue = expected[answer.index]
        if not issue["canonical_sha256"] or answer.path != issue["path"] or not answer.confirmed:
            return value, ["source not confirmed at its exact frozen path"]
    revised = value.model_copy(deep=True)
    refs = dict((index, ref) for index, (_, ref) in enumerate(references(revised)))
    for answer in answers:
        refs[answer.index].sha256 = expected[answer.index]["canonical_sha256"]
        refs[answer.index].section = answer.section
    return revised, []


def retained_hypotheses(frontier):
    ids = {item.id for item in frontier.conditions}
    return [f"{RETAINED_HYPOTHESIS}{cell.id}: {text}"
            for cell in frontier.cells if cell.bound is not None
            for text in cell.bound.hypothesis_conditions if text not in ids]


def frontier_repair_errors(original, repaired, obligation):
    """A metadata correction cannot erase geometry, bounds, premises or gaps."""
    errors = []
    if repaired.obligation_id != obligation:
        errors.append("frontier obligation was not restored")
    for field in ("partition_argument", "partition_dependencies", "parameters"):
        if getattr(original, field) != getattr(repaired, field):
            errors.append("metadata repair changed mathematical field: " + field)
    for condition in original.conditions:
        if condition not in repaired.conditions:
            errors.append("metadata repair removed or changed an existing condition")
    required = [*original.partition_gaps, *retained_hypotheses(original)]
    if not set(required) <= set(repaired.partition_gaps):
        errors.append("metadata repair dropped an unresolved gap or hypothesis")
    if [cell.id for cell in original.cells] != [cell.id for cell in repaired.cells]:
        errors.append("metadata repair removed, reordered or renamed cells")
        return errors
    known = {item.id for item in original.conditions}
    for before, after in zip(original.cells, repaired.cells):
        old, new = before.model_dump(), after.model_dump()
        if before.bound is not None and after.bound is not None:
            old_ids = set(old["bound"].pop("hypothesis_conditions")) & known
            new_ids = set(new["bound"].pop("hypothesis_conditions"))
            if not old_ids <= new_ids:
                errors.append("metadata repair dropped a valid condition reference: " + before.id)
        if old != new:
            errors.append("metadata repair changed a cell's mathematical content: " + before.id)
    return errors
