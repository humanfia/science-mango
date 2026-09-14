"""Untrusted coverage planning and exact power-cutoff compatibility, not proof.

Geometry, constant uniformity and provenance applicability remain mathematical
obligations. This module never certifies a partition, an estimate or quantum-code classification.
"""

from typing import Literal

from pydantic import BaseModel, Field

from ._linear import solve_strict_system

RETAINED_HYPOTHESIS = "UNRESOLVED_PROTOCOL_HYPOTHESIS "

class Data(BaseModel):
    model_config = {"extra": "forbid", "strict": True}


class Evidence(Data):
    path: str
    sha256: str = Field(pattern=r"^[a-f0-9]{64}$")
    section: str = Field(min_length=1, max_length=2000)


RATIONAL = r"^-?(0|[1-9][0-9]{0,8})(/[1-9][0-9]{0,8})?$"


class Power(Data):
    parameter: str = Field(pattern=r"^[a-z][a-z0-9_]{0,31}$")
    value: str = Field(pattern=RATIONAL)


class Parameter(Data):
    name: str = Field(pattern=r"^[a-z][a-z0-9_]{0,31}$")
    meaning: str = Field(min_length=1, max_length=2000)
    shrinks: bool = Field(description=(
        "Every parameter denotes delta(T)=T^(-a), a>=0; shrinks requires a>0. "
        "Use distinct names for different geometric cutoffs; identical symbols do not establish equivalence."
    ))


class Condition(Data):
    id: str = Field(pattern=r"^[a-z][a-z0-9_]{0,47}$")
    coefficients: list[Power] = Field(max_length=8)
    rhs: str = Field(pattern=RATIONAL)
    strict: bool
    justification: str = Field(min_length=1, max_length=3000)
    dependencies: list[Evidence] = Field(min_length=1, max_length=12)


class Bound(Data):
    time_power: str = Field(pattern=RATIONAL)
    log_power: str = Field(pattern=RATIONAL)
    cutoff_powers: list[Power] = Field(max_length=8, description=(
        "Physical powers in C*T^p*log(2+T)^q*product(delta_j^power_j). "
        "Include ALL quantified constant and cutoff-derivative losses. "
        "Substitution gives time exponent p-sum(power_j*a_j)."
    ))
    constant_policy: Literal["uniform", "quantified", "unknown"]
    unknown_dependencies: list[str] = Field(max_length=16)
    norm: str = Field(min_length=1, max_length=2000)
    window_and_limits: str = Field(min_length=1, max_length=3000)
    hypothesis_conditions: list[str] = Field(max_length=48, description=(
        "Only exact IDs declared in Frontier.conditions[].id. Do not put inequalities, "
        "parameter names or generated condition:/bound: row IDs here."
    ))
    dependencies: list[Evidence] = Field(min_length=1, max_length=12)


class Cell(Data):
    id: str = Field(pattern=r"^[a-z][a-z0-9_]{0,47}$")
    placements: list[str] = Field(min_length=1, max_length=12, description=(
        "For r3_b_remaining use outer_1..outer_3 and residual_1..residual_9. "
        "Listing a placement records a local selector, NOT complete coverage of that placement."
    ))
    source_labels: str = Field(min_length=1, max_length=2000)
    temporal_signs: str = Field(min_length=1, max_length=2000)
    outputs: str = Field(min_length=1, max_length=2000)
    region: str = Field(min_length=1, max_length=3000)
    boundary_and_overlap: str = Field(min_length=1, max_length=3000)
    localization: str = Field(min_length=1, max_length=3000)
    status: Literal["bounded", "open"]
    bound: Bound | None
    gap: str = Field(max_length=3000)
    dependencies: list[Evidence] = Field(min_length=1, max_length=12)


class Frontier(Data):
    obligation_id: str
    partition_argument: str = Field(min_length=1, max_length=12000)
    partition_dependencies: list[Evidence] = Field(min_length=1, max_length=12)
    partition_gaps: list[str] = Field(max_length=32)
    parameters: list[Parameter] = Field(max_length=8)
    conditions: list[Condition] = Field(max_length=48)
    cells: list[Cell] = Field(min_length=1, max_length=64)


CAUTION = (
    "UNVERIFIED PLANNING ONLY. A listed bounded cell is a claimed local estimate, "
    "not a proved partition or complete placement. Exact rational arithmetic checks "
    "only the supplied power inequalities; it does not verify geometry, constants, "
    "norms, limit order or proof applicability. Feasibility is only a sufficient "
    "strict-power schedule for these declarations. Infeasibility does not exclude "
    "logarithmic boundary schedules, other estimates or quantum-code classification. "
    "Only pieces explicitly proposed as o(T^2) errors belong in this power system; "
    "a possibly nonzero T^2 leading term must be retained, not assumed to vanish."
)

FRONTIER_PROMPT = """
Also return a structured frontier for the unchanged authoritative obligation.
This is a planning attachment, never a proof or a substitute for the full Candidate.
Encode only pieces explicitly proposed as o(T^2) remainders, not possibly nonzero
T^2 leading terms. Preserve those leading terms and their outstanding analysis in
partition_gaps. The goal is not to assume the original source's limit is zero.
List selected cells by original placement, source labels, temporal signs, all
outputs, exact region, boundary/overlap handling and admissible localization.
Do NOT invent a reduced target universe or mark a whole placement covered because
one local selector is bounded. Explicitly list unresolved partition obligations.
For r3_b_remaining the target remains three outer-loop and nine residual-cross
placements, all original source labels/signs/outputs; use outer_1..outer_3 and
residual_1..residual_9 as identifiers.
Select at most ONE bound per cell for the proposed joint schedule. Record physical
cutoff powers, time and log powers, every constant/cutoff-derivative loss, norm,
actual window and limit order. C_delta with unknown delta-dependence MUST have
constant_policy=unknown and a nonempty unknown_dependencies list. Never silently
replace C_delta by a uniform constant. Use rational strings, not executable math.
Every named cutoff means delta=T^(-a), a>=0; shrinks requires a>0. Explicit linear
conditions act on these a's. Include all overlap, applicability and scale-order
conditions; hypotheses that are not representable must remain partition_gaps.
hypothesis_conditions contains ONLY IDs from conditions[].id, never explanatory
prose. Keep qualitative premises in Candidate and partition_gaps, not dummy
inequalities. A metadata repair does not establish those premises.
Do not identify geometrically different cutoffs merely because notation matches.
Physical cutoff powers b give time exponent p-sum(b*a); the checker searches only
strict exponent <2, not logarithmic endpoint gains. Put ALL statements required
by your mathematical claim in Candidate itself: reviewers audit that full claim,
not the attachment. Give exact frozen dependency hashes for every row/condition.
"""


def analyze_frontier(frontier, manifest, obligation):
    """Validate references, solve declared powers and produce bounded research tasks."""
    from fractions import Fraction

    # Manifest structure is checked by the flow's evidence layer / offline CLI.
    known = {entry["path"]: entry["sha256"] for entry in manifest["files"]}
    errors = []
    if frontier.obligation_id != obligation:
        errors.append("frontier obligation changed")
    if obligation not in {"self_audit", "r3_b_remaining", "r5_global", "r3_r5_leading"}:
        errors.append("T^2 cutoff planning is not supported for this obligation")
    references = list(frontier.partition_dependencies)
    for condition in frontier.conditions:
        references.extend(condition.dependencies)
    for cell in frontier.cells:
        references.extend(cell.dependencies)
        if cell.bound:
            references.extend(cell.bound.dependencies)
    for ref in references:
        if known.get(ref.path) != ref.sha256:
            errors.append("unlocked frontier dependency: " + ref.path)

    def unique(values, kind):
        if len(values) != len(set(values)):
            errors.append("duplicate " + kind)
        return set(values)

    parameters = unique([item.name for item in frontier.parameters], "parameter")
    condition_ids = unique([item.id for item in frontier.conditions], "condition")
    unique([item.id for item in frontier.cells], "cell")

    def coefficients(values):
        names = [item.parameter for item in values]
        unique(names, "coefficient parameter")
        if not set(names) <= parameters:
            errors.append("unknown coefficient parameter")
        return {item.parameter: item.value for item in values}

    rows = [{"id": "parameter:" + item.name, "coefficients": {item.name: "-1"},
             "rhs": "0", "strict": item.shrinks} for item in frontier.parameters]
    row_dependencies = {row["id"]: frontier.partition_dependencies for row in rows}
    for condition in frontier.conditions:
        rows.append({"id": "condition:" + condition.id,
                     "coefficients": coefficients(condition.coefficients),
                     "rhs": condition.rhs, "strict": condition.strict})
        row_dependencies["condition:" + condition.id] = condition.dependencies
    unknowns = []
    required = ([f"outer_{index}" for index in range(1, 4)] +
                [f"residual_{index}" for index in range(1, 10)]
                if obligation == "r3_b_remaining" else [])
    mentioned = set()
    for cell in frontier.cells:
        unique(cell.placements, "placement within cell")
        mentioned.update(cell.placements)
        if required and not set(cell.placements) <= set(required):
            errors.append("unknown original placement in " + cell.id)
        if (cell.status == "bounded") != (cell.bound is not None):
            errors.append("cell status/bound mismatch: " + cell.id)
        if cell.status == "open" and not cell.gap:
            errors.append("open cell lacks a concrete gap: " + cell.id)
        bound = cell.bound
        if bound is None:
            continue
        powers = coefficients(bound.cutoff_powers)
        if not set(bound.hypothesis_conditions) <= condition_ids:
            errors.append("unknown hypothesis condition in " + cell.id)
        if bound.constant_policy == "unknown" or bound.unknown_dependencies:
            unknowns.append({"cell": cell.id, "dependencies": bound.unknown_dependencies or
                             ["constant dependence has not been quantified"]})
            continue
        rows.append({"id": "bound:" + cell.id,
                     "coefficients": {key: str(-Fraction(value)) for key, value in powers.items()},
                     "rhs": str(Fraction(2) - Fraction(bound.time_power)), "strict": True})
        row_dependencies["bound:" + cell.id] = [*bound.dependencies, *cell.dependencies]

    report = {
        "obligation_id": obligation, "trusted_proof": False, "coverage_complete": False,
        "caution": CAUTION, "validation_errors": sorted(set(errors)),
        "coverage": {
            "bounded_cells": [cell.id for cell in frontier.cells if cell.status == "bounded"],
            "open_cells": [cell.id for cell in frontier.cells if cell.status == "open"],
            "unmentioned_placements": [name for name in required if name not in mentioned],
            "partition_gaps": frontier.partition_gaps,
            "partition_verified": False,
        },
        "cutoffs": {"status": "invalid", "unknowns": unknowns, "rows": rows},
        "tasks": [],
    }
    if errors:
        return report
    algebra = solve_strict_system([item.name for item in frontier.parameters], rows)
    retained = [gap for gap in frontier.partition_gaps if gap.startswith(RETAINED_HYPOTHESIS)]
    if retained:
        unknowns.append({"cell": "", "protocol_hypotheses": True, "dependencies": retained})
    report["cutoffs"].update(status="unknown" if unknowns else algebra["status"], algebra=algebra)

    def task(objective, success, dependencies):
        refs = []
        for ref in dependencies:
            value = ref.model_dump()
            if value not in refs:
                refs.append(value)
        report["tasks"].append({
            "obligation_id": obligation,
            "objective": ("UNVERIFIED RESEARCH TARGET: " + objective)[:4000],
            "success_criterion": success[:2000], "dependencies": refs[:30],
        })

    if algebra["status"] == "infeasible":
        conflict = [row for row in rows if row["id"] in algebra["conflict_ids"]]
        expressions = []
        for row in conflict:
            lhs = " + ".join(f"({value})*a_{name}" for name, value in row["coefficients"].items()) or "0"
            expressions.append(row["id"] + ": " + lhs + (" < " if row["strict"] else " <= ") + row["rhs"])
        # Bound/condition sources precede generic parameter-definition references.
        sources = [ref for row in sorted(conflict, key=lambda row: row["id"].startswith("parameter:"))
                   for ref in row_dependencies[row["id"]]]
        excerpt = "; ".join(expressions)
        if len(excerpt) > 2600:
            excerpt = excerpt[:2600] + " [TRUNCATED conflict excerpt]"
        meanings = "; ".join(item.name + "=" + item.meaning[:100] for item in frontier.parameters)
        task("Resolve conflicting DECLARED conditions on delta_j=T^(-a_j): " + excerpt +
             ". Cutoff descriptions (abbreviated): " + meanings,
             "Supply a justified stronger bound or alternative schedule with all losses explicit. "
             "This bounded excerpt and at most 30 cited sections may be incomplete; rederive the full "
             "scheme from source proofs, never infer it from opaque row IDs. "
             "A conflict here is not a theorem that other bounds or quantum-code classification are impossible.",
             sources)
    for unknown in unknowns:
        if unknown.get("protocol_hypotheses"):
            task("Justify retained prerequisites: " + "; ".join(unknown["dependencies"]),
                 "Prove each original premise from the full source, with all parameter losses. "
                 "Metadata confirmation and feasible exponent algebra do not discharge these premises.",
                 frontier.partition_dependencies)
            continue
        cell = next(item for item in frontier.cells if item.id == unknown["cell"])
        task("Quantify constant and cutoff-derivative dependence for cell " + cell.id +
             ": " + "; ".join(unknown["dependencies"]),
             "Read the full bound, give explicit uniform parameter powers and all validity conditions; "
             "do not assume a fixed-cutoff constant is uniform.", cell.bound.dependencies)
    for cell in frontier.cells:
        if cell.status == "open" or cell.gap:
            task("Resolve cell " + cell.id + ": " + cell.gap + "; region: " + cell.region,
                 "Prove the stated missing local estimate or a precise obstruction, retaining source labels, "
                 "signs, all outputs, localization validity, window and explicit cutoff losses.", cell.dependencies)
    partition_gaps = list(frontier.partition_gaps)
    if report["coverage"]["unmentioned_placements"]:
        partition_gaps.append("No cells yet listed for " +
                              ", ".join(report["coverage"]["unmentioned_placements"]))
    for gap in partition_gaps:
        task("Audit or close this partition obligation: " + gap,
             "Give a checkable partition identity or admissible partition of unity with all boundaries "
             "and overlaps accounted for; label remaining uncovered sets explicitly.", frontier.partition_dependencies)
    report["tasks"] = report["tasks"][:8]
    return report
