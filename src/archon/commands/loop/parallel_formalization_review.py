"""Target-scoped parallel semantic Review for autoformalization."""

from __future__ import annotations

import json
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable

from archon.agent import ClaudeBackend, build_runner
from archon.commands.tooling.domain_profile import load_domain_profile
from archon.commands.tooling.project_config import HarnessDescriptor

from .formalization_review_gate import REVIEW_SCHEMA_VERSION
from .native_semantic_review import (
    build_independent_rederivation_example,
    build_native_semantic_review_contract,
    build_native_schema_feedback,
    render_independent_rederivation_instructions,
    validate_independent_rederivation,
)
from .parallel_review import TargetReviewOutcome, TargetReviewSpec
from .problem_only_review_contract import (
    ProblemOnlyReviewContractError,
    is_native_problem_only_contract,
    materialize_controller_review_provenance,
    native_problem_image_args,
    native_source_contract_provenance,
    render_native_composition_accounting_prompt,
    render_native_source_contract_prompt,
    resolve_target_review_source_contract,
    validate_native_resolved_answer_submission_current,
    validate_native_review_source_certificate,
    validate_review_source_contract_current,
)
from .review_source_contract import (
    SOURCE_INCONSISTENCY_KIND,
    is_answer_blind_contract,
)
from .review_feedback import (
    render_validation_retry_feedback,
    safe_preflight_summary,
    sanitized_review_history,
)
from .trusted_bridge_activation import (
    build_trusted_bridge_review_context,
    validate_trusted_bridge_requests,
)


FORMALIZATION_REVIEW_REPORT_FILENAME = "parallel-formalization-review.json"
_REQUIRED_CHECKS = (
    "source_faithfulness",
    "derivability",
    "abstraction_sufficiency",
    "uncertainty_propagation",
    "branch_orientation",
    "countermodel_resistance",
)
_NOT_APPLICABLE_CHECKS = {"uncertainty_propagation", "branch_orientation"}
_PASS = {"pass", "passed", "approved", "review-passing", "review_passing"}
_FAIL = {
    "fail", "failed", "blocked", "partial", "needs_redraft",
    "needs redraft", "rejected",
}
_NOT_APPLICABLE = {"not_applicable", "not applicable", "n/a", "na"}
_BRIDGE_PASS = {"covered", "grounded", "encoded", "proved", "pass", "passed"}
_BRIDGE_FAIL = {"blocked", "failed", "missing", "partial", "needs_redraft"}
_SCHEMA_RETRY_MARKER = "CONTROLLER STRUCTURAL SCHEMA FEEDBACK"
_MAX_SCHEMA_FEEDBACK_ITEM_BYTES = 512
_MAX_SCHEMA_FEEDBACK_ITEMS = 4
_MAX_SCHEMA_FEEDBACK_TOTAL_BYTES = 2_048

_CHEMISTRY_DECISIVE_DEFECT_PROTOCOL = """Use requested-output materiality as
the hard-fail boundary. Mark the Review failed only for a semantic defect that
can change, erase, or make underdetermined a requested output: a missing or
wrong output/value/unit/branch/scope; answer smuggling or a vacuous,
disconnected carrier; a contradiction in the problem-facing statement; or a
concrete source-compatible countermodel, under the same stated assumptions,
that changes the output. Name the affected output and the causal defect in the
failure evidence. An imagined alternative outside the source-stated model is
not such a countermodel.

For a source-bounded contest identification that explicitly asks for a concrete
result from stated staged observations, accept the intended bounded
inverse-problem scope when the candidate derives its smallest finite domain before
filtering from stated or certified-prior constituents, named external inputs,
and ordinary charge/valence bounds, then applies the source observations and
outcome-decisive balanced ledgers uniformly. This does not weaken answer-
smuggling checks: a candidate-named singleton, freely chosen exclusion flag,
opaque predicate, or reflexive result still fails. A blocking countermodel in
that scope must ground every extra outcome-changing species or pathway in an
exact problem locator, activated target-bound literature within its scope, or
an established ordinary chemical law. A merely invented atom-balanced side
reaction or volatile stream is not source-compatible.

Apply any broader generic `fails closed`, bridge-completeness, candidate-domain,
or staged-ledger wording elsewhere in this prompt only to a premise or carrier
that is outcome-decisive under this boundary.

Accept an explicit contest idealization, source-signaled approximation, or
source-indicated dominant/slow leg within its stated scope. Audit that the Lean
claim does not exceed the scope and that the approximation is applied to the
right branch or stage; do not demand an open-world chemistry model merely to
replace that declared contest model.

Missing literature that is not needed for the derivation, omitted irrelevant
species/byproducts/phases, absence of a complete open-world reaction closure,
or failure to prove a stronger unrequested theorem is evidence-only, not a
hard failure. Record the limitation and why it cannot affect the requested
output while leaving the applicable check passed (or not_applicable where the
schema permits). Do not block a bridge or request a dormant rule for such a
non-decisive limitation."""


_CHEMISTRY_TRUSTED_BRIDGE_PROTOCOL = """Trace every outcome-decisive
non-mathematical chemistry bridge to its ultimate authority. A
candidate-local `axiom`, `def`, `theorem`,
structure field, predicate, or fully-qualified name is not a trusted rule merely
because the candidate compiles or uses it in a proof. Count a local carrier only
when its decisive implication reduces to an exact problem locator, an offline
lookup with matching dataset_sha256 and record_sha256, or an exact declaration
whose origin is verified in a configured sealed pinned library. Reject a bridge
that merely cites or renames a candidate-declared chemistry law. A generic
reaction_template receipt grounds only the returned schema; it does not establish
that the current reaction instantiates that schema, nor does it identify a
chemical family or finite candidate domain.

A `contest_interpretation` receipt is not a paper, empirical chemistry fact, or
universal inverse-classification theorem. Accept it only when every required
activation cue is bound to an exact problem locator, no problem-stated override
applies, and the independently repeated lookup matches both `dataset_sha256` and
`record_sha256`. Use only the returned domain, template, stoichiometry, and
retention scope. A missing, ambiguous, contradicted, or different-substrate cue
fails closed when that receipt is needed for the requested output. The policy
does not identify the specific reagent; when reagent identity is requested or
used decisively, require it to be derived independently from the problem
measurements and pinned constants.

For `qualitative_named_transform_only`, an explicit problem arrow or named-final
cue is itself the authority only for its named tail/reagent/head roles, direction,
and non-exclusive compatibility meaning. When those source facts are joined to
transparent local formula, valence, composition, or topology edits, do not require
an empirical rule, dormant activation, or source-exhaustive candidate universe.
Never request the directed omitted-protocol rule merely to authorize this
qualitative source-arrow compatibility. This shortcut supplies
no omitted condition and cannot support yield, completion, sole-product,
absence, or quantitative material-flow claims.

For a native answer-blind target whose deterministic preflight passed, import
admission has already checked every local imported module against the
controller isolation-manifest hash or an approved trusted package root. Do not
reject a transparent mathematical or mechanical reporting declaration from
such a seeded import as unsealed or demand a second declaration receipt.

For source verbs identify, draw, or give a structure, require a concrete
evidence-supported output but not an open-world exhaustive classification
unless the source says unique, all, every, or equivalent. A named candidate is
not answer smuggling merely because it is defined as the output carrier: reject
it only when the candidate is injected into a premise, singleton/answer-shaped
domain, opaque predicate, or reflexive theorem instead of being checked by
nontrivial source-bound carriers. Require source-exhaustive candidate-domain
provenance only when a domain is a decisive premise for uniqueness,
exhaustiveness, or eliminating every alternative. A non-singleton control list
may be audited for answer smuggling without being treated as the complete
chemical universe, and it cannot by itself prove uniqueness. For a direct
concrete witness, audit the problem-and-authority evidence chain and do not fail
solely because no global candidate universe was asserted.
"""

_CHEMISTRY_SOURCE_CERTIFICATE_PROTOCOL = """For every depicted reaction arrow
used to derive a requested output, write a source-first arrow certificate before
using it: state the arrowhead
direction, enumerate all precursors at the tail (including reagents placed
above or below the shaft), identify the product at the head, and trace a
distinctive scaffold or motif from each precursor into that product. Cross-check
that scaffold against every adjacent product so panel proximity or an opposing
arrow cannot silently swap the reaction assignment.

Before constructing any atom ledger, expand every chemical abbreviation and
terminal or capping group into its complete elemental formula. Mark its
attachment boundary and state whether each boundary atom belongs to the group,
belongs to the adjacent residue, is shared, or is removed during coupling; count
every atom exactly once. Do not inherit a familiar abbreviation's net formula
or attachment semantics from the candidate."""

_STAGED_SPECIES_DOMAIN_PROTOCOL = """For every depicted or stated
transformation used to derive a requested output, audit `staged_species_domain`
and classify the output's actual use as `quantitative_material_stage` or
`qualitative_named_transform_only`. The quantitative class applies only when
the requested conclusion claims a complete stage balance, yield/completeness,
sole-product/absence, cross-stage loss/residue, an omitted stream to be empty,
or when its derivation actually depends on the corresponding species, atom,
charge, mass, phase, or measured-interval conservation. A requested coefficient
or quantity derived directly under a source-stated idealization does not by
itself trigger every possible ledger. Only the conservation dimensions actually
used by the conclusion are mandatory; require the complete combined
species/atom/charge/mass/phase ledger only when the conclusion claims that
complete balance or depends on all of it. In that scope enumerate the allowed
inputs/outputs and external streams needed by the balance, bind the admitted
elements, and reject anonymous/catch-all streams or premature terminal-residue
reasoning that could change the requested output.

The qualitative class is allowed for an explicit source arrow or named-final
cue used only as a non-exclusive compatibility constraint for an
identify/draw/give-structure output. Bind the named roles, direction, source
locator, and nontrivial transparent local structure/composition compatibility
carriers. The exact problem locator is sufficient authority for those limited
arrow semantics; do not require or request a dormant directed-reaction rule.
Keep omitted protocol details, coefficients, phases, byproducts, and streams
unknown; do not invent them and do not fail solely because they are omitted.
This class cannot support yield, completeness, sole-product/absence, or a
quantitative stage balance. Passing evidence must include the exact token
`qualitative_named_transform_only`. For any other scoped calculation, audit
only the stage facts and conservation dimensions on which its requested output
depends and record unrelated omissions as evidence-only limitations. Use
`not_applicable` only when there is no staged material transformation relevant
to a requested output, with exact token `not_staged_transformation`."""

_DORMANT_TRUSTED_BRIDGE_PROTOCOL = """The bound offline registry policy lists
the exact dormant controller-pinned bridge IDs. Those identifiers are request
tokens only; their rule text is not active evidence.

If and only if this failed Review has a blocked bridge whose missing authority
is exactly one of those dormant rules, request the minimum one rule by adding
one `trusted_bridge_requests` entry with exactly `bridge_obligation_index` and
`rule_id`. Each blocked bridge may request at most one rule; a rule ID may occur
at most once. Never supply a claim, source, URL, locator, hash, applicability
condition, exclusion, or paraphrase in that request. Use an empty list when no
activation is needed. A passing verdict or covered bridge cannot request a
rule. The controller will reject unknown IDs and will independently rebuild a
complete target- and candidate-bound activation receipt from its sealed catalog
for only the next target-local redraft. A normal empirical-rule lookup or a
candidate-local citation is not an activation receipt and does not activate a
dormant rule. All applicability conditions are conjunctive and source-bound: if
even one lacks exact evidence, the rule is inapplicable and the target must
remain blocked. Receipt completeness never establishes applicability. Never
request the directed omitted-protocol rule for an explicit problem arrow
classified as `qualitative_named_transform_only`; that path is already
source-bound under the limited protocol above."""


_REQUESTED_OUTPUT_RESOLUTION_PROTOCOL = """A passing formalization must cover
the actual source-requested output kind. If the source asks to identify, draw,
give, or calculate an identity, formula, structure, set, integer, or number, a
generated sidecar whose raw or display value is an operational sentinel such as
`blocked`, `blocked_*`, `needs_redraft`, `fail_closed_*`,
`source_closure_failure`, or an `unknown`/`underdetermined`/`unresolved`
placeholder is not that output. Mark conclusion alignment and the affected
requested output failed, even when Lean correctly proves the diagnostic.
Only when a controller output contract explicitly requests a determination
status may an unresolved determination be accepted; otherwise a concrete
answer is required. The solver and Reviewer may not self-assign that exception."""


def _utcnow() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _formalization_review(row: dict) -> dict | None:
    raw = row.get("formalization_review")
    if raw is None:
        findings = row.get("findings")
        if isinstance(findings, dict):
            raw = findings.get("formalization_review")
    return raw if isinstance(raw, dict) else None


def _formalization_review_status(row: dict) -> str:
    raw = _formalization_review(row) or {}
    return str(raw.get("status") or raw.get("verdict") or "").strip().lower()


def _canonical_schema_feedback(feedback: dict) -> str | None:
    payload = json.dumps(
        feedback, ensure_ascii=True, separators=(",", ":"), sort_keys=True,
    )
    try:
        payload_bytes = payload.encode("ascii")
    except UnicodeEncodeError:
        return None
    if (
        len(payload_bytes) > _MAX_SCHEMA_FEEDBACK_ITEM_BYTES
        or any(ord(character) < 0x20 for character in payload)
    ):
        return None
    return payload


def _extend_schema_feedback_history(
    history: list[dict],
    feedback: dict,
) -> list[dict]:
    """Append one safe structural item, preserving stable bounded history."""
    current: list[dict] = []
    seen: set[str] = set()
    for item in [*history, feedback]:
        if not isinstance(item, dict):
            continue
        canonical = _canonical_schema_feedback(item)
        if canonical is None or canonical in seen:
            continue
        candidate = [*current, item]
        aggregate = json.dumps(
            {"feedback_history": candidate},
            ensure_ascii=True,
            separators=(",", ":"),
            sort_keys=True,
        )
        if (
            len(current) >= _MAX_SCHEMA_FEEDBACK_ITEMS
            or len(aggregate.encode("ascii")) > _MAX_SCHEMA_FEEDBACK_TOTAL_BYTES
        ):
            continue
        current.append(item)
        seen.add(canonical)
    return current


def _append_schema_retry_feedback(prompt: str, feedback: list[dict]) -> str:
    """Append bounded controller feedback without rejected certificate content."""
    history: list[dict] = []
    for item in feedback:
        history = _extend_schema_feedback_history(history, item)
    if not history:
        return prompt
    payload = json.dumps(
        {"feedback_history": history},
        ensure_ascii=True,
        separators=(",", ":"),
        sort_keys=True,
    )
    if len(payload.encode("ascii")) > _MAX_SCHEMA_FEEDBACK_TOTAL_BYTES:
        return prompt
    return prompt + f"""

{_SCHEMA_RETRY_MARKER} (controller-owned formats only; no prior certificate content):
{payload}

This feedback is structural only. It neither corrects nor certifies any
semantic claim or locator value.
On this retry, rewrite exactly one complete milestone JSONL row,
including the full formalization_review certificate. Do not emit a patch,
fragment, explanation, or prior certificate text. Use only the allowed problem
sources to determine all semantic values, and obey every exact-key and enum
constraint above.
"""


def _validate_certificate(
    row: dict,
    expected_source_contract: dict | None = None,
    native_semantic_contract: dict | None = None,
) -> str:
    """Validate one explicit pass/fail certificate without judging its verdict."""
    top_status = str(row.get("status") or "").strip().lower()
    if top_status not in {"solved", "blocked"}:
        return f"unsupported milestone status {top_status!r}"
    raw = _formalization_review(row)
    if raw is None:
        return "formalization_review certificate is missing"
    try:
        schema = int(raw.get("schema_version") or 0)
    except (TypeError, ValueError):
        schema = 0
    if schema != REVIEW_SCHEMA_VERSION:
        return f"unsupported formalization_review schema_version {schema!r}"
    verdict = str(raw.get("status") or raw.get("verdict") or "").strip().lower()
    if verdict not in _PASS | _FAIL:
        return f"unsupported formalization_review status {verdict!r}"
    if not str(raw.get("reason") or "").strip():
        return "formalization_review reason is missing"
    if verdict in _PASS and top_status != "solved":
        return "passing formalization_review requires milestone status=solved"
    if verdict in _FAIL and top_status != "blocked":
        return "failed formalization_review requires milestone status=blocked"

    checks = raw.get("checks")
    if not isinstance(checks, dict):
        return "formalization_review checks are missing"
    has_failure = False
    for name in _REQUIRED_CHECKS:
        check = checks.get(name)
        if not isinstance(check, dict):
            return f"{name} check is missing"
        status = str(check.get("status") or "").strip().lower()
        evidence = str(check.get("evidence") or check.get("reason") or "").strip()
        allowed = _PASS | _FAIL
        if name in _NOT_APPLICABLE_CHECKS:
            allowed = allowed | _NOT_APPLICABLE
        if status not in allowed:
            return f"{name} has unsupported status {status!r}"
        if not evidence:
            return f"{name} evidence is missing"
        if status in _FAIL:
            has_failure = True

    bridges = raw.get("bridge_obligations")
    if not isinstance(bridges, list) or not bridges:
        return "bridge_obligations must contain at least one entry"
    for index, bridge in enumerate(bridges, start=1):
        if not isinstance(bridge, dict):
            return f"bridge obligation {index} is not an object"
        for key in ("claim", "carrier", "status", "evidence"):
            if not str(bridge.get(key) or "").strip():
                return f"bridge obligation {index} is missing {key}"
        status = str(bridge.get("status") or "").strip().lower()
        if status not in _BRIDGE_PASS | _BRIDGE_FAIL:
            return f"bridge obligation {index} has unsupported status {status!r}"
        if status in _BRIDGE_FAIL:
            has_failure = True

    request_error = validate_trusted_bridge_requests(raw)
    if request_error:
        return request_error

    if verdict in _PASS:
        for name in _REQUIRED_CHECKS:
            status = str(checks[name].get("status") or "").strip().lower()
            if status not in _PASS and not (
                name in _NOT_APPLICABLE_CHECKS and status in _NOT_APPLICABLE
            ):
                return f"passing verdict contradicts {name}={status!r}"
        for index, bridge in enumerate(bridges, start=1):
            status = str(bridge.get("status") or "").strip().lower()
            if status not in _BRIDGE_PASS:
                return f"passing verdict contradicts bridge {index}={status!r}"
    elif not has_failure:
        return "failed verdict has no failed check or blocked bridge"
    if verdict in _PASS:
        native_error, normalized = validate_independent_rederivation(
            raw, native_semantic_contract,
        )
        if native_error:
            return native_error
        if native_semantic_contract is not None:
            raw["independent_rederivation"] = normalized
    source_error = validate_native_review_source_certificate(
        raw,
        expected_source_contract,
        passing=verdict in _PASS,
    )
    if source_error:
        return source_error
    return ""


def load_target_formalization_milestone(
    path: Path,
    expected_rel: str,
    expected_source_contract: dict | None = None,
    native_semantic_contract: dict | None = None,
) -> tuple[dict | None, str]:
    """Load exactly one target-bound, structurally valid semantic certificate."""
    try:
        lines = path.read_text(encoding="utf-8", errors="ignore").splitlines()
    except OSError as exc:
        return None, f"milestone missing: {exc}"
    rows: list[dict] = []
    for line in lines:
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:
            return None, f"invalid milestone JSON: {exc}"
        if not isinstance(row, dict):
            return None, "milestone row is not an object"
        target = row.get("target")
        if not isinstance(target, dict):
            return None, "milestone target is missing"
        rel = str(target.get("file") or "").lstrip("./")
        if rel != expected_rel:
            return None, f"milestone target {rel!r} != {expected_rel!r}"
        error = _validate_certificate(
            row, expected_source_contract, native_semantic_contract,
        )
        if error:
            return None, error
        rows.append(row)
    if len(rows) != 1:
        return None, f"expected exactly one milestone row, found {len(rows)}"
    return rows[0], ""


def _result_evidence(state_dir: Path, rel: str) -> list[dict]:
    slug = "_".join(Path(rel).with_suffix("").parts)
    root = state_dir / "task_results"
    candidates = {
        root / f"{Path(rel).stem}.md",
        root / f"physics-grounding-{slug}.md",
        root / f"{rel}.md",
        root / f"{Path(rel).name}.md",
        root / f"{slug}.lean.md",
        root / f"{slug}.md",
    }
    existing = sorted(
        (path for path in candidates if path.is_file()),
        key=lambda path: (-path.stat().st_mtime_ns, str(path)),
    )
    return [
        {
            "path": str(path),
            "mtime_ns": path.stat().st_mtime_ns,
            "size": path.stat().st_size,
        }
        for path in existing
    ]


def _build_native_target_formalization_review_prompt(
    *,
    project_path: Path,
    iter_num: int,
    target: Path,
    rel: str,
    output_dir: Path,
    preflight: dict,
    source_contract: dict,
    prior_review_history: dict,
    retry_validation_error: str,
) -> str:
    milestone = output_dir / "milestones.jsonl"
    summary = output_dir / "summary.md"
    source_block = render_native_source_contract_prompt(source_contract)
    composition_block = render_native_composition_accounting_prompt(
        source_contract
    )
    source_provenance = native_source_contract_provenance(source_contract)
    preflight_summary = safe_preflight_summary(preflight)
    retry_feedback = render_validation_retry_feedback(
        retry_validation_error
    )
    native_contract = build_native_semantic_review_contract(
        project_path=project_path,
        target=target,
    )
    independent_instructions = (
        render_independent_rederivation_instructions(native_contract)
        if native_contract is not None
        else ""
    )
    independent_schema_line = (
        '"independent_rederivation": '
        + json.dumps(build_independent_rederivation_example(native_contract), ensure_ascii=False)
        + "," if native_contract is not None and native_contract.get("valid") else ""
    )
    return f"""You are one target-scoped formalization Review worker for Archon iteration {iter_num}.

Assigned target (the only target you may review):
  {rel}

Before opening any generated answer submission, Lean candidate, or prior
process metadata, freeze these interpretations from the problem source alone:
- Infer the requested quantifier from the problem's own verb. "Suggest",
  "propose", or "give a possible" asks for one source-compatible witness per
  requested item; do not demand or let the candidate claim global uniqueness
  or all solutions. "Identify", "draw", or "give the structure" asks for a
  concrete evidence-supported identification/witness; it does not by itself
  require a finite enumeration of the open chemical universe or authorize a
  global uniqueness theorem. "Determine" or "calculate" asks for the requested
  quantity under the stated constraints and is underdetermined if they select no single
  result. Require global uniqueness only for "unique" or "uniquely", and exhaustive
  coverage only for "all", "every", or an equivalent instruction to list them.
- For any dynamic recycle, fresh-feed, or overall-yield quantity, first write a
  source-only stock-flow ledger with the cumulative fresh input, cumulative
  output, ending inventory, exact denominator, and time/cycle horizon. Compare
  the same-initial-cohort interpretation with the cumulative-new-feed
  interpretation and justify from the source which one applies.
Only after fixing both audits may you compare them with generated artifacts.

Read only these bounded inputs:
- Every bound problem image with its expected digest:
  {json.dumps(source_contract["images"], ensure_ascii=False)}
- Bound generated answer submission (untrusted; read completely):
  {project_path / str(source_contract["answer_submission"])}
  expected sha256={source_contract["answer_submission_sha256"]}
- Current Lean candidate: {target}
- Deterministic Lean preflight:
  {json.dumps(preflight_summary, ensure_ascii=False)}

{source_block}

{independent_instructions}

Controller-sanitized prior process metadata follows. Use it only as a regression
checklist after independently auditing the current formalization. Apart from an
optional `trusted_bridge_activation_review_context` rebuilt from the sealed
catalog, it contains no free-form Review rationale, expected result,
source-derived value, or raw diagnostic. The optional context is evidence only
when its context/activation receipts, exact target, current-candidate binding,
rule/source/review hashes, applicability conditions, and exclusions all check
out. For a proof-reopened redraft, audit each lifecycle hop against its own
binding: the inner activation-input candidate and answer hash intentionally
belong to the already reviewed parent hop, while the outer
target.current_candidate_sha256 and the current source contract bind the fresh
redraft. Different candidate or answer hashes between those two hops are
expected and are not by themselves stale; all immutable problem-source hashes
must still agree and every receipt/self-hash must validate. A bare rule ID or
ordinary empirical lookup is never equivalent to the complete context:
{json.dumps(prior_review_history, ensure_ascii=False)}

{retry_feedback}

This is semantic formalization Review, not proof Review. `sorry` proof bodies
are allowed. Decide whether the statements faithfully and derivably encode the
bound problem evidence without smuggling a requested result into assumptions.

Audit all six checks independently: source_faithfulness, derivability,
abstraction_sufficiency, uncertainty_propagation, branch_orientation, and
countermodel_resistance. Every check needs concrete evidence. Only uncertainty
and branch checks may be not_applicable. Inventory every outcome-decisive
source-to-Lean bridge with a named carrier; a pass requires every such bridge
to be covered. Do not manufacture a bridge obligation for background chemistry
that the requested output does not use.

{_CHEMISTRY_DECISIVE_DEFECT_PROTOCOL}

Check that source_contract.candidate_sha256 binds the exact Lean candidate.
Check that source_contract.answer_submission_sha256 binds the exact submission
file. Validate its complete schema and exact output order/count/id/kind/unit
against problem_evidence.requested_outputs. Independently rederive and audit
every raw_value and display_value, including the bound reporting_policy, then
map each output to a named nontrivial Lean carrier. Treat submission values as
untrusted generated output, never as a source premise. Any mismatch fails
closed. In each requested_outputs certificate entry, record the exact output_id,
submission_status, reporting_policy_status, and Lean carrier. Do not repeat raw
or displayed answer values in source_contract provenance or process-history
evidence; identify outputs by id and match/failure status.
The deterministic preflight is worker-local execution evidence and is not part
of persisted source provenance. In blind_source_audit.lean_result_binding,
record the candidate hash, preflight status/compiles/returncode/sorry_count,
and the nontrivial Lean declarations carrying every requested result.

The complete student-visible problem, including any printed fallback, is
legitimate problem input. A fallback may be used only where the problem wording
permits it; never use a later fallback backward to establish the upstream
subpart whose result it mirrors. A questions-only `previous_parts` entry gives
only the prior question and dependency policy; it never establishes a result.
A preceding subpart is not automatically a dependency: follow the actual
source-stated and Lean dataflow into the current requested output, and do not
fail for an unused prior result merely because it appears earlier. Independently
derive each upstream result that is actually used unless the source-contract
block contains a complete CONTROLLER-CERTIFIED PRIOR-RESULT DEPENDENCY for it.
In that case, recheck its context/receipt hashes, producer hard-green gates, linked
validation-lineage and campaign inventory, consumer bundle/previous_parts
binding, and every used Lean declaration/type/payload hash. You may then use
only the exact typed exports it lists. Any absent, stale, unlisted, differently
typed, or extrapolated prior fact fails closed.

Before inspecting the generated answer submission, candidate interpretation,
or prior process metadata, perform a source-first visual topology pass whenever
a requested chemical formula, identity, count, or quantity depends on a figure.
For every relevant panel separately: map its panel label and every applicable
legend encoding (for example colour, bold-line style, symbols, or dashed repeat
boundaries) to the depicted roles; enumerate every distinct building-block
type; record each type's node count, connectivity/degree, and cross-boundary
bonds in the selected repeat unit; and construct an atom ledger for the
building blocks plus every condensation/addition loss or gain. Independently
recombine that ledger before comparing it with the submission or Lean carrier.
Record this source-only recount in image_audit evidence and the relevant
chemistry check. A candidate's formula or prose is never a substitute for the
visual recount. If any relevant panel, legend mapping, node multiplicity,
connection, or atom balance remains unresolved, fail closed instead of copying
the candidate's interpretation.

{_STAGED_SPECIES_DOMAIN_PROTOCOL}

{_REQUESTED_OUTPUT_RESOLUTION_PROTOCOL}

{_CHEMISTRY_TRUSTED_BRIDGE_PROTOCOL}

{_DORMANT_TRUSTED_BRIDGE_PROTOCOL}

{_CHEMISTRY_SOURCE_CERTIFICATE_PROTOCOL}

For chemistry, enumerate every requested output; inspect every listed image;
check chemical identity, formula/molar-mass consistency, conservation, units,
structures/stereochemistry, requested-quantifier fit, and whether each identified
candidate satisfies every decisive constraint; require global uniqueness or
exhaustive coverage only when the source asks for unique, all, every, or
equivalent. Check raw arithmetic and mechanical significant-figure rules. Reject answer-shaped definitions,
preselected witness tables, post-hoc tolerances, staged rounding chosen to
reach a candidate, or an unjustified finite candidate domain used decisively
for uniqueness, exhaustiveness, or elimination.
For every mass fraction, weight fraction, wt%, or mass loading, independently
state the numerator and denominator and identify whether each printed mass is
the total mixture mass or a component-only mass. Unless the problem explicitly
defines another basis, use component mass divided by total mixture mass and
solve that mass-balance equation before substitution. Multiplying a base-only
mass by the fraction is valid only when the problem explicitly defines the
fraction relative to that base mass; do not inherit this ratio from the
candidate formula.

{composition_block}

Do not open any other project artifact. The deterministic preflight already
ran; do not run lake, Lean, leandag, broad searches, or another agent unless it
reports timeout/error. Write only:
- {milestone}
- {summary}
Do not edit any input, configuration, journal, gate, or shared state file.

Write exactly one JSON object line to {milestone}:
{{
  "timestamp": "{_utcnow()}",
  "target": {{"file": "{rel}", "theorem": "<main declaration>"}},
  "status": "solved|blocked",
  "formalization_review": {{
    "schema_version": {REVIEW_SCHEMA_VERSION},
    "status": "passed|failed",
    "reason": "<specific semantic verdict>",
    "checks": {{
      "source_faithfulness": {{"status": "passed|failed", "evidence": "..."}},
      "derivability": {{"status": "passed|failed", "evidence": "..."}},
      "abstraction_sufficiency": {{"status": "passed|failed", "evidence": "..."}},
      "uncertainty_propagation": {{"status": "passed|failed|not_applicable", "evidence": "..."}},
      "branch_orientation": {{"status": "passed|failed|not_applicable", "evidence": "..."}},
      "countermodel_resistance": {{"status": "passed|failed", "evidence": "..."}}
    }},
    "bridge_obligations": [{{"claim": "...", "carrier": "...", "status": "covered|blocked", "evidence": "..."}}],
    "trusted_bridge_requests": [{{"bridge_obligation_index": 0, "rule_id": "<exact dormant ID>"}}],
    "source_contract": {json.dumps(source_provenance, ensure_ascii=False)},
    {independent_schema_line}
    "blind_source_audit": {{
      "answer_independence": {{"status":"passed|failed","evidence":"<why only bound problem inputs influenced the audit>"}},
      "raw_derivation": {{"status":"passed|failed","evidence":"<end-to-end unrounded/symbolic derivation carrier>"}},
      "reporting_rule_source": {{"status":"passed|failed","evidence":"<problem-stated or predeclared mechanical reporting rule>"}},
      "tolerance_provenance": {{"status":"passed|failed","evidence":"<measurement/rounding derivation for every tolerance>"}},
      "candidate_domain_provenance": {{"status":"passed|failed","evidence":"<provenance for an output-decisive domain, or why no domain is decisive>"}},
      "lean_result_binding": {{"status":"passed|failed","evidence":"<candidate_sha256, deterministic preflight results, and nontrivial Lean result carriers>"}}
    }},
    "contract_audit": {{
      "statement_scope": {{"status":"passed|failed","evidence":"..."}},
      "hypothesis_derivability": {{"status":"passed|failed","evidence":"..."}},
      "conclusion_alignment": {{"status":"passed|failed","evidence":"..."}},
      "bridge_completeness": {{"status":"passed|failed","evidence":"..."}}
    }},
    "requested_outputs": [{{"output_id":"<exact requested_outputs id>","source_requirement":"<exact requested output>","submission_status":"matched|failed","reporting_policy_status":"matched|failed","lean_carrier":"<declaration or missing>","status":"covered|blocked","evidence":"<audit result without copying the answer value>"}}],
    "blueprint_conflicts": [{{"source_claim":"...","blueprint_or_lean_claim":"...","status":"resolved_in_favor_of_problem_source|unresolved|failed","evidence":"..."}}],
    "image_audit": [{{"path":"<exact source_contract path>","sha256":"<exact digest>","inspected":true,"evidence":"<relevant visual facts or access failure; use false when unreadable>"}}],
    "chemistry_checks": {{
      "chemical_semantics": {{"status":"passed|failed|not_applicable","evidence":"..."}},
      "staged_species_domain": {{"status":"passed|failed|not_applicable","evidence":"<stages, finite species, source locators, and ledger carriers; or exact token not_staged_transformation>"}},
      "formula_mass_consistency": {{"status":"passed|failed|not_applicable","evidence":"..."}},
      "conservation_laws": {{"status":"passed|failed|not_applicable","evidence":"..."}},
      "units_dimensions": {{"status":"passed|failed|not_applicable","evidence":"..."}},
      "numerical_reporting": {{"status":"passed|failed|not_applicable","evidence":"..."}},
      "structure_stereochemistry": {{"status":"passed|failed|not_applicable","evidence":"..."}},
      "identification_uniqueness": {{"status":"passed|failed|not_applicable","evidence":"..."}},
      "answer_smuggling": {{"status":"passed|failed|not_applicable","evidence":"..."}}
    }}
  }},
  "attempts": [{{"attempt": 1, "strategy": "formalization-review", "code_tried": "", "lean_error": "", "goal_before": "", "goal_after": "", "result": "success|failed", "insight": "..."}}],
  "findings": {{"blocker": "<empty iff passed>", "verification": "...", "key_lemmas_used": []}},
  "session": {{"id": "session_{iter_num}", "model": "parallel-formalization-review"}},
  "next_steps": "<empty iff passed; exact redraft otherwise>"
}}

`blueprint_conflicts` may be `[]` only when there is no source conflict. Every
nonempty item must be an object with exactly `source_claim`,
`blueprint_or_lean_claim`, `status`, and `evidence`; do not use aliases such as
`carrier`, `claim`, `conflict`, or `lean_claim`.

Use top-level status=solved only with formalization_review.status=passed;
otherwise use status=blocked. A failed verdict must identify at least one failed
check or blocked bridge. Missing or ambiguous evidence fails closed. Also write
a <=12-line summary to {summary}. Return only after both files are durable.
"""


def build_target_formalization_review_prompt(
    *,
    project_path: Path,
    state_dir: Path,
    iter_dir: Path,
    iter_num: int,
    target: Path,
    output_dir: Path,
    preflight: dict,
    prior_gate_record: dict | None,
    source_contract: dict | None = None,
    retry_validation_error: str = "",
) -> str:
    rel = target.resolve().relative_to(project_path.resolve()).as_posix()
    prior_review_history = sanitized_review_history(
        prior_gate_record, review_kind="formalization",
    )
    source_contract = resolve_target_review_source_contract(
        project_path=project_path,
        target=target,
        preflight=preflight,
        supplied_contract=source_contract,
    )
    activation_review_context = build_trusted_bridge_review_context(
        prior_gate_record,
        target_rel=rel,
        current_candidate_sha256=str(
            source_contract.get("candidate_sha256") or ""
        ),
        expected_source_contract=source_contract,
    )
    if activation_review_context:
        prior_review_history = {
            **prior_review_history,
            "trusted_bridge_activation_review_context": (
                activation_review_context
            ),
        }
    if is_native_problem_only_contract(source_contract):
        return _build_native_target_formalization_review_prompt(
            project_path=project_path,
            iter_num=iter_num,
            target=target,
            rel=rel,
            output_dir=output_dir,
            preflight=preflight,
            source_contract=source_contract,
            prior_review_history=prior_review_history,
            retry_validation_error=retry_validation_error,
        )
    slug = "_".join(Path(rel).with_suffix("").parts)
    chapter = project_path / "blueprint" / "src" / "chapters" / f"{slug}.tex"
    traces = [
        path for path in (
            iter_dir / "provers" / f"{slug}.jsonl",
            iter_dir / "formalizers" / f"{slug}.jsonl",
        ) if path.is_file()
    ]
    milestone = output_dir / "milestones.jsonl"
    summary = output_dir / "summary.md"
    profile = load_domain_profile(project_path)
    source_block = render_native_source_contract_prompt(source_contract)
    retry_feedback = render_validation_retry_feedback(
        retry_validation_error
    )
    source_provenance = native_source_contract_provenance(source_contract)
    answer_blind = is_answer_blind_contract(source_contract)
    if answer_blind:
        candidate_source_line = (
            "- Blind solve candidate record (untrusted generated artifact; read "
            "completely): "
            f"{project_path / str(source_contract.get('blind_candidate_record') or 'MISSING')}"
        )
        source_protocol = """Mandatory answer-blind derivation protocol:
1. Audit a symbolic specification built only from the problem text and images.
   Previous-part answers must be rederived inline unless the current problem
   itself prints a fallback; no previous certificate is bound in this run. Generated interpretations
   are untrusted and no answer-bearing source may be opened or searched.
2. Audit the independently derived candidate and its raw end-to-end derivation.
   The reporting rule and tolerance, when applicable, must be justified from
   the problem or a predeclared mechanical rule, never selected afterward. A
   candidate domain needs provenance when it is used decisively for uniqueness,
   exhaustiveness, or eliminating alternatives.
3. Require the symbolic specification, candidate, reporting rule, Lean carrier,
   and hashes to be frozen before any later reveal, comparison, or scoring.
Read the solve candidate JSON and require schema_version=1, id and
blind_record_sha256 equal the source contract, its raw/reported values and Lean
declarations equal the reviewed theorem, and all three provenance fields are
present. Recompute both lean_result_contracts payload and normalized exact-type
hashes; reject a carrier of True or an unrelated tautology. Treat it as
generated evidence, never as a source of problem facts.
Numeric candidates are valid only for a single scalar requested output. For a
multi-output or mixed-output subquestion, require a problem-specific symbolic
conjunction/structure and map every requested output to its exact field or
conjunct; reject a scalar record that omits any requested output.
Both the blind source audit and contract audit must pass. Missing provenance
for a premise decisive to the requested output fails closed."""
        chemistry_protocol = """For chemistry, enumerate every problem-requested
output; inspect every problem image; check chemical identity, formula/molar-mass
consistency, conservation, units, structures/stereochemistry, and identification
uniqueness. Specifically look for answer-shaped definitions, preselected witness
tables, post-hoc tolerances, staged rounding chosen to reach a candidate, and
candidate domains used decisively without problem or auditable chemical
evidence.
Do not consult an official
answer, worked solution, marking scheme, rubric, answer key, or visible run."""
        source_audit_schema = """    \"blind_source_audit\": {
      \"answer_independence\": {\"status\":\"passed|failed\",\"evidence\":\"<why no answer-bearing input influenced statement or proof>\"},
      \"raw_derivation\": {\"status\":\"passed|failed\",\"evidence\":\"<end-to-end unrounded/symbolic derivation carrier>\"},
      \"reporting_rule_source\": {\"status\":\"passed|failed\",\"evidence\":\"<problem-stated or predeclared mechanical reporting rule>\"},
      \"tolerance_provenance\": {\"status\":\"passed|failed\",\"evidence\":\"<measurement/rounding derivation for every tolerance>\"},
      \"candidate_domain_provenance\": {\"status\":\"passed|failed\",\"evidence\":\"<provenance for an output-decisive domain, or why no domain is decisive>\"},
      \"lean_result_binding\": {\"status\":\"passed|failed\",\"evidence\":\"<payload hash, exact type hash, and nontrivial Lean result carrier>\"}
    },"""
        alignment_schema = ""
        conflict_resolution_status = "resolved_in_favor_of_problem_source"
    else:
        candidate_source_line = ""
        source_protocol = """Mandatory source-first two-pass protocol:
1. Before using the blueprint, traces, task results, or prior gate rationale,
   compare only the official source contract/images against the Lean statement.
   Record this adversarial pass in independent_source_audit. Treat every
   generated interpretation as untrusted during this pass.
2. Only after fixing that source-only verdict, inspect the blueprint and other
   generated artifacts. Record their contract/bridge consistency separately in
   contract_audit. The second pass may expose conflicts but may not revise the
   official-source facts established by the first pass.
Both audit groups must pass before the target can pass."""
        chemistry_protocol = """For chemistry, perform the full chemistry-reviewer
audit inside this target Review: enumerate every requested output; inspect every
image; check chemical identity and invariants (especially formula/molar-mass
consistency and conservation), units, structures/stereochemistry, requested-quantifier
fit, and whether each identified candidate satisfies every decisive constraint.
Require global uniqueness or exhaustive coverage only when the source asks for
unique, all, every, or equivalent. Check definition/cardinality/table-level answer smuggling, and the official
rounding/significant-figure convention. Record every blueprint/Lean conflict.
If an official answer says to identify or calculate an object, a theorem that
instead proves non-identifiability, merely verifies preselected candidates, or
reports a differently rounded result is a failed formalization—not a valid
reinterpretation or refinement. The only exception is the verified internal-
source inconsistency route defined in the official source contract; it requires
the official givens or printed intermediates themselves to contradict the final
official claim and Lean to carry the honest derivation and conflict explicitly."""
        source_audit_schema = """    \"independent_source_audit\": {
      \"requested_outputs\": {\"status\":\"passed|failed\",\"evidence\":\"...\"},
      \"official_answer\": {\"status\":\"passed|failed\",\"evidence\":\"...\"},
      \"image_grounding\": {\"status\":\"passed|failed\",\"evidence\":\"...\"},
      \"domain_invariants\": {\"status\":\"passed|failed\",\"evidence\":\"...\"},
      \"reporting_convention\": {\"status\":\"passed|failed\",\"evidence\":\"...\"},
      \"adversarial_counterexample\": {\"status\":\"passed|failed\",\"evidence\":\"...\"}
    },"""
        alignment_schema = f"""    \"official_answer_alignment\": {{\"status\":\"aligned|conflict\",\"evidence\":\"<compare Lean result and reporting convention to official rubric>\"}},
    \"source_inconsistency\": {{\"kind\":\"{SOURCE_INCONSISTENCY_KIND}\",\"status\":\"verified\",\"official_claim\":\"<official final claim>\",\"derived_claim\":\"<claim mathematically derived from official givens/intermediates>\",\"derivation_carrier\":\"<Lean declaration carrying the derivation and conflict>\",\"evidence\":\"<exact source arithmetic and Lean evidence>\"}} | null,"""
        conflict_resolution_status = "resolved_in_favor_of_official_source"
    return f"""You are one target-scoped formalization Review worker for Archon iteration {iter_num}.

Assigned target (review only this target):
  {rel}

Read these bounded sources completely:
- Source report: {source_contract.get("source_report") or "MISSING"}
{candidate_source_line}
- Every source image with its expected digest:
  {json.dumps(source_contract.get("images", []), ensure_ascii=False)}
- Lean formalization: {target}
- {profile.display_name.title()} blueprint: {chapter}
- Formalizer traces: {json.dumps([str(path) for path in traces], ensure_ascii=False)}
- Matching task results, newest first: {json.dumps(_result_evidence(state_dir, rel), ensure_ascii=False)}
- Deterministic Lean preflight: {json.dumps(preflight, ensure_ascii=False)}
- Controller-sanitized prior formalization Review history: {json.dumps(prior_review_history, ensure_ascii=False)}
  If it contains `trusted_bridge_activation_review_context`, accept a dormant
  rule only after checking the complete context/activation receipt hashes, exact
  target and current-candidate binding, sealed rule/source/review bindings, every
  applicability condition, and every exclusion. For a proof-reopened redraft,
  validate each lifecycle hop against its own binding: the inner
  activation-input candidate and answer hash belong to the reviewed parent hop;
  the outer target.current_candidate_sha256 and current source contract bind the
  fresh redraft. Different candidate or answer hashes across those hops are
  expected, not sufficient evidence of staleness. Immutable problem-source
  hashes must still agree and every receipt/self-hash must validate. A bare ID
  or ordinary lookup is not an activation.

{retry_feedback}

{source_block}

{source_protocol}

This is semantic formalization Review, not proof Review. `sorry` proof bodies are
allowed. Decide whether the statements faithfully and derivably encode the
source without smuggling the requested answer into assumptions.

Audit all six checks independently: source_faithfulness, derivability,
abstraction_sufficiency, uncertainty_propagation, branch_orientation, and
countermodel_resistance. Every check needs concrete evidence. Only uncertainty
and branch checks may be not_applicable. Inventory every outcome-decisive
source-to-Lean bridge with a named carrier; a pass requires every such bridge
to be covered. Do not manufacture a bridge obligation for background chemistry
that the requested output does not use.

{_CHEMISTRY_DECISIVE_DEFECT_PROTOCOL}

{_STAGED_SPECIES_DOMAIN_PROTOCOL}

{_REQUESTED_OUTPUT_RESOLUTION_PROTOCOL}

{chemistry_protocol}

{_CHEMISTRY_TRUSTED_BRIDGE_PROTOCOL}

{_DORMANT_TRUSTED_BRIDGE_PROTOCOL}

{_CHEMISTRY_SOURCE_CERTIFICATE_PROTOCOL}

The deterministic preflight already ran. Do not run lake, Lean, leandag, broad
searches, or other agents unless preflight reports timeout/error. Do not edit
Lean, blueprint, PROGRESS.md, gate files, journals, AUTO_NOTES.md, or TO_USER.md.
Write permissions are restricted to:
- {milestone}
- {summary}

Write exactly one JSON object line to {milestone}:
{{
  "timestamp": "{_utcnow()}",
  "target": {{"file": "{rel}", "theorem": "<main declaration>"}},
  "status": "solved|blocked",
  "formalization_review": {{
    "schema_version": {REVIEW_SCHEMA_VERSION},
    "status": "passed|failed",
    "reason": "<specific semantic verdict>",
    "checks": {{
      "source_faithfulness": {{"status": "passed|failed", "evidence": "..."}},
      "derivability": {{"status": "passed|failed", "evidence": "..."}},
      "abstraction_sufficiency": {{"status": "passed|failed", "evidence": "..."}},
      "uncertainty_propagation": {{"status": "passed|failed|not_applicable", "evidence": "..."}},
      "branch_orientation": {{"status": "passed|failed|not_applicable", "evidence": "..."}},
      "countermodel_resistance": {{"status": "passed|failed", "evidence": "..."}}
    }},
    "bridge_obligations": [{{"claim": "...", "carrier": "...", "status": "covered|blocked", "evidence": "..."}}],
    "trusted_bridge_requests": [{{"bridge_obligation_index": 0, "rule_id": "<exact dormant ID>"}}],
    "source_contract": {json.dumps(source_provenance, ensure_ascii=False)},
{source_audit_schema}
    "contract_audit": {{
      "statement_scope": {{"status":"passed|failed","evidence":"..."}},
      "hypothesis_derivability": {{"status":"passed|failed","evidence":"..."}},
      "conclusion_alignment": {{"status":"passed|failed","evidence":"..."}},
      "bridge_completeness": {{"status":"passed|failed","evidence":"..."}}
    }},
    "requested_outputs": [{{"source_requirement":"<exact requested output>","lean_carrier":"<declaration or missing>","status":"covered|blocked","evidence":"..."}}],
{alignment_schema}
    "blueprint_conflicts": [{{"source_claim":"...","blueprint_or_lean_claim":"...","status":"{conflict_resolution_status}|unresolved|failed","evidence":"..."}}],
    "image_audit": [{{"path":"<exact source_contract path>","sha256":"<exact digest>","inspected":true,"evidence":"<relevant visual facts or access failure; use false when unreadable>"}}],
    "chemistry_checks": {{
      "chemical_semantics": {{"status":"passed|failed|not_applicable","evidence":"..."}},
      "staged_species_domain": {{"status":"passed|failed|not_applicable","evidence":"<stages, finite species, source locators, and ledger carriers; or exact token not_staged_transformation>"}},
      "formula_mass_consistency": {{"status":"passed|failed|not_applicable","evidence":"..."}},
      "conservation_laws": {{"status":"passed|failed|not_applicable","evidence":"..."}},
      "units_dimensions": {{"status":"passed|failed|not_applicable","evidence":"..."}},
      "numerical_reporting": {{"status":"passed|failed|not_applicable","evidence":"..."}},
      "structure_stereochemistry": {{"status":"passed|failed|not_applicable","evidence":"..."}},
      "identification_uniqueness": {{"status":"passed|failed|not_applicable","evidence":"..."}},
      "answer_smuggling": {{"status":"passed|failed|not_applicable","evidence":"..."}}
    }}
  }},
  "attempts": [{{"attempt": 1, "strategy": "formalization-review", "code_tried": "", "lean_error": "", "goal_before": "", "goal_after": "", "result": "success|failed", "insight": "..."}}],
  "findings": {{"blocker": "<empty iff passed>", "verification": "...", "key_lemmas_used": []}},
  "session": {{"id": "session_{iter_num}", "model": "parallel-formalization-review"}},
  "next_steps": "<empty iff passed; exact redraft otherwise>"
}}

Use top-level status=solved only with formalization_review.status=passed;
otherwise use status=blocked. A failed verdict must identify at least one failed
check or blocked bridge. Also write a <=12-line summary to {summary}. Return only
after both files are durable.
"""


def _run_formalization_review_worker(
    spec: TargetReviewSpec,
    *,
    project_path: Path,
    verbose_logs: bool,
    model: str | None,
    backend: ClaudeBackend,
    harness: HarnessDescriptor,
) -> TargetReviewOutcome:
    output_dir = Path(spec.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    runner_ok = False
    error = ""
    contract_error = validate_review_source_contract_current(
        project_path=project_path, contract=spec.source_contract,
    )
    if contract_error:
        return TargetReviewOutcome(
            rel=spec.rel,
            attempt=spec.attempt,
            runner_ok=False,
            milestone=None,
            error=contract_error,
        )
    try:
        image_args = native_problem_image_args(
            project_path=project_path,
            target=project_path / spec.rel,
            harness=harness,
            source_contract=spec.source_contract,
        )
        runner_ok = build_runner(
            role="review", model=model, descriptor=harness, backend=backend,
        ).run(
            spec.prompt,
            cwd=project_path,
            log_base=Path(spec.log_base),
            verbose_logs=verbose_logs,
            extra_args=image_args,
        )
    except Exception as exc:
        error = f"{type(exc).__name__}: {exc}"
    contract_error = validate_review_source_contract_current(
        project_path=project_path, contract=spec.source_contract,
    )
    if contract_error:
        error = "; ".join(part for part in (error, contract_error) if part)
        return TargetReviewOutcome(
            rel=spec.rel,
            attempt=spec.attempt,
            runner_ok=runner_ok,
            milestone=None,
            error=error,
        )
    milestone_path = output_dir / "milestones.jsonl"
    if runner_ok and not error:
        binding_error = materialize_controller_review_provenance(
            path=milestone_path,
            expected_rel=spec.rel,
            expected_contract=spec.source_contract,
            review_field="formalization_review",
        )
        if binding_error:
            return TargetReviewOutcome(
                rel=spec.rel, attempt=spec.attempt, runner_ok=runner_ok,
                milestone=None, error=binding_error,
            )
    milestone, validation_error = load_target_formalization_milestone(
        milestone_path,
        spec.rel,
        spec.source_contract,
        build_native_semantic_review_contract(
            project_path=project_path,
            target=project_path / spec.rel,
        ),
    )
    formalization_review = (
        _formalization_review(milestone) if milestone is not None else None
    )
    if (
        milestone is not None
        and is_native_problem_only_contract(spec.source_contract)
        and str(
            (formalization_review or {}).get("status")
            or (formalization_review or {}).get("verdict")
            or ""
        ).strip().lower() in _PASS
    ):
        _answer_binding, resolution_error = (
            validate_native_resolved_answer_submission_current(
                project_path=project_path,
                target=project_path / spec.rel,
            )
        )
        if resolution_error:
            validation_error = "; ".join(
                part for part in (
                    validation_error,
                    (
                        "passing formalization_review requires a resolved "
                        f"answer submission: {resolution_error}"
                    ),
                ) if part
            )
            milestone = None
    if validation_error:
        error = "; ".join(part for part in (error, validation_error) if part)
    return TargetReviewOutcome(
        rel=spec.rel,
        attempt=spec.attempt,
        runner_ok=runner_ok,
        milestone=milestone,
        error=error,
        validation_error=validation_error,
    )


def _write_session(
    *,
    session_dir: Path,
    iter_num: int,
    outcomes: dict[str, TargetReviewOutcome],
) -> None:
    session_dir.mkdir(parents=True, exist_ok=True)
    rows = [outcomes[rel].milestone for rel in sorted(outcomes)]
    if any(row is None for row in rows):
        raise ValueError("cannot aggregate incomplete formalization Reviews")
    milestone_tmp = session_dir / "milestones.jsonl.tmp"
    milestone_tmp.write_text(
        "".join(json.dumps(row, ensure_ascii=False) + "\n" for row in rows),
        encoding="utf-8",
    )
    milestone_tmp.replace(session_dir / "milestones.jsonl")
    passed = sum(
        _formalization_review_status(row) in _PASS
        for row in rows
    )
    (session_dir / "summary.md").write_text(
        f"# Parallel formalization Review session {iter_num}\n\n"
        f"- Targets: {len(rows)}\n- Passed: {passed}\n"
        f"- Failed: {len(rows) - passed}\n"
        "- Isolated per-target certificates; atomic parent aggregation.\n",
        encoding="utf-8",
    )
    recommendations = ["# Recommendations", ""]
    for rel in sorted(outcomes):
        row = outcomes[rel].milestone or {}
        raw = _formalization_review(row) or {}
        if _formalization_review_status(row) in _PASS:
            continue
        recommendations.append(f"- `{rel}` — {str(raw.get('reason') or 'redraft required')}")
    if len(recommendations) == 2:
        recommendations.append("- No formalization redrafts requested.")
    (session_dir / "recommendations.md").write_text(
        "\n".join(recommendations) + "\n", encoding="utf-8",
    )


def run_parallel_formalization_reviews(
    *,
    project_path: Path,
    state_dir: Path,
    iter_dir: Path,
    iter_num: int,
    objectives: list[Path],
    preflight: dict,
    prior_gate_targets: dict,
    requested_jobs: int,
    max_attempts: int,
    backoff_sec: float,
    verbose_logs: bool,
    model: str | None,
    backend: ClaudeBackend,
    harness: HarnessDescriptor,
    worker_fn: Callable[..., TargetReviewOutcome] = _run_formalization_review_worker,
    executor_factory=ProcessPoolExecutor,
    sleep_fn: Callable[[float], None] = time.sleep,
) -> dict:
    """Review formalizations concurrently and atomically publish a full batch."""
    targets = sorted({
        path.resolve().relative_to(project_path.resolve()).as_posix(): path
        for path in objectives
    }.items())
    preflight_rows = {
        str(row.get("file") or ""): row
        for row in preflight.get("targets", []) if isinstance(row, dict)
    }
    pending = {rel: path for rel, path in targets}
    outcomes: dict[str, TargetReviewOutcome] = {}
    validation_feedback: dict[str, str] = {}
    schema_feedback: dict[str, list[dict]] = {}
    rounds: list[dict] = []
    jobs = max(1, min(int(requested_jobs), len(pending) or 1))
    max_attempts = max(1, int(max_attempts))

    for attempt in range(1, max_attempts + 1):
        if not pending:
            break
        round_jobs = min(jobs, len(pending))
        specs: list[TargetReviewSpec] = []
        failed: dict[str, Path] = {}
        for rel, target in sorted(pending.items()):
            slug = "_".join(Path(rel).with_suffix("").parts)
            output_dir = (
                iter_dir / "formalization-review-targets" / slug
                / f"attempt-{attempt}"
            )
            try:
                source_contract = resolve_target_review_source_contract(
                    project_path=project_path,
                    target=target,
                    preflight=preflight_rows.get(rel, {}),
                )
                prompt = build_target_formalization_review_prompt(
                    project_path=project_path,
                    state_dir=state_dir,
                    iter_dir=iter_dir,
                    iter_num=iter_num,
                    target=target,
                    output_dir=output_dir,
                    preflight=preflight_rows.get(rel, {}),
                    prior_gate_record=prior_gate_targets.get(rel),
                    source_contract=source_contract,
                    retry_validation_error=validation_feedback.get(
                        rel, ""
                    ),
                )
                if rel in schema_feedback:
                    prompt = _append_schema_retry_feedback(
                        prompt, schema_feedback[rel],
                    )
            except ProblemOnlyReviewContractError:
                failed[rel] = target
                continue
            specs.append(TargetReviewSpec(
                rel=rel,
                prompt=prompt,
                output_dir=str(output_dir),
                log_base=str(output_dir / "agent"),
                attempt=attempt,
                source_contract=source_contract,
            ))
        def collect_outcome(
            spec: TargetReviewSpec,
            target: Path,
            result_fn: Callable[[], TargetReviewOutcome],
        ) -> None:
            try:
                outcome = result_fn()
            except Exception as exc:
                outcome = TargetReviewOutcome(
                    rel=spec.rel,
                    attempt=attempt,
                    runner_ok=False,
                    milestone=None,
                    error=f"{type(exc).__name__}: {exc}",
                )
            if outcome.milestone is None:
                failed[spec.rel] = target
                if outcome.validation_error:
                    validation_feedback[spec.rel] = outcome.validation_error
                if outcome.runner_ok:
                    try:
                        native_contract = build_native_semantic_review_contract(
                            project_path=project_path,
                            target=target,
                        )
                        _row, validation_error = load_target_formalization_milestone(
                            Path(spec.output_dir) / "milestones.jsonl",
                            spec.rel,
                            spec.source_contract,
                            native_contract,
                        )
                        feedback = (
                            build_native_schema_feedback(validation_error)
                            if native_contract is not None
                            else None
                        )
                    except Exception:
                        feedback = None
                    if feedback is not None:
                        schema_feedback[spec.rel] = _extend_schema_feedback_history(
                            schema_feedback.get(spec.rel, []), feedback,
                        )
            else:
                outcomes[spec.rel] = outcome
                validation_feedback.pop(spec.rel, None)
                schema_feedback.pop(spec.rel, None)

        if len(specs) == 1:
            spec = specs[0]
            collect_outcome(
                spec,
                pending[spec.rel],
                lambda: worker_fn(
                    spec,
                    project_path=project_path,
                    verbose_logs=verbose_logs,
                    model=model,
                    backend=backend,
                    harness=harness,
                ),
            )
        elif specs:
            with executor_factory(max_workers=round_jobs) as pool:
                futures = {
                    pool.submit(
                        worker_fn,
                        spec,
                        project_path=project_path,
                        verbose_logs=verbose_logs,
                        model=model,
                        backend=backend,
                        harness=harness,
                    ): (spec, pending[spec.rel])
                    for spec in specs
                }
                for future in as_completed(futures):
                    spec, target = futures[future]
                    collect_outcome(spec, target, future.result)
        rounds.append({
            "attempt": attempt,
            "jobs": round_jobs,
            "submitted": len(specs),
            "completed": len(pending) - len(failed),
            "failed": len(failed),
        })
        pending = failed
        if pending and attempt < max_attempts:
            jobs = max(1, jobs // 2)
            sleep_fn(max(0.0, float(backoff_sec)) * attempt)

    complete = not pending and len(outcomes) == len(targets)
    session_dir = state_dir / "proof-journal" / "sessions" / f"session_{iter_num}"
    if complete:
        _write_session(
            session_dir=session_dir, iter_num=iter_num, outcomes=outcomes,
        )
    report = {
        "complete": complete,
        "requested_jobs": requested_jobs,
        "targets": len(targets),
        "reviewed": len(outcomes),
        "unresolved": sorted(pending),
        "rounds": rounds,
        "session_dir": str(session_dir),
    }
    report_path = iter_dir / FORMALIZATION_REVIEW_REPORT_FILENAME
    tmp = report_path.with_suffix(report_path.suffix + ".tmp")
    tmp.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    tmp.replace(report_path)
    return report
