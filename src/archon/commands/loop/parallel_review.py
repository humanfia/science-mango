"""Target-scoped parallel Review with deterministic aggregation."""

from __future__ import annotations

import json
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable, Mapping

from archon.agent import ClaudeBackend, build_runner
from archon.commands.tooling.domain_profile import load_domain_profile
from archon.commands.tooling.project_config import HarnessDescriptor

from .proof_review_gate import (
    PROOF_REVIEW_ROUTES,
    PROOF_REVIEW_SCHEMA_VERSION,
    REDRAFT_KINDS,
)
from .problem_only_review_contract import (
    ProblemOnlyReviewContractError,
    is_native_problem_only_contract,
    materialize_controller_review_provenance,
    native_problem_only_enabled,
    native_problem_image_args,
    native_source_contract_provenance,
    render_native_composition_accounting_prompt,
    render_native_source_contract_prompt,
    resolve_target_review_source_contract,
    stored_review_provenance_matches_current,
    validate_native_passing_preflight,
    validate_native_pipelined_preflight,
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
from .shared_infrastructure import load_shared_infrastructure_policy
from .trusted_bridge_activation import (
    build_trusted_bridge_activation_audit_context,
    trusted_bridge_lineage_matches_formalization_pass,
)

PIPELINED_REVIEW_REPORT_FILENAME = "pipelined-review.json"
PIPELINED_REVIEW_SCHEMA_VERSION = 1
_NEEDS_REDRAFT_PARTIAL_STATUS_ERROR = (
    "proof_review route=needs_redraft requires milestone status=blocked"
)

_CHEMISTRY_TRUSTED_BRIDGE_PROTOCOL = """Trace every non-mathematical chemistry
bridge to its ultimate authority. A candidate-local `axiom`, `def`, `theorem`,
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
fails closed. The policy does not identify the specific reagent; require that
identity to be derived independently from the problem measurements and pinned
constants.

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

For an activated empirical contest rule, keep `SourceFact` distinct from
`AuthorizedCandidate`. Candidate nomination must be bound to the exact rule and
auditable origin evidence. For source verbs identify, draw, or give a structure,
require a concrete evidence-supported output but not an open-world exhaustive
classification unless the source says unique, all, every, or equivalent.
Require source-exhaustive candidate-domain provenance only when a domain is a
decisive premise for uniqueness, exhaustiveness, or eliminating every
alternative. A non-singleton control list may be audited for answer smuggling
without being treated as the complete chemical universe, and it cannot by
itself prove uniqueness. For a direct concrete witness, audit the
problem-and-authority evidence chain and do not fail solely because no global
candidate universe was asserted. A named output carrier is not answer smuggling
unless it is injected into a premise, singleton/answer-shaped domain, opaque
predicate, or reflexive theorem.
A finite-exhaustive Lean theorem may be recorded when available but is optional
and is never a passing prerequisite.
"""

_STAGED_SPECIES_DOMAIN_PROTOCOL = """For every depicted or stated
transformation, the `staged_species_domain` check is mandatory, but first
classify the requested output's use as `quantitative_material_stage` or
`qualitative_named_transform_only`. Require a finite species domain and
complete atom/charge/mass/interval ledgers only when the conclusion needs
yield, completeness, sole-product/absence, coefficients or phase amounts,
cross-stage balance, loss/residue, or an omitted stream to be empty. Reject
anonymous/catch-all streams and premature terminal-residue reasoning in that
quantitative class.

For an explicit source arrow or named-final cue used only as a non-exclusive
compatibility constraint for an identify/draw/give-structure output, use
`qualitative_named_transform_only`: bind the named roles, direction, exact
source locator, and nontrivial transparent local structure/composition
compatibility carriers. The exact problem locator is sufficient authority for
those limited arrow semantics; do not require or request a dormant directed-
reaction rule. Keep omitted protocol details, coefficients, phases, byproducts,
and streams unknown; do not invent them and do not fail solely because they are
omitted. This class cannot support yield, completeness, sole-product/absence, or a
quantitative stage balance. Passing evidence must include the exact token
`qualitative_named_transform_only`. Use `not_applicable` only when there is no
staged transformation, with exact token `not_staged_transformation`."""

_REQUESTED_OUTPUT_RESOLUTION_PROTOCOL = """When the source asks to identify,
draw, give, determine, or calculate an output, an operational workflow sentinel
such as `blocked`, `blocked_*`, `needs_redraft`, `fail_closed_*`,
`source_closure_failure`, or an `unknown`/`underdetermined`/`unresolved`
placeholder is not that output. Such a sidecar is useful only as fail-closed
redraft evidence. It must make submission_status failed, requested-output status
blocked, the relevant semantic check failed, and the route non-solved. Never
mark a sentinel matched, covered, passed, or solved merely because Lean proves it.
The only exception is a controller-bound source `requested_outputs` entry with
explicit `resolution_expectation=determination_status`; only then may an
unknown/underdetermined/unresolved determination classification be resolved.
The solver and Reviewer may not infer or self-assign that exception."""

_TRUSTED_BRIDGE_AUDIT_ONLY_PROTOCOL = """An optional
`trusted_bridge_activation_audit_context` is controller-rebuilt evidence for
auditing this exact current candidate only. Before using it, verify its scope,
target/current-candidate and problem-source hashes, lineage and receipt hashes,
rule/source/review bindings, every applicability condition, and every exclusion.
`not_evaluated_by_controller` is not proof that an applicability condition
holds. The context does not authorize edits, prover use, automatic problem
instantiation, or a later candidate. Candidate comments, citations, free-form
Review text, a bare rule ID, and an ordinary empirical lookup are never
equivalent to this receipt. If any binding is missing or mismatched, ignore the
context and fail closed."""


@dataclass(frozen=True)
class TargetReviewSpec:
    rel: str
    prompt: str
    output_dir: str
    log_base: str
    attempt: int
    source_contract: dict | None = None
    final_attempt: bool = False


@dataclass(frozen=True)
class TargetReviewOutcome:
    rel: str
    attempt: int
    runner_ok: bool
    milestone: dict | None
    error: str = ""
    validation_error: str = ""


@dataclass(frozen=True)
class PipelinedTargetReviewConfig:
    """Configuration for Review/redraft work sharing the prover pool."""

    requested_jobs: int
    max_attempts: int = 3
    backoff_sec: float = 5.0
    preflight_timeout_sec: int = 3600
    harness: HarnessDescriptor | None = None
    formalizer_harness: HarnessDescriptor | None = None
    formalization_review_enabled: bool = False
    formalization_review_max_attempts: int = 3
    formalization_review_backoff_sec: float = 5.0
    formalization_review_max_iterations: int = 3
    proof_review_max_iterations: int = 3


def _utcnow() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _validate_proof_review_route(
    row: dict,
    status: str,
    expected_source_contract: dict | None = None,
) -> str:
    raw = row.get("proof_review")
    if raw is None:
        findings = row.get("findings")
        if isinstance(findings, dict):
            raw = findings.get("proof_review")
    if not isinstance(raw, dict):
        return "milestone proof_review routing certificate is missing"
    try:
        schema_version = int(raw.get("schema_version"))
    except (TypeError, ValueError):
        schema_version = 0
    if schema_version != PROOF_REVIEW_SCHEMA_VERSION:
        return f"unsupported proof_review schema_version {schema_version!r}"
    route = str(raw.get("route") or "").strip().lower().replace("-", "_")
    if route not in PROOF_REVIEW_ROUTES:
        return f"unsupported proof_review route {route!r}"
    if not str(raw.get("reason") or "").strip():
        return "proof_review reason is missing"
    if not str(raw.get("evidence") or "").strip():
        return "proof_review evidence is missing"
    redraft_kind = str(raw.get("redraft_kind") or "").strip().lower()
    if redraft_kind not in REDRAFT_KINDS:
        return f"unsupported proof_review redraft_kind {redraft_kind!r}"
    if route == "needs_redraft" and redraft_kind == "not_applicable":
        return "needs_redraft requires a concrete redraft_kind"
    if route != "needs_redraft" and redraft_kind != "not_applicable":
        return f"route {route!r} requires redraft_kind=not_applicable"
    if route == "solved" and status != "solved":
        return "proof_review route=solved requires milestone status=solved"
    if route != "solved" and status == "solved":
        return f"proof_review route={route} contradicts milestone status=solved"
    if route == "needs_redraft" and status != "blocked":
        return _NEEDS_REDRAFT_PARTIAL_STATUS_ERROR
    if route == "blocked_infrastructure" and status != "blocked":
        return "proof_review route=blocked_infrastructure requires milestone status=blocked"
    if route == "retry_proof" and status not in {"partial", "blocked"}:
        return "proof_review route=retry_proof requires status=partial|blocked"
    source_error = validate_native_review_source_certificate(
        raw,
        expected_source_contract,
        passing=route == "solved",
    )
    if source_error:
        return source_error
    if route == "solved":
        preflight_error = validate_native_passing_preflight(
            expected_source_contract,
            require_zero_sorries=True,
        )
        if preflight_error:
            return preflight_error
    return ""


def load_target_milestone(
    path: Path,
    expected_rel: str,
    expected_source_contract: dict | None = None,
    *,
    final_attempt: bool = False,
) -> tuple[dict | None, str]:
    """Load exactly one well-formed milestone for ``expected_rel``."""
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
        status = str(row.get("status") or "").strip().lower()
        if status not in {"solved", "partial", "blocked", "not_started"}:
            return None, f"unsupported milestone status {status!r}"
        route_error = _validate_proof_review_route(
            row, status, expected_source_contract,
        )
        if (
            final_attempt
            and status == "partial"
            and route_error == _NEEDS_REDRAFT_PARTIAL_STATUS_ERROR
        ):
            # Preserve strict retries on earlier attempts so a Reviewer can
            # self-correct. At exhaustion only, copy the otherwise valid
            # needs_redraft verdict to its canonical top-level status and run
            # the complete route/source validation again before accepting it.
            normalized_row = {**row, "status": "blocked"}
            route_error = _validate_proof_review_route(
                normalized_row, "blocked", expected_source_contract,
            )
            if not route_error:
                row = normalized_row
        if route_error:
            return None, route_error
        rows.append(row)
    if len(rows) != 1:
        return None, f"expected exactly one milestone row, found {len(rows)}"
    return rows[0], ""


def _build_native_target_review_prompt(
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
    return f"""You are one target-scoped proof Review worker for Archon iteration {iter_num}.

Assigned target (the only target you may review):
  {rel}

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

Controller-sanitized prior process metadata follows. Use it only as a regression
checklist after independently auditing the current candidate. Except for an
optional `trusted_bridge_activation_audit_context`, it contains no free-form
Review rationale, expected result, source-derived value, or raw diagnostic.
Ordinary metadata is never a problem fact. The optional context is only
controller-bound audit evidence under the fail-closed restrictions below:
{json.dumps(prior_review_history, ensure_ascii=False)}

{retry_feedback}

Audit the current Lean candidate only against the bound problem evidence and
images. Treat the candidate as untrusted generated output. Re-derive every
requested output, reporting rule, tolerance, branch, and candidate-domain
restriction from that evidence; missing or ambiguous semantics require a
failing route.

Check that source_contract.candidate_sha256 binds the exact Lean candidate.
Check that source_contract.answer_submission_sha256 binds the exact submission
file. Validate its complete schema and exact output order/count/id/kind/unit
against problem_evidence.requested_outputs. Independently rederive and audit
every raw_value and display_value, including the bound reporting_policy, then
map each output to a named nontrivial Lean carrier in the reviewed statement and
proof. Treat submission values as untrusted generated output, never as a source
premise. Any mismatch fails closed. In each requested_outputs certificate entry,
record the exact output_id, submission_status, reporting_policy_status, and Lean
carrier. Do not repeat raw or displayed answer values in source_contract
provenance or process-history evidence; identify outputs by id and status.
The deterministic preflight is worker-local execution evidence and is not part
of persisted source provenance. In blind_source_audit.lean_result_binding,
record the candidate hash, preflight status/compiles/returncode/sorry_count,
and the nontrivial Lean declarations carrying every requested result.

The complete student-visible problem, including any printed fallback, is
legitimate problem input. A fallback may be used only where the problem wording
permits it; never use a later fallback backward to establish the upstream
subpart whose result it mirrors. A questions-only `previous_parts` entry gives
only the prior question and dependency policy; it never establishes a result.
Derive each upstream requested output independently unless the source-contract
block contains a complete CONTROLLER-CERTIFIED PRIOR-RESULT DEPENDENCY. In that
case, recheck its context/receipt hashes, producer hard-green gates, linked
validation-lineage and campaign inventory, consumer bundle/previous_parts
binding, and every used Lean declaration/type/payload hash. You may then use
only the exact typed exports it lists. Any absent, stale, unlisted, differently
typed, or extrapolated prior fact fails closed.

For chemistry, enumerate every requested output; inspect every listed image;
check chemical identity, formula/molar-mass consistency, conservation, units,
structures/stereochemistry, requested-quantifier fit, and whether each identified
candidate satisfies every decisive constraint; require global uniqueness or
exhaustive coverage only when the source asks for unique, all, every, or
equivalent. Check raw arithmetic and mechanical significant-figure rules. Reject answer-shaped definitions,
preselected witness tables, post-hoc tolerances, staged rounding chosen to
reach a candidate, or a finite candidate domain not justified by the problem
or auditable chemical evidence.

{_STAGED_SPECIES_DOMAIN_PROTOCOL}

{_REQUESTED_OUTPUT_RESOLUTION_PROTOCOL}

{_TRUSTED_BRIDGE_AUDIT_ONLY_PROTOCOL}

{_CHEMISTRY_TRUSTED_BRIDGE_PROTOCOL}

{composition_block}

Review the actual theorem contract and proof for:
1. direct Lean compilation and zero active sorry/admit/axiom laundering,
2. signature preservation and no weakened/trivialized statement,
3. faithful chemistry semantics relative to the bound problem evidence,
4. honest use of every binder, hypothesis, side condition, convention, bound,
   and requested conclusion,
5. whether the bound Lean candidate and deterministic preflight support the
   claimed proof.

Do not open any other project artifact. The deterministic preflight already
ran; do not run lake, Lean, leandag, broad searches, or another agent unless it
reports timeout/error. Write only:
- {milestone}
- {summary}
Do not edit any input, configuration, journal, gate, or shared state file.

Write exactly one JSON object line to {milestone}. Required shape:
{{
  "timestamp": "{_utcnow()}",
  "target": {{"file": "{rel}", "theorem": "<reviewed declaration>"}},
  "status": "solved|partial|blocked|not_started",
  "proof_review": {{
    "schema_version": {PROOF_REVIEW_SCHEMA_VERSION},
    "route": "solved|retry_proof|needs_redraft|blocked_infrastructure",
    "reason": "<specific root cause>",
    "evidence": "<Lean goal/error plus contract evidence>",
    "redraft_kind": "not_applicable|underdetermined_contract|answer_as_assumption|missing_uncertainty|branch_ambiguous|missing_foundational_bridge|wrong_or_weakened_target|other_modeling_defect",
    "infrastructure_request": null,
    "source_contract": {json.dumps(source_provenance, ensure_ascii=False)},
    "blind_source_audit": {{
      "answer_independence": {{"status":"passed|failed","evidence":"<why only bound problem inputs influenced the audit>"}},
      "raw_derivation": {{"status":"passed|failed","evidence":"<end-to-end unrounded/symbolic derivation carrier>"}},
      "reporting_rule_source": {{"status":"passed|failed","evidence":"<problem-stated or predeclared mechanical reporting rule>"}},
      "tolerance_provenance": {{"status":"passed|failed","evidence":"<measurement/rounding derivation for every tolerance>"}},
      "candidate_domain_provenance": {{"status":"passed|failed","evidence":"<problem or auditable chemistry evidence supporting the candidate domain>"}},
      "lean_result_binding": {{"status":"passed|failed","evidence":"<candidate_sha256, deterministic preflight results, and nontrivial Lean result carriers>"}}
    }},
    "contract_audit": {{
      "statement_scope": {{"status":"passed|failed","evidence":"..."}},
      "hypothesis_derivability": {{"status":"passed|failed","evidence":"..."}},
      "conclusion_alignment": {{"status":"passed|failed","evidence":"..."}},
      "bridge_completeness": {{"status":"passed|failed","evidence":"..."}}
    }},
    "requested_outputs": [{{"output_id":"<exact requested_outputs id>","source_requirement":"<exact requested output>","submission_status":"matched|failed","reporting_policy_status":"matched|failed","lean_carrier":"<declaration or missing>","status":"covered|blocked","evidence":"<audit result without copying the answer value>"}}],
    "blueprint_conflicts": [],
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
  "attempts": [{{"attempt": 1, "strategy": "review", "code_tried": "",
    "lean_error": "", "goal_before": "", "goal_after": "",
    "result": "success|partial|failed", "insight": "<specific evidence>"}}],
  "findings": {{"blocker": "<empty iff solved>",
    "verification": "<concise semantic and proof audit>",
    "key_lemmas_used": []}},
  "session": {{"id": "session_{iter_num}", "model": "parallel-review"}},
  "next_steps": "<empty iff solved; otherwise exact repair>"
}}

Classify root cause, not just the last Lean error. Use retry_proof only for a
faithful and derivable contract whose remaining issue is proof construction.
Use needs_redraft for a wrong, weakened, underdetermined, or answer-shaped
contract, a missing output/branch/uncertainty, or a missing modeling bridge.
Use blocked_infrastructure only for an unavailable external capability; never
request an install or dependency update. A target-local helper is retry_proof.

The top-level status is route-specific: solved -> solved; retry_proof ->
partial or blocked; needs_redraft -> blocked (never partial); and
blocked_infrastructure -> blocked.

Use status=solved only when all five checks pass and route=solved. Missing or
ambiguous evidence fails closed. Also write a <=12-line summary to {summary}.
Return only after both files are durable on disk.
"""


def _trusted_bridge_audit_context(
    *,
    state_dir: Path,
    rel: str,
    source_contract: dict,
) -> dict:
    """Load only a controller-validated formalization-pass lineage."""
    from .formalization_review_gate import load_gate_state

    gate_state = load_gate_state(state_dir) or {}
    targets = gate_state.get("targets")
    formal_record = targets.get(rel) if isinstance(targets, dict) else None
    lineage = (
        formal_record.get("trusted_bridge_activation_lineage")
        if isinstance(formal_record, dict)
        else None
    )
    lineage_target = (
        lineage.get("target") if isinstance(lineage, dict) else None
    )
    formalization_pass_sha256 = (
        lineage_target.get("formalization_pass_candidate_sha256")
        if isinstance(lineage_target, dict)
        else None
    )
    current_candidate_sha256 = str(
        source_contract.get("candidate_sha256") or ""
    )
    if (
        not isinstance(formal_record, dict)
        or formal_record.get("status") != "passed"
        or formal_record.get("candidate_sha256") != formalization_pass_sha256
        or not isinstance(lineage, dict)
        or not trusted_bridge_lineage_matches_formalization_pass(
            lineage,
            target_rel=rel,
            formalization_pass_candidate_sha256=formalization_pass_sha256,
            passing_certificate=(
                formal_record.get("certificate")
                if isinstance(formal_record.get("certificate"), Mapping)
                else None
            ),
        )
    ):
        return {}
    return build_trusted_bridge_activation_audit_context(
        lineage,
        target_rel=rel,
        current_candidate_sha256=current_candidate_sha256,
        expected_source_contract=source_contract,
    )


def build_target_review_prompt(
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
        prior_gate_record, review_kind="proof",
    )
    source_contract = resolve_target_review_source_contract(
        project_path=project_path,
        target=target,
        preflight=preflight,
        supplied_contract=source_contract,
    )
    activation_audit_context = _trusted_bridge_audit_context(
        state_dir=state_dir,
        rel=rel,
        source_contract=source_contract,
    )
    if activation_audit_context:
        prior_review_history = {
            **prior_review_history,
            "trusted_bridge_activation_audit_context": activation_audit_context,
        }
    if is_native_problem_only_contract(source_contract):
        return _build_native_target_review_prompt(
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
    prover_log = iter_dir / "provers" / f"{slug}.jsonl"
    result_root = state_dir / "task_results"
    result_candidates = {
        result_root / f"{rel}.md",
        result_root / f"{Path(rel).name}.md",
        result_root / f"{slug}.lean.md",
        result_root / f"{slug}.md",
    }
    existing_results = sorted(
        (path for path in result_candidates if path.is_file()),
        key=lambda path: (-path.stat().st_mtime, str(path)),
    )
    result_evidence = [
        {
            "path": str(path),
            "mtime_ns": path.stat().st_mtime_ns,
            "size": path.stat().st_size,
        }
        for path in existing_results
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
1. Audit the symbolic specification against only the problem text and images.
   Earlier results must be rederived inline unless the current problem prints
   a fallback; no previous certificate is controller-bound. No answer-bearing source may be
   opened or searched; generated interpretations are untrusted.
2. Audit the independently derived candidate and raw end-to-end proof. Every
   reporting rule, tolerance, and candidate-domain restriction must come from
   the problem, an applicable auditable chemistry authority allowed by the bound
   policy, or a predeclared mechanical rule, never a known result.
3. Verify that the symbolic specification, candidate, reporting rule, Lean
   carrier, and hashes were frozen before any later reveal or scoring.
Read the solve candidate JSON and require schema_version=1, id and
blind_record_sha256 equal the source contract, its raw/reported values and Lean
declarations equal the reviewed theorem/proof, and reporting-rule, tolerance,
and candidate-domain provenance are present. Recompute both
lean_result_contracts payload and normalized exact-type hashes; reject a carrier
of True or an unrelated tautology. It is generated evidence, not a source of
problem facts.
Numeric candidates are valid only for a single scalar requested output. For a
multi-output or mixed-output subquestion, require a problem-specific symbolic
conjunction/structure and map every requested output to its exact field or
conjunct; reject a scalar record that omits any requested output. Every numeric
field inside such a symbolic result must still carry its own exact raw equality
and `ReportsAtQuantum` reporting proposition.
Both the blind source audit and contract audit must pass. Missing provenance
fails closed."""
        chemistry_protocol = """For chemistry, enumerate every problem-requested
output; inspect every problem image; check chemical identity, formula/molar-mass
consistency, conservation, units, structures/stereochemistry, requested-quantifier
fit, and whether each identified candidate satisfies every decisive constraint.
Require global uniqueness or exhaustive coverage only when the source asks for
unique, all, every, or equivalent. Check raw arithmetic and mechanical significant-figure rules. Reject
answer-shaped definitions, preselected witness tables, post-hoc tolerances,
staged rounding chosen to reach a candidate, or a finite candidate domain not
justified by the problem or auditable chemical evidence. Do not consult an
official answer, worked solution, marking scheme, rubric, answer key, or visible
run."""
        source_audit_schema = """    \"blind_source_audit\": {
      \"answer_independence\": {\"status\":\"passed|failed\",\"evidence\":\"<why no answer-bearing input influenced statement or proof>\"},
      \"raw_derivation\": {\"status\":\"passed|failed\",\"evidence\":\"<end-to-end unrounded/symbolic derivation carrier>\"},
      \"reporting_rule_source\": {\"status\":\"passed|failed\",\"evidence\":\"<problem-stated or predeclared mechanical reporting rule>\"},
      \"tolerance_provenance\": {\"status\":\"passed|failed\",\"evidence\":\"<measurement/rounding derivation for every tolerance>\"},
      \"candidate_domain_provenance\": {\"status\":\"passed|failed\",\"evidence\":\"<problem or auditable chemistry evidence supporting the candidate domain>\"},
      \"lean_result_binding\": {\"status\":\"passed|failed\",\"evidence\":\"<payload hash, exact type hash, and nontrivial Lean result carrier>\"}
    },"""
        alignment_schema = ""
        conflict_resolution_status = "resolved_in_favor_of_problem_source"
    else:
        candidate_source_line = ""
        source_protocol = """Mandatory source-first two-pass protocol:
1. Before using the blueprint, traces, task results, or prior gate rationale,
   compare only the official source contract/images against the Lean statement
   and proof. Record this adversarial pass in independent_source_audit; treat
   generated interpretations as untrusted during this pass.
2. Only after fixing that verdict, inspect the blueprint and generated reports
   and record contract/bridge consistency in contract_audit. The second pass
   may expose conflicts but may not revise official-source facts from pass one.
Both audit groups must pass before route=solved."""
        chemistry_protocol = """For chemistry, perform the full chemistry-reviewer
audit inside this target Review: enumerate every requested output; inspect every
image; check chemical identity and invariants (including formula/molar-mass
consistency and conservation), units, structures/stereochemistry, requested-quantifier
fit, and whether each identified candidate satisfies every decisive constraint.
Require global uniqueness or exhaustive coverage only when the source asks for
unique, all, every, or equivalent. Check answer smuggling through definitions/cardinalities/tables, and official
rounding/significant-figure conventions. Record every blueprint/Lean conflict.
An official-answer conflict is a modeling failure even when Lean compiles and
even when the blueprint and generated reports agree with one another, except
for the verified internal-source inconsistency route defined in the official
source contract. That narrow route requires the official givens or printed
intermediates themselves to contradict the final official claim and Lean to
carry the honest derivation and conflict explicitly."""
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
    shared_policy = load_shared_infrastructure_policy(project_path)
    shared_roots = [path.as_posix() for path in shared_policy.module_roots]
    blueprint_label = f"{profile.display_name.title()} blueprint"
    if profile.enforce_classical_physics_modeling:
        semantic_checks = (
            "3. faithful physical semantics relative to the source comments and blueprint,\n"
            "4. honest use of hypotheses, units, answer choice, and numerical tolerance,"
        )
    else:
        semantic_checks = (
            f"3. faithful {profile.display_name} semantics relative to the natural-language source and blueprint,\n"
            "4. honest use of every binder, hypothesis, side condition, convention, bound, and requested conclusion,"
        )
    return f"""You are one target-scoped proof Review worker for Archon iteration {iter_num}.

Assigned target (the only target you may review):
  {rel}

Read these bounded sources completely:
- Source report: {source_contract.get("source_report") or "MISSING"}
{candidate_source_line}
- Every source image with its expected digest:
  {json.dumps(source_contract.get("images", []), ensure_ascii=False)}
- Lean statement/proof: {target}
- {blueprint_label}: {chapter}
- Prover trace: {prover_log}
- Matching prover task results, newest first:
  {json.dumps(result_evidence, ensure_ascii=False)}
- Deterministic Lean preflight: {json.dumps(preflight, ensure_ascii=False)}
- Controller-sanitized prior proof Review history: {json.dumps(prior_review_history, ensure_ascii=False)}

{retry_feedback}

{source_block}

{source_protocol}

Review the actual theorem contract and proof for:
1. direct Lean compilation and zero active sorry/admit/axiom laundering,
2. signature preservation and no weakened/trivialized statement,
{semantic_checks}
5. whether the current prover trace and newest matching task result support
   the claimed proof.

{chemistry_protocol}

{_STAGED_SPECIES_DOMAIN_PROTOCOL}

{_REQUESTED_OUTPUT_RESOLUTION_PROTOCOL}

{_TRUSTED_BRIDGE_AUDIT_ONLY_PROTOCOL}

{_CHEMISTRY_TRUSTED_BRIDGE_PROTOCOL}

Task-result layouts can be nested or flattened. Prefer the newest matching
artifact whose contents agree with this iteration's trace. Do not fail a target
solely because an older alternate-path artifact is stale or missing. If no
matching artifact exists, use the current prover trace as primary evidence and
report the missing result as a process warning, not a semantic proof failure.

The deterministic preflight already ran. Do not run lake, Lean, leandag, or
repository-wide searches unless the supplied preflight reports timeout/error.
The mechanical \\leanok marker sync may run after this target-scoped Review.
Judge proof validity from the Lean source and preflight; do not fail a target
solely because a blueprint \\leanok marker is temporarily stale.

Write permissions are restricted to:
- {milestone}
- {summary}
Do not edit Lean, blueprint, PROGRESS.md, gate files, AUTO_NOTES.md, TO_USER.md,
or any shared journal/state file.

Write exactly one JSON object line to {milestone}. Required shape:
{{
  "timestamp": "{_utcnow()}",
  "target": {{"file": "{rel}", "theorem": "<reviewed declaration>"}},
  "status": "solved|partial|blocked|not_started",
  "proof_review": {{
    "schema_version": {PROOF_REVIEW_SCHEMA_VERSION},
    "route": "solved|retry_proof|needs_redraft|blocked_infrastructure",
    "reason": "<specific root cause>",
    "evidence": "<Lean goal/error plus contract evidence>",
    "redraft_kind": "not_applicable|underdetermined_contract|answer_as_assumption|missing_uncertainty|branch_ambiguous|missing_foundational_bridge|wrong_or_weakened_target|other_modeling_defect",
    "infrastructure_request": null,
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
  "attempts": [{{"attempt": 1, "strategy": "review", "code_tried": "",
    "lean_error": "", "goal_before": "", "goal_after": "",
    "result": "success|partial|failed", "insight": "<specific evidence>"}}],
  "findings": {{"blocker": "<empty iff solved>",
    "verification": "<concise semantic and proof audit>",
    "key_lemmas_used": []}},
  "session": {{"id": "session_{iter_num}", "model": "parallel-review"}},
  "next_steps": "<empty iff solved; otherwise exact repair>"
}}

Classify root cause, not just the last Lean error:
- route=retry_proof only when the contract is faithful and derivable and the
  remaining issue is tactics, lemma search, arithmetic, elaboration, or budget;
- route=needs_redraft for an underdetermined/wrong/weakened contract,
  answer-as-assumption, missing requested output, uncertainty/branch omission,
  opaque relation without an eliminator, or missing foundational bridge;
- route=blocked_infrastructure when an indispensable gap is either a reusable
  cross-target project-local module or an unavailable external capability.
  Project-local automatic builds are enabled={shared_policy.enabled} and the
  only allowed module roots are {json.dumps(shared_roots)}. For an allowlisted
  local gap use
  {{"kind":"project_local_shared_module","module":"<root/File.lean>","declarations":["Name"]}};
  for an external package/tool use
  {{"kind":"external_dependency","package":"name"}}. The loop records but
  never installs external dependencies. Keep the optional field null/absent
  for every other route. A target-local helper is retry_proof; a missing
  statement/modeling bridge normally routes to needs_redraft. Use
  redraft_kind=not_applicable for every route except needs_redraft.

Use status=solved only when all five checks pass and route=solved. Use
status=blocked for needs_redraft or blocked_infrastructure, and partial/blocked
for retry_proof. Missing or ambiguous evidence must fail closed. Also write a
<=12-line summary to {summary}.
Return only after both files are durable on disk.
"""


def _run_review_worker(
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
    except Exception as exc:  # worker isolation; parent decides whether to retry
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
            review_field="proof_review",
        )
        if binding_error:
            return TargetReviewOutcome(
                rel=spec.rel, attempt=spec.attempt, runner_ok=runner_ok,
                milestone=None, error=binding_error,
            )
    milestone, validation_error = load_target_milestone(
        milestone_path,
        spec.rel,
        spec.source_contract,
        final_attempt=(spec.final_attempt and runner_ok and not error),
    )
    if (
        milestone is not None
        and str(milestone.get("status") or "").strip().lower() == "solved"
        and is_native_problem_only_contract(spec.source_contract)
    ):
        _answer_binding, resolved_error = (
            validate_native_resolved_answer_submission_current(
                project_path=project_path,
                target=project_path / spec.rel,
            )
        )
        if resolved_error:
            milestone = None
            validation_error = "; ".join(
                x for x in (validation_error, resolved_error) if x
            )
    if validation_error:
        error = "; ".join(x for x in (error, validation_error) if x)
    return TargetReviewOutcome(
        rel=spec.rel,
        attempt=spec.attempt,
        runner_ok=runner_ok,
        milestone=milestone,
        error=error,
        validation_error=validation_error,
    )


def write_parallel_review_session(
    *,
    session_dir: Path,
    iter_num: int,
    outcomes: dict[str, TargetReviewOutcome],
) -> None:
    """Atomically materialize the one global journal consumed by Review gates."""
    session_dir.mkdir(parents=True, exist_ok=True)
    rows = [outcomes[rel].milestone for rel in sorted(outcomes)]
    if any(row is None for row in rows):
        raise ValueError("cannot aggregate incomplete target Review outcomes")
    milestone_tmp = session_dir / "milestones.jsonl.tmp"
    milestone_tmp.write_text(
        "".join(json.dumps(row, ensure_ascii=False) + "\n" for row in rows),
        encoding="utf-8",
    )
    milestone_tmp.replace(session_dir / "milestones.jsonl")
    counts: dict[str, int] = {}
    for row in rows:
        status = str(row.get("status") or "not_started")
        counts[status] = counts.get(status, 0) + 1
    summary = [
        f"# Parallel Review session {iter_num}",
        "",
        f"- Targets: {len(rows)}",
        "- " + ", ".join(f"{k}={v}" for k, v in sorted(counts.items())),
        "- One isolated Reviewer per target; deterministic parent aggregation.",
    ]
    (session_dir / "summary.md").write_text(
        "\n".join(summary) + "\n", encoding="utf-8",
    )
    recommendations = [
        "# Recommendations",
        "",
    ]
    for rel in sorted(outcomes):
        row = outcomes[rel].milestone or {}
        if str(row.get("status") or "") == "solved":
            continue
        findings = row.get("findings")
        blocker = (
            str(findings.get("blocker") or "")
            if isinstance(findings, dict) else ""
        )
        recommendations.append(f"- `{rel}` — {blocker or 'Review did not pass.'}")
    if len(recommendations) == 2:
        recommendations.append("- No proof retries requested.")
    (session_dir / "recommendations.md").write_text(
        "\n".join(recommendations) + "\n", encoding="utf-8",
    )


def validate_parallel_review_session(
    *,
    session_dir: Path,
    expected_rels: list[str],
    project_path: Path | None = None,
) -> str:
    """Validate the durable aggregate before Review consumes it."""
    native = False
    if project_path is not None:
        try:
            native = native_problem_only_enabled(project_path)
        except ProblemOnlyReviewContractError as exc:
            return str(exc)

    milestone_path = session_dir / "milestones.jsonl"
    try:
        lines = milestone_path.read_text(
            encoding="utf-8", errors="ignore",
        ).splitlines()
    except OSError as exc:
        return f"pipelined Review session is missing: {exc}"

    rows: dict[str, dict] = {}
    for line in lines:
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:
            return f"invalid pipelined Review milestone JSON: {exc}"
        if not isinstance(row, dict):
            return "pipelined Review milestone row is not an object"
        target = row.get("target")
        if not isinstance(target, dict):
            return "pipelined Review milestone target is missing"
        rel = str(target.get("file") or "").lstrip("./")
        if not rel:
            return "pipelined Review milestone file is missing"
        if rel in rows:
            return f"duplicate pipelined Review milestone for {rel!r}"
        status = str(row.get("status") or "").strip().lower()
        if status not in {"solved", "partial", "blocked", "not_started"}:
            return f"unsupported pipelined Review status {status!r}"
        expected_contract = None
        if native and project_path is not None:
            raw_review = row.get("proof_review")
            if raw_review is None:
                findings = row.get("findings")
                if isinstance(findings, dict):
                    raw_review = findings.get("proof_review")
            provenance = (
                raw_review.get("source_contract")
                if isinstance(raw_review, dict)
                else None
            )
            fresh, reason = stored_review_provenance_matches_current(
                project_path=project_path,
                target=project_path / rel,
                provenance=provenance,
                bind_candidate=True,
            )
            if not fresh:
                return f"{rel}: {reason}"
            try:
                expected_contract = resolve_target_review_source_contract(
                    project_path=project_path,
                    target=project_path / rel,
                    preflight=None,
                )
            except ProblemOnlyReviewContractError as exc:
                return f"{rel}: {exc}"
            expected_contract["preflight_sha256"] = provenance.get(
                "preflight_sha256"
            )
        route_error = _validate_proof_review_route(row, status, expected_contract)
        if route_error:
            return f"{rel}: {route_error}"
        rows[rel] = row

    expected = sorted(set(expected_rels))
    actual = sorted(rows)
    if actual != expected:
        return (
            "pipelined Review target mismatch: "
            f"expected={expected!r}, actual={actual!r}"
        )
    return ""


def write_pipelined_review_report(*, iter_dir: Path, report: dict) -> Path:
    """Atomically publish the hand-off consumed by :class:`ReviewPhase`."""
    path = iter_dir / PIPELINED_REVIEW_REPORT_FILENAME
    payload = {
        "schema_version": PIPELINED_REVIEW_SCHEMA_VERSION,
        **report,
    }
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    tmp.replace(path)
    return path


def load_pipelined_review_report(
    *,
    project_path: Path,
    state_dir: Path,
    iter_dir: Path,
    iter_num: int,
    objectives: list[Path],
) -> tuple[dict | None, str]:
    """Load a complete, exact-target pipeline hand-off or fail closed."""
    path = iter_dir / PIPELINED_REVIEW_REPORT_FILENAME
    try:
        report = json.loads(path.read_text(encoding="utf-8"))
    except OSError as exc:
        return None, f"pipelined Review report unavailable: {exc}"
    except json.JSONDecodeError as exc:
        return None, f"invalid pipelined Review report: {exc}"
    if not isinstance(report, dict):
        return None, "pipelined Review report is not an object"
    try:
        schema_version = int(report.get("schema_version") or 0)
        report_iteration = int(report.get("iteration") or 0)
    except (TypeError, ValueError):
        return None, "pipelined Review report has invalid numeric metadata"
    if schema_version != PIPELINED_REVIEW_SCHEMA_VERSION:
        return None, "unsupported pipelined Review report schema"
    if report_iteration != int(iter_num):
        return None, "pipelined Review report iteration mismatch"
    if report.get("complete") is not True:
        return None, "pipelined Review report is incomplete"

    expected: list[str] = []
    for objective in objectives:
        try:
            rel = objective.resolve().relative_to(project_path.resolve()).as_posix()
        except ValueError:
            rel = str(objective)
        expected.append(rel.lstrip("./"))
    expected = sorted(set(expected))
    raw_targets = report.get("target_files")
    if not isinstance(raw_targets, list):
        return None, "pipelined Review report target_files is not a list"
    actual = sorted(
        set(str(x).lstrip("./") for x in raw_targets)
    )
    if actual != expected:
        return None, (
            "pipelined Review report target mismatch: "
            f"expected={expected!r}, actual={actual!r}"
        )

    proof_expected = expected
    if str(report.get("pipeline_mode") or "") == "target_lifecycle":
        raw_pending = report.get("pending_formalization_targets", [])
        if not isinstance(raw_pending, list):
            return None, (
                "target lifecycle report pending_formalization_targets "
                "is not a list"
            )
        pending = sorted({
            str(item).lstrip("./") for item in raw_pending
            if str(item).strip()
        })
        if pending:
            return None, (
                "target lifecycle report is complete but still has pending "
                f"formalization targets: {pending!r}"
            )
        raw_settled = report.get("settled_target_files")
        if not isinstance(raw_settled, list):
            return None, "target lifecycle report settled_target_files is not a list"
        settled = sorted({
            str(item).lstrip("./") for item in raw_settled
            if str(item).strip()
        })
        if settled != expected:
            return None, (
                "target lifecycle settled-target mismatch: "
                f"expected={expected!r}, actual={settled!r}"
            )
        raw_proof_targets = report.get("proof_review_target_files")
        if not isinstance(raw_proof_targets, list):
            return None, (
                "target lifecycle report proof_review_target_files is not a list"
            )
        proof_expected = sorted({
            str(item).lstrip("./") for item in raw_proof_targets
            if str(item).strip()
        })
        if any(rel not in expected for rel in proof_expected):
            return None, "target lifecycle proof Review target is out of scope"

    session_dir = state_dir / "proof-journal" / "sessions" / f"session_{iter_num}"
    error = validate_parallel_review_session(
        session_dir=session_dir,
        expected_rels=proof_expected,
        project_path=project_path,
    )
    if error:
        return None, error
    solved_rels: list[str] = []
    try:
        native = native_problem_only_enabled(project_path)
    except ProblemOnlyReviewContractError as exc:
        return None, str(exc)
    if native:
        try:
            session_lines = (session_dir / "milestones.jsonl").read_text(
                encoding="utf-8", errors="ignore",
            ).splitlines()
            for line in session_lines:
                if not line.strip():
                    continue
                row = json.loads(line)
                if not isinstance(row, dict):
                    return None, "pipelined Review milestone row is not an object"
                proof_review = row.get("proof_review")
                if proof_review is None:
                    findings = row.get("findings")
                    if isinstance(findings, dict):
                        proof_review = findings.get("proof_review")
                if not isinstance(proof_review, dict) or (
                    str(proof_review.get("route") or "").strip().lower()
                    != "solved"
                ):
                    continue
                target = row.get("target")
                if not isinstance(target, dict):
                    return None, "pipelined Review milestone target is missing"
                solved_rels.append(
                    str(target.get("file") or "").lstrip("./")
                )
        except (OSError, json.JSONDecodeError) as exc:
            return None, f"cannot revalidate pipelined Review session: {exc}"
    error = validate_native_pipelined_preflight(
        project_path=project_path, preflight=report.get("preflight"),
        expected_rels=expected, solved_rels=solved_rels,
        expected_iteration=iter_num,
    )
    if error:
        return None, error
    return report, ""


def run_parallel_target_reviews(
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
    worker_fn: Callable[..., TargetReviewOutcome] = _run_review_worker,
    executor_factory=ProcessPoolExecutor,
    sleep_fn: Callable[[float], None] = time.sleep,
) -> dict:
    """Review targets concurrently, halving concurrency after infrastructure failures."""
    targets = sorted(
        {p.resolve().relative_to(project_path.resolve()).as_posix(): p for p in objectives}.items()
    )
    preflight_rows = {
        str(row.get("file") or ""): row
        for row in preflight.get("targets", [])
        if isinstance(row, dict)
    }
    pending = {rel: path for rel, path in targets}
    outcomes: dict[str, TargetReviewOutcome] = {}
    validation_feedback: dict[str, str] = {}
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
            attempt_dir = iter_dir / "review-targets" / slug / f"attempt-{attempt}"
            try:
                source_contract = resolve_target_review_source_contract(
                    project_path=project_path,
                    target=target,
                    preflight=preflight_rows.get(rel, {}),
                )
                prompt = build_target_review_prompt(
                    project_path=project_path,
                    state_dir=state_dir,
                    iter_dir=iter_dir,
                    iter_num=iter_num,
                    target=target,
                    output_dir=attempt_dir,
                    preflight=preflight_rows.get(rel, {}),
                    prior_gate_record=prior_gate_targets.get(rel),
                    source_contract=source_contract,
                    retry_validation_error=validation_feedback.get(
                        rel, ""
                    ),
                )
            except ProblemOnlyReviewContractError:
                failed[rel] = target
                continue
            specs.append(TargetReviewSpec(
                rel=rel,
                prompt=prompt,
                output_dir=str(attempt_dir),
                log_base=str(attempt_dir / "agent"),
                attempt=attempt,
                source_contract=source_contract,
                final_attempt=attempt == max_attempts,
            ))
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
                try:
                    outcome = future.result()
                except Exception as exc:
                    outcome = TargetReviewOutcome(
                        rel=spec.rel, attempt=attempt, runner_ok=False,
                        milestone=None, error=f"{type(exc).__name__}: {exc}",
                    )
                if outcome.milestone is None:
                    failed[spec.rel] = target
                    if outcome.validation_error:
                        validation_feedback[spec.rel] = (
                            outcome.validation_error
                        )
                else:
                    outcomes[spec.rel] = outcome
                    validation_feedback.pop(spec.rel, None)
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
        write_parallel_review_session(
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
    report_path = iter_dir / "parallel-review.json"
    tmp = report_path.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    tmp.replace(report_path)
    return report
