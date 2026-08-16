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
from .parallel_review import TargetReviewOutcome, TargetReviewSpec
from .problem_only_review_contract import (
    ProblemOnlyReviewContractError,
    is_native_problem_only_contract,
    native_problem_image_args,
    native_source_contract_provenance,
    render_native_source_contract_prompt,
    resolve_target_review_source_contract,
    validate_native_review_source_certificate,
    validate_review_source_contract_current,
)
from .review_source_contract import (
    SOURCE_INCONSISTENCY_KIND,
    is_answer_blind_contract,
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


def _utcnow() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _formalization_review(row: dict) -> dict | None:
    raw = row.get("formalization_review")
    if raw is None:
        findings = row.get("findings")
        if isinstance(findings, dict):
            raw = findings.get("formalization_review")
    return raw if isinstance(raw, dict) else None


def _validate_certificate(
    row: dict,
    expected_source_contract: dict | None = None,
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
        error = _validate_certificate(row, expected_source_contract)
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
) -> str:
    milestone = output_dir / "milestones.jsonl"
    summary = output_dir / "summary.md"
    source_block = render_native_source_contract_prompt(source_contract)
    source_provenance = native_source_contract_provenance(source_contract)
    return f"""You are one target-scoped formalization Review worker for Archon iteration {iter_num}.

Assigned target (the only target you may review):
  {rel}

Read only these bounded inputs:
- Every bound problem image with its expected digest:
  {json.dumps(source_contract["images"], ensure_ascii=False)}
- Current Lean candidate: {target}
- Deterministic Lean preflight:
  {json.dumps(preflight, ensure_ascii=False)}

{source_block}

This is semantic formalization Review, not proof Review. `sorry` proof bodies
are allowed. Decide whether the statements faithfully and derivably encode the
bound problem evidence without smuggling a requested result into assumptions.

Audit all six checks independently: source_faithfulness, derivability,
abstraction_sufficiency, uncertainty_propagation, branch_orientation, and
countermodel_resistance. Every check needs concrete evidence. Only uncertainty
and branch checks may be not_applicable. Inventory every nontrivial
source-to-Lean bridge with a named carrier; a pass requires every bridge to be
covered.

Check that source_contract.candidate_sha256 binds the exact Lean candidate.
The deterministic preflight is worker-local execution evidence and is not part
of persisted source provenance. In blind_source_audit.lean_result_binding,
record the candidate hash, preflight status/compiles/returncode/sorry_count,
and the nontrivial Lean declarations carrying every requested result.

The complete student-visible problem, including any printed fallback, is
legitimate problem input. A fallback may be used only where the problem wording
permits it; never use a later fallback backward to establish the upstream
subpart whose result it mirrors. Derive each upstream requested output
independently from its givens.

For chemistry, enumerate every requested output; inspect every listed image;
check chemical identity, formula/molar-mass consistency, conservation, units,
structures/stereochemistry, identification uniqueness, raw arithmetic, and
mechanical significant-figure rules. Reject answer-shaped definitions,
preselected witness tables, post-hoc tolerances, staged rounding chosen to
reach a candidate, or a finite candidate domain not derived from the problem.

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
    "source_contract": {json.dumps(source_provenance, ensure_ascii=False)},
    "blind_source_audit": {{
      "answer_independence": {{"status":"passed|failed","evidence":"<why only bound problem inputs influenced the audit>"}},
      "raw_derivation": {{"status":"passed|failed","evidence":"<end-to-end unrounded/symbolic derivation carrier>"}},
      "reporting_rule_source": {{"status":"passed|failed","evidence":"<problem-stated or predeclared mechanical reporting rule>"}},
      "tolerance_provenance": {{"status":"passed|failed","evidence":"<measurement/rounding derivation for every tolerance>"}},
      "candidate_domain_provenance": {{"status":"passed|failed","evidence":"<problem-derived domain or explicit underdetermination>"}},
      "lean_result_binding": {{"status":"passed|failed","evidence":"<candidate_sha256, deterministic preflight results, and nontrivial Lean result carriers>"}}
    }},
    "contract_audit": {{
      "statement_scope": {{"status":"passed|failed","evidence":"..."}},
      "hypothesis_derivability": {{"status":"passed|failed","evidence":"..."}},
      "conclusion_alignment": {{"status":"passed|failed","evidence":"..."}},
      "bridge_completeness": {{"status":"passed|failed","evidence":"..."}}
    }},
    "requested_outputs": [{{"source_requirement":"<exact requested output>","lean_carrier":"<declaration or missing>","status":"covered|blocked","evidence":"..."}}],
    "blueprint_conflicts": [],
    "image_audit": [{{"path":"<exact source_contract path>","sha256":"<exact digest>","inspected":true,"evidence":"<relevant visual facts or access failure; use false when unreadable>"}}],
    "chemistry_checks": {{
      "chemical_semantics": {{"status":"passed|failed|not_applicable","evidence":"..."}},
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
) -> str:
    rel = target.resolve().relative_to(project_path.resolve()).as_posix()
    source_contract = resolve_target_review_source_contract(
        project_path=project_path,
        target=target,
        preflight=preflight,
        supplied_contract=source_contract,
    )
    if is_native_problem_only_contract(source_contract):
        return _build_native_target_formalization_review_prompt(
            project_path=project_path,
            iter_num=iter_num,
            target=target,
            rel=rel,
            output_dir=output_dir,
            preflight=preflight,
            source_contract=source_contract,
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
   The reporting rule, tolerance, and candidate domain must each be justified
   from the problem or a predeclared mechanical rule, never selected afterward.
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
fails closed."""
        chemistry_protocol = """For chemistry, enumerate every problem-requested
output; inspect every problem image; check chemical identity, formula/molar-mass
consistency, conservation, units, structures/stereochemistry, and identification
uniqueness. Specifically look for answer-shaped definitions, preselected witness
tables, post-hoc tolerances, staged rounding chosen to reach a candidate, and
candidate domains not derivable from the problem. Do not consult an official
answer, worked solution, marking scheme, rubric, answer key, or visible run."""
        source_audit_schema = """    \"blind_source_audit\": {
      \"answer_independence\": {\"status\":\"passed|failed\",\"evidence\":\"<why no answer-bearing input influenced statement or proof>\"},
      \"raw_derivation\": {\"status\":\"passed|failed\",\"evidence\":\"<end-to-end unrounded/symbolic derivation carrier>\"},
      \"reporting_rule_source\": {\"status\":\"passed|failed\",\"evidence\":\"<problem-stated or predeclared mechanical reporting rule>\"},
      \"tolerance_provenance\": {\"status\":\"passed|failed\",\"evidence\":\"<measurement/rounding derivation for every tolerance>\"},
      \"candidate_domain_provenance\": {\"status\":\"passed|failed\",\"evidence\":\"<problem-derived domain or explicit underdetermination>\"},
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
consistency and conservation), units, structures/stereochemistry, identification
uniqueness, definition/cardinality/table-level answer smuggling, and the official
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
- Prior formalization gate record: {json.dumps(prior_gate_record or {}, ensure_ascii=False)}

{source_block}

{source_protocol}

This is semantic formalization Review, not proof Review. `sorry` proof bodies are
allowed. Decide whether the statements faithfully and derivably encode the
source without smuggling the requested answer into assumptions.

Audit all six checks independently: source_faithfulness, derivability,
abstraction_sufficiency, uncertainty_propagation, branch_orientation, and
countermodel_resistance. Every check needs concrete evidence. Only uncertainty
and branch checks may be not_applicable. Inventory every nontrivial source-to-
Lean bridge with a named carrier; a pass requires every bridge to be covered.

{chemistry_protocol}

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
    milestone, validation_error = load_target_formalization_milestone(
        output_dir / "milestones.jsonl",
        spec.rel,
        spec.source_contract,
    )
    if validation_error:
        error = "; ".join(part for part in (error, validation_error) if part)
    return TargetReviewOutcome(
        rel=spec.rel,
        attempt=spec.attempt,
        runner_ok=runner_ok,
        milestone=milestone,
        error=error,
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
        str((_formalization_review(row) or {}).get("status") or "").lower() in _PASS
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
        if str(raw.get("status") or "").lower() in _PASS:
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
                        rel=spec.rel,
                        attempt=attempt,
                        runner_ok=False,
                        milestone=None,
                        error=f"{type(exc).__name__}: {exc}",
                    )
                if outcome.milestone is None:
                    failed[spec.rel] = target
                else:
                    outcomes[spec.rel] = outcome
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
