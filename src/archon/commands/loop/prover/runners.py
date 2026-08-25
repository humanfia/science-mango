"""Serial and parallel prover runners.

`SerialProverRunner` runs one prover invocation in the project's main
checkout. `ParallelProverRunner` fans out one prover per file in
`PROGRESS.md ## Current Objectives` over a `ProcessPoolExecutor`.

Both runners write meta status into the iteration's `meta.json` so the
dashboard can surface live state.
"""

from __future__ import annotations

import hashlib
import heapq
import json
import stat
import time
from collections.abc import Mapping
from collections import deque
from concurrent.futures import (
    FIRST_COMPLETED,
    Future,
    ProcessPoolExecutor,
    ThreadPoolExecutor,
    as_completed,
    wait,
)
from dataclasses import dataclass
from datetime import datetime, timezone
from itertools import count
from pathlib import Path

from archon import log
from archon.agent import (
    ClaudeBackend,
    DEFAULT_HARNESS,
    QuotaExhaustedError,
    build_runner,
)
from archon.commands.tooling.project_config import HarnessDescriptor
from archon.commands.tooling.domain_profile import load_domain_profile
from archon.prompts import (
    build_parallel_prover_prompt,
    build_prover_prompt,
    default_prover_mode_for_stage,
    normalize_stage_for_prompt_path,
)
from archon.state import (
    archive_task_results,
    parse_objective_files,
    parse_objectives_with_modes,
    read_meta,
    write_meta,
)

from ..formalization_review_gate import (
    apply_target_formalization_review,
    effective_formalization_review_limit,
    filter_materialized_redrafts_for_dispatch,
    formalization_review_decision,
    load_gate_state as load_formalization_review_state,
    reopen_formalization_targets,
)
from ..parallel_formalization_review import (
    _run_formalization_review_worker,
    build_target_formalization_review_prompt,
)
from ..parallel_review import (
    PipelinedTargetReviewConfig,
    TargetReviewOutcome,
    TargetReviewSpec,
    _run_review_worker,
    build_target_review_prompt,
    load_target_milestone,
    write_parallel_review_session,
    write_pipelined_review_report,
)
from ..proof_review_gate import (
    apply_target_proof_review,
    load_proof_review_state,
    proof_review_decision,
    reset_proof_review_targets_after_redraft,
)
from ..numeric_reporting_guard import MAX_NUMERIC_REPORTING_REASON_LENGTH
from ..review_preflight import check_review_target
from ..review_feedback import (
    MAX_REPAIR_TASK_PROMPT_BYTES,
    bound_repair_task,
    build_feedback_event,
    build_repair_task,
    render_repair_task,
    validated_trusted_bridge_redraft_projection,
)
from ..trusted_bridge_activation import (
    build_trusted_bridge_activation_redraft_projection,
    trusted_bridge_lineage_matches_formalization_pass,
)
from ..problem_only_review_contract import (
    ProblemOnlyReviewContractError,
    native_problem_image_args,
    native_problem_only_enabled,
    render_native_certified_prior_result_prompt,
    render_native_chemistry_constant_policy,
    render_native_formalizer_composition_accounting_prompt,
    render_native_formalizer_answer_submission_prompt,
    render_native_formalizer_semantic_dag_prompt,
    resolve_native_formalizer_source_contract,
    resolve_target_review_source_contract,
    validate_native_answer_submission_current,
)
from ..resume import PROVER_CONTINUE, persist_session_id, pick_resume_session
from ..sorry_count import file_open_sorry_count
from ..utils import file_slug, relpath
from .environment import ProverEnvironment, snapshot_baseline


def _default_harness() -> HarnessDescriptor:
    """The built-in claude-code descriptor (zero-config default).

    Used as the default for the prover runners so an unconfigured project
    threads exactly the built-in claude-code runner — :func:`build_runner`
    short-circuits a ``runner == "claude-code"`` descriptor to the legacy
    :class:`~archon.agent.ClaudeAgent` (carrying the loop-wide backend).
    """
    return HarnessDescriptor(name=DEFAULT_HARNESS, runner=DEFAULT_HARNESS)


def _load_mode_content(state_dir: Path, mode_name: str | None) -> str | None:
    """Load the body of a prover-mode descriptor (after frontmatter), or None."""
    if not mode_name:
        return None
    mode_file = state_dir / "prover-modes" / f"{mode_name}.md"
    if not mode_file.exists():
        return None
    text = mode_file.read_text(encoding="utf-8")
    # Strip YAML frontmatter (---...---) so only the body is injected.
    import re as _re
    stripped = _re.sub(r"^---\s*\n.*?\n---\s*\n", "", text, count=1, flags=_re.DOTALL)
    return stripped.strip() or None


class _ImmediateRedraftPromptError(ValueError):
    """A target-local prompt construction failure safe to route as an error."""


_MAX_SEALED_MODE_BYTES = 32 * 1024
MAX_IMMEDIATE_REDRAFT_PROMPT_BYTES = 128 * 1024


def _sealed_mode_reference(
    state_dir: Path,
    mode_name: str | None,
) -> str | None:
    """Bind a compact redraft instruction to one sealed prover-mode file."""
    if mode_name is None:
        return None
    if (
        not isinstance(mode_name, str)
        or not mode_name
        or len(mode_name) > 128
        or any(
            not char.isascii() or not (char.isalnum() or char in "-_")
            for char in mode_name
        )
    ):
        raise _ImmediateRedraftPromptError(
            "sealed prover mode name is invalid"
        )

    modes_dir = state_dir / "prover-modes"
    mode_file = modes_dir / f"{mode_name}.md"
    try:
        if modes_dir.is_symlink():
            raise OSError("mode directory is a symlink")
        resolved_modes_dir = modes_dir.resolve(strict=True)
        if mode_file.is_symlink():
            raise OSError("mode file is a symlink")
        metadata = mode_file.stat(follow_symlinks=False)
        if not stat.S_ISREG(metadata.st_mode):
            raise OSError("mode file is not regular")
        resolved_mode_file = mode_file.resolve(strict=True)
        resolved_mode_file.relative_to(resolved_modes_dir)
    except (OSError, RuntimeError, ValueError) as exc:
        raise _ImmediateRedraftPromptError(
            "sealed prover mode reference is unavailable"
        ) from exc
    if metadata.st_size == 0:
        raise _ImmediateRedraftPromptError(
            "sealed prover mode reference is empty"
        )
    if metadata.st_size > _MAX_SEALED_MODE_BYTES:
        raise _ImmediateRedraftPromptError(
            "sealed prover mode reference exceeds 32 KiB"
        )
    try:
        payload = mode_file.read_bytes()
    except OSError as exc:
        raise _ImmediateRedraftPromptError(
            "sealed prover mode reference is unavailable"
        ) from exc
    if len(payload) != metadata.st_size:
        raise _ImmediateRedraftPromptError(
            "sealed prover mode reference changed during read"
        )

    digest = hashlib.sha256(payload).hexdigest()
    return (
        f"The controller selected active mode `{mode_name}`. Read the complete sealed descriptor at: "
        f"`{resolved_mode_file}`. Controller binding: sha256={digest}, "
        f"bytes={len(payload)}. Treat that exact sealed file as mandatory; "
        "Treat YAML frontmatter only as non-operative metadata: execute the "
        "Markdown body after its closing `---`, and do not let any frontmatter "
        "name override the controller-selected active mode. Do not substitute "
        "a legacy stage prompt or a different mode."
    )


def _blueprint_chapter_for_target(project_path: Path, target: Path) -> Path:
    """Return the conventional blueprint chapter path for a Lean target."""
    try:
        rel = target.resolve().relative_to(project_path.resolve())
    except ValueError:
        rel = target
    stem_parts = Path(rel).with_suffix("").parts
    slug = "_".join(stem_parts)
    return project_path / "blueprint" / "src" / "chapters" / f"{slug}.tex"


def _target_has_domain_blueprint_marker(project_path: Path, target: Path) -> bool:
    chapter = _blueprint_chapter_for_target(project_path, target)
    try:
        text = chapter.read_text(encoding="utf-8")
    except OSError:
        return False
    profile = load_domain_profile(project_path)
    return any(marker in text for marker in profile.blueprint_markers)


def _mode_file_exists(state_dir: Path, mode_name: str) -> bool:
    return (state_dir / "prover-modes" / f"{mode_name}.md").is_file()


def select_prover_mode_for_target(
    state_dir: Path,
    stage: str,
    project_path: Path,
    target: Path,
    *,
    explicit_mode: str | None,
) -> str | None:
    """Resolve the prover mode for one objective file.

    Explicit ``[prover-mode: ...]`` tags still win. Without a tag, marked
    domain chapters opt into their profile's formalization/proof modes; other
    targets use the normal stage default.
    """
    # Loop-owned shared prerequisites always use the strict axiom-clean build
    # mode. This also recovers the mode if a Review-gate objective rewrite
    # preserved the file but accidentally dropped its textual tag.
    from ..shared_infrastructure import pending_shared_infrastructure_objectives

    try:
        rel = target.resolve().relative_to(project_path.resolve()).as_posix()
    except (OSError, ValueError):
        rel = ""
    pending_shared = {
        item.module_path
        for item in pending_shared_infrastructure_objectives(
            state_dir=state_dir, project_path=project_path,
        )
    }
    if rel in pending_shared and _mode_file_exists(state_dir, "mathlib-build"):
        return "mathlib-build"
    if explicit_mode:
        return explicit_mode
    canonical = normalize_stage_for_prompt_path(stage)
    if _target_has_domain_blueprint_marker(project_path, target):
        domain_mode = load_domain_profile(project_path).mode_for_stage(canonical)
        if domain_mode and _mode_file_exists(state_dir, domain_mode):
            return domain_mode
    return default_prover_mode_for_stage(state_dir, stage)


def _restrict_progress_to_pending_shared_modules(
    *, progress_file: Path, state_dir: Path, project_path: Path,
) -> list[Path]:
    """Keep infrastructure builds isolated from ordinary proof targets."""
    from ..formalization_review_gate import _replace_objectives
    from ..shared_infrastructure import pending_shared_infrastructure_objectives

    pending = {
        (project_path / item.module_path).resolve(): item
        for item in pending_shared_infrastructure_objectives(
            state_dir=state_dir, project_path=project_path,
        )
        if (project_path / item.module_path).is_file()
    }
    selected = [
        path for path in parse_objective_files(progress_file, project_path)
        if path.resolve() in pending
    ]
    if not selected:
        return []
    _replace_objectives(progress_file, [
        f"- **`{path.resolve().relative_to(project_path.resolve()).as_posix()}`** — "
        "Build pending shared infrastructure axiom-clean. "
        "[prover-mode: mathlib-build]"
        for path in selected
    ])
    return selected


def _target_sha256(target: Path) -> str:
    try:
        return hashlib.sha256(target.read_bytes()).hexdigest()
    except OSError:
        return ""


_ANSWER_SUBMISSION_REPAIR_LABEL = "answer submission validation"


def _answer_submission_repair_handoff(error: str) -> dict[str, object]:
    """Return a fixed, answer-free repair task for one invalid sidecar."""

    lowered = error.lower()
    if "display_value must be a finite decimal or scientific value" in lowered:
        code = "numeric_display_syntax"
    elif "has invalid fields" in lowered:
        code = "invalid_output_fields"
    else:
        code = "invalid_answer_submission"
    return {
        "schema_version": 1,
        "kind": "controller_answer_submission_repair",
        "outcome": "invalid",
        "reason_codes": [code],
        "failed_check_ids": ["answer_submission_contract"],
        "actions": ["repair_answer_submission_contract"],
    }


def _durable_formalization_retry_handoff(
    record: Mapping[str, object],
    *,
    candidate_sha256: str,
    expected_source_contract: Mapping[str, object] | None,
    target_rel: str,
) -> dict[str, object]:
    """Rebuild one retry hand-off through the strict sanitizer boundary.

    Gate files are mutable lifecycle state, so a persisted ``repair_handoff``
    is never inserted into a prompt directly. The controller reconstructs it
    from allowlisted certificate fields and candidate-bound status instead.
    This also upgrades pre-handoff batch records without trusting free text.
    """
    gate_digest = str(record.get("candidate_sha256") or "").strip().lower()
    if gate_digest != candidate_sha256:
        return {}
    raw_certificate = record.get("certificate")
    certificate: Mapping[str, object] = (
        raw_certificate if isinstance(raw_certificate, Mapping) else {}
    )
    raw_milestones = certificate.get("milestones")
    if (
        isinstance(raw_milestones, list)
        and len(raw_milestones) == 1
        and isinstance(raw_milestones[0], Mapping)
    ):
        certificate = raw_milestones[0]

    reviews_value = record.get("reviews")
    reviews = (
        reviews_value
        if isinstance(reviews_value, int)
        and not isinstance(reviews_value, bool)
        and reviews_value >= 0
        else 0
    )
    iter_value = record.get("last_review_iter")
    iteration = (
        iter_value
        if isinstance(iter_value, int)
        and not isinstance(iter_value, bool)
        and iter_value >= 0
        else 0
    )
    feedback_event = build_feedback_event(
        review_kind="formalization",
        candidate_sha256=candidate_sha256,
        event_id=f"durable:{iteration}:formalization:{reviews}",
        iteration=iteration,
        attempt=reviews,
        resulting_status="retry",
        certificate=certificate,
        decision="failed",
    )
    raw_events = record.get("repair_events")
    repair_events = list(raw_events) if isinstance(raw_events, list) else []
    repair_record = {
        **record,
        "certificate": certificate,
        "repair_events": [*repair_events, feedback_event][-20:],
    }
    return build_repair_task(
        repair_record,
        review_kind="formalization",
        worker_stage="formalization",
        candidate_sha256=candidate_sha256,
        discard_stale_record=True,
        expected_source_contract=expected_source_contract,
        target_rel=target_rel,
    )


def _proof_formalization_redraft_handoff(
    proof_record: Mapping[str, object],
    formalization_record: Mapping[str, object],
    *,
    project_path: Path,
    target: Path,
    target_rel: str,
    preflight: Mapping[str, object] | None = None,
) -> dict[str, object]:
    """Rebuild a proof-to-formalizer handoff from exact gate state.

    Only the formalization gate's controller-carried redraft projection can
    cross this boundary.  Proof prose and candidate contents are never
    inspected for an activation.
    """
    candidate_sha256 = _target_sha256(target)
    try:
        expected_source_contract = resolve_target_review_source_contract(
            project_path=project_path,
            target=target,
            preflight=None,
        )
    except ProblemOnlyReviewContractError:
        expected_source_contract = None
    activation = None
    raw_pass_candidate_sha256 = formalization_record.get("candidate_sha256")
    formalization_pass_candidate_sha256 = (
        raw_pass_candidate_sha256
        if isinstance(raw_pass_candidate_sha256, str)
        else ""
    )
    history = formalization_record.get("reopen_history")
    latest_reopen = history[-1] if isinstance(history, list) and history else None
    previous_certificate = (
        latest_reopen.get("previous_certificate")
        if isinstance(latest_reopen, Mapping)
        and isinstance(latest_reopen.get("previous_certificate"), Mapping)
        else None
    )
    lineage = formalization_record.get("trusted_bridge_activation_lineage")
    parent_bound = (
        formalization_record.get("status") == "retry"
        and formalization_record.get("reopened_by") == "proof_review"
        and isinstance(latest_reopen, Mapping)
        and latest_reopen.get("previous_status") == "passed"
        and latest_reopen.get("previous_reviews")
        == formalization_record.get("reviews")
        and latest_reopen.get("proof_review_iter")
        == formalization_record.get("last_reopened_iter")
        and trusted_bridge_lineage_matches_formalization_pass(
            lineage if isinstance(lineage, Mapping) else None,
            target_rel=target_rel,
            formalization_pass_candidate_sha256=(
                formalization_pass_candidate_sha256
            ),
            passing_certificate=previous_certificate,
        )
    )
    if parent_bound:
        raw_activation = formalization_record.get(
            "trusted_bridge_redraft_activation"
        )
        rebuilt_activation = (
            build_trusted_bridge_activation_redraft_projection(
                lineage,
                target_rel=target_rel,
                current_candidate_sha256=candidate_sha256,
                expected_source_contract=expected_source_contract,
            )
        )
        if (
            isinstance(raw_activation, Mapping)
            and rebuilt_activation
            and raw_activation == rebuilt_activation
        ):
            activation = raw_activation
    return build_repair_task(
        proof_record,
        review_kind="proof",
        worker_stage="formalization",
        candidate_sha256=candidate_sha256,
        preflight=preflight,
        discard_stale_record=True,
        expected_source_contract=expected_source_contract,
        target_rel=target_rel,
        trusted_bridge_activations=activation,
        trusted_bridge_formalization_pass_candidate_sha256=(
            formalization_pass_candidate_sha256
        ),
    )


def _task_result_fingerprints(state_dir: Path, rel: str) -> dict[str, str]:
    result_root = state_dir / "task_results"
    slug = file_slug(rel)
    candidates = {
        result_root / f"{rel}.md",
        result_root / f"{Path(rel).name}.md",
        result_root / f"{slug}.lean.md",
        result_root / f"{slug}.md",
    }
    fingerprints: dict[str, str] = {}
    for path in candidates:
        digest = _target_sha256(path)
        if digest:
            fingerprints[str(path)] = digest
    return fingerprints


def _native_formalizer_semantic_dag_block(
    *, project_path: Path, target: Path,
) -> str:
    """Resolve a fresh controller DAG before a native Formalizer launch."""
    if not native_problem_only_enabled(project_path):
        return ""
    contract = resolve_native_formalizer_source_contract(
        project_path=project_path,
        target=target,
    )
    return "\n\n".join(
        block
        for block in (
            render_native_chemistry_constant_policy(contract),
            render_native_certified_prior_result_prompt(contract),
            render_native_formalizer_semantic_dag_prompt(contract),
            render_native_formalizer_composition_accounting_prompt(contract),
            render_native_formalizer_answer_submission_prompt(contract),
        )
        if block
    )


_INCOMPLETE_REPAIR_FEEDBACK_ERROR = (
    "immediate redraft prompt cannot retain complete repair feedback"
)


def _validate_complete_repair_projection(
    original_task: Mapping[str, object],
    bounded_task: Mapping[str, object],
    *,
    target_rel: str = "",
    expected_source_contract: Mapping[str, object] | None = None,
) -> None:
    """Reject a bounded prompt that loses any required repair feedback."""
    if not bounded_task:
        raise _ImmediateRedraftPromptError(
            _INCOMPLETE_REPAIR_FEEDBACK_ERROR
        )

    ignored_top_level = {"history", "source_bound_review"}
    original_core = {
        key: value
        for key, value in original_task.items()
        if key not in ignored_top_level
    }
    bounded_core = {
        key: value
        for key, value in bounded_task.items()
        if key not in ignored_top_level
    }
    if bounded_core != original_core:
        raise _ImmediateRedraftPromptError(
            _INCOMPLETE_REPAIR_FEEDBACK_ERROR
        )

    if "history" in original_task:
        original_history = original_task.get("history")
        bounded_history = bounded_task.get("history")
        if isinstance(original_history, Mapping) and isinstance(
            bounded_history, Mapping
        ):
            original_history_core = {
                key: value
                for key, value in original_history.items()
                if key != "events"
            }
            bounded_history_core = {
                key: value
                for key, value in bounded_history.items()
                if key != "events"
            }
            if bounded_history_core != original_history_core:
                raise _ImmediateRedraftPromptError(
                    _INCOMPLETE_REPAIR_FEEDBACK_ERROR
                )
            original_events = original_history.get("events")
            bounded_events = bounded_history.get("events")
            if isinstance(original_events, list) and original_events:
                if (
                    not isinstance(bounded_events, list)
                    or not bounded_events
                    or bounded_events
                    != original_events[-len(bounded_events):]
                ):
                    raise _ImmediateRedraftPromptError(
                        _INCOMPLETE_REPAIR_FEEDBACK_ERROR
                    )
            elif bounded_events != original_events:
                raise _ImmediateRedraftPromptError(
                    _INCOMPLETE_REPAIR_FEEDBACK_ERROR
                )
        elif bounded_history != original_history:
            raise _ImmediateRedraftPromptError(
                _INCOMPLETE_REPAIR_FEEDBACK_ERROR
            )
    elif "history" in bounded_task:
        raise _ImmediateRedraftPromptError(
            _INCOMPLETE_REPAIR_FEEDBACK_ERROR
        )

    original_activation = original_task.get("trusted_bridge_activations")
    bounded_activation = bounded_task.get("trusted_bridge_activations")
    if original_activation is not None or bounded_activation is not None:
        reason_codes = original_task.get("reason_codes")
        candidate_sha256 = original_task.get("candidate_sha256")
        if (
            original_task.get("review_kind") != "proof"
            or original_task.get("worker_stage") != "formalization"
            or not isinstance(reason_codes, list)
            or "needs_redraft" not in reason_codes
            or not isinstance(candidate_sha256, str)
            or not isinstance(original_activation, Mapping)
            or not isinstance(bounded_activation, Mapping)
        ):
            raise _ImmediateRedraftPromptError(
                _INCOMPLETE_REPAIR_FEEDBACK_ERROR
            )
        raw_receipts = original_activation.get("receipts")
        first_receipt = (
            raw_receipts[0]
            if isinstance(raw_receipts, list) and raw_receipts
            else None
        )
        lineage_binding = (
            first_receipt.get("lineage_binding")
            if isinstance(first_receipt, Mapping)
            else None
        )
        formalization_pass_candidate_sha256 = (
            lineage_binding.get("formalization_pass_candidate_sha256")
            if isinstance(lineage_binding, Mapping)
            else ""
        )
        validated_activation = (
            validated_trusted_bridge_redraft_projection(
                original_activation,
                target_rel=target_rel,
                candidate_sha256=candidate_sha256,
                expected_source_contract=expected_source_contract,
                formalization_pass_candidate_sha256=str(
                    formalization_pass_candidate_sha256 or ""
                ),
            )
        )
        if (
            not validated_activation
            or validated_activation != original_activation
            or bounded_activation != original_activation
        ):
            raise _ImmediateRedraftPromptError(
                _INCOMPLETE_REPAIR_FEEDBACK_ERROR
            )

    if "source_bound_review" not in original_task:
        if "source_bound_review" in bounded_task:
            raise _ImmediateRedraftPromptError(
                _INCOMPLETE_REPAIR_FEEDBACK_ERROR
            )
        return

    original_source = original_task.get("source_bound_review")
    bounded_source = bounded_task.get("source_bound_review")
    if not isinstance(original_source, Mapping) or not isinstance(
        bounded_source, Mapping
    ):
        raise _ImmediateRedraftPromptError(
            _INCOMPLETE_REPAIR_FEEDBACK_ERROR
        )

    for source_review in (original_source, bounded_source):
        projection = source_review.get("repair_action_projection")
        actions = source_review.get("repair_actions")
        if not isinstance(projection, Mapping) or not isinstance(actions, list):
            raise _ImmediateRedraftPromptError(
                _INCOMPLETE_REPAIR_FEEDBACK_ERROR
            )
        failed_count = projection.get("failed_bridge_count")
        retained_count = projection.get("retained_count")
        if (
            type(failed_count) is not int
            or failed_count < 0
            or type(retained_count) is not int
            or retained_count != failed_count
            or projection.get("truncated") is not False
            or len(actions) != failed_count
        ):
            raise _ImmediateRedraftPromptError(
                _INCOMPLETE_REPAIR_FEEDBACK_ERROR
            )

    for source_review in (original_source, bounded_source):
        activation = source_review.get("trusted_bridge_activations")
        if activation is None:
            continue
        if (
            not isinstance(activation, Mapping)
            or set(activation) != {
                "schema_version", "requested_count", "activated_count",
                "complete", "requests_sha256", "receipts",
            }
            or activation.get("schema_version") != 1
            or type(activation.get("requested_count")) is not int
            or activation.get("requested_count") <= 0
            or activation.get("activated_count")
            != activation.get("requested_count")
            or activation.get("complete") is not True
            or not isinstance(activation.get("receipts"), list)
            or len(activation["receipts"])
            != activation.get("requested_count")
        ):
            raise _ImmediateRedraftPromptError(
                _INCOMPLETE_REPAIR_FEEDBACK_ERROR
            )
        for receipt in activation["receipts"]:
            if not isinstance(receipt, Mapping):
                raise _ImmediateRedraftPromptError(
                    _INCOMPLETE_REPAIR_FEEDBACK_ERROR
                )
            unsigned = dict(receipt)
            receipt_sha256 = unsigned.pop("activation_receipt_sha256", "")
            target_binding = receipt.get("target")
            rule = receipt.get("rule")
            applicability = receipt.get("applicability")
            if (
                receipt.get("schema_version") != 1
                or receipt.get("kind")
                != "controller_trusted_bridge_activation"
                or not isinstance(target_binding, Mapping)
                or target_binding.get("candidate_sha256")
                != original_task.get("candidate_sha256")
                or not isinstance(rule, Mapping)
                or rule.get("automatic_problem_instantiation") is not False
                or not isinstance(rule.get("applicability_conditions"), list)
                or not rule.get("applicability_conditions")
                or not isinstance(rule.get("exclusions"), list)
                or not isinstance(applicability, Mapping)
                or applicability.get("status")
                != "not_evaluated_by_controller"
                or applicability.get("condition_semantics")
                != "all_required_fail_closed"
                or applicability.get("required_condition_count")
                != len(rule["applicability_conditions"])
                or type(applicability.get("required_condition_count")) is not int
                or applicability["required_condition_count"] <= 0
                or applicability.get(
                    "complete_receipt_does_not_establish_conditions"
                ) is not True
                or set(applicability) != {
                    "status",
                    "condition_semantics",
                    "required_condition_count",
                    "complete_receipt_does_not_establish_conditions",
                }
                or not isinstance(receipt_sha256, str)
                or hashlib.sha256(json.dumps(
                    unsigned, ensure_ascii=False, sort_keys=True,
                    separators=(",", ":"), allow_nan=False,
                ).encode("utf-8")).hexdigest() != receipt_sha256
            ):
                raise _ImmediateRedraftPromptError(
                    _INCOMPLETE_REPAIR_FEEDBACK_ERROR
                )

    if bounded_source != original_source:
        raise _ImmediateRedraftPromptError(
            _INCOMPLETE_REPAIR_FEEDBACK_ERROR
        )


def build_immediate_redraft_prompt(
    *,
    project_name: str,
    project_path: Path,
    state_dir: Path,
    iter_num: int,
    target: Path,
    review_certificate: dict,
    debug_feedback: bool,
    handoff_label: str = "proof Review",
) -> str:
    """Build a target-only formalizer prompt from a semantic Review route."""
    rel = relpath(target, project_path)
    mode_name = select_prover_mode_for_target(
        state_dir, "autoformalize", project_path, target, explicit_mode=None,
    )
    mode_reference = _sealed_mode_reference(state_dir, mode_name)
    base_prompt = build_parallel_prover_prompt(
        project_name,
        project_path,
        state_dir,
        "autoformalize",
        iter_num,
        assigned_rel_lean_path=rel,
        debug_feedback=debug_feedback,
        mode_name=mode_name,
        # Keep the active-mode branch without duplicating the full sealed mode
        # body. The short hash-bound reference preserves routing and leaves
        # room for the accepted Review's structured repair hand-off.
        mode_content=mode_reference,
    )
    semantic_block = _native_formalizer_semantic_dag_block(
        project_path=project_path, target=target,
    )
    expected_source_contract: Mapping[str, object] | None = None
    if "trusted_bridge_activations" in review_certificate:
        try:
            expected_source_contract = resolve_target_review_source_contract(
                project_path=project_path,
                target=target,
                preflight=None,
            )
        except ProblemOnlyReviewContractError:
            expected_source_contract = None
    prompt_prefix = f"""{base_prompt}

{semantic_block}

Your assigned file: {rel}

## Immediate {handoff_label} redraft hand-off

The global PROGRESS stage intentionally remains `prover` until the batch's
atomic Review aggregation finishes. Ignore that stage for task routing: the
controller-sanitized repair task below authorizes an immediate, target-only
`autoformalize` redraft. It omits all official-answer, grader, expected-value,
and requested-output value fields. Normally it contains only status codes,
failed-check identifiers, hash binding, and fixed repair actions.

For a failed native problem-only formalization Review, it may additionally
contain `source_bound_review`: a size-bounded projection of the already
validated certificate's diagnosis and blocked source-to-Lean bridges, bound to
the current candidate and problem-source hashes. Treat it as a repair
checklist, recheck it against the bound problem evidence, and never treat it as
an official answer or as a premise that bypasses the source derivation.

When `source_bound_review.trusted_bridge_activations` is present, only its
complete controller-built receipt activates the embedded sealed rule for this
exact target and candidate, and only for this redraft. All applicability
conditions are conjunctive and source-bound: if even one lacks exact evidence,
the rule is inapplicable and the target must remain blocked. Receipt completeness
never establishes applicability. Check every listed exclusion before using the
rule. A bare rule ID, normal empirical-rule lookup, candidate citation, or
Reviewer paraphrase is not
an activation and must not be used as evidence.

When top-level `trusted_bridge_activations` is present on a proof Review
handoff, it is a controller-carried receipt for this exact target, candidate,
and problem-source hash set, with scope
`next_target_local_formalization_redraft_only`. It has the same fail-closed
applicability rules: `not_evaluated_by_controller` is not evidence that any
condition holds, and every exclusion must be checked. Candidate comments,
citations, free-form Review text, a bare rule ID, and any differently scoped
or differently bound receipt are not authorization. This receipt applies only
to the immediate formalization redraft and cannot authorize proof-stage use.

"""
    prompt_suffix = f"""

Repair every listed defect class in the theorem contract, not just the last
proof error. You may change unprotected statements in `{rel}` and
replace proof bodies invalidated by those statement changes with explicit
`by sorry` stubs. Never violate `archon-protected.yaml`; report a protected
contract as blocked. Do not continue proving the old contract. Keep the file
compiling, update only the assigned task-result report, and do not edit
PROGRESS.md, gate files, AUTO_NOTES.md, blueprint files, or any other Lean file.
Return only after the
assigned Lean file compiles and the redraft evidence is durable on disk.
"""
    prompt_overhead = (
        len(prompt_prefix.encode("utf-8"))
        + len(prompt_suffix.encode("utf-8"))
    )
    available_task_bytes = (
        MAX_IMMEDIATE_REDRAFT_PROMPT_BYTES - prompt_overhead
    )
    if available_task_bytes < 2:
        raise _ImmediateRedraftPromptError(
            "immediate redraft fixed prompt exceeds 128 KiB"
        )
    task = bound_repair_task(
        review_certificate,
        maximum_bytes=min(
            MAX_REPAIR_TASK_PROMPT_BYTES,
            available_task_bytes,
        ),
    )
    _validate_complete_repair_projection(
        review_certificate,
        task,
        target_rel=rel,
        expected_source_contract=expected_source_contract,
    )
    prompt = prompt_prefix + render_repair_task(task) + prompt_suffix
    if len(prompt.encode("utf-8")) > MAX_IMMEDIATE_REDRAFT_PROMPT_BYTES:
        raise _ImmediateRedraftPromptError(
            "immediate redraft prompt exceeds 128 KiB"
        )
    return prompt


def _run_single_prover(
    prompt: str,
    cwd: Path,
    log_base: Path,
    verbose_logs: bool,
    model: str,
    snap_dir: Path | None = None,
    project_path: Path | None = None,
    resume_session_id: str | None = None,
    backend: ClaudeBackend | None = None,
    harness: HarnessDescriptor | None = None,
    image_target: Path | None = None,
) -> bool:
    """Top-level for `ProcessPoolExecutor` — must be importable by the worker.

    ``harness`` is the resolved, **picklable** :class:`HarnessDescriptor`
    (a frozen dataclass) — not a bare name string — so the worker can build
    a fully-configured runner (codex model / effort / gateway, or the
    claude-code engine carrying ``backend``) via :func:`build_runner`
    without re-reading config. ``None`` → built-in claude-code.
    """
    descriptor = harness if harness is not None else _default_harness()
    image_args = (
        native_problem_image_args(
            project_path=project_path or cwd,
            target=image_target,
            harness=descriptor,
        ) if image_target is not None else []
    )
    agent = build_runner(
        role="prover", model=model, descriptor=descriptor,
        backend=backend or ClaudeBackend(),
    )
    if snap_dir is not None and project_path is not None:
        with ProverEnvironment(
            snap_dir=snap_dir,
            prover_jsonl=Path(str(log_base) + ".jsonl"),
            project_path=project_path,
        ):
            return agent.run(
                prompt, cwd=cwd, log_base=log_base, verbose_logs=verbose_logs,
                resume_session_id=resume_session_id,
                extra_args=image_args,
            )
    return agent.run(
        prompt, cwd=cwd, log_base=log_base, verbose_logs=verbose_logs,
        resume_session_id=resume_session_id,
        extra_args=image_args,
    )


@dataclass(frozen=True)
class _PipelineWork:
    kind: str
    target: Path
    rel: str
    slug: str
    attempt: int = 0
    cycle: int = 0
    baseline_sha256: str = ""
    result_fingerprints: tuple[tuple[str, str], ...] = ()
    source_contract: dict | None = None


def _pipeline_cycle(value: object) -> int:
    """Return one persisted positive lifecycle cycle, or zero if malformed."""
    if isinstance(value, int) and not isinstance(value, bool):
        cycle = value
    elif isinstance(value, str) and value.isascii() and value.isdigit():
        try:
            cycle = int(value)
        except ValueError:
            return 0
        if str(cycle) != value:
            return 0
    else:
        return 0
    return cycle if cycle > 0 else 0


def _latest_pipeline_event_cycle(
    record: dict,
    *,
    history_key: str,
    iter_num: int,
    rel: str,
    kind: str,
) -> int:
    """Recover the latest current-iteration cycle already consumed by a gate."""
    history = record.get(history_key)
    if not isinstance(history, list):
        return 0
    prefix = f"pipeline:{iter_num}:{rel}:{kind}:"
    latest = 0
    for entry in history:
        if not isinstance(entry, dict):
            continue
        event_id = str(entry.get("event_id") or "")
        if not event_id.startswith(prefix):
            continue
        suffix = event_id[len(prefix):]
        if suffix.isdigit():
            latest = max(latest, _pipeline_cycle(suffix))
    return latest


def _pipeline_event_field(
    record: dict,
    *,
    history_key: str,
    iter_num: int,
    rel: str,
    kind: str,
    cycle: int,
    field: str,
) -> str:
    """Return one field from an exact durable lifecycle gate event."""
    history = record.get(history_key)
    if not isinstance(history, list) or cycle <= 0:
        return ""
    event_id = f"pipeline:{iter_num}:{rel}:{kind}:{cycle}"
    for entry in reversed(history):
        if isinstance(entry, dict) and entry.get("event_id") == event_id:
            value = entry.get(field)
            return str(value).strip() if value is not None else ""
    return ""


class SerialProverRunner:
    """Runs a single prover prompt over the whole stage.

    The plan agent's objectives mention chapters; we don't pre-split by
    file because we don't know which file a serial run will touch in
    which order.
    """

    def __init__(
        self,
        *,
        project_name: str,
        project_path: Path,
        state_dir: Path,
        stage: str,
        iter_dir: Path,
        iter_num: int,
        verbose_logs: bool,
        model: str,
        debug_feedback: bool = False,
        iter_meta: Path | None = None,
        resume_enabled: bool = False,
        backend: ClaudeBackend | None = None,
        harness: HarnessDescriptor | None = None,
    ) -> None:
        self.project_name = project_name
        self.project_path = project_path
        self.state_dir = state_dir
        self.stage = stage
        self.iter_dir = iter_dir
        self.iter_num = iter_num
        self.verbose_logs = verbose_logs
        self.model = model
        self.debug_feedback = debug_feedback
        self.iter_meta = iter_meta
        self.resume_enabled = resume_enabled
        self.backend = backend or ClaudeBackend()
        self.harness = harness if harness is not None else _default_harness()

    def run(self, *, dry_run: bool, progress_file: Path) -> None:
        # No per-file tags on the serial whole-stage path → use the stage's
        # default prover mode (the static prover-<stage>.md prompts were
        # retired; modes are the single source of truth).
        shared = _restrict_progress_to_pending_shared_modules(
            progress_file=progress_file,
            state_dir=self.state_dir,
            project_path=self.project_path,
        )
        stage_mode = (
            "mathlib-build" if shared
            else default_prover_mode_for_stage(self.state_dir, self.stage)
        )
        prompt = build_prover_prompt(
            self.project_name, self.project_path, self.state_dir, self.stage,
            self.iter_num, debug_feedback=self.debug_feedback,
            mode_name=stage_mode,
            mode_content=_load_mode_content(self.state_dir, stage_mode),
        )
        if dry_run:
            log.step("[dry-run] Prover prompt:")
            print(prompt)
            return

        archive_task_results(self.state_dir, self.iter_dir)

        prover_log = self.iter_dir / "prover"
        for sf in parse_objective_files(progress_file, self.project_path):
            srel = relpath(sf, self.project_path)
            sslug = file_slug(srel)
            snapshot_baseline(sf, self.iter_dir / "snapshots" / sslug)

        resume_sid = pick_resume_session(
            self.iter_meta, "prover.sessionId",
            enabled=self.resume_enabled, label="prover",
            cwd=self.project_path,
            jsonl_fallback=Path(str(prover_log) + ".jsonl"),
        )
        with ProverEnvironment(
            snap_dir=self.iter_dir / "snapshots",
            prover_jsonl=Path(str(prover_log) + ".jsonl"),
            project_path=self.project_path,
            serial_mode=True,
        ):
            build_runner(
                role="prover", model=self.model, descriptor=self.harness,
                backend=self.backend,
            ).run(
                PROVER_CONTINUE if resume_sid else prompt,
                cwd=self.project_path,
                log_base=prover_log, verbose_logs=self.verbose_logs,
                resume_session_id=resume_sid,
            )
        persist_session_id(
            self.iter_meta, Path(str(prover_log) + ".jsonl"),
            "prover.sessionId",
        )


class ParallelProverRunner:
    """Runs one prover per objective file in a process pool.

    Single-file rounds collapse to serial-with-blueprint-pointer for
    determinism: spawning a process pool for one worker just adds noise.
    """

    def __init__(
        self,
        *,
        project_name: str,
        project_path: Path,
        state_dir: Path,
        stage: str,
        iter_dir: Path,
        iter_meta: Path,
        iter_num: int,
        max_parallel: int,
        max_objectives: int,
        block_on_blocked_deps: bool,
        verbose_logs: bool,
        model: str,
        dashboard_url: str | None = None,
        blueprint_url: str | None = None,
        debug_feedback: bool = False,
        resume_enabled: bool = False,
        backend: ClaudeBackend | None = None,
        harness: HarnessDescriptor | None = None,
        pipeline_review: PipelinedTargetReviewConfig | None = None,
        executor_factory=ProcessPoolExecutor,
        prover_worker=_run_single_prover,
        review_worker=_run_review_worker,
        formalization_review_worker=_run_formalization_review_worker,
        formalizer_worker=None,
        preflight_checker=check_review_target,
    ) -> None:
        self.project_name = project_name
        self.project_path = project_path
        self.state_dir = state_dir
        self.stage = stage
        self.iter_dir = iter_dir
        self.iter_meta = iter_meta
        self.iter_num = iter_num
        self.max_parallel = max_parallel
        self.max_objectives = max_objectives
        self.block_on_blocked_deps = block_on_blocked_deps
        self.verbose_logs = verbose_logs
        self.model = model
        self.dashboard_url = dashboard_url
        self.blueprint_url = blueprint_url
        self.debug_feedback = debug_feedback
        self.resume_enabled = resume_enabled
        self.backend = backend or ClaudeBackend()
        self.harness = harness if harness is not None else _default_harness()
        self.pipeline_review = pipeline_review
        self.executor_factory = executor_factory
        self.prover_worker = prover_worker
        self.review_worker = review_worker
        self.formalization_review_worker = formalization_review_worker
        self.formalizer_worker = (
            formalizer_worker if formalizer_worker is not None else prover_worker
        )
        self.preflight_checker = preflight_checker

    def run(self, *, dry_run: bool) -> None:
        progress = self.state_dir / "PROGRESS.md"
        shared = _restrict_progress_to_pending_shared_modules(
            progress_file=progress,
            state_dir=self.state_dir,
            project_path=self.project_path,
        )
        if shared:
            # The dedicated axiom/build gate replaces target Review for this
            # batch. Never start pipelined problem Review/formalization.
            self.pipeline_review = None
        objectives_with_modes = parse_objectives_with_modes(progress, self.project_path)
        sorry_files = [p for p, _ in objectives_with_modes]
        file_modes: dict[str, str | None] = {
            str(p): m for p, m in objectives_with_modes
        }
        if not sorry_files:
            log.warn("No files parsed from PROGRESS.md ## Current Objectives.")
            log.warn("The plan agent must list target files in **bold** or `backticks`.")
            log.warn("Skipping prover iteration.")
            return

        # Drop files whose transitive imports failed the previous lake
        # build. plan_validate already filtered these and hinted the
        # planner; the runner enforces it again so a stale PROGRESS.md
        # replayed via --from prover still gets the filter applied.
        if self.block_on_blocked_deps:
            from ..blocked_deps import (
                build_local_import_graph,
                filter_objectives_for_blocked_deps,
                parse_blocked_files_from_log,
            )
            log_path = self.state_dir / "last_lake_build.log"
            blocked = parse_blocked_files_from_log(
                log_path, project_path=self.project_path,
            )
            if blocked:
                graph = build_local_import_graph(self.project_path)
                sorry_files, dropped = filter_objectives_for_blocked_deps(
                    sorry_files,
                    blocked=blocked,
                    graph=graph,
                    project_path=self.project_path,
                )
                if dropped:
                    log.warn(
                        f"Dropped {len(dropped)} objective(s) whose "
                        f"transitive imports failed the previous lake "
                        f"build — they were already noted for the "
                        f"planner via AUTO_NOTES."
                    )
                if not sorry_files:
                    log.warn(
                        "All objectives are blocked by upstream compile "
                        "errors; skipping prover dispatch."
                    )
                    return

        # Drop objectives that name an existing .lean file with zero open
        # sorries — a prover on them quits immediately with no work (the
        # "all 10 provers quit without doing anything" failure). Scaffold
        # dispatches and new files are exempt. plan_validate already
        # hinted the planner; the runner enforces it again so a stale
        # PROGRESS.md replayed via --from prover still gets filtered.
        from ..sorry_count import filter_noop_objectives

        noop_dropped: list[Path] = []
        pipeline_resume = (
            self.pipeline_review is not None and self.resume_enabled
        )
        if (
            normalize_stage_for_prompt_path(self.stage)
            not in {"autoformalize", "polish"}
            and not pipeline_resume
        ):
            polish_targets = {
                path.resolve()
                for path, mode in objectives_with_modes
                if mode is not None and mode.strip().casefold() == "polish"
            }
            sorry_files, noop_dropped = filter_noop_objectives(
                sorry_files,
                progress_file=progress,
                state_dir=self.state_dir,
                zero_sorry_exemptions=polish_targets,
            )
        if noop_dropped:
            log.warn(
                f"Dropped {len(noop_dropped)} objective(s) naming an "
                f"existing .lean file with zero open sorries (no work to "
                f"do) — already noted for the planner via AUTO_NOTES."
            )
        if not sorry_files:
            log.warn(
                "Every objective was a no-op (zero open sorries); "
                "skipping prover dispatch."
            )
            return

        # A prior prover→Review lane may already have materialized a requested
        # statement redraft. A full target lifecycle resumes those files at
        # formalization Review; the legacy phase-barrier path leaves them in
        # PROGRESS and skips a duplicate formalizer.
        all_review_candidates = list(sorry_files)
        filtered_files, materialized_redrafts = (
            filter_materialized_redrafts_for_dispatch(
                sorry_files,
                state_dir=self.state_dir,
                project_path=self.project_path,
                stage=self.stage,
                enabled=True,
            )
        )
        lifecycle_autoformalize = (
            self.pipeline_review is not None
            and self.pipeline_review.formalization_review_enabled
            and normalize_stage_for_prompt_path(self.stage) == "autoformalize"
        )
        self._materialized_lifecycle_targets: set[str] = set()
        if lifecycle_autoformalize and materialized_redrafts:
            self._materialized_lifecycle_targets = {
                relpath(path, self.project_path)
                for path, _reason in materialized_redrafts
            }
            sorry_files = all_review_candidates
            log.success(
                f"Resuming {len(materialized_redrafts)} already-materialized "
                "redraft(s) directly at per-target formalization Review."
            )
        else:
            sorry_files = filtered_files
            if materialized_redrafts:
                log.success(
                    f"Skipping {len(materialized_redrafts)} already-materialized "
                    "pipelined redraft(s); they remain queued for "
                    "formalization Review."
                )
        if not sorry_files:
            return

        # Hard cap on dispatched provers. plan_validate already warned
        # loudly and queued the deferred list into AUTO_NOTES; we slice
        # here so the dispatcher is deterministic even if plan_validate
        # was bypassed (e.g. --from prover replay of a stale PROGRESS.md
        # that's over the cap).
        if len(sorry_files) > self.max_objectives:
            log.warn(
                f"PROGRESS.md lists {len(sorry_files)} objectives — "
                f"capping dispatch at {self.max_objectives}. The remaining "
                f"{len(sorry_files) - self.max_objectives} files are "
                f"already queued for the next plan agent via AUTO_NOTES."
            )
            sorry_files = sorry_files[: self.max_objectives]

        file_count = len(sorry_files)

        if dry_run:
            for f in sorry_files:
                mode = select_prover_mode_for_target(
                    self.state_dir, self.stage, self.project_path, f,
                    explicit_mode=file_modes.get(str(f)),
                )
                mode_tag = f" (mode: {mode})" if mode else ""
                log.step(f"dry-run Prover: {relpath(f, self.project_path)}{mode_tag}")
            return

        if materialized_redrafts:
            # Their target-scoped reports were written after the preceding
            # iteration's archive and are evidence for the imminent Review.
            log.info("Preserving task_results for pipelined redraft Review")
        else:
            archive_task_results(self.state_dir, self.iter_dir)

        if file_count == 1 and self.pipeline_review is None:
            self._run_single_file(sorry_files[0], mode_name=file_modes.get(str(sorry_files[0])))
            return

        self._run_fanout(sorry_files, file_modes=file_modes)

    def _run_single_file(self, target: Path, mode_name: str | None = None) -> None:
        # Fall back to the stage's default mode when the objective carried no
        # explicit [prover-mode: …] tag (modes replaced the static prompts).
        mode_name = select_prover_mode_for_target(
            self.state_dir, self.stage, self.project_path, target,
            explicit_mode=mode_name,
        )
        rel = relpath(target, self.project_path)
        slug = file_slug(rel)
        log.info(f"Only 1 file ({rel}) — running serial prover")

        prover_log = self.iter_dir / "provers" / slug
        meta_update: dict[str, object] = {
            f"provers.{slug}.file": rel,
            f"provers.{slug}.status": "running",
        }
        if mode_name:
            meta_update[f"provers.{slug}.mode"] = mode_name
        write_meta(self.iter_meta, **meta_update)

        snap_dir = self.iter_dir / "snapshots" / slug
        snapshot_baseline(target, snap_dir)

        mode_content = _load_mode_content(self.state_dir, mode_name)
        base_prompt = build_parallel_prover_prompt(
            self.project_name, self.project_path, self.state_dir, self.stage,
            self.iter_num,
            assigned_rel_lean_path=rel,
            debug_feedback=self.debug_feedback,
            mode_name=mode_name,
            mode_content=mode_content,
        )
        prompt = f"{base_prompt}\nYour assigned file: {rel}"
        image_args = native_problem_image_args(
            project_path=self.project_path,
            target=target,
            harness=self.harness,
        )
        resume_sid = pick_resume_session(
            self.iter_meta, f"provers.{slug}.sessionId",
            enabled=self.resume_enabled, label=f"prover[{slug}]",
            cwd=self.project_path,
            jsonl_fallback=Path(str(prover_log) + ".jsonl"),
        )
        with ProverEnvironment(
            snap_dir=snap_dir,
            prover_jsonl=Path(str(prover_log) + ".jsonl"),
            project_path=self.project_path,
        ):
            ok = build_runner(
                role="prover", model=self.model, descriptor=self.harness,
                backend=self.backend,
            ).run(
                PROVER_CONTINUE if resume_sid else prompt,
                cwd=self.project_path,
                log_base=prover_log, verbose_logs=self.verbose_logs,
                resume_session_id=resume_sid,
                extra_args=image_args,
            )

        persist_session_id(
            self.iter_meta, Path(str(prover_log) + ".jsonl"),
            f"provers.{slug}.sessionId",
        )
        write_meta(
            self.iter_meta,
            **{f"provers.{slug}.status": "done" if ok else "error"},
        )

    def _run_fanout(self, sorry_files: list[Path], *, file_modes: dict[str, str | None] | None = None) -> None:
        file_count = len(sorry_files)
        log.info(
            f"Found {file_count} file(s) — launching parallel provers "
            f"(max {self.max_parallel} concurrent)"
        )

        log.info("Watch progress:")
        if self.dashboard_url:
            log.step(f"Dashboard:       {self.dashboard_url}")
            log.step(f"Iteration view:  {self.dashboard_url}/logs")
        if self.blueprint_url:
            log.step(f"Blueprint:       {self.blueprint_url}")
        log.step(f"tail -f {self.iter_dir}/provers/*.jsonl")
        log.step(f"watch -n10 'ls -lt {self.state_dir}/task_results/'")

        if self.pipeline_review is not None:
            self._run_pipelined_fanout(
                sorry_files, file_modes=file_modes,
            )
            return

        file_modes = file_modes or {}
        futures = {}
        prover_logs: dict[str, Path] = {}
        with ProcessPoolExecutor(
            max_workers=min(self.max_parallel, file_count),
        ) as pool:
            for f in sorry_files:
                rel = relpath(f, self.project_path)
                slug = file_slug(rel)
                prover_log = self.iter_dir / "provers" / slug
                prover_logs[slug] = prover_log

                mode_name = select_prover_mode_for_target(
                    self.state_dir, self.stage, self.project_path, f,
                    explicit_mode=file_modes.get(str(f)),
                )
                mode_content = _load_mode_content(self.state_dir, mode_name)
                base_prompt = build_parallel_prover_prompt(
                    self.project_name, self.project_path, self.state_dir, self.stage,
                    self.iter_num,
                    assigned_rel_lean_path=rel,
                    debug_feedback=self.debug_feedback,
                    mode_name=mode_name,
                    mode_content=mode_content,
                )
                prompt = f"{base_prompt}\nYour assigned file: {rel}"

                snap_dir = self.iter_dir / "snapshots" / slug
                snapshot_baseline(f, snap_dir)

                # Per-slug resume: each parallel prover keeps its own
                # session id under provers.<slug>.sessionId. Files added
                # in this round that weren't part of the prior run have
                # no stored id; pick_resume_session degrades to fresh
                # (or recovers from the slug's JSONL fallback if the
                # prior run crashed mid-prove).
                resume_sid = pick_resume_session(
                    self.iter_meta, f"provers.{slug}.sessionId",
                    enabled=self.resume_enabled, label=f"prover[{slug}]",
                    cwd=self.project_path,
                    jsonl_fallback=Path(str(prover_log) + ".jsonl"),
                )
                if resume_sid:
                    submit_prompt = PROVER_CONTINUE
                else:
                    submit_prompt = prompt

                log.step(f"Starting prover for {rel}")
                meta_update: dict[str, object] = {
                    f"provers.{slug}.file": rel,
                    f"provers.{slug}.status": "running",
                }
                if mode_name:
                    meta_update[f"provers.{slug}.mode"] = mode_name
                write_meta(self.iter_meta, **meta_update)

                future = pool.submit(
                    _run_single_prover,
                    submit_prompt, self.project_path, prover_log,
                    self.verbose_logs, self.model,
                    snap_dir, self.project_path, resume_sid,
                    self.backend, self.harness, f,
                )
                futures[future] = (rel, slug)

            failed = 0
            for future in as_completed(futures):
                rel, slug = futures[future]
                try:
                    ok = future.result()
                except QuotaExhaustedError:
                    raise  # propagate — stop the loop immediately
                except Exception:
                    ok = False
                # Stamp the session id from the prover's JSONL — works
                # whether this was a fresh run or a --resume continuation
                # (Claude reports the same session id back on resume, so
                # the next --resume keeps targeting the same conversation).
                persist_session_id(
                    self.iter_meta,
                    Path(str(prover_logs[slug]) + ".jsonl"),
                    f"provers.{slug}.sessionId",
                )
                status = "done" if ok else "error"
                write_meta(self.iter_meta, **{f"provers.{slug}.status": status})
                if ok:
                    log.success(f"Prover finished: {rel}")
                else:
                    log.error(f"Prover failed: {rel}")
                    failed += 1

        if failed:
            log.warn(f"{failed}/{file_count} prover(s) had errors")
        else:
            log.success(f"All {file_count} prover(s) finished")

        results_dir = self.state_dir / "task_results"
        result_count = len(list(results_dir.glob("*.md"))) if results_dir.exists() else 0
        log.info(f"Task result files: {result_count}/{file_count}")

        self._emit_round_end(file_count, failed)

    def _run_pipelined_fanout(
        self,
        sorry_files: list[Path],
        *,
        file_modes: dict[str, str | None] | None = None,
    ) -> None:
        """Share one bounded pool between prover, Review, and redraft work."""
        config = self.pipeline_review
        if config is None:
            raise RuntimeError("pipelined fanout requires Review configuration")

        file_modes = file_modes or {}
        file_count = len(sorry_files)
        workers = max(1, min(self.max_parallel, file_count))
        review_jobs = max(1, min(config.requested_jobs, workers))
        max_attempts = max(1, int(config.max_attempts))
        full_pipeline = bool(config.formalization_review_enabled)
        native_answer_required = native_problem_only_enabled(self.project_path)
        initial_formalization = (
            normalize_stage_for_prompt_path(self.stage) == "autoformalize"
        )
        if initial_formalization and not full_pipeline:
            raise RuntimeError(
                "autoformalize target lifecycle requires immediate "
                "formalization Review"
            )
        if initial_formalization and native_answer_required:
            # Validate every controller-certified prior-result dependency before
            # launching any model.  In particular, A6 must not race or silently
            # inline an uncertified A4/A5 conclusion when its frozen context is
            # absent, stale, or bound to another validation lineage.
            for target in sorry_files:
                resolve_native_formalizer_source_contract(
                    project_path=self.project_path,
                    target=target,
                )
        formalization_max_attempts = max(
            1, int(config.formalization_review_max_attempts),
        )
        formalization_max_iterations = max(
            1, int(config.formalization_review_max_iterations),
        )
        proof_max_iterations = max(1, int(config.proof_review_max_iterations))
        prior_state = load_proof_review_state(self.state_dir)
        prior_targets = prior_state.get("targets", {})
        if not isinstance(prior_targets, dict):
            prior_targets = {}
        prior_formalization_state = (
            load_formalization_review_state(self.state_dir) or {}
        )
        prior_formalization_targets = prior_formalization_state.get("targets", {})
        if not isinstance(prior_formalization_targets, dict):
            prior_formalization_targets = {}

        pending_provers: deque[tuple[Path, int]] = deque()
        pending_initial_formalizers: deque[tuple[Path, int]] = deque()
        resumed_completed: list[tuple[Path, str, str, int]] = []
        resumed_formalized: list[tuple[Path, str, str, int]] = []
        proof_cycles: dict[str, int] = {}
        resumed_terminal_proofs: list[tuple[Path, str, str, int]] = []
        resumed_terminal_formalizations: set[str] = set()
        resumed_redrafts: list[tuple[Path, str, str, int, dict, str]] = []
        restored_formal_events: list[tuple[Path, str, int, str]] = []

        formalization_cycles: dict[str, int] = {}
        shadow_proof_attempts: dict[str, int] = {}
        shadow_proof_records: dict[str, dict] = {}
        shadow_formalization_reviews: dict[str, int] = {}
        shadow_formalization_records: dict[str, dict] = {}
        for target in sorry_files:
            rel = relpath(target, self.project_path)
            slug = file_slug(rel)
            prior_proof = prior_targets.get(rel)
            prior_proof = prior_proof if isinstance(prior_proof, dict) else {}
            shadow_proof_attempts[rel] = int(prior_proof.get("attempts") or 0)
            shadow_proof_records[rel] = dict(prior_proof)
            prior_formalization = prior_formalization_targets.get(rel)
            prior_formalization = (
                prior_formalization
                if isinstance(prior_formalization, dict) else {}
            )
            if native_answer_required:
                answer_binding, answer_submission_error = (
                    validate_native_answer_submission_current(
                        project_path=self.project_path,
                        target=target,
                    )
                )
                answer_submission_valid = answer_binding is not None
            else:
                answer_binding = None
                answer_submission_error = ""
                answer_submission_valid = True
            write_meta(self.iter_meta, **{
                f"pipelineFormalizers.{slug}.answerSubmissionValid": (
                    answer_submission_valid
                ),
                f"pipelineFormalizers.{slug}.answerSubmissionError": (
                    answer_submission_error
                ),
            })
            if self.resume_enabled:
                restored_proof_cycle = max(
                    _pipeline_cycle(
                        read_meta(
                            self.iter_meta, f"provers.{slug}.cycle",
                        )
                    ),
                    _pipeline_cycle(
                        read_meta(
                            self.iter_meta, f"pipelineReviews.{slug}.cycle",
                        )
                    ),
                    _latest_pipeline_event_cycle(
                        prior_proof,
                        history_key="history",
                        iter_num=self.iter_num,
                        rel=rel,
                        kind="proof",
                    ),
                )
                restored_formalization_cycle = max(
                    _pipeline_cycle(
                        read_meta(
                            self.iter_meta, f"pipelineFormalizers.{slug}.cycle",
                        )
                    ),
                    _pipeline_cycle(
                        read_meta(
                            self.iter_meta,
                            f"pipelineFormalizationReviews.{slug}.cycle",
                        )
                    ),
                    _latest_pipeline_event_cycle(
                        prior_formalization,
                        history_key="review_events",
                        iter_num=self.iter_num,
                        rel=rel,
                        kind="formalization",
                    ),
                )
            else:
                restored_proof_cycle = 0
                restored_formalization_cycle = 0
            proof_cycles[rel] = max(
                0 if initial_formalization else 1,
                restored_proof_cycle,
            )
            formalization_cycles[rel] = max(
                1 if initial_formalization else 0,
                restored_formalization_cycle,
            )
            shadow_formalization_reviews[rel] = int(
                prior_formalization.get("reviews") or 0
            )
            shadow_formalization_records[rel] = dict(prior_formalization)
            if initial_formalization:
                prior_status = (
                    read_meta(
                        self.iter_meta,
                        f"pipelineFormalizers.{slug}.status",
                    )
                    if self.resume_enabled else None
                )
                legacy_status = (
                    read_meta(self.iter_meta, f"provers.{slug}.status")
                    if self.resume_enabled else None
                )
                legacy_baseline = _target_sha256(
                    self.iter_dir / "snapshots" / slug / "baseline.lean"
                )
                legacy_materialized = bool(
                    answer_submission_valid
                    and legacy_status == "done"
                    and legacy_baseline
                    and _target_sha256(target) != legacy_baseline
                    and _task_result_fingerprints(self.state_dir, rel)
                )
                formal_status = str(
                    prior_formalization.get("status") or ""
                )
                proof_status = str(prior_proof.get("status") or "")
                formal_event_cycle = _latest_pipeline_event_cycle(
                    prior_formalization,
                    history_key="review_events",
                    iter_num=self.iter_num,
                    rel=rel,
                    kind="formalization",
                )
                proof_event_cycle = _latest_pipeline_event_cycle(
                    prior_proof,
                    history_key="history",
                    iter_num=self.iter_num,
                    rel=rel,
                    kind="proof",
                )
                formal_event_decision = _pipeline_event_field(
                    prior_formalization,
                    history_key="review_events",
                    iter_num=self.iter_num,
                    rel=rel,
                    kind="formalization",
                    cycle=formal_event_cycle,
                    field="decision",
                )
                if (
                    self.resume_enabled
                    and proof_event_cycle
                    and proof_status == "needs_redraft"
                ):
                    proof_event_id = (
                        f"pipeline:{self.iter_num}:{rel}:proof:"
                        f"{proof_event_cycle}"
                    )
                    if (
                        formal_status == "passed"
                        and prior_formalization.get("last_reopen_event_id")
                        == proof_event_id
                    ):
                        # The redraft passed its gate, but the process died
                        # before that gate reset the older proof decision.
                        reset_proof_review_targets_after_redraft(
                            state_dir=self.state_dir,
                            targets=(rel,),
                            iter_num=self.iter_num,
                            formalization_records={rel: prior_formalization},
                        )
                        refreshed_proof = load_proof_review_state(
                            self.state_dir
                        ).get("targets", {}).get(rel, {})
                        prior_proof = (
                            refreshed_proof
                            if isinstance(refreshed_proof, dict) else {}
                        )
                        proof_status = str(prior_proof.get("status") or "")
                        shadow_proof_records[rel] = dict(prior_proof)
                        shadow_proof_attempts[rel] = int(
                            prior_proof.get("attempts") or 0
                        )
                    elif formal_status == "passed":
                        # The proof event is durable but its formalization
                        # reopen was the next write. Replay that idempotently
                        # instead of invoking the proof Reviewer again.
                        reopen_formalization_targets(
                            state_dir=self.state_dir,
                            project_path=self.project_path,
                            progress_file=self.state_dir / "PROGRESS.md",
                            redrafts={
                                rel: {
                                    "reason": prior_proof.get("reason"),
                                    "redraft_kind": prior_proof.get(
                                        "redraft_kind"
                                    ),
                                    "pipeline_event_id": proof_event_id,
                                }
                            },
                            iter_num=self.iter_num,
                            max_iterations=formalization_max_iterations,
                            route_progress=False,
                            enforce_budget=True,
                        )
                        refreshed_formal = (
                            load_formalization_review_state(self.state_dir)
                            or {}
                        ).get("targets", {}).get(rel, {})
                        prior_formalization = (
                            refreshed_formal
                            if isinstance(refreshed_formal, dict) else {}
                        )
                        formal_status = str(
                            prior_formalization.get("status") or ""
                        )
                        shadow_formalization_records[rel] = dict(
                            prior_formalization
                        )
                        shadow_formalization_reviews[rel] = int(
                            prior_formalization.get("reviews") or 0
                        )
                if (
                    answer_submission_valid
                    and self.resume_enabled
                    and proof_event_cycle
                    and proof_status in {
                        "solved",
                        "blocked_infrastructure",
                        "proof_review_exhausted",
                    }
                ):
                    if formal_event_cycle:
                        restored_formal_events.append((
                            target, rel, formal_event_cycle, formal_event_decision,
                        ))
                    resumed_terminal_proofs.append((
                        target, rel, slug, proof_event_cycle,
                    ))
                    continue
                if (
                    self.resume_enabled
                    and formal_event_cycle
                    and formal_status == "review_exhausted"
                ):
                    restored_formal_events.append((
                        target, rel, formal_event_cycle, formal_event_decision,
                    ))
                    resumed_terminal_formalizations.add(rel)
                    continue
                if (
                    answer_submission_valid
                    and self.resume_enabled
                    and formal_event_cycle
                    and formal_status == "passed"
                ):
                    restored_formal_events.append((
                        target, rel, formal_event_cycle, formal_event_decision,
                    ))
                    prover_meta_cycle = _pipeline_cycle(
                        read_meta(self.iter_meta, f"provers.{slug}.cycle")
                    )
                    if proof_event_cycle and proof_status == "retry":
                        if prover_meta_cycle > proof_event_cycle:
                            proof_cycles[rel] = max(
                                proof_cycles[rel], prover_meta_cycle,
                            )
                            if legacy_status == "done":
                                resumed_completed.append((
                                    target, rel, slug, prover_meta_cycle,
                                ))
                            else:
                                pending_provers.append((
                                    target, prover_meta_cycle,
                                ))
                        else:
                            next_cycle = proof_event_cycle + 1
                            proof_cycles[rel] = max(
                                proof_cycles[rel], next_cycle,
                            )
                            pending_provers.append((target, next_cycle))
                    elif (
                        proof_event_cycle == 0
                        and file_open_sorry_count(target) == 0
                    ):
                        resumed_completed.append((
                            target, rel, slug, max(1, proof_cycles[rel]),
                        ))
                    elif legacy_status == "done":
                        resumed_completed.append((
                            target, rel, slug, max(1, proof_cycles[rel]),
                        ))
                    else:
                        pending_provers.append((
                            target, max(1, proof_cycles[rel]),
                        ))
                    continue
                if formal_status == "retry" and not formal_event_cycle:
                    # A durable retry from an earlier outer iteration is not a
                    # fresh target. Preserve its controller-owned Review
                    # hand-off even though this process is not resuming the
                    # prior iteration session.
                    next_cycle = max(
                        formalization_cycles[rel],
                        _pipeline_cycle(
                            prior_formalization.get("reviews")
                        ) + 1,
                        1,
                    )
                    formalization_cycles[rel] = next_cycle
                    if prior_formalization.get("reopened_by") == "proof_review":
                        handoff = _proof_formalization_redraft_handoff(
                            prior_proof,
                            prior_formalization,
                            project_path=self.project_path,
                            target=target,
                            target_rel=rel,
                        )
                        handoff_label = "proof Review"
                    else:
                        current_digest = _target_sha256(target)
                        try:
                            expected_source_contract = (
                                resolve_target_review_source_contract(
                                    project_path=self.project_path,
                                    target=target,
                                    preflight=None,
                                )
                            )
                        except ProblemOnlyReviewContractError:
                            expected_source_contract = None
                        handoff = _durable_formalization_retry_handoff(
                            prior_formalization,
                            candidate_sha256=current_digest,
                            expected_source_contract=expected_source_contract,
                            target_rel=rel,
                        )
                        handoff_label = "formalization Review"
                    resumed_redrafts.append((
                        target, rel, slug, next_cycle,
                        handoff, handoff_label,
                    ))
                    continue
                if (
                    self.resume_enabled
                    and formal_event_cycle
                    and formal_status == "retry"
                ):
                    restored_formal_events.append((
                        target, rel, formal_event_cycle, formal_event_decision,
                    ))
                    formalizer_meta_cycle = _pipeline_cycle(
                        read_meta(
                            self.iter_meta,
                            f"pipelineFormalizers.{slug}.cycle",
                        )
                    )
                    if (
                        answer_submission_valid
                        and prior_status == "materialized"
                        and formalizer_meta_cycle > formal_event_cycle
                    ):
                        formalization_cycles[rel] = formalizer_meta_cycle
                        resumed_formalized.append((
                            target, rel, slug, formalizer_meta_cycle,
                        ))
                    else:
                        next_cycle = (
                            formalizer_meta_cycle
                            if formalizer_meta_cycle > formal_event_cycle
                            else formal_event_cycle + 1
                        )
                        formalization_cycles[rel] = next_cycle
                        if prior_formalization.get("reopened_by") == "proof_review":
                            handoff = _proof_formalization_redraft_handoff(
                                prior_proof,
                                prior_formalization,
                                project_path=self.project_path,
                                target=target,
                                target_rel=rel,
                            )
                            handoff_label = "proof Review"
                        else:
                            try:
                                expected_source_contract = (
                                    resolve_target_review_source_contract(
                                        project_path=self.project_path,
                                        target=target,
                                        preflight=None,
                                    )
                                )
                            except ProblemOnlyReviewContractError:
                                expected_source_contract = None
                            handoff = build_repair_task(
                                prior_formalization,
                                review_kind="formalization",
                                worker_stage="formalization",
                                candidate_sha256=_target_sha256(target),
                                discard_stale_record=True,
                                expected_source_contract=(
                                    expected_source_contract
                                ),
                                target_rel=rel,
                            )
                            handoff_label = "formalization Review"
                        resumed_redrafts.append((
                            target, rel, slug, next_cycle,
                            handoff, handoff_label,
                        ))
                    continue
                if (
                    answer_submission_valid
                    and (
                    rel in getattr(
                        self, "_materialized_lifecycle_targets", set()
                    )
                    or prior_status == "materialized"
                    or legacy_materialized
                    )
                ):
                    resumed_formalized.append((
                        target,
                        rel,
                        slug,
                        formalization_cycles[rel],
                    ))
                else:
                    pending_initial_formalizers.append((
                        target, formalization_cycles[rel],
                    ))
                continue
            prior_status = (
                read_meta(self.iter_meta, f"provers.{slug}.status")
                if self.resume_enabled else None
            )
            if prior_status == "done":
                resumed_completed.append((
                    target, rel, slug, proof_cycles[rel],
                ))
            else:
                pending_provers.append((target, proof_cycles[rel]))
        review_queue: list[
            tuple[float, int, Path, str, str, int, int]
        ] = []
        formalizer_queue: deque[
            tuple[Path, str, str, int, dict, str]
        ] = deque(resumed_redrafts)
        formalization_review_queue: list[
            tuple[float, int, Path, str, str, int, int]
        ] = []
        sequence = count()
        futures: dict[object, _PipelineWork] = {}
        outcomes: dict[str, TargetReviewOutcome] = {}
        preflight_rows: dict[str, dict] = {}
        formalizer_results: dict[str, dict] = {}
        formalizer_history: dict[str, list[dict]] = {}
        gate_events: list[dict] = []
        pending_formalization: set[str] = set()
        settled_targets: set[str] = set()
        unresolved: dict[str, str] = {}
        review_rounds: dict[int, dict[str, int]] = {}
        proof_review_validation_feedback: dict[tuple[str, int], str] = {}
        formalization_review_validation_feedback: dict[tuple[str, int], str] = {}
        settled_targets.update(resumed_terminal_formalizations)
        for target, rel, cycle, decision in restored_formal_events:
            gate_events.append({
                "kind": "formalization",
                "event_id": (
                    f"pipeline:{self.iter_num}:{rel}:formalization:{cycle}"
                ),
                "target": target,
                "rel": rel,
                "cycle": cycle,
                "milestone": {"target": {"file": rel}},
                "source_contract": None,
                "restored_decision": (
                    decision if decision in {"passed", "failed"} else "failed"
                ),
            })
        formalization_review_rounds: dict[
            tuple[int, int], dict[str, int]
        ] = {}
        active_reviews = 0
        failed = 0
        started = time.monotonic()
        target_rels = sorted(relpath(path, self.project_path) for path in sorry_files)

        if initial_formalization:
            log.info(
                "Independent target lifecycle enabled: each target starts "
                "with its own formalizer, then advances immediately through "
                "formalization Review, prover, and proof Review; combined "
                f"concurrency is capped at {workers}."
            )
        else:
            log.info(
                "Pipelined target Review enabled: each completed prover is "
                "reviewed immediately, and needs_redraft starts that target's "
                "formalizer immediately; combined concurrency "
                f"is capped at {workers}."
            )
        if full_pipeline:
            log.info(
                "Full target loop enabled: each materialized redraft gets an "
                "immediate formalization Review and a passing target is "
                "re-enqueued to prover without a phase barrier."
            )
        write_meta(self.iter_meta, **{
            "prover.pipelineReviewEnabled": True,
            "prover.pipelineImmediateRedraftEnabled": True,
            "prover.pipelineFormalizationReviewEnabled": full_pipeline,
            "prover.pipelineStartsAt": (
                "formalizer" if initial_formalization else "prover"
            ),
            "prover.pipelineReviewMaxCombined": workers,
            "prover.pipelineReviewMaxReviewers": review_jobs,
        })
        write_pipelined_review_report(
            iter_dir=self.iter_dir,
            report={
                "iteration": self.iter_num,
                "complete": False,
                "status": "running",
                "pipeline_mode": (
                    "target_lifecycle" if full_pipeline else "proof_review"
                ),
                "starts_at": (
                    "formalizer" if initial_formalization else "prover"
                ),
                "target_files": target_rels,
                "targets": file_count,
                "reviewed": 0,
                "unresolved": target_rels,
                "gate_events_applied": False,
                "formalization_reviews": {"reviewed": 0, "unresolved": []},
                "formalizers": {"requested": 0, "materialized": 0, "failed": 0},
            },
        )

        def enqueue_review(
            target: Path,
            rel: str,
            slug: str,
            attempt: int,
            cycle: int,
            *,
            delay: float = 0.0,
        ) -> None:
            heapq.heappush(
                review_queue,
                (
                    time.monotonic() + max(0.0, delay),
                    next(sequence),
                    target,
                    rel,
                    slug,
                    attempt,
                    cycle,
                ),
            )

        def run_preflight(target: Path, rel: str) -> dict:
            try:
                return self.preflight_checker(
                    project_path=self.project_path,
                    target=target,
                    timeout_sec=config.preflight_timeout_sec,
                )
            except Exception as exc:
                reason = (
                    f"{type(exc).__name__}: {exc}"
                )[:MAX_NUMERIC_REPORTING_REASON_LENGTH]
                return {
                    "file": rel,
                    "status": "error",
                    "compiles": False,
                    "returncode": None,
                    "sorry_count": None,
                    "duration_secs": 0.0,
                    "diagnostics": reason,
                    "numeric_reporting": {
                        "active": False,
                        "status": "error",
                        "reason": reason,
                    },
                }

        if resumed_terminal_proofs:
            log.info(
                f"Resume detected {len(resumed_terminal_proofs)} durable "
                "proof Review outcome(s); restoring them without a model call."
            )
            for target, rel, slug, cycle in resumed_terminal_proofs:
                preflight = run_preflight(target, rel)
                preflight_rows[rel] = preflight
                try:
                    source_contract = resolve_target_review_source_contract(
                        project_path=self.project_path,
                        target=target,
                        preflight=preflight,
                    )
                    attempt = _pipeline_cycle(
                        read_meta(
                            self.iter_meta,
                            f"pipelineReviews.{slug}.attempt",
                        )
                    ) or 1
                    output_dir = (
                        self.iter_dir / "review-targets" / slug
                        / f"cycle-{cycle}" / f"attempt-{attempt}"
                    )
                    milestone, error = load_target_milestone(
                        output_dir / "milestones.jsonl",
                        rel,
                        source_contract,
                    )
                    if error or milestone is None:
                        raise ValueError(
                            error or "durable proof Review milestone is missing"
                        )
                except Exception as exc:
                    unresolved[rel] = (
                        "durable proof Review restore failed: "
                        f"{type(exc).__name__}: {exc}"
                    )
                    continue
                outcome = TargetReviewOutcome(
                    rel=rel,
                    attempt=attempt,
                    runner_ok=True,
                    milestone=milestone,
                )
                outcomes[rel] = outcome
                settled_targets.add(rel)
                gate_events.append({
                    "kind": "proof",
                    "event_id": f"pipeline:{self.iter_num}:{rel}:proof:{cycle}",
                    "target": target,
                    "rel": rel,
                    "cycle": cycle,
                    "milestone": milestone,
                    "source_contract": source_contract,
                })
                stats = review_rounds.setdefault(
                    attempt,
                    {"attempt": attempt, "submitted": 0, "completed": 0, "failed": 0},
                )
                stats["completed"] += 1

        if resumed_completed:
            preflight_jobs = min(review_jobs, len(resumed_completed))
            log.info(
                f"Resume detected {len(resumed_completed)} completed prover "
                "lane(s); skipping re-proving and preparing their Reviews."
            )
            with ThreadPoolExecutor(max_workers=preflight_jobs) as check_pool:
                checks = {
                    check_pool.submit(run_preflight, target, rel): (
                        target, rel, slug, cycle,
                    )
                    for target, rel, slug, cycle in resumed_completed
                }
                for future in as_completed(checks):
                    target, rel, slug, cycle = checks[future]
                    preflight_rows[rel] = future.result()
                    enqueue_review(target, rel, slug, 1, cycle)

        def submit_prover(pool, target: Path, cycle: int) -> None:
            rel = relpath(target, self.project_path)
            slug = file_slug(rel)
            prover_log = self.iter_dir / "provers" / slug
            dispatch_stage = "prover" if initial_formalization else self.stage
            mode_name = select_prover_mode_for_target(
                self.state_dir,
                dispatch_stage,
                self.project_path,
                target,
                explicit_mode=(
                    None if initial_formalization else file_modes.get(str(target))
                ),
            )
            mode_content = _load_mode_content(self.state_dir, mode_name)
            base_prompt = build_parallel_prover_prompt(
                self.project_name,
                self.project_path,
                self.state_dir,
                dispatch_stage,
                self.iter_num,
                assigned_rel_lean_path=rel,
                debug_feedback=self.debug_feedback,
                mode_name=mode_name,
                mode_content=mode_content,
            )
            if initial_formalization:
                base_prompt = f"""{base_prompt}

## Target-lifecycle proof hand-off

The target's formalization Review has passed. The global PROGRESS stage and
any per-objective `chemistry-formalize` tag are stale routing metadata for
this independent lane; do not follow their statement-only or `by sorry`
instructions. This lane is now in the `prover` stage with active mode
`{mode_name or 'chemistry'}`.

Keep the accepted statement/model fixed and replace every remaining proof hole
in the assigned target with a kernel-checked proof. Do not leave `sorry`,
`admit`, or an equivalent placeholder.
"""
            repair_task = build_repair_task(
                shadow_proof_records.get(rel),
                review_kind="proof",
                worker_stage="proof",
                candidate_sha256=_target_sha256(target),
                preflight=preflight_rows.get(rel),
                discard_stale_record=self.resume_enabled,
            )
            if repair_task:
                base_prompt = f"""{base_prompt}

## Controller-sanitized proof Review repair hand-off

This structure contains only controller-validated status codes, check IDs,
candidate hashes, and deterministic preflight metadata. It contains no expected
answer or free-form Reviewer evidence. Address every listed failed check and
required action while preserving the accepted statement.

{json.dumps(repair_task, ensure_ascii=False, indent=2)}
"""
            prompt = f"{base_prompt}\nYour assigned file: {rel}"
            snap_dir = self.iter_dir / "snapshots" / slug
            snapshot_baseline(target, snap_dir)
            resume_sid = pick_resume_session(
                self.iter_meta,
                f"provers.{slug}.sessionId",
                enabled=self.resume_enabled and cycle == 1,
                label=f"prover[{slug}]",
                cwd=self.project_path,
                jsonl_fallback=Path(str(prover_log) + ".jsonl"),
            )
            submit_prompt = PROVER_CONTINUE if resume_sid else prompt
            meta_update: dict[str, object] = {
                f"provers.{slug}.file": rel,
                f"provers.{slug}.status": "running",
                f"provers.{slug}.cycle": cycle,
            }
            if mode_name:
                meta_update[f"provers.{slug}.mode"] = mode_name
            write_meta(self.iter_meta, **meta_update)
            cycle_label = f" (cycle {cycle})" if cycle > 1 else ""
            log.step(f"Starting prover for {rel}{cycle_label}")
            future = pool.submit(
                self.prover_worker,
                submit_prompt,
                self.project_path,
                prover_log,
                self.verbose_logs,
                self.model,
                snap_dir,
                self.project_path,
                resume_sid,
                self.backend,
                self.harness, target,
            )
            futures[future] = _PipelineWork(
                kind="prover", target=target, rel=rel, slug=slug, cycle=cycle,
            )

        def submit_review(
            pool,
            target: Path,
            rel: str,
            slug: str,
            attempt: int,
            cycle: int,
        ) -> None:
            nonlocal active_reviews
            output_dir = (
                self.iter_dir / "review-targets" / slug
                / f"cycle-{cycle}" / f"attempt-{attempt}"
            )
            source_contract = None
            try:
                source_contract = resolve_target_review_source_contract(
                    project_path=self.project_path,
                    target=target,
                    preflight=preflight_rows.get(rel, {}),
                )
                prompt = build_target_review_prompt(
                    project_path=self.project_path,
                    state_dir=self.state_dir,
                    iter_dir=self.iter_dir,
                    iter_num=self.iter_num,
                    target=target,
                    output_dir=output_dir,
                    preflight=preflight_rows.get(rel, {}),
                    prior_gate_record=shadow_proof_records.get(rel) or None,
                    source_contract=source_contract,
                    retry_validation_error=proof_review_validation_feedback.get(
                        (rel, cycle), ""
                    ),
                )
                spec = TargetReviewSpec(
                    rel=rel,
                    prompt=prompt,
                    output_dir=str(output_dir),
                    log_base=str(output_dir / "agent"),
                    attempt=attempt,
                    source_contract=source_contract,
                    final_attempt=attempt == max_attempts,
                )
                future = pool.submit(
                    self.review_worker,
                    spec,
                    project_path=self.project_path,
                    verbose_logs=self.verbose_logs,
                    model=self.model,
                    backend=self.backend,
                    harness=config.harness or self.harness,
                )
            except ProblemOnlyReviewContractError as exc:
                future = Future()
                future.set_result(TargetReviewOutcome(
                    rel=rel,
                    attempt=attempt,
                    runner_ok=False,
                    milestone=None,
                    error=f"{type(exc).__name__}: {exc}",
                ))
            futures[future] = _PipelineWork(
                kind="review",
                target=target,
                rel=rel,
                slug=slug,
                attempt=attempt,
                cycle=cycle,
                source_contract=source_contract,
            )
            active_reviews += 1
            stats = review_rounds.setdefault(
                attempt,
                {"attempt": attempt, "submitted": 0, "completed": 0, "failed": 0},
            )
            stats["submitted"] += 1
            write_meta(self.iter_meta, **{
                f"pipelineReviews.{slug}.status": "running",
                f"pipelineReviews.{slug}.attempt": attempt,
                f"pipelineReviews.{slug}.cycle": cycle,
            })
            cycle_label = f" (cycle {cycle})" if cycle > 1 else ""
            log.step(f"Starting immediate proof Review for {rel}{cycle_label}")

        def submit_initial_formalizer(
            pool,
            target: Path,
            cycle: int,
        ) -> None:
            rel = relpath(target, self.project_path)
            slug = file_slug(rel)
            formalizer_log = self.iter_dir / "formalizers" / slug
            snap_dir = self.iter_dir / "formalizer-snapshots" / slug
            mode_name = select_prover_mode_for_target(
                self.state_dir,
                self.stage,
                self.project_path,
                target,
                explicit_mode=file_modes.get(str(target)),
            )
            mode_content = _load_mode_content(self.state_dir, mode_name)
            base_prompt = build_parallel_prover_prompt(
                self.project_name,
                self.project_path,
                self.state_dir,
                self.stage,
                self.iter_num,
                assigned_rel_lean_path=rel,
                debug_feedback=self.debug_feedback,
                mode_name=mode_name,
                mode_content=mode_content,
            )
            semantic_block = _native_formalizer_semantic_dag_block(
                project_path=self.project_path, target=target,
            )
            prompt = (
                f"{base_prompt}\n\n{semantic_block}\nYour assigned file: {rel}"
            )
            baseline_sha256 = _target_sha256(target)
            baseline_results = _task_result_fingerprints(self.state_dir, rel)
            resume_sid = pick_resume_session(
                self.iter_meta,
                f"pipelineFormalizers.{slug}.sessionId",
                enabled=self.resume_enabled and cycle == 1,
                label=f"formalizer[{slug}]",
                cwd=self.project_path,
                jsonl_fallback=Path(str(formalizer_log) + ".jsonl"),
            )
            legacy_resume = False
            if not resume_sid and self.resume_enabled and cycle == 1:
                resume_sid = pick_resume_session(
                    self.iter_meta,
                    f"provers.{slug}.sessionId",
                    enabled=True,
                    label=f"legacy-formalizer[{slug}]",
                    cwd=self.project_path,
                    jsonl_fallback=(
                        self.iter_dir / "provers" / f"{slug}.jsonl"
                    ),
                )
                legacy_resume = bool(resume_sid)
            if resume_sid:
                stored_baseline = str(
                    read_meta(
                        self.iter_meta,
                        f"pipelineFormalizers.{slug}.baselineSha256",
                    ) or ""
                )
                baseline_candidates = (
                    stored_baseline,
                    _target_sha256(snap_dir / "baseline.lean"),
                    _target_sha256(
                        self.iter_dir / "snapshots" / slug / "baseline.lean"
                    ),
                )
                baseline_sha256 = next((
                    digest for digest in baseline_candidates if len(digest) == 64
                ), baseline_sha256)
                baseline_results = {}
                snap_dir.mkdir(parents=True, exist_ok=True)
            else:
                snapshot_baseline(target, snap_dir)
            submit_prompt = (
                f"{PROVER_CONTINUE}\n\n{semantic_block}"
                if resume_sid
                else prompt
            )
            meta_update: dict[str, object] = {
                f"pipelineFormalizers.{slug}.file": rel,
                f"pipelineFormalizers.{slug}.status": "running",
                f"pipelineFormalizers.{slug}.cycle": cycle,
                f"pipelineFormalizers.{slug}.origin": (
                    "legacy-autoformalize-resume"
                    if legacy_resume else "initial"
                ),
                f"pipelineFormalizers.{slug}.baselineSha256": (
                    baseline_sha256
                ),
            }
            if mode_name:
                meta_update[f"pipelineFormalizers.{slug}.mode"] = mode_name
            write_meta(self.iter_meta, **meta_update)
            log.step(f"Starting target formalizer for {rel}")
            future = pool.submit(
                self.formalizer_worker,
                submit_prompt,
                self.project_path,
                formalizer_log,
                self.verbose_logs,
                self.model,
                snap_dir,
                self.project_path,
                resume_sid,
                self.backend,
                config.formalizer_harness or self.harness, target,
            )
            futures[future] = _PipelineWork(
                kind="initial_formalizer",
                target=target,
                rel=rel,
                slug=slug,
                attempt=cycle,
                cycle=cycle,
                baseline_sha256=baseline_sha256,
                result_fingerprints=tuple(sorted(baseline_results.items())),
            )

        def submit_formalizer(
            pool,
            target: Path,
            rel: str,
            slug: str,
            cycle: int,
            certificate: dict,
            handoff_label: str,
        ) -> None:
            formalizer_log = self.iter_dir / "formalizers" / slug
            snap_dir = self.iter_dir / "formalizer-snapshots" / slug
            baseline_sha256 = _target_sha256(target)
            baseline_results = _task_result_fingerprints(self.state_dir, rel)
            snapshot_baseline(target, snap_dir)
            try:
                prompt = build_immediate_redraft_prompt(
                    project_name=self.project_name,
                    project_path=self.project_path,
                    state_dir=self.state_dir,
                    iter_num=self.iter_num,
                    target=target,
                    review_certificate=certificate,
                    debug_feedback=self.debug_feedback,
                    handoff_label=handoff_label,
                )
            except _ImmediateRedraftPromptError as exc:
                # A controller-owned hand-off that cannot be represented
                # without dropping its required bindings is a target-scoped
                # infrastructure failure. Surface it through the normal
                # formalizer outcome path instead of crashing every lane.
                future = Future()
                future.set_exception(ValueError(
                    f"safe immediate redraft prompt rejection: {exc}"
                ))
                futures[future] = _PipelineWork(
                    kind=(
                        "answer_submission_repair"
                        if handoff_label == _ANSWER_SUBMISSION_REPAIR_LABEL
                        else "formalizer"
                    ),
                    target=target,
                    rel=rel,
                    slug=slug,
                    attempt=cycle,
                    cycle=cycle,
                    baseline_sha256=baseline_sha256,
                    result_fingerprints=tuple(sorted(baseline_results.items())),
                )
                return
            resume_sid = None
            submit_prompt = prompt
            write_meta(self.iter_meta, **{
                f"pipelineFormalizers.{slug}.file": rel,
                f"pipelineFormalizers.{slug}.status": "running",
                f"pipelineFormalizers.{slug}.reviewAttempt": cycle,
                f"pipelineFormalizers.{slug}.cycle": cycle,
                f"pipelineFormalizers.{slug}.origin": "review-redraft",
            })
            cycle_label = f" (cycle {cycle})" if cycle > 1 else ""
            log.step(f"Starting immediate formalizer for {rel}{cycle_label}")
            future = pool.submit(
                self.formalizer_worker,
                submit_prompt,
                self.project_path,
                formalizer_log,
                self.verbose_logs,
                self.model,
                snap_dir,
                self.project_path,
                resume_sid,
                self.backend,
                config.formalizer_harness or self.harness, target,
            )
            futures[future] = _PipelineWork(
                kind=(
                    "answer_submission_repair"
                    if handoff_label == _ANSWER_SUBMISSION_REPAIR_LABEL
                    else "formalizer"
                ),
                target=target,
                rel=rel,
                slug=slug,
                attempt=cycle,
                cycle=cycle,
                baseline_sha256=baseline_sha256,
                result_fingerprints=tuple(sorted(baseline_results.items())),
            )

        def enqueue_formalization_review(
            target: Path,
            rel: str,
            slug: str,
            cycle: int,
            attempt: int,
            *,
            delay: float = 0.0,
        ) -> None:
            heapq.heappush(
                formalization_review_queue,
                (
                    time.monotonic() + max(0.0, delay),
                    next(sequence),
                    target,
                    rel,
                    slug,
                    cycle,
                    attempt,
                ),
            )

        def submit_formalization_review(
            pool,
            target: Path,
            rel: str,
            slug: str,
            cycle: int,
            attempt: int,
        ) -> None:
            nonlocal active_reviews
            output_dir = (
                self.iter_dir / "formalization-review-targets" / slug
                / f"cycle-{cycle}" / f"attempt-{attempt}"
            )
            source_contract = None
            try:
                source_contract = resolve_target_review_source_contract(
                    project_path=self.project_path,
                    target=target,
                    preflight=preflight_rows.get(rel, {}),
                )
                prompt = build_target_formalization_review_prompt(
                    project_path=self.project_path,
                    state_dir=self.state_dir,
                    iter_dir=self.iter_dir,
                    iter_num=self.iter_num,
                    target=target,
                    output_dir=output_dir,
                    preflight=preflight_rows.get(rel, {}),
                    prior_gate_record=shadow_formalization_records.get(rel),
                    source_contract=source_contract,
                    retry_validation_error=(
                        formalization_review_validation_feedback.get(
                            (rel, cycle), ""
                        )
                    ),
                )
                spec = TargetReviewSpec(
                    rel=rel,
                    prompt=prompt,
                    output_dir=str(output_dir),
                    log_base=str(output_dir / "agent"),
                    attempt=attempt,
                    source_contract=source_contract,
                )
                future = pool.submit(
                    self.formalization_review_worker,
                    spec,
                    project_path=self.project_path,
                    verbose_logs=self.verbose_logs,
                    model=self.model,
                    backend=self.backend,
                    harness=config.harness or self.harness,
                )
            except ProblemOnlyReviewContractError as exc:
                future = Future()
                future.set_result(TargetReviewOutcome(
                    rel=rel,
                    attempt=attempt,
                    runner_ok=False,
                    milestone=None,
                    error=f"{type(exc).__name__}: {exc}",
                ))
            futures[future] = _PipelineWork(
                kind="formalization_review",
                target=target,
                rel=rel,
                slug=slug,
                attempt=attempt,
                cycle=cycle,
                source_contract=source_contract,
            )
            active_reviews += 1
            key = (cycle, attempt)
            stats = formalization_review_rounds.setdefault(
                key,
                {
                    "cycle": cycle,
                    "attempt": attempt,
                    "submitted": 0,
                    "completed": 0,
                    "failed": 0,
                },
            )
            stats["submitted"] += 1
            write_meta(self.iter_meta, **{
                f"pipelineFormalizationReviews.{slug}.status": "running",
                f"pipelineFormalizationReviews.{slug}.cycle": cycle,
                f"pipelineFormalizationReviews.{slug}.attempt": attempt,
            })
            log.step(
                f"Starting immediate formalization Review for {rel} "
                f"(cycle {cycle})"
            )

        if resumed_formalized:
            preflight_jobs = min(review_jobs, len(resumed_formalized))
            log.info(
                f"Resume detected {len(resumed_formalized)} materialized "
                "formalizer lane(s); skipping duplicate formalization and "
                "preparing their semantic Reviews."
            )
            with ThreadPoolExecutor(max_workers=preflight_jobs) as check_pool:
                checks = {
                    check_pool.submit(run_preflight, target, rel): (
                        target, rel, slug, cycle,
                    )
                    for target, rel, slug, cycle in resumed_formalized
                }
                for future in as_completed(checks):
                    target, rel, slug, cycle = checks[future]
                    preflight_rows[rel] = future.result()
                    enqueue_formalization_review(
                        target, rel, slug, cycle, 1,
                    )

        def fill_slots(pool) -> None:
            while len(futures) < workers:
                now = time.monotonic()
                formalization_review_ready = (
                    bool(formalization_review_queue)
                    and formalization_review_queue[0][0] <= now
                    and active_reviews < review_jobs
                )
                review_ready = (
                    bool(review_queue)
                    and review_queue[0][0] <= now
                    and active_reviews < review_jobs
                )
                if formalization_review_ready:
                    _, _, target, rel, slug, cycle, attempt = heapq.heappop(
                        formalization_review_queue
                    )
                    submit_formalization_review(
                        pool, target, rel, slug, cycle, attempt,
                    )
                elif review_ready:
                    _, _, target, rel, slug, attempt, cycle = heapq.heappop(
                        review_queue
                    )
                    submit_review(pool, target, rel, slug, attempt, cycle)
                elif formalizer_queue:
                    target, rel, slug, cycle, certificate, handoff_label = (
                        formalizer_queue.popleft()
                    )
                    submit_formalizer(
                        pool,
                        target,
                        rel,
                        slug,
                        cycle,
                        certificate,
                        handoff_label,
                    )
                elif pending_provers:
                    target, cycle = pending_provers.popleft()
                    submit_prover(pool, target, cycle)
                elif pending_initial_formalizers:
                    target, cycle = pending_initial_formalizers.popleft()
                    submit_initial_formalizer(pool, target, cycle)
                else:
                    break

        with self.executor_factory(max_workers=workers) as pool:
            fill_slots(pool)
            while (
                futures
                or pending_provers
                or pending_initial_formalizers
                or review_queue
                or formalizer_queue
                or formalization_review_queue
            ):
                fill_slots(pool)
                if not futures:
                    due_times = [
                        queue[0][0]
                        for queue in (review_queue, formalization_review_queue)
                        if queue
                    ]
                    delay = max(0.0, min(due_times) - time.monotonic())
                    if delay:
                        time.sleep(delay)
                    continue

                timeout = None
                delayed_reviews = [
                    queue[0][0]
                    for queue in (review_queue, formalization_review_queue)
                    if queue
                ]
                if delayed_reviews and active_reviews < review_jobs:
                    timeout = max(
                        0.0, min(delayed_reviews) - time.monotonic(),
                    )
                done, _ = wait(
                    tuple(futures),
                    timeout=timeout,
                    return_when=FIRST_COMPLETED,
                )
                if not done:
                    continue

                for future in done:
                    work = futures.pop(future)
                    if work.kind == "prover":
                        try:
                            ok = bool(future.result())
                        except QuotaExhaustedError:
                            raise
                        except Exception:
                            ok = False
                        prover_log = self.iter_dir / "provers" / work.slug
                        persist_session_id(
                            self.iter_meta,
                            Path(str(prover_log) + ".jsonl"),
                            f"provers.{work.slug}.sessionId",
                        )
                        status = "done" if ok else "error"
                        write_meta(
                            self.iter_meta,
                            **{f"provers.{work.slug}.status": status},
                        )
                        if ok:
                            log.success(f"Prover finished: {work.rel}")
                        else:
                            failed += 1
                            log.error(f"Prover failed: {work.rel}")
                        preflight = run_preflight(work.target, work.rel)
                        preflight_rows[work.rel] = preflight
                        enqueue_review(
                            work.target, work.rel, work.slug, 1, work.cycle,
                        )
                        continue

                    if work.kind in {
                        "formalizer",
                        "initial_formalizer",
                        "answer_submission_repair",
                    }:
                        runner_error = ""
                        try:
                            runner_ok = bool(future.result())
                        except QuotaExhaustedError:
                            raise
                        except Exception as exc:
                            runner_ok = False
                            runner_error = f"{type(exc).__name__}: {exc}"
                        formalizer_log = (
                            self.iter_dir / "formalizers" / work.slug
                        )
                        persist_session_id(
                            self.iter_meta,
                            Path(str(formalizer_log) + ".jsonl"),
                            f"pipelineFormalizers.{work.slug}.sessionId",
                        )
                        digest = _target_sha256(work.target)
                        changed = bool(
                            digest and digest != work.baseline_sha256
                        )
                        if full_pipeline and changed:
                            outcomes.pop(work.rel, None)
                        postflight = run_preflight(work.target, work.rel)
                        compiles = bool(postflight.get("compiles"))
                        before_results = dict(work.result_fingerprints)
                        after_results = _task_result_fingerprints(
                            self.state_dir, work.rel,
                        )
                        result_updated = any(
                            before_results.get(path) != digest
                            for path, digest in after_results.items()
                        )
                        if native_answer_required:
                            answer_binding, answer_submission_error = (
                                validate_native_answer_submission_current(
                                    project_path=self.project_path,
                                    target=work.target,
                                )
                            )
                            answer_submission_valid = answer_binding is not None
                        else:
                            answer_binding = None
                            answer_submission_error = ""
                            answer_submission_valid = True
                        answer_only_repair = (
                            work.kind == "answer_submission_repair"
                        )
                        materialized = answer_submission_valid and compiles and (
                            (runner_ok if answer_only_repair else True)
                            and (
                                answer_only_repair
                                or (changed and result_updated)
                            )
                        )
                        errors = [runner_error] if runner_error else []
                        if not changed and not answer_only_repair:
                            errors.append("formalizer did not change the Lean target")
                        if not compiles:
                            errors.append("redrafted Lean target did not compile")
                        if not result_updated and not answer_only_repair:
                            errors.append("formalizer did not update its task result")
                        if not answer_submission_valid:
                            errors.append(answer_submission_error)
                        result = {
                            "iteration": self.iter_num,
                            "file": work.rel,
                            "cycle": work.cycle,
                            "status": "materialized" if materialized else "error",
                            "review_attempt": work.attempt,
                            "runner_ok": runner_ok,
                            "baseline_sha256": work.baseline_sha256,
                            "lean_sha256": digest,
                            "changed": changed,
                            "answer_submission_repair": answer_only_repair,
                            "task_result_updated": result_updated,
                            "answer_submission_valid": answer_submission_valid,
                            "answer_submission_binding": answer_binding,
                            "answer_submission_error": answer_submission_error,
                            "task_result_fingerprints": after_results,
                            "preflight": postflight,
                            "error": "; ".join(errors),
                        }
                        formalizer_results[work.rel] = result
                        formalizer_history.setdefault(work.rel, []).append(result)
                        preflight_rows[work.rel] = postflight
                        write_meta(self.iter_meta, **{
                            f"pipelineFormalizers.{work.slug}.status": (
                                "materialized" if materialized else "error"
                            ),
                            f"pipelineFormalizers.{work.slug}.runnerOk": runner_ok,
                            f"pipelineFormalizers.{work.slug}.changed": changed,
                            f"pipelineFormalizers.{work.slug}.compiles": compiles,
                            f"pipelineFormalizers.{work.slug}.taskResultUpdated": (
                                result_updated
                            ),
                            f"pipelineFormalizers.{work.slug}.answerSubmissionValid": (
                                answer_submission_valid
                            ),
                            f"pipelineFormalizers.{work.slug}.answerSubmissionSha256": (
                                (answer_binding or {}).get("sha256")
                            ),
                            f"pipelineFormalizers.{work.slug}.answerSubmissionPath": (
                                (answer_binding or {}).get("path")
                            ),
                            f"pipelineFormalizers.{work.slug}.answerSubmissionError": (
                                answer_submission_error
                            ),
                            f"pipelineFormalizers.{work.slug}.leanSha256": digest,
                            f"pipelineFormalizers.{work.slug}.error": "; ".join(errors),
                        })
                        if materialized:
                            pending_formalization.discard(work.rel)
                            unresolved.pop(work.rel, None)
                            log.success(
                                f"Immediate formalizer materialized: {work.rel}"
                            )
                            if full_pipeline:
                                enqueue_formalization_review(
                                    work.target,
                                    work.rel,
                                    work.slug,
                                    work.cycle,
                                    1,
                                )
                        else:
                            pending_formalization.add(work.rel)
                            queued_answer_repair = False
                            if full_pipeline:
                                unresolved[work.rel] = "; ".join(errors)
                                can_repair_answer = (
                                    native_answer_required
                                    and not answer_submission_valid
                                    and work.kind != "answer_submission_repair"
                                    and runner_ok
                                    and changed
                                    and compiles
                                    and result_updated
                                    and shadow_formalization_reviews[work.rel]
                                    < effective_formalization_review_limit(
                                        shadow_formalization_records.get(work.rel),
                                        formalization_max_iterations,
                                    )
                                )
                                if can_repair_answer:
                                    queued_answer_repair = True
                                    next_cycle = work.cycle + 1
                                    formalization_cycles[work.rel] = max(
                                        formalization_cycles[work.rel],
                                        next_cycle,
                                    )
                                    formalizer_queue.append((
                                        work.target,
                                        work.rel,
                                        work.slug,
                                        next_cycle,
                                        _answer_submission_repair_handoff(
                                            answer_submission_error
                                        ),
                                        _ANSWER_SUBMISSION_REPAIR_LABEL,
                                    ))
                                    write_meta(self.iter_meta, **{
                                        f"pipelineFormalizers.{work.slug}.status": "queued",
                                        f"pipelineFormalizers.{work.slug}.cycle": next_cycle,
                                        f"pipelineFormalizers.{work.slug}.answerSubmissionRepair": True,
                                    })
                            else:
                                settled_targets.add(work.rel)
                            log.error(
                                f"Immediate formalizer incomplete: {work.rel}; "
                                f"{'; '.join(errors)}"
                            )
                            if queued_answer_repair:
                                log.step(
                                    "Queued one bounded answer-submission repair "
                                    f"for {work.rel}"
                                )
                        continue

                    if work.kind == "formalization_review":
                        active_reviews -= 1
                        try:
                            outcome = future.result()
                        except Exception as exc:
                            outcome = TargetReviewOutcome(
                                rel=work.rel,
                                attempt=work.attempt,
                                runner_ok=False,
                                milestone=None,
                                error=f"{type(exc).__name__}: {exc}",
                            )
                        stats = formalization_review_rounds[
                            (work.cycle, work.attempt)
                        ]
                        if (
                            isinstance(outcome, TargetReviewOutcome)
                            and outcome.rel == work.rel
                            and outcome.milestone is not None
                        ):
                            formalization_review_validation_feedback.pop(
                                (work.rel, work.cycle), None
                            )
                            stats["completed"] += 1
                            decision, reason, certificate = (
                                formalization_review_decision(outcome.milestone)
                            )
                            event_id = (
                                f"pipeline:{self.iter_num}:{work.rel}:"
                                f"formalization:{work.cycle}"
                            )
                            event = {
                                "kind": "formalization",
                                "event_id": event_id,
                                "target": work.target,
                                "rel": work.rel,
                                "cycle": work.cycle,
                                "milestone": outcome.milestone,
                                "source_contract": work.source_contract,
                            }
                            gate_events.append(event)
                            update = apply_target_formalization_review(
                                state_dir=self.state_dir,
                                project_path=self.project_path,
                                target=work.target,
                                milestone=outcome.milestone,
                                iter_num=self.iter_num,
                                max_iterations=formalization_max_iterations,
                                event_id=event_id,
                                expected_source_contract=work.source_contract,
                                preflight=preflight_rows.get(work.rel),
                            )
                            status = update.status
                            reviews = update.reviews
                            reason = update.reason
                            refreshed_formal = (
                                load_formalization_review_state(self.state_dir) or {}
                            ).get("targets", {}).get(work.rel, {})
                            if not isinstance(refreshed_formal, dict):
                                refreshed_formal = {}
                            shadow_formalization_reviews[work.rel] = reviews
                            shadow_formalization_records[work.rel] = dict(
                                refreshed_formal
                            )
                            write_meta(self.iter_meta, **{
                                f"pipelineFormalizationReviews.{work.slug}.status": (
                                    status
                                ),
                                f"pipelineFormalizationReviews.{work.slug}.reviews": (
                                    reviews
                                ),
                                f"pipelineFormalizationReviews.{work.slug}.reason": (
                                    reason
                                ),
                            })
                            review_limit = (
                                effective_formalization_review_limit(
                                    refreshed_formal,
                                    formalization_max_iterations,
                                )
                            )
                            log.success(
                                "Formalization Review finished: "
                                f"{work.rel} ({status}, {reviews}/{review_limit})"
                            )
                            if status == "passed":
                                pending_formalization.discard(work.rel)
                                refreshed_proof = load_proof_review_state(
                                    self.state_dir
                                ).get("targets", {}).get(work.rel, {})
                                if not isinstance(refreshed_proof, dict):
                                    refreshed_proof = {}
                                shadow_proof_records[work.rel] = dict(refreshed_proof)
                                shadow_proof_attempts[work.rel] = int(
                                    refreshed_proof.get("attempts") or 0
                                )
                                next_cycle = proof_cycles[work.rel] + 1
                                proof_cycles[work.rel] = next_cycle
                                open_sorries = file_open_sorry_count(work.target)
                                if open_sorries == 0:
                                    preflight_rows[work.rel] = run_preflight(
                                        work.target, work.rel,
                                    )
                                    enqueue_review(
                                        work.target,
                                        work.rel,
                                        work.slug,
                                        1,
                                        next_cycle,
                                    )
                                    log.step(
                                        "Formalization Review passed with no "
                                        "open proof holes; immediately queued "
                                        f"proof Review for {work.rel}"
                                    )
                                else:
                                    pending_provers.append(
                                        (work.target, next_cycle)
                                    )
                                    log.step(
                                        "Formalization Review passed; "
                                        "immediately re-enqueued prover for "
                                        f"{work.rel}"
                                    )
                            elif status == "retry":
                                next_cycle = formalization_cycles[work.rel] + 1
                                formalization_cycles[work.rel] = next_cycle
                                handoff = build_repair_task(
                                    shadow_formalization_records.get(work.rel),
                                    review_kind="formalization",
                                    worker_stage="formalization",
                                    candidate_sha256=_target_sha256(work.target),
                                    preflight=preflight_rows.get(work.rel),
                                    expected_source_contract=(
                                        work.source_contract
                                    ),
                                    target_rel=work.rel,
                                )
                                formalizer_queue.append((
                                    work.target,
                                    work.rel,
                                    work.slug,
                                    next_cycle,
                                    handoff,
                                    "formalization Review",
                                ))
                            else:
                                pending_formalization.discard(work.rel)
                                settled_targets.add(work.rel)
                        else:
                            stats["failed"] += 1
                            error = (
                                outcome.error
                                if isinstance(outcome, TargetReviewOutcome)
                                else "invalid formalization Review worker outcome"
                            )
                            if (
                                isinstance(outcome, TargetReviewOutcome)
                                and outcome.validation_error
                            ):
                                formalization_review_validation_feedback[
                                    (work.rel, work.cycle)
                                ] = outcome.validation_error
                            if work.attempt < formalization_max_attempts:
                                enqueue_formalization_review(
                                    work.target,
                                    work.rel,
                                    work.slug,
                                    work.cycle,
                                    work.attempt + 1,
                                    delay=(
                                        config.formalization_review_backoff_sec
                                        * work.attempt
                                    ),
                                )
                            else:
                                pending_formalization.add(work.rel)
                                unresolved[work.rel] = error
                                write_meta(self.iter_meta, **{
                                    f"pipelineFormalizationReviews.{work.slug}.status": "error",
                                    f"pipelineFormalizationReviews.{work.slug}.error": error,
                                })
                                log.error(
                                    "Formalization Review failed after "
                                    f"{formalization_max_attempts} harness "
                                    f"attempt(s): {work.rel}"
                                )
                        continue

                    active_reviews -= 1
                    try:
                        outcome = future.result()
                    except Exception as exc:
                        outcome = TargetReviewOutcome(
                            rel=work.rel,
                            attempt=work.attempt,
                            runner_ok=False,
                            milestone=None,
                            error=f"{type(exc).__name__}: {exc}",
                        )
                    stats = review_rounds[work.attempt]
                    if (
                        isinstance(outcome, TargetReviewOutcome)
                        and outcome.rel == work.rel
                        and outcome.milestone is not None
                    ):
                        proof_review_validation_feedback.pop(
                            (work.rel, work.cycle), None
                        )
                        outcomes[work.rel] = outcome
                        stats["completed"] += 1
                        certificate = outcome.milestone.get("proof_review")
                        route, reason, evidence, redraft_kind, _explicit = (
                            proof_review_decision(outcome.milestone)
                        )
                        proof_status = {
                            "solved": "solved",
                            "retry_proof": "retry",
                            "needs_redraft": "needs_redraft",
                            "blocked_infrastructure": "blocked_infrastructure",
                        }.get(route, "retry")
                        prior_proof = shadow_proof_records.get(work.rel)
                        refreshed_proof = dict(
                            prior_proof if isinstance(prior_proof, dict) else {}
                        )
                        refreshed_proof.update({
                            "candidate_sha256": _target_sha256(work.target),
                            "status": proof_status,
                            "proof_review_route": route,
                            "redraft_kind": redraft_kind,
                            "blind_review_certificate": (
                                dict(certificate)
                                if isinstance(certificate, dict)
                                else {}
                            ),
                        })
                        if full_pipeline:
                            event_id = (
                                f"pipeline:{self.iter_num}:{work.rel}:"
                                f"proof:{work.cycle}"
                            )
                            event = {
                                "kind": "proof",
                                "event_id": event_id,
                                "target": work.target,
                                "rel": work.rel,
                                "cycle": work.cycle,
                                "milestone": outcome.milestone,
                                "source_contract": work.source_contract,
                            }
                            gate_events.append(event)
                            update = apply_target_proof_review(
                                state_dir=self.state_dir,
                                project_path=self.project_path,
                                target=work.target,
                                milestone=outcome.milestone,
                                iter_num=self.iter_num,
                                max_iterations=proof_max_iterations,
                                event_id=event_id,
                                expected_source_contract=work.source_contract,
                                preflight=preflight_rows.get(work.rel),
                            )
                            route = update.route
                            reason = update.reason
                            redraft_kind = update.redraft_kind
                            attempts = update.attempts
                            proof_status = update.status
                            refreshed_proof = load_proof_review_state(
                                self.state_dir
                            ).get("targets", {}).get(work.rel, {})
                            if not isinstance(refreshed_proof, dict):
                                refreshed_proof = {}
                            shadow_proof_attempts[work.rel] = attempts
                            shadow_proof_records[work.rel] = dict(refreshed_proof)
                            if route == "needs_redraft":
                                reopen_formalization_targets(
                                    state_dir=self.state_dir,
                                    project_path=self.project_path,
                                    progress_file=self.state_dir / "PROGRESS.md",
                                    redrafts={
                                        work.rel: {
                                            "reason": reason,
                                            "redraft_kind": redraft_kind,
                                            "pipeline_event_id": event_id,
                                            "repair_handoff": build_repair_task(
                                                refreshed_proof,
                                                review_kind="proof",
                                                worker_stage="formalization",
                                                candidate_sha256=_target_sha256(
                                                    work.target
                                                ),
                                                preflight=preflight_rows.get(
                                                    work.rel
                                                ),
                                            ),
                                        }
                                    },
                                    iter_num=self.iter_num,
                                    max_iterations=formalization_max_iterations,
                                    route_progress=False,
                                    enforce_budget=True,
                                )
                        write_meta(self.iter_meta, **{
                            f"pipelineReviews.{work.slug}.status": "done",
                            f"pipelineReviews.{work.slug}.route": route,
                        })
                        log.success(f"Proof Review finished: {work.rel} ({route})")
                        if route == "needs_redraft":
                            refreshed_formal = (
                                load_formalization_review_state(
                                    self.state_dir
                                ) or {}
                            ).get("targets", {}).get(work.rel, {})
                            if not isinstance(refreshed_formal, dict):
                                refreshed_formal = {}
                            shadow_formalization_records[work.rel] = dict(
                                refreshed_formal
                            )
                            shadow_formalization_reviews[work.rel] = int(
                                refreshed_formal.get("reviews") or 0
                            )
                            budget_available = (
                                not full_pipeline
                                or refreshed_formal.get("status") == "retry"
                            )
                            if budget_available:
                                pending_formalization.add(work.rel)
                                next_cycle = formalization_cycles[work.rel] + 1
                                formalization_cycles[work.rel] = next_cycle
                                handoff = _proof_formalization_redraft_handoff(
                                    refreshed_proof,
                                    refreshed_formal,
                                    project_path=self.project_path,
                                    target=work.target,
                                    target_rel=work.rel,
                                    preflight=preflight_rows.get(work.rel),
                                )
                                formalizer_queue.append((
                                    work.target,
                                    work.rel,
                                    work.slug,
                                    next_cycle,
                                    handoff,
                                    "proof Review",
                                ))
                                write_meta(self.iter_meta, **{
                                    f"pipelineFormalizers.{work.slug}.status": (
                                        "queued"
                                    ),
                                    f"pipelineFormalizers.{work.slug}.cycle": (
                                        next_cycle
                                    ),
                                })
                            else:
                                pending_formalization.discard(work.rel)
                                settled_targets.add(work.rel)
                                log.warn(
                                    "Formalization Review budget exhausted; "
                                    f"cannot redraft {work.rel} after proof "
                                    f"Review: {reason}"
                                )
                            if not full_pipeline:
                                settled_targets.add(work.rel)
                        elif not full_pipeline:
                            settled_targets.add(work.rel)
                        elif route in {"solved", "blocked_infrastructure"}:
                            settled_targets.add(work.rel)
                        elif route == "retry_proof":
                            if proof_status == "retry":
                                next_cycle = proof_cycles[work.rel] + 1
                                proof_cycles[work.rel] = next_cycle
                                pending_provers.append((work.target, next_cycle))
                                log.step(
                                    "Proof Review requested a proof-only retry; "
                                    f"immediately re-enqueued prover for {work.rel}"
                                )
                            else:
                                settled_targets.add(work.rel)
                        else:
                            settled_targets.add(work.rel)
                    else:
                        stats["failed"] += 1
                        error = (
                            outcome.error
                            if isinstance(outcome, TargetReviewOutcome)
                            else "invalid Review worker outcome"
                        )
                        if (
                            isinstance(outcome, TargetReviewOutcome)
                            and outcome.validation_error
                        ):
                            proof_review_validation_feedback[
                                (work.rel, work.cycle)
                            ] = outcome.validation_error
                        if work.attempt < max_attempts:
                            write_meta(self.iter_meta, **{
                                f"pipelineReviews.{work.slug}.status": "retrying",
                                f"pipelineReviews.{work.slug}.error": error,
                            })
                            enqueue_review(
                                work.target,
                                work.rel,
                                work.slug,
                                work.attempt + 1,
                                work.cycle,
                                delay=config.backoff_sec * work.attempt,
                            )
                        else:
                            unresolved[work.rel] = error
                            write_meta(self.iter_meta, **{
                                f"pipelineReviews.{work.slug}.status": "error",
                                f"pipelineReviews.{work.slug}.error": error,
                            })
                            log.error(
                                f"Proof Review failed after {max_attempts} "
                                f"harness attempt(s): {work.rel}"
                            )

        complete = (
            not unresolved
            and (
                (
                    not pending_formalization
                    and len(settled_targets) == file_count
                )
                if full_pipeline else len(outcomes) == file_count
            )
        )
        session_dir = (
            self.state_dir / "proof-journal" / "sessions"
            / f"session_{self.iter_num}"
        )
        gate_events_applied = False
        proof_gate_result = {
            "solved": [],
            "retry": [],
            "needs_redraft": [],
            "blocked_infrastructure": [],
            "exhausted": [],
            "reviewed": [],
        }
        formalization_gate_result = {
            "passed": [],
            "retry": [],
            "exhausted": [],
            "reviewed": [],
        }
        if complete and full_pipeline:
            gate_events_applied = True

            proof_state = load_proof_review_state(self.state_dir)
            proof_records = proof_state.get("targets", {})
            proof_records = (
                proof_records if isinstance(proof_records, dict) else {}
            )
            formalization_state = (
                load_formalization_review_state(self.state_dir) or {}
            )
            formalization_records = formalization_state.get("targets", {})
            formalization_records = (
                formalization_records
                if isinstance(formalization_records, dict) else {}
            )
            for event in gate_events:
                records = (
                    proof_records
                    if event["kind"] == "proof"
                    else formalization_records
                )
                record = records.get(event["rel"])
                history_key = (
                    "history"
                    if event["kind"] == "proof"
                    else "review_events"
                )
                history = (
                    record.get(history_key)
                    if isinstance(record, dict)
                    else None
                )
                history = history if isinstance(history, list) else []
                matches = sum(
                    isinstance(entry, dict)
                    and entry.get("event_id") == event["event_id"]
                    for entry in history
                )
                if matches != 1:
                    unresolved[event["rel"]] = (
                        "durable target Review gate event mismatch: "
                        f"{event['event_id']} persisted {matches} time(s)"
                    )
                    gate_events_applied = False

            for rel in target_rels:
                proof_was_reviewed = any(
                    event["kind"] == "proof" and event["rel"] == rel
                    for event in gate_events
                )
                proof_record = proof_records.get(rel)
                proof_status = (
                    str(proof_record.get("status") or "retry")
                    if isinstance(proof_record, dict) else "retry"
                )
                if proof_was_reviewed:
                    if proof_status == "proof_review_exhausted":
                        proof_gate_result["exhausted"].append(rel)
                    elif proof_status in proof_gate_result:
                        proof_gate_result[proof_status].append(rel)
                    proof_gate_result["reviewed"].append(rel)

                formalization_record = formalization_records.get(rel)
                formalization_status = (
                    str(formalization_record.get("status") or "")
                    if isinstance(formalization_record, dict) else ""
                )
                if formalization_status == "review_exhausted":
                    formalization_gate_result["exhausted"].append(rel)
                elif formalization_status in {"passed", "retry"}:
                    formalization_gate_result[formalization_status].append(rel)
                if any(
                    event["kind"] == "formalization" and event["rel"] == rel
                    for event in gate_events
                ):
                    formalization_gate_result["reviewed"].append(rel)
                if formalization_status == "retry" or (
                    proof_status == "needs_redraft"
                    and formalization_status != "review_exhausted"
                ):
                    pending_formalization.add(rel)

        # Publish a consumable Review session only after the read-only durable
        # gate audit confirms that no target remains pending.
        if full_pipeline:
            settled_targets.difference_update(pending_formalization)
            complete = (
                complete
                and not unresolved
                and not pending_formalization
                and len(settled_targets) == file_count
            )
        if complete:
            write_parallel_review_session(
                session_dir=session_dir,
                iter_num=self.iter_num,
                outcomes=outcomes,
            )

        checks = [preflight_rows[rel] for rel in sorted(preflight_rows)]
        preflight = {
            "iteration": self.iter_num,
            "jobs": 1,
            "duration_secs": round(sum(
                float(row.get("duration_secs") or 0.0) for row in checks
            ), 3),
            "summary": {
                "total": len(checks),
                "passed": sum(bool(row.get("compiles")) for row in checks),
                "failed": sum(not bool(row.get("compiles")) for row in checks),
            },
            "targets": checks,
        }
        rounds = [review_rounds[key] for key in sorted(review_rounds)]
        formalization_rounds = [
            formalization_review_rounds[key]
            for key in sorted(formalization_review_rounds)
        ]
        formalizer_invocations = [
            result
            for rel in sorted(formalizer_history)
            for result in formalizer_history[rel]
        ]
        materialized_invocations = [
            result
            for result in formalizer_invocations
            if result.get("status") == "materialized"
        ]
        failed_invocations = [
            result
            for result in formalizer_invocations
            if result.get("status") != "materialized"
        ]
        gate_event_summaries = []
        for event in gate_events:
            summary = {
                "kind": event["kind"],
                "event_id": event["event_id"],
                "file": event["rel"],
                "cycle": event["cycle"],
            }
            if event["kind"] == "proof":
                summary["route"] = proof_review_decision(event["milestone"])[0]
            else:
                summary["decision"] = event.get(
                    "restored_decision"
                ) or formalization_review_decision(event["milestone"])[0]
            gate_event_summaries.append(summary)
        proof_redrafts_reopened = sorted({
            row["file"]
            for row in gate_event_summaries
            if row.get("kind") == "proof"
            and row.get("route") == "needs_redraft"
        })
        materialized_redrafts = {
            rel: result
            for rel, result in sorted(formalizer_results.items())
            if result.get("status") == "materialized"
        }
        failed_redrafts = {
            rel: result for rel, result in sorted(formalizer_results.items())
            if result.get("status") != "materialized"
        }
        report_path = write_pipelined_review_report(
            iter_dir=self.iter_dir,
            report={
                "iteration": self.iter_num,
                "complete": complete,
                "status": "complete" if complete else "incomplete",
                "pipeline_mode": (
                    "target_lifecycle" if full_pipeline else "proof_review"
                ),
                "starts_at": (
                    "formalizer" if initial_formalization else "prover"
                ),
                "target_files": target_rels,
                "settled_target_files": sorted(settled_targets),
                "proof_review_target_files": sorted(outcomes),
                "targets": file_count,
                "reviewed": len(outcomes),
                "unresolved": sorted(unresolved),
                "errors": unresolved,
                "requested_jobs": config.requested_jobs,
                "max_combined_workers": workers,
                "max_reviewers": review_jobs,
                "max_attempts": max_attempts,
                "rounds": rounds,
                "duration_secs": round(time.monotonic() - started, 3),
                "preflight": preflight,
                "session_dir": str(session_dir),
                "formalizers": {
                    "requested": len(formalizer_invocations),
                    "materialized": len(materialized_invocations),
                    "failed": len(failed_invocations),
                },
                "formalizer_results": formalizer_results,
                "formalizer_history": formalizer_history,
                "formalization_handoffs": materialized_redrafts,
                "formalization_reviews": {
                    "enabled": full_pipeline,
                    "reviewed": len(formalization_gate_result["reviewed"]),
                    "rounds": formalization_rounds,
                    "unresolved": sorted(pending_formalization),
                },
                "gate_events_applied": gate_events_applied,
                "gate_events": gate_event_summaries,
                "proof_gate_result": proof_gate_result,
                "formalization_gate_result": formalization_gate_result,
                "proof_redrafts_reopened": proof_redrafts_reopened,
                "pending_formalization_targets": sorted(pending_formalization),
            },
        )
        write_meta(self.iter_meta, **{
            "prover.pipelineReviewComplete": complete,
            "prover.pipelineReviewTargets": file_count,
            "prover.pipelineReviewReviewed": len(outcomes),
            "prover.pipelineReviewUnresolved": len(unresolved),
            "prover.pipelineReviewReport": str(report_path),
            "prover.pipelineFormalizersRequested": len(formalizer_invocations),
            "prover.pipelineFormalizersMaterialized": len(
                materialized_invocations
            ),
            "prover.pipelineFormalizersFailed": len(failed_invocations),
            "prover.pipelineFormalizationReviews": len(
                formalization_gate_result["reviewed"]
            ),
            "prover.pipelineFormalizationPending": len(pending_formalization),
            "prover.pipelineGateEventsApplied": gate_events_applied,
            "prover.pipelineGateEvents": len(gate_event_summaries),
        })
        if complete:
            if initial_formalization:
                log.success(
                    "Independent target lifecycle settled all "
                    f"{file_count} target(s)"
                )
            else:
                log.success(
                    "Pipelined proof Review finished for all "
                    f"{file_count} target(s)"
                )
        else:
            log.warn(
                "Pipelined proof Review hand-off is incomplete; ReviewPhase "
                "will fail closed and rerun the normal target Review batch."
            )

        if materialized_redrafts:
            log.success(
                f"Immediate redrafts materialized: {len(materialized_redrafts)}"
            )
        if failed_redrafts:
            if full_pipeline:
                log.warn(
                    f"Immediate redrafts incomplete: {len(failed_redrafts)}; "
                    "target lifecycle remains incomplete and fail-closed"
                )
            else:
                log.warn(
                    f"Immediate redrafts incomplete: {len(failed_redrafts)}; "
                    "normal autoformalize fallback remains enabled"
                )

        if failed:
            log.warn(f"{failed}/{file_count} prover(s) had errors")
        else:
            log.success(f"All {file_count} prover(s) finished")
        results_dir = self.state_dir / "task_results"
        result_count = (
            len(list(results_dir.glob("*.md"))) if results_dir.exists() else 0
        )
        log.info(f"Task result files: {result_count}/{file_count}")
        self._emit_round_end(file_count, failed)

    def _emit_round_end(self, prover_count: int, failed: int) -> None:
        provers_dir = self.iter_dir / "provers"
        target = None
        if provers_dir.exists():
            # is_file() filters dangling symlinks — left over from cancelled
            # multilane runs or prior runs with a different lane set.
            logs = sorted(
                p for p in provers_dir.glob("*.jsonl")
                if not p.name.endswith(".raw.jsonl") and p.is_file()
            )
            if logs:
                target = logs[0]
        if target is None:
            target = self.iter_dir / "parallel.jsonl"

        row = {
            "ts": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "event": "parallel_round_end",
            "prover_count": prover_count,
            "failed": failed,
        }
        with target.open("a") as f:
            f.write(json.dumps(row) + "\n")
