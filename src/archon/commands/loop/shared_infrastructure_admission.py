"""Explicit, user-authorized admission to the shared-infrastructure queue.

The normal queue entrypoint is a structured proof Review verdict.  This module
provides the deliberately narrower administrative counterpart for a user who
has already decided that several existing Lean targets must share one
project-local module.  It reuses the normal request validator/registrar and
keeps every downstream build, axiom, migration, and reopen gate intact.

External dependencies are intentionally unsupported here.  This entrypoint
also refuses missing or unsafe consumers and fails closed on proof-gate states
whose meaning an architecture request must not overwrite.
"""

from __future__ import annotations

import json
import shutil
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

from .proof_review_gate import (
    PROOF_REVIEW_SCHEMA_VERSION,
    STATE_VERSION as PROOF_GATE_STATE_VERSION,
    _write_report as _write_proof_review_report,
    _write_routing_notes,
    load_proof_review_state,
)
from .shared_infrastructure import (
    PROJECT_LOCAL_KIND,
    STATE_FILENAME as SHARED_STATE_FILENAME,
    _safe_consumer_path,
    _sha256,
    load_shared_infrastructure_state,
    normalize_infrastructure_request,
    register_shared_infrastructure_request,
)


_ALLOWED_PRIOR_STATUSES = {
    "",
    "retry",
    "solved",
    "blocked_infrastructure",
}
_CONFLICTING_PRIOR_STATUSES = {
    "needs_redraft",
    "proof_review_exhausted",
}
_ORIGIN = "explicit_user_architecture_request"
_SUCCESSFUL_MODULE_PROOF_STATUSES = {"solved", "passed"}


class SharedInfrastructureAdmissionError(ValueError):
    """The explicit request was rejected before any loop state was changed."""


@dataclass(frozen=True)
class SharedInfrastructureAdmissionResult:
    """Audit-friendly result of one multi-consumer admission."""

    request: dict[str, Any]
    consumers: tuple[str, ...]
    transitioned_from_solved: tuple[str, ...]
    prior_statuses: tuple[tuple[str, str], ...]


def _utcnow() -> str:
    from datetime import datetime, timezone

    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _write_json_atomic(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".admission.tmp")
    tmp.write_text(
        json.dumps(data, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    tmp.replace(path)


def _validate_project_and_state(
    project_path: Path,
    state_dir: Path,
) -> tuple[Path, Path]:
    project = project_path.resolve()
    state = state_dir.resolve()
    if not project.is_dir():
        raise SharedInfrastructureAdmissionError(
            f"project path does not exist: {project}"
        )
    expected_state = (project / ".archon").resolve()
    if state != expected_state or not state.is_dir():
        raise SharedInfrastructureAdmissionError(
            "state_dir must be the existing .archon directory of project_path"
        )
    return project, state


def _validate_consumers(
    *,
    project_path: Path,
    raw_consumers: Iterable[str | Path],
    module: str,
) -> tuple[str, ...]:
    consumers: set[str] = set()
    for raw in raw_consumers:
        rel = _safe_consumer_path(project_path, raw)
        if rel is None:
            raise SharedInfrastructureAdmissionError(
                f"unsafe shared-infrastructure consumer path: {raw!s}"
            )
        if rel == module:
            raise SharedInfrastructureAdmissionError(
                "shared-infrastructure module cannot be its own consumer"
            )
        consumer = project_path / rel
        if not consumer.is_file():
            raise SharedInfrastructureAdmissionError(
                f"shared-infrastructure consumer does not exist: {rel}"
            )
        consumers.add(rel)
    if not consumers:
        raise SharedInfrastructureAdmissionError(
            "at least one existing project-local .lean consumer is required"
        )
    return tuple(sorted(consumers))


def _validate_prior_gate_records(
    *,
    gate: dict[str, Any],
    consumers: Iterable[str],
) -> tuple[tuple[str, str], ...]:
    targets = gate.get("targets", {})
    targets = targets if isinstance(targets, dict) else {}
    prior_statuses: list[tuple[str, str]] = []
    for rel in consumers:
        record = targets.get(rel)
        record = record if isinstance(record, dict) else {}
        status = str(record.get("status") or "")
        if status in _CONFLICTING_PRIOR_STATUSES:
            raise SharedInfrastructureAdmissionError(
                f"consumer {rel} has conflicting proof-gate status {status!r}"
            )
        if status not in _ALLOWED_PRIOR_STATUSES:
            raise SharedInfrastructureAdmissionError(
                f"consumer {rel} has unsupported proof-gate status {status!r}"
            )
        if status == "blocked_infrastructure":
            previous_request = record.get("infrastructure_request")
            if (
                not isinstance(previous_request, dict)
                or previous_request.get("kind") != PROJECT_LOCAL_KIND
            ):
                raise SharedInfrastructureAdmissionError(
                    f"consumer {rel} already has a non-project-local "
                    "infrastructure blocker"
                )
        prior_statuses.append((rel, status))
    return tuple(prior_statuses)


def _stage_registered_queue(
    *,
    state_dir: Path,
    project_path: Path,
    consumers: Iterable[str],
    request: dict[str, Any],
    reason: str,
    evidence: str,
    iter_num: int,
) -> dict[str, Any]:
    """Run the normal registrar on isolated state before publishing once."""
    with tempfile.TemporaryDirectory(
        prefix="shared-admission-", dir=state_dir,
    ) as temp_dir:
        staged_state_dir = Path(temp_dir)
        current = state_dir / SHARED_STATE_FILENAME
        if current.is_file():
            shutil.copyfile(current, staged_state_dir / SHARED_STATE_FILENAME)
        for rel in consumers:
            registered, error = register_shared_infrastructure_request(
                state_dir=staged_state_dir,
                project_path=project_path,
                target_rel=rel,
                raw_request=request,
                reason=reason,
                evidence=evidence,
                iter_num=iter_num,
            )
            if error or registered is None:
                raise SharedInfrastructureAdmissionError(
                    error or f"failed to register consumer {rel}"
                )
        return load_shared_infrastructure_state(staged_state_dir)


def _transition_consumers_to_infrastructure_blocked(
    *,
    gate: dict[str, Any],
    consumers: Iterable[str],
    request: dict[str, Any],
    reason: str,
    evidence: str,
    iter_num: int,
) -> tuple[dict[str, Any], tuple[str, ...]]:
    targets = gate.get("targets")
    targets = dict(targets) if isinstance(targets, dict) else {}
    transitioned_from_solved: list[str] = []
    now = _utcnow()
    module = str(request["module"])
    declarations = list(request.get("declarations", []))
    for rel in consumers:
        previous = targets.get(rel)
        previous = dict(previous) if isinstance(previous, dict) else {}
        prior_status = str(previous.get("status") or "")
        if prior_status == "solved":
            transitioned_from_solved.append(rel)
        history = previous.get("history")
        history = list(history) if isinstance(history, list) else []
        history.append({
            "iter": int(iter_num),
            "event": "explicit_user_architecture_request_admitted",
            "origin": _ORIGIN,
            "prior_status": prior_status or "unreviewed",
            "resulting_status": "blocked_infrastructure",
            "module": module,
            "declarations": declarations,
            "reason": reason,
            "evidence": evidence,
            "reviewed_at": now,
        })
        targets[rel] = {
            **previous,
            "status": "blocked_infrastructure",
            "attempts": int(previous.get("attempts") or 0),
            "reason": reason,
            "evidence": evidence,
            "redraft_kind": "not_applicable",
            "proof_review_schema_version": PROOF_REVIEW_SCHEMA_VERSION,
            "infrastructure_request": request,
            "infrastructure_request_error": "",
            "architecture_request_origin": _ORIGIN,
            "architecture_request_iter": int(iter_num),
            "history": history[-50:],
            "updated_at": now,
        }
    updated = {
        **gate,
        "version": PROOF_GATE_STATE_VERSION,
        "max_iterations": int(gate.get("max_iterations") or 3),
        "last_architecture_request_iter": int(iter_num),
        "updated_at": now,
        "targets": targets,
    }
    return updated, tuple(sorted(transitioned_from_solved))


def _invalidate_unverified_module_proof_certificate(
    *,
    gate: dict[str, Any],
    shared_state: dict[str, Any],
    module: str,
    project_path: Path,
) -> dict[str, Any]:
    """Drop an ordinary proof certificate when shared evidence was reset.

    The shared-infrastructure registrar preserves ``verified_sha256`` only
    when the existing module verification can be reused.  A new module or an
    enlarged declaration contract clears it, so any older ordinary proof
    Review record for that module describes a stale API.
    """
    modules = shared_state.get("modules", {})
    modules = modules if isinstance(modules, dict) else {}
    raw_module_record = modules.get(module, {})
    module_record = (
        raw_module_record if isinstance(raw_module_record, dict) else {}
    )
    verified_sha256 = str(module_record.get("verified_sha256") or "")
    module_path = project_path / module
    if (
        verified_sha256
        and module_path.is_file()
        and _sha256(module_path) == verified_sha256
    ):
        return gate

    targets = gate.get("targets", {})
    targets = dict(targets) if isinstance(targets, dict) else {}
    certificate = targets.get(module)
    certificate = certificate if isinstance(certificate, dict) else {}
    certificate_status = str(certificate.get("status") or "").strip().lower()
    if certificate_status not in _SUCCESSFUL_MODULE_PROOF_STATUSES:
        return gate
    targets.pop(module)
    return {**gate, "targets": targets}


def admit_explicit_user_architecture_request(
    *,
    state_dir: Path,
    project_path: Path,
    raw_request: Any,
    consumers: Iterable[str | Path],
    reason: str,
    evidence: str = "",
    iter_num: int,
) -> SharedInfrastructureAdmissionResult:
    """Admit one local shared module for several existing Lean consumers.

    All paths, the project policy, the request, and prior proof-gate states are
    validated before queue or proof state is published.  The ordinary registrar
    is run in isolated staging state for every consumer, so requests still use
    the same coalescing and migration-invalidation semantics as proof Review.
    """
    project, state = _validate_project_and_state(project_path, state_dir)
    if int(iter_num) < 1:
        raise SharedInfrastructureAdmissionError(
            "architecture-request iteration must be a positive integer"
        )
    normalized, error = normalize_infrastructure_request(
        raw_request, project_path=project,
    )
    if error:
        raise SharedInfrastructureAdmissionError(error)
    if normalized is None or normalized.get("kind") != PROJECT_LOCAL_KIND:
        raise SharedInfrastructureAdmissionError(
            "explicit architecture admission accepts project-local shared "
            "modules only; external dependencies are never installed"
        )
    normalized_reason = str(reason or "").strip()
    if not normalized_reason:
        raise SharedInfrastructureAdmissionError(
            "an explicit architecture-request reason is required"
        )
    normalized_evidence = str(evidence or "").strip()
    normalized_consumers = _validate_consumers(
        project_path=project,
        raw_consumers=consumers,
        module=str(normalized["module"]),
    )

    gate = load_proof_review_state(state)
    gate = dict(gate) if isinstance(gate, dict) else {}
    prior_statuses = _validate_prior_gate_records(
        gate=gate, consumers=normalized_consumers,
    )
    staged_queue = _stage_registered_queue(
        state_dir=state,
        project_path=project,
        consumers=normalized_consumers,
        request=normalized,
        reason=normalized_reason,
        evidence=normalized_evidence,
        iter_num=int(iter_num),
    )
    updated_gate, transitioned_from_solved = (
        _transition_consumers_to_infrastructure_blocked(
            gate=gate,
            consumers=normalized_consumers,
            request=normalized,
            reason=normalized_reason,
            evidence=normalized_evidence,
            iter_num=int(iter_num),
        )
    )
    updated_gate = _invalidate_unverified_module_proof_certificate(
        gate=updated_gate,
        shared_state=staged_queue,
        module=str(normalized["module"]),
        project_path=project,
    )

    # Publish the fail-closed proof state first.  If the queue publication
    # then fails, rerunning this same request is safe: blocked consumers are
    # accepted as prior state and the registrar reconstructs the staged queue.
    # Publishing in the opposite order would leave a durable invalidated
    # shared verification beside a stale ordinary ``solved`` certificate.
    try:
        _write_json_atomic(state / "proof-review-gate.json", updated_gate)
    except OSError as exc:
        raise SharedInfrastructureAdmissionError(
            "failed to publish the fail-closed proof gate; the shared queue "
            "was not published, so rerun the same architecture request"
        ) from exc
    try:
        _write_json_atomic(state / SHARED_STATE_FILENAME, staged_queue)
    except OSError as exc:
        raise SharedInfrastructureAdmissionError(
            "the proof gate was published fail-closed, but the shared queue "
            "was not; rerun the same architecture request to recover"
        ) from exc
    _write_proof_review_report(state, updated_gate)
    _write_routing_notes(state, updated_gate)
    return SharedInfrastructureAdmissionResult(
        request=normalized,
        consumers=normalized_consumers,
        transitioned_from_solved=transitioned_from_solved,
        prior_statuses=prior_statuses,
    )
