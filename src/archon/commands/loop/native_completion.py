"""Conservative terminal-state detection for native gated problem sets."""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

from archon.state import parse_objective_files, read_stage

from .formalization_review_gate import load_gate_state
from .proof_review_gate import STATE_VERSION as PROOF_GATE_STATE_VERSION
from .proof_review_gate import load_proof_review_state
from .shared_infrastructure import (
    pending_shared_consumer_migrations,
    pending_shared_infrastructure_objectives,
)


@dataclass(frozen=True)
class NativeCompletion:
    complete: bool
    reason: str
    target_count: int = 0


def _project_relative_lean(project_path: Path, value: Any) -> str | None:
    if not isinstance(value, str) or not value.strip():
        return None
    try:
        root = project_path.resolve()
        path = Path(value)
        resolved = path.resolve() if path.is_absolute() else (root / path).resolve()
        relative = resolved.relative_to(root)
    except (OSError, RuntimeError, ValueError):
        return None
    normalized = relative.as_posix()
    if not normalized.endswith(".lean") or normalized.startswith(".archon/"):
        return None
    return normalized


def _target_set(project_path: Path, rows: Iterable[Any]) -> set[str] | None:
    targets: set[str] = set()
    count = 0
    for raw in rows:
        count += 1
        row = raw if isinstance(raw, dict) else {}
        rel = _project_relative_lean(project_path, row.get("rel_lean"))
        if rel is None or rel in targets or not (project_path / rel).is_file():
            return None
        targets.add(rel)
    return targets if count and len(targets) == count else None


def _prepared_target_universe(project_path: Path) -> set[str] | None:
    """Read the exact target set recorded by the preparing native command."""
    latest = project_path / ".archon" / "physics-formalize" / "latest.json"
    try:
        metadata = json.loads(latest.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    if not isinstance(metadata, dict) or metadata.get("command") != "physics-formalize":
        return None
    if metadata.get("dry_run") is True:
        return None

    records = metadata.get("records")
    if isinstance(records, list) and records:
        return _target_set(project_path, records)
    record = metadata.get("record")
    if isinstance(record, dict):
        return _target_set(project_path, [record])

    # Older problem-set metadata points at the authoritative summary rather
    # than embedding records.  Keep the read inside the project tree.
    work_dir = metadata.get("work_dir")
    if not isinstance(work_dir, str) or not work_dir.strip():
        return None
    try:
        root = project_path.resolve()
        path = Path(work_dir)
        resolved = path.resolve() if path.is_absolute() else (root / path).resolve()
        resolved.relative_to(root)
        lines = (resolved / "summary.jsonl").read_text(encoding="utf-8").splitlines()
        rows = [json.loads(line) for line in lines if line.strip()]
    except (OSError, RuntimeError, ValueError, json.JSONDecodeError):
        return None
    return _target_set(project_path, rows)


def _normalized_gate_targets(
    project_path: Path, state: dict[str, Any] | None,
) -> dict[str, dict[str, Any]] | None:
    if not isinstance(state, dict) or not isinstance(state.get("targets"), dict):
        return None
    normalized: dict[str, dict[str, Any]] = {}
    for raw_rel, raw_record in state["targets"].items():
        rel = _project_relative_lean(project_path, raw_rel)
        if rel is None or rel in normalized or not isinstance(raw_record, dict):
            return None
        normalized[rel] = raw_record
    return normalized


def native_iteration_completion(
    *,
    project_path: Path,
    state_dir: Path,
    progress_file: Path,
    iter_meta: Path,
    formalization_gate_enabled: bool,
    proof_gate_enabled: bool,
    current_sorry_count: int | None,
    current_lake_ok: bool | None,
    force_stage: str | None = None,
) -> NativeCompletion:
    """Return complete only for a fully evidenced, current native iteration.

    This deliberately does not infer a target universe from the gates: two
    equally incomplete gates must never make an ordinary project terminate.
    """
    if force_stage is not None:
        return NativeCompletion(False, "stage was explicitly forced")
    if not formalization_gate_enabled or not proof_gate_enabled:
        return NativeCompletion(False, "both native review gates are required")
    try:
        if read_stage(progress_file).strip().lower() != "prover":
            return NativeCompletion(False, "current stage is not prover")
        meta = json.loads(iter_meta.read_text(encoding="utf-8"))
    except (OSError, ValueError, json.JSONDecodeError):
        return NativeCompletion(False, "current iteration metadata is unavailable")
    if not isinstance(meta, dict) or not meta.get("completedAt"):
        return NativeCompletion(False, "current iteration is not complete")
    plan = meta.get("plan")
    if not isinstance(plan, dict) or plan.get("status") not in {"done", "skipped"}:
        return NativeCompletion(False, "plan phase is not settled")
    for phase in ("prover", "review"):
        section = meta.get(phase)
        if not isinstance(section, dict) or section.get("status") != "done":
            return NativeCompletion(False, f"{phase} phase is not done")
    # Require live results from this invocation.  Meta is deliberately not
    # enough here: a resumed iteration can retain an older successful build.
    if current_lake_ok is not True:
        return NativeCompletion(False, "this invocation's Lake build did not pass")
    if current_sorry_count != 0:
        return NativeCompletion(False, "current iteration has unresolved sorries")

    expected = _prepared_target_universe(project_path)
    if not expected:
        return NativeCompletion(False, "exact prepared target universe is unavailable")
    formal = _normalized_gate_targets(project_path, load_gate_state(state_dir))
    proof_state = load_proof_review_state(state_dir)
    if proof_state.get("version") != PROOF_GATE_STATE_VERSION:
        return NativeCompletion(False, "proof review gate version is invalid")
    proof = _normalized_gate_targets(project_path, proof_state)
    if formal is None or proof is None or set(formal) != expected or set(proof) != expected:
        return NativeCompletion(False, "review gates do not match the prepared target universe")
    if any(record.get("status") != "passed" for record in formal.values()):
        return NativeCompletion(False, "formalization review gate is unsettled")
    if any(record.get("status") != "solved" for record in proof.values()):
        return NativeCompletion(False, "proof review gate is unsettled")

    progress_targets = {
        path.resolve().relative_to(project_path.resolve()).as_posix()
        for path in parse_objective_files(progress_file, project_path)
    }
    if not progress_targets.issubset(expected):
        return NativeCompletion(False, "PROGRESS contains a non-terminal objective")
    if pending_shared_infrastructure_objectives(
        state_dir=state_dir, project_path=project_path,
    ) or pending_shared_consumer_migrations(
        state_dir=state_dir, project_path=project_path,
    ):
        return NativeCompletion(False, "shared infrastructure work remains")
    return NativeCompletion(True, "all native targets are solved", len(expected))
