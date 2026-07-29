"""Persistent audit gate for target-triggered foundation construction.

A proof Review may discover that the target is faithful but depends on a
substantial theorem missing from the local Lean library.  Those failures use a
separate budget from statement redrafts.  This module records each attempt and
binds a successful hand-off to the exact foundation and target file digests.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping


STATE_FILENAME = "foundation-build-gate.json"
REPORT_FILENAME = "FOUNDATION_BUILD_GATE.md"
STATE_VERSION = 1


@dataclass(frozen=True)
class FoundationBuildUpdate:
    """One idempotent foundation-build transition."""

    rel: str
    status: str
    attempts: int
    foundation_file: str
    reason: str
    applied: bool


def _utcnow() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _sha256(path: Path) -> str:
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError:
        return ""


def _normal_rel(value: str) -> str:
    return Path(value).as_posix().lstrip("./")


def normalize_foundation_root(value: str) -> str:
    """Return a safe project-relative directory for generated foundations."""
    raw = str(value or "ArchonFoundations").strip()
    path = Path(raw)
    if (
        not raw
        or path.is_absolute()
        or raw in {".", ".."}
        or ".." in path.parts
    ):
        raise ValueError(
            "pipeline_foundation_root must be a non-empty project-relative "
            "directory without '..'"
        )
    return path.as_posix().strip("/")


def foundation_relpath(target_rel: str, foundation_root: str) -> str:
    """Choose a deterministic, filesystem-safe Lean file for a target."""
    root = normalize_foundation_root(foundation_root)
    raw_slug = Path(_normal_rel(target_rel)).with_suffix("").as_posix()
    slug = re.sub(r"[^A-Za-z0-9_]+", "_", raw_slug).strip("_")
    if not slug:
        slug = "Target"
    if slug[0].isdigit():
        slug = f"Target_{slug}"
    return f"{root}/{slug}_Foundation.lean"


def load_foundation_build_state(state_dir: Path) -> dict[str, Any]:
    try:
        data = json.loads(
            (state_dir / STATE_FILENAME).read_text(encoding="utf-8")
        )
    except (OSError, json.JSONDecodeError):
        return {}
    if (
        not isinstance(data, dict)
        or data.get("version") != STATE_VERSION
        or not isinstance(data.get("targets", {}), dict)
    ):
        return {}
    return data


def foundation_record(
    state_dir: Path,
    target_rel: str,
) -> dict[str, Any]:
    state = load_foundation_build_state(state_dir)
    raw = state.get("targets", {}).get(_normal_rel(target_rel))
    return dict(raw) if isinstance(raw, dict) else {}


def latest_proof_review_event_id(record: Mapping[str, Any]) -> str:
    """Return the newest durable Proof Review event identifier."""
    history = record.get("history")
    if not isinstance(history, list):
        return ""
    for entry in reversed(history):
        if isinstance(entry, dict):
            event_id = str(entry.get("event_id") or "").strip()
            if event_id:
                return event_id
    return ""


def foundation_build_is_dispatchable(
    *,
    state_dir: Path,
    project_path: Path,
    target_rel: str,
    max_iterations: int,
) -> bool:
    """Return whether a missing-foundation target has useful work left."""
    from .proof_review_gate import load_proof_review_state

    rel = _normal_rel(target_rel)
    proof_state = load_proof_review_state(state_dir)
    targets = proof_state.get("targets", {})
    proof = targets.get(rel) if isinstance(targets, dict) else None
    if not (
        isinstance(proof, dict)
        and proof.get("status") == "needs_redraft"
        and proof.get("redraft_kind") == "missing_foundational_bridge"
    ):
        return False
    record = foundation_record(state_dir, rel)
    if foundation_materialization_matches_proof_review(
        state_dir=state_dir,
        project_path=project_path,
        target_rel=rel,
        proof_record=proof,
    ):
        return True
    return int(record.get("attempts") or 0) < max(1, int(max_iterations))


def foundation_materialization_is_current(
    *,
    state_dir: Path,
    project_path: Path,
    target_rel: str,
) -> bool:
    """Check that a persisted successful hand-off still matches disk."""
    rel = _normal_rel(target_rel)
    record = foundation_record(state_dir, rel)
    foundation_rel = _normal_rel(str(record.get("foundation_file") or ""))
    target_digest = str(record.get("target_sha256") or "")
    foundation_digest = str(record.get("foundation_sha256") or "")
    return bool(
        record.get("status") == "materialized"
        and foundation_rel
        and len(target_digest) == 64
        and len(foundation_digest) == 64
        and _sha256(project_path / rel) == target_digest
        and _sha256(project_path / foundation_rel) == foundation_digest
    )


def foundation_materialization_matches_proof_review(
    *,
    state_dir: Path,
    project_path: Path,
    target_rel: str,
    proof_record: Mapping[str, Any] | None = None,
) -> bool:
    """Check that a hand-off was built for the latest missing-bridge event.

    A later Proof Review event means the prior compiling foundation did not
    resolve the blocker and another independent build attempt is warranted.
    Records created before event binding remain resumable for compatibility.
    """
    rel = _normal_rel(target_rel)
    if not foundation_materialization_is_current(
        state_dir=state_dir,
        project_path=project_path,
        target_rel=rel,
    ):
        return False
    foundation = foundation_record(state_dir, rel)
    certificate = foundation.get("certificate")
    source_event_id = (
        str(certificate.get("source_proof_event_id") or "").strip()
        if isinstance(certificate, dict) else ""
    )
    if not source_event_id:
        return True
    if proof_record is None:
        from .proof_review_gate import load_proof_review_state

        proof_state = load_proof_review_state(state_dir)
        targets = proof_state.get("targets", {})
        raw = targets.get(rel) if isinstance(targets, dict) else None
        proof_record = raw if isinstance(raw, dict) else {}
    return source_event_id == latest_proof_review_event_id(proof_record)


def _write_state(state_dir: Path, state: dict[str, Any]) -> None:
    path = state_dir / STATE_FILENAME
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(
        json.dumps(state, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    tmp.replace(path)


def _write_report(state_dir: Path, state: dict[str, Any]) -> None:
    targets = state.get("targets", {})
    buckets: dict[str, list[tuple[str, dict[str, Any]]]] = {
        "materialized": [],
        "retry": [],
        "foundation_exhausted": [],
    }
    for rel, raw in sorted(targets.items()):
        if not isinstance(raw, dict):
            continue
        buckets.setdefault(str(raw.get("status") or "retry"), []).append(
            (rel, raw)
        )
    lines = [
        "# Foundation Build Gate",
        "",
        f"- Maximum build attempts per target: {state.get('max_iterations', 0)}",
        f"- Materialized: {len(buckets.get('materialized', []))}",
        f"- Retry: {len(buckets.get('retry', []))}",
        f"- Exhausted: {len(buckets.get('foundation_exhausted', []))}",
        "",
    ]
    for status, title in (
        ("retry", "Retry foundation construction"),
        ("foundation_exhausted", "Foundation budget exhausted"),
        ("materialized", "Validated foundations"),
    ):
        lines.extend([f"## {title}", ""])
        rows = buckets.get(status, [])
        if not rows:
            lines.append("- None")
        for rel, record in rows:
            reason = " ".join(str(record.get("reason") or "").split())
            lines.append(
                f"- `{rel}` → `{record.get('foundation_file', '')}` — "
                f"attempts {record.get('attempts', 0)}/"
                f"{state.get('max_iterations', 0)}; {reason}"
            )
        lines.append("")
    (state_dir / REPORT_FILENAME).write_text(
        "\n".join(lines).rstrip() + "\n",
        encoding="utf-8",
    )


def record_foundation_build_attempt(
    *,
    state_dir: Path,
    project_path: Path,
    target_rel: str,
    foundation_file: str,
    certificate: Mapping[str, Any],
    result: Mapping[str, Any],
    iter_num: int,
    max_iterations: int,
    event_id: str,
) -> FoundationBuildUpdate:
    """Persist one build result without double-consuming its budget."""
    if not event_id.strip():
        raise ValueError("foundation build event_id is required")
    rel = _normal_rel(target_rel)
    foundation_rel = _normal_rel(foundation_file)
    max_iterations = max(1, int(max_iterations))
    state = load_foundation_build_state(state_dir)
    targets = state.get("targets")
    if not isinstance(targets, dict):
        targets = {}
    old = targets.get(rel)
    old = dict(old) if isinstance(old, dict) else {}
    history = old.get("history")
    history = list(history) if isinstance(history, list) else []
    for entry in history:
        if isinstance(entry, dict) and entry.get("event_id") == event_id:
            return FoundationBuildUpdate(
                rel=rel,
                status=str(old.get("status") or "retry"),
                attempts=int(old.get("attempts") or 0),
                foundation_file=str(
                    old.get("foundation_file") or foundation_rel
                ),
                reason=str(old.get("reason") or ""),
                applied=False,
            )

    attempts = int(old.get("attempts") or 0) + 1
    initial_target_digest = str(
        old.get("initial_target_sha256")
        or result.get("initial_target_sha256")
        or result.get("baseline_target_sha256")
        or ""
    )
    target_digest = _sha256(project_path / rel)
    foundation_digest = _sha256(project_path / foundation_rel)
    materialized = bool(
        str(result.get("status") or "") == "materialized"
        and target_digest
        and foundation_digest
    )
    reason = str(result.get("error") or "").strip()
    if materialized:
        status = "materialized"
        reason = (
            "foundation compiled with zero open sorries; target hand-off compiled"
        )
    elif attempts >= max_iterations:
        status = "foundation_exhausted"
        reason = reason or "foundation builder did not materialize a valid hand-off"
    else:
        status = "retry"
        reason = reason or "foundation builder did not materialize a valid hand-off"

    history.append({
        "event_id": event_id,
        "iter": iter_num,
        "attempt": attempts,
        "status": status,
        "reason": reason,
        "result": dict(result),
        "recorded_at": _utcnow(),
    })
    record = {
        **old,
        "status": status,
        "attempts": attempts,
        "initial_target_sha256": initial_target_digest,
        "foundation_file": foundation_rel,
        "reason": reason,
        "certificate": dict(certificate),
        "target_sha256": target_digest if materialized else "",
        "foundation_sha256": foundation_digest if materialized else "",
        "last_iter": iter_num,
        "last_event_id": event_id,
        "history": history[-50:],
        "updated_at": _utcnow(),
    }
    targets[rel] = record
    state = {
        **state,
        "version": STATE_VERSION,
        "max_iterations": max_iterations,
        "targets": targets,
        "updated_at": _utcnow(),
    }
    _write_state(state_dir, state)
    _write_report(state_dir, state)
    return FoundationBuildUpdate(
        rel=rel,
        status=status,
        attempts=attempts,
        foundation_file=foundation_rel,
        reason=reason,
        applied=True,
    )
