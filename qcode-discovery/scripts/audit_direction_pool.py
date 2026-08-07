#!/usr/bin/env python3
"""Run resumable Stage 3 logical-direction audits over a Stage 2 pool."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import sys
import time
import uuid
from collections import deque
from pathlib import Path
from typing import Any, Callable, Iterable, Mapping

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from scripts.screen_frontier_candidate import (
    build_candidate_code,
    screen_candidate,
)
from scripts.screen_frontier_sat import screen_sat_candidate
from scripts.screen_frontier_twobga import (
    TWOBGA_STAGE3_BACKEND,
    screen_twobga_candidate,
)
from scripts.screen_frontier_xor import verify_bb_translation_symmetry
from evaluation.bb_sector_isometry import verify_bb_xz_sector_isometry
from evaluation.distance_sat import (
    SAT_ENCODINGS,
    enforce_sat_native_thread_budget,
)
from evaluation.twobga_subsystem import derive_twobga_subsystem_problem
from evaluation.solver_budget import (
    SolverBudgetError,
    acquire_solver_budget,
)
from evaluation.process_hard_wall import (
    DEFAULT_TERMINATION_GRACE_S,
    IsolatedCallOutcome,
    IsolatedCallStartupTimeout,
    poll_isolated_call,
    positive_wall_timeout,
    start_isolated_call,
)
from evaluation.geometry import candidate_geometry
from evaluation.target_policy import (
    DEFAULT_TARGET_MODE,
    SUPPORTED_TARGET_MODES,
    target_binding,
    validate_target_binding,
    validate_target_mode,
)


PROJECT = Path(__file__).resolve().parent.parent
STAGE3_BACKENDS = frozenset({
    "legacy-directions",
    "sat-sectors",
    TWOBGA_STAGE3_BACKEND,
})
DEFAULT_STAGE3_BACKEND = "legacy-directions"
DEFAULT_SAT_CARDINALITY_ENCODING = "kmtotalizer"
RECOVERABLE_INCOMPLETE_EXIT_CODE = 2
CONSTRUCTION_FIELDS = (
    "source", "trial", "ansatz", "construction", "geometry", "ell", "m", "A_terms", "B_terms",
    "C_terms", "D_terms", "n", "k", "required_distance",
    "target_mode", "target",
    "max_row_weight", "max_qubit_degree", "tanner_components", "novelty",
    "canonical_digest",
)


def _atomic_write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(
        f".{path.name}.{os.getpid()}.{uuid.uuid4().hex}.tmp",
    )
    try:
        with temporary.open("w") as stream:
            stream.write(text)
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(path)
        try:
            descriptor = os.open(path.parent, os.O_RDONLY)
        except OSError:
            return
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
    finally:
        temporary.unlink(missing_ok=True)


def atomic_write_json(path: Path, value: Mapping[str, Any]) -> None:
    _atomic_write_text(path, json.dumps(dict(value), indent=2) + "\n")


def atomic_write_jsonl(
    path: Path, rows: Iterable[Mapping[str, Any]],
) -> None:
    _atomic_write_text(
        path,
        "".join(json.dumps(dict(row), sort_keys=True) + "\n" for row in rows),
    )


def read_ranked_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open() as stream:
        for line_number, line in enumerate(stream, start=1):
            if not line.strip():
                continue
            try:
                value = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(
                    f"{path}:{line_number}: invalid JSON: {exc.msg}",
                ) from exc
            if not isinstance(value, dict):
                raise ValueError(f"{path}:{line_number}: row must be an object")
            rows.append(value)
    return rows


def canonical_digest(row: Mapping[str, Any]) -> str:
    identity = row.get("triage_identity")
    digest = (
        identity.get("canonical_digest")
        if isinstance(identity, Mapping) else row.get("canonical_digest")
    )
    if not isinstance(digest, str) or not digest:
        raise ValueError("Stage 2 row lacks a canonical digest")
    return digest


def candidate_from_stage2(
    row: Mapping[str, Any],
    *,
    target_mode: str = DEFAULT_TARGET_MODE,
) -> dict[str, Any]:
    audit = row.get("campaign_audit")
    if not isinstance(audit, Mapping) or audit.get("status") != "UNRESOLVED":
        raise ValueError("Stage 3 accepts only campaign_audit.status=UNRESOLVED")
    digest = canonical_digest(row)
    candidate = {
        name: row[name]
        for name in CONSTRUCTION_FIELDS
        if name in row and row[name] is not None
    }
    candidate["canonical_digest"] = digest
    compact_css = isinstance(candidate.get("construction"), Mapping)
    required_fields = (
        ("n", "k", "required_distance")
        if compact_css
        else (
            "ell", "m", "A_terms", "B_terms", "n", "k",
            "required_distance",
        )
    )
    missing = [name for name in required_fields if name not in candidate]
    if missing:
        raise ValueError("Stage 2 row lacks: " + ", ".join(missing))
    if compact_css:
        from evaluation.construction import normalize_construction_claim

        normalized = normalize_construction_claim(candidate)
        candidate["construction"] = (
            dict(normalized["construction"])
            if isinstance(normalized.get("construction"), Mapping)
            else dict(normalized)
        )
        candidate.pop("geometry", None)
    else:
        geometry = candidate_geometry(candidate)
        if geometry is None:
            candidate.pop("geometry", None)
        else:
            candidate["geometry"] = geometry
    if candidate.get("C_terms") or candidate.get("D_terms"):
        raise ValueError("Stage 3 pool currently supports CSS candidates only")
    mode = validate_target_mode(target_mode)
    supplied_mode = candidate.get("target_mode")
    supplied_target = candidate.get("target")
    if supplied_mode is None and supplied_target is None:
        if mode != DEFAULT_TARGET_MODE:
            raise ValueError("scalar Stage 3 handoff lacks a target binding")
        canonical_target = target_binding(candidate["n"], candidate["k"], mode)
    else:
        if supplied_mode != mode:
            raise ValueError("Stage 2 target_mode does not match Stage 3")
        canonical_target = validate_target_binding(
            supplied_target,
            n=candidate["n"],
            k=candidate["k"],
            mode=mode,
        )
    if candidate["required_distance"] != canonical_target["required_distance"]:
        raise ValueError("Stage 2 required_distance does not match its target")
    candidate["target_mode"] = mode
    candidate["target"] = canonical_target
    return candidate


def select_unresolved(
    rows: list[dict[str, Any]],
    top: int = 0,
    *,
    target_mode: str = DEFAULT_TARGET_MODE,
) -> tuple[list[tuple[str, dict[str, Any]]], dict[str, int]]:
    selected: list[tuple[str, dict[str, Any]]] = []
    seen: set[str] = set()
    malformed = duplicates = unselected = 0
    for row in rows:
        audit = row.get("campaign_audit")
        if not isinstance(audit, Mapping) or audit.get("status") != "UNRESOLVED":
            continue
        try:
            digest = canonical_digest(row)
            candidate = candidate_from_stage2(
                row,
                target_mode=target_mode,
            )
        except (KeyError, TypeError, ValueError):
            malformed += 1
            continue
        if digest in seen:
            duplicates += 1
            continue
        seen.add(digest)
        if top > 0 and len(selected) >= top:
            unselected += 1
        else:
            selected.append((digest, candidate))
    return selected, {
        "input_rows": len(rows),
        "selected_candidates": len(selected),
        "malformed_unresolved_rows": malformed,
        "duplicate_digests_skipped": duplicates,
        "unselected_unresolved_candidates": unselected,
        "selection_exhausted": unselected == 0,
    }


def validate_worker_budget(
    candidate_workers: int,
    direction_workers: int,
    max_total_workers: int,
) -> None:
    if candidate_workers < 1:
        raise ValueError("candidate_workers must be positive")
    if not 1 <= direction_workers <= 8:
        raise ValueError("direction_workers must be between 1 and 8")
    if max_total_workers < 1:
        raise ValueError("max_total_workers must be positive")
    requested = candidate_workers * direction_workers
    if requested > max_total_workers:
        raise ValueError(
            "candidate_workers * direction_workers exceeds max_total_workers "
            f"({candidate_workers} * {direction_workers} = {requested} > "
            f"{max_total_workers})",
        )


def safe_digest(digest: str) -> str:
    return hashlib.sha256(digest.encode()).hexdigest()


def direction_state_path(state_dir: Path, digest: str) -> Path:
    return state_dir / "directions" / f"{safe_digest(digest)}.json"


def sat_state_path(state_dir: Path, digest: str) -> Path:
    """Keep SAT-sector decisions independent from legacy direction state."""

    return state_dir / "sat-sectors" / f"{safe_digest(digest)}.json"


def twobga_state_path(state_dir: Path, digest: str) -> Path:
    """Keep theorem-gated subsystem decisions in a typed state tree."""

    return state_dir / TWOBGA_STAGE3_BACKEND / f"{safe_digest(digest)}.json"


def artifact_state_path(state_dir: Path, digest: str, backend: str) -> Path:
    if backend == "legacy-directions":
        return direction_state_path(state_dir, digest)
    if backend == "sat-sectors":
        return sat_state_path(state_dir, digest)
    if backend == TWOBGA_STAGE3_BACKEND:
        return twobga_state_path(state_dir, digest)
    raise ValueError(f"unsupported Stage 3 backend: {backend}")


def _terminal_sat_resume_score(
    state_dir: Path,
    digest: str,
    candidate: Mapping[str, Any],
) -> tuple[int, int]:
    """Rank durable SAT progress without treating it as trusted evidence.

    A required-weight upper witness makes a candidate much more valuable than
    an object for which even an upper bound is unresolved.  Resume scheduling
    should therefore put such candidates into the finite worker pool first.
    Every checkpoint is still reconstructed and validated by the screener;
    this parser affects scheduling only and cannot promote proof status.
    """

    unit_dir = (
        state_dir / "sat-sectors" / "sat-units" / safe_digest(digest)
    )
    required = candidate.get("required_distance")
    terminal = 0
    required_upper = False
    try:
        paths = tuple(unit_dir.glob("*.json"))
    except OSError:
        paths = ()
    for path in paths:
        try:
            value = json.loads(path.read_text())
        except (OSError, UnicodeError, json.JSONDecodeError):
            continue
        if not isinstance(value, Mapping) or value.get("outcome") not in {
            "sat", "unsat",
        }:
            continue
        terminal += 1
        objective = value.get("objective")
        if (
            path.name.startswith("upper-")
            and value.get("outcome") == "sat"
            and isinstance(required, int)
            and not isinstance(required, bool)
            and isinstance(objective, int)
            and not isinstance(objective, bool)
            and objective <= required
        ):
            required_upper = True
    if required_upper:
        return (0, -terminal)
    if terminal:
        return (1, -terminal)
    artifact = sat_state_path(state_dir, digest)
    try:
        value = json.loads(artifact.read_text())
    except (OSError, UnicodeError, json.JSONDecodeError):
        return (3, 0)
    attempted = value.get("attempted_units") if isinstance(value, Mapping) else 0
    return (
        2,
        -attempted
        if isinstance(attempted, int) and not isinstance(attempted, bool)
        else 0,
    )


def prioritize_resume_candidates(
    selected: list[tuple[str, dict[str, Any]]],
    state_dir: Path,
    *,
    backend: str,
    resume: bool,
) -> list[tuple[str, dict[str, Any]]]:
    """Put candidates with replayable terminal progress first, stably."""

    if not resume or backend != "sat-sectors":
        return list(selected)
    ranked = sorted(
        enumerate(selected),
        key=lambda item: (
            *_terminal_sat_resume_score(
                state_dir, item[1][0], item[1][1],
            ),
            item[0],
        ),
    )
    return [item for _, item in ranked]


def expected_proof_units(candidate: Mapping[str, Any], backend: str) -> int:
    """Rebuild the exact operational Stage 3 proof-plan size.

    This is public because the Humanize outer hard wall must use the same
    candidate-dependent sector/cube plan as the worker it supervises.  A
    duplicated ``2*k`` estimate can become an unsafe underestimate whenever
    the verified translation cover or X/Z-isometry changes.
    """

    k = candidate.get("k")
    if isinstance(k, bool) or not isinstance(k, int) or k <= 0:
        raise ValueError("Stage 3 candidate k must be a positive integer")
    if backend == "legacy-directions":
        return 2 * k
    if backend == "sat-sectors":
        if isinstance(candidate.get("construction"), Mapping):
            try:
                from evaluation.distance_milp import get_code_matrices
                from scripts.screen_frontier_sat import (
                    verify_construction_symmetry,
                )

                code = build_candidate_code(dict(candidate))
                hx, hz, _lx, _lz = (
                    np.asarray(value, dtype=np.uint8) & 1
                    for value in get_code_matrices(code)
                )
                symmetry = verify_construction_symmetry(
                    candidate, hx, hz,
                )
                raw_anchors = symmetry.get("orbit_representatives")
                anchor_cubes = (
                    len(raw_anchors)
                    if symmetry.get("verified") is True
                    and symmetry.get("orbits_cover_all_qubits") is True
                    and isinstance(raw_anchors, list)
                    and raw_anchors
                    else 1
                )
            except Exception:
                anchor_cubes = 1
            # Generic proofs keep both X/Z sectors and a global logical OR.
            # Verified orbit anchors split only the support cover, so the plan
            # is A lower cubes + one global-lower portfolio lane + one upper
            # lane per sector.  Without usable symmetry it is just lower+upper.
            return 2 * (
                anchor_cubes + 1 + (1 if anchor_cubes > 1 else 0)
            )
        # Reduce to canonical X only after reconstructing this exact candidate
        # and replaying the matrix isometry.  Any build/geometry/report failure
        # falls back to the conservative complete X/Z budget.
        try:
            code = build_candidate_code(dict(candidate))
            geometry_matches = bool(
                int(code.num_qudits) == candidate.get("n")
                and int(code.dimension) == k
            )
            report = verify_bb_xz_sector_isometry(
                np.asarray(code.matrix_x, dtype=np.uint8) & 1,
                np.asarray(code.matrix_z, dtype=np.uint8) & 1,
                ell=int(candidate["ell"]),
                m=int(candidate["m"]),
                geometry=candidate_geometry(candidate),
            )
            symmetry = verify_bb_translation_symmetry(dict(candidate))
        except Exception:
            geometry_matches = False
            report = {}
            symmetry = {}
        proof_sectors = 1 if (
            geometry_matches
            and report.get("verified") is True
            and report.get("canonical_sector") == "X"
            and report.get("covered_sectors") == ["X", "Z"]
        ) else 2
        raw_anchors = symmetry.get("orbit_representatives")
        anchor_cubes = (
            len(raw_anchors)
            if symmetry.get("verified") is True
            and isinstance(raw_anchors, list)
            and raw_anchors
            else 1
        )
        # One lower unit per logical partition and disjoint anchor cube, one
        # exact upper unit per proof sector, and (when the cover really
        # splits) one redundant global-lower portfolio lane per sector.
        # The global lane can finish the proof early but must still be covered
        # by the outer wall when it times out alongside all cube units.
        return proof_sectors * (
            k * anchor_cubes
            + 1
            + (1 if anchor_cubes > 1 else 0)
        )
    if backend == TWOBGA_STAGE3_BACKEND:
        # Two dressed auxiliary lower-bound sectors plus one optional original
        # upper-witness search.  The conservative count also covers threshold
        # mode and INELIGIBLE candidates, whose screener returns earlier.
        return 3
    raise ValueError(f"unsupported Stage 3 backend: {backend}")


def twobga_solver_eligible(candidate: Mapping[str, Any]) -> bool:
    """Preflight whether the auxiliary backend can possibly start SAT.

    Failures are treated conservatively as solver-eligible so malformed or
    unexpectedly changed candidates cannot bypass the global worker lease.
    The authoritative screener repeats the complete derivation and emits the
    typed theorem report.
    """

    if isinstance(candidate.get("construction"), Mapping):
        return False
    try:
        if candidate_geometry(candidate) is not None:
            return False
        code = build_candidate_code(dict(candidate))
        problem = derive_twobga_subsystem_problem(
            np.asarray(code.matrix_x, dtype=np.uint8) & 1,
            np.asarray(code.matrix_z, dtype=np.uint8) & 1,
            ell=int(candidate["ell"]),
            m=int(candidate["m"]),
            expected_n=int(candidate["n"]),
            expected_k=int(candidate["k"]),
        )
    except Exception:
        return True
    return problem.eligible


def _expected_proof_units(candidate: Mapping[str, Any], backend: str) -> int:
    """Backward-compatible private alias used by older tests/callers."""

    return expected_proof_units(candidate, backend)


def _screen_one(
    digest: str,
    candidate: dict[str, Any],
    state_dir: Path,
    *,
    timeout: float,
    direction_workers: int,
    threshold_only: bool,
    resume: bool,
    direction_hard_timeout: float | None = None,
    candidate_hard_timeout: float | None = None,
    termination_grace: float = DEFAULT_TERMINATION_GRACE_S,
    backend: str = DEFAULT_STAGE3_BACKEND,
    sat_cardinality_encoding: str = DEFAULT_SAT_CARDINALITY_ENCODING,
    screener: Callable[..., dict[str, Any]] | None = None,
) -> dict[str, Any]:
    path = artifact_state_path(state_dir, digest, backend)
    selected_screener = screener
    if selected_screener is None:
        selected_screener = {
            "legacy-directions": screen_candidate,
            "sat-sectors": screen_sat_candidate,
            TWOBGA_STAGE3_BACKEND: screen_twobga_candidate,
        }[backend]
    try:
        screener_kwargs: dict[str, Any] = {
            "output": path,
            "timeout": timeout,
            "workers": direction_workers,
            "threshold_only": threshold_only,
            "resume": resume,
            "hard_timeout": direction_hard_timeout,
            "candidate_timeout": candidate_hard_timeout,
            "termination_grace": termination_grace,
        }
        if backend in {"sat-sectors", TWOBGA_STAGE3_BACKEND}:
            if sat_cardinality_encoding not in SAT_ENCODINGS:
                raise ValueError(
                    "unsupported SAT cardinality encoding: "
                    f"{sat_cardinality_encoding}"
                )
            screener_kwargs["cardinality_encoding"] = (
                sat_cardinality_encoding
            )
        artifact = selected_screener(candidate, **screener_kwargs)
        result = {
            "canonical_digest": digest,
            "backend": backend,
            "status": artifact["status"],
            "artifact_path": str(path),
        }
        if backend in {"sat-sectors", TWOBGA_STAGE3_BACKEND}:
            result.update({
                "sat_cardinality_encoding": sat_cardinality_encoding,
                "completed_proof_units": artifact["terminal_units"],
                "expected_proof_units": artifact["expected_units"],
            })
        else:
            result.update({
                "completed_directions": artifact["completed_directions"],
                "expected_directions": artifact["expected_directions"],
            })
        return result
    except Exception as exc:
        return {
            "canonical_digest": digest,
            "backend": backend,
            "status": "ERROR",
            "artifact_path": str(path),
            "error": f"{type(exc).__name__}: {exc}",
        }


def _screen_worker(payload: tuple[Any, ...]) -> dict[str, Any]:
    if len(payload) not in {10, 11, 12}:
        raise ValueError("invalid Stage 3 screen-worker payload")
    (
        digest,
        candidate,
        state_dir,
        timeout,
        workers,
        threshold_only,
        resume,
        direction_hard_timeout,
        candidate_hard_timeout,
        termination_grace,
    ) = payload[:10]
    backend = (
        str(payload[10])
        if len(payload) >= 11
        else DEFAULT_STAGE3_BACKEND
    )
    sat_cardinality_encoding = (
        str(payload[11])
        if len(payload) == 12
        else DEFAULT_SAT_CARDINALITY_ENCODING
    )
    return _screen_one(
        digest,
        candidate,
        state_dir,
        timeout=timeout,
        direction_workers=workers,
        threshold_only=threshold_only,
        resume=resume,
        direction_hard_timeout=direction_hard_timeout,
        candidate_hard_timeout=candidate_hard_timeout,
        termination_grace=termination_grace,
        backend=backend,
        sat_cardinality_encoding=sat_cardinality_encoding,
    )


def _candidate_wall_timeout(
    candidate: Mapping[str, Any],
    *,
    timeout: float,
    direction_workers: int,
    direction_hard_timeout: float | None,
    candidate_hard_timeout: float | None,
    backend: str = DEFAULT_STAGE3_BACKEND,
) -> float:
    """Bound setup, replay, every direction, and worker cleanup from submit."""

    expected = _expected_proof_units(candidate, backend)
    if candidate_hard_timeout is not None:
        return positive_wall_timeout(
            candidate_hard_timeout,
            "candidate hard timeout",
        )
    per_direction = positive_wall_timeout(
        timeout + 5.0
        if direction_hard_timeout is None
        else direction_hard_timeout,
        "direction hard timeout",
    )
    return positive_wall_timeout(
        math.ceil(expected / direction_workers) * per_direction + 5.0,
        "candidate hard timeout",
    )


def _load_partial_artifact(path: Path) -> dict[str, Any] | None:
    try:
        value = json.loads(path.read_text())
    except (FileNotFoundError, OSError, UnicodeError, json.JSONDecodeError):
        return None
    return dict(value) if isinstance(value, Mapping) else None


def _hard_wall_result(
    digest: str,
    candidate: Mapping[str, Any],
    path: Path,
    outcome: IsolatedCallOutcome,
    *,
    timeout_s: float,
    backend: str = DEFAULT_STAGE3_BACKEND,
) -> dict[str, Any]:
    """Recover durable progress after killing exactly one candidate session."""

    artifact = _load_partial_artifact(path)
    expected = _expected_proof_units(candidate, backend)
    completed = 0
    if artifact is not None:
        raw_completed = artifact.get(
            (
                "terminal_units"
                if backend in {"sat-sectors", TWOBGA_STAGE3_BACKEND}
                else "completed_directions"
            ),
            0,
        )
        if (
            isinstance(raw_completed, int)
            and not isinstance(raw_completed, bool)
            and 0 <= raw_completed <= expected
        ):
            completed = raw_completed
    result: dict[str, Any] = {
        "canonical_digest": digest,
        "backend": backend,
        # A killed worker never promotes terminal mathematics in the same
        # attempt.  A subsequent resume can validate the durable directions
        # and return a terminal artifact without recomputing them.
        "status": "UNRESOLVED",
        "artifact_path": str(path),
        "hard_wall": {
            "timed_out": True,
            "candidate_timeout_s": timeout_s,
            **dict(outcome.hard_wall or {}),
        },
    }
    if backend in {"sat-sectors", TWOBGA_STAGE3_BACKEND}:
        result.update({
            "completed_proof_units": completed,
            "expected_proof_units": expected,
        })
        result["hard_wall"]["completed_proof_units_retained"] = completed
    else:
        result.update({
            "completed_directions": completed,
            "expected_directions": expected,
        })
        result["hard_wall"]["completed_directions_retained"] = completed
    if outcome.error:
        result["hard_wall"]["error"] = outcome.error
    return result


def screen_selected_candidates(
    selected: list[tuple[str, dict[str, Any]]],
    state_dir: Path,
    *,
    timeout: float,
    candidate_workers: int,
    direction_workers: int,
    threshold_only: bool,
    resume: bool,
    direction_hard_timeout: float | None = None,
    candidate_hard_timeout: float | None = None,
    termination_grace: float = DEFAULT_TERMINATION_GRACE_S,
    backend: str = DEFAULT_STAGE3_BACKEND,
    sat_cardinality_encoding: str = DEFAULT_SAT_CARDINALITY_ENCODING,
    screener: Callable[..., dict[str, Any]] | None = None,
) -> list[dict[str, Any]]:
    if candidate_workers < 1:
        raise ValueError("candidate_workers must be positive")
    if (
        backend in {"sat-sectors", TWOBGA_STAGE3_BACKEND}
        and sat_cardinality_encoding not in SAT_ENCODINGS
    ):
        raise ValueError(
            "unsupported SAT cardinality encoding: "
            f"{sat_cardinality_encoding}"
        )
    grace = positive_wall_timeout(
        termination_grace,
        "hard-wall termination grace",
    )
    queued = deque(selected)
    results: dict[str, dict[str, Any]] = {}
    active: dict[
        str,
        tuple[Any, dict[str, Any], Path, float],
    ] = {}

    def submit_available() -> None:
        while queued and len(active) < candidate_workers:
            digest, candidate = queued.popleft()
            path = artifact_state_path(state_dir, digest, backend)
            try:
                wall_timeout = _candidate_wall_timeout(
                    candidate,
                    timeout=timeout,
                    direction_workers=direction_workers,
                    direction_hard_timeout=direction_hard_timeout,
                    candidate_hard_timeout=candidate_hard_timeout,
                    backend=backend,
                )
                handle = start_isolated_call(
                    _screen_one,
                    args=(digest, candidate, state_dir),
                    kwargs={
                        "timeout": timeout,
                        "direction_workers": direction_workers,
                        "threshold_only": threshold_only,
                        "resume": resume,
                        "direction_hard_timeout": direction_hard_timeout,
                        "candidate_hard_timeout": candidate_hard_timeout,
                        "termination_grace": termination_grace,
                        "backend": backend,
                        "sat_cardinality_encoding": (
                            sat_cardinality_encoding
                        ),
                        "screener": screener,
                    },
                    timeout_s=wall_timeout,
                    termination_grace_s=grace,
                )
            except IsolatedCallStartupTimeout as exc:
                results[digest] = _hard_wall_result(
                    digest,
                    candidate,
                    path,
                    IsolatedCallOutcome(
                        status="timeout",
                        error=str(exc),
                        hard_wall=dict(exc.hard_wall),
                    ),
                    timeout_s=wall_timeout,
                    backend=backend,
                )
                continue
            except Exception as exc:
                results[digest] = {
                    "canonical_digest": digest,
                    "backend": backend,
                    "status": "ERROR",
                    "artifact_path": str(path),
                    "error": f"{type(exc).__name__}: {exc}",
                }
                continue
            active[digest] = (handle, candidate, path, wall_timeout)

    submit_available()
    while active:
        made_progress = False
        for digest, (handle, candidate, path, wall_timeout) in list(
            active.items()
        ):
            try:
                outcome = poll_isolated_call(handle)
            except Exception as exc:
                made_progress = True
                del active[digest]
                if handle.remaining() <= 0:
                    results[digest] = _hard_wall_result(
                        digest,
                        candidate,
                        path,
                        IsolatedCallOutcome(
                            status="timeout",
                            error=(
                                "candidate hard-wall cleanup failed: "
                                f"{type(exc).__name__}: {exc}"
                            ),
                            hard_wall={"cleanup_failed": True},
                        ),
                        timeout_s=wall_timeout,
                        backend=backend,
                    )
                else:
                    results[digest] = {
                        "canonical_digest": digest,
                        "backend": backend,
                        "status": "ERROR",
                        "artifact_path": str(path),
                        "error": (
                            "isolated Stage 3 worker poll failed: "
                            f"{type(exc).__name__}: {exc}"
                        ),
                    }
                continue
            if outcome is None:
                continue
            made_progress = True
            del active[digest]
            if outcome.status == "completed" and isinstance(
                outcome.value, Mapping
            ):
                result = dict(outcome.value)
                if outcome.hard_wall is not None:
                    result["hard_wall_cleanup"] = dict(outcome.hard_wall)
            elif outcome.status == "timeout":
                result = _hard_wall_result(
                    digest,
                    candidate,
                    path,
                    outcome,
                    timeout_s=wall_timeout,
                    backend=backend,
                )
            else:
                result = {
                    "canonical_digest": digest,
                    "backend": backend,
                    "status": "ERROR",
                    "artifact_path": str(path),
                    "error": outcome.error or "isolated Stage 3 worker failed",
                }
            if result.get("canonical_digest") != digest:
                result = {
                    "canonical_digest": digest,
                    "backend": backend,
                    "status": "ERROR",
                    "artifact_path": str(path),
                    "error": "isolated Stage 3 worker returned the wrong digest",
                }
            results[digest] = result
        submit_available()
        if active and not made_progress:
            nearest = min(handle.deadline for handle, *_ in active.values())
            time.sleep(min(0.01, max(0.0, nearest - time.monotonic())))
    return [results[digest] for digest, _ in selected]


def annotate_rows(
    rows: list[dict[str, Any]],
    selected: list[tuple[str, dict[str, Any]]],
    results: Iterable[Mapping[str, Any]],
) -> list[dict[str, Any]]:
    selected_digests = {digest for digest, _ in selected}
    by_digest = {
        str(result["canonical_digest"]): dict(result) for result in results
    }
    annotated = []
    remaining_selected = set(selected_digests)
    for row in rows:
        updated = dict(row)
        try:
            digest = canonical_digest(row)
        except ValueError:
            annotated.append(updated)
            continue
        is_selected = digest in remaining_selected
        updated["campaign_direction_selected"] = is_selected
        if is_selected:
            remaining_selected.remove(digest)
        if is_selected and digest in by_digest:
            updated["campaign_direction_audit"] = by_digest[digest]
        else:
            updated.pop("campaign_direction_audit", None)
        annotated.append(updated)
    return annotated


def threshold_artifacts(
    results: Iterable[Mapping[str, Any]],
) -> tuple[list[dict[str, Any]], dict[str, str]]:
    """Load replay-validated threshold or exact artifacts for Stage 4."""

    from scripts.audit_candidate_pool import (
        CERTIFIABLE_PROOF_STATUSES,
        SECTOR_SAT_STAGE3_GATE,
        TWOBGA_STAGE3_GATE,
        claim_from_certifiable_stage3_artifact,
        claim_from_sector_sat_artifact,
        claim_from_twobga_artifact,
    )

    artifacts = []
    failures: dict[str, str] = {}
    for result in results:
        status = result.get("status")
        if status not in CERTIFIABLE_PROOF_STATUSES:
            continue
        digest = str(result["canonical_digest"])
        try:
            value = json.loads(Path(str(result["artifact_path"])).read_text())
            if not isinstance(value, dict):
                raise ValueError("Stage 3 artifact must be an object")
            if value.get("status") != status:
                raise ValueError(
                    "Stage 3 result and artifact statuses do not match"
                )
            if value.get("gate") == SECTOR_SAT_STAGE3_GATE:
                # This typed handoff installs the reserved
                # _exact_sector_certificate request consumed by Stage 4's
                # certificate dispatcher.  The manifest intentionally keeps
                # the signed Stage-3 artifact; Stage 4 reconstructs the claim.
                claim_from_sector_sat_artifact(value)
            elif value.get("gate") == TWOBGA_STAGE3_GATE:
                # The 2BGA theorem lane has distinct lower-bound semantics;
                # replay it through its own typed Stage-4 handoff.
                claim_from_twobga_artifact(value)
            else:
                claim_from_certifiable_stage3_artifact(value)
            artifacts.append(value)
        except Exception as exc:
            failures[digest] = (
                f"artifact validation failed: {type(exc).__name__}: {exc}"
            )
    return artifacts, failures


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("ranked_input", type=Path)
    parser.add_argument("--state-dir", type=Path, required=True)
    parser.add_argument("--ranked-output", type=Path, required=True)
    parser.add_argument("--summary-output", type=Path, required=True)
    parser.add_argument("--stage4-manifest", type=Path)
    parser.add_argument("--top", type=int, default=0)
    parser.add_argument(
        "--target-mode",
        choices=sorted(SUPPORTED_TARGET_MODES),
        default=DEFAULT_TARGET_MODE,
        help="target policy; defaults to the historical gist gate",
    )
    parser.add_argument("--timeout", type=float, default=300)
    parser.add_argument("--candidate-workers", type=int, default=1)
    parser.add_argument("--direction-workers", type=int, default=4)
    parser.add_argument("--max-total-workers", type=int, default=8)
    parser.add_argument(
        "--backend",
        choices=sorted(STAGE3_BACKENDS),
        default=DEFAULT_STAGE3_BACKEND,
        help=(
            "legacy per-logical MILP directions, disjoint exact SAT sector "
            "decisions, or the rank-defect-gated 2BGA subsystem lane"
        ),
    )
    parser.add_argument(
        "--sat-cardinality-encoding",
        "--cardinality-encoding",
        dest="sat_cardinality_encoding",
        choices=sorted(SAT_ENCODINGS),
        default=DEFAULT_SAT_CARDINALITY_ENCODING,
        help=(
            "initial cardinality encoding for the sat-sectors portfolio "
            f"(default: {DEFAULT_SAT_CARDINALITY_ENCODING})"
        ),
    )
    parser.add_argument("--exact", action="store_true")
    parser.add_argument(
        "--resume", action=argparse.BooleanOptionalAction, default=True,
    )
    parser.add_argument(
        "--certify", action=argparse.BooleanOptionalAction, default=False,
        help="run the separate certificate pool after all Stage 3 work",
    )
    parser.add_argument("--certificate-workers", type=int, default=1)
    parser.add_argument("--certificate-solver-workers", type=int, default=1)
    parser.add_argument(
        "--known-answer-artifact", type=Path,
        default=PROJECT / "results" / "known_answer_gate.json",
    )
    parser.add_argument("--certificate-timeout-per-logical", type=float, default=300)
    parser.add_argument("--certificate-total-timeout", type=float, default=7200)
    parser.add_argument("--verification-timeout-per-logical", type=float, default=300)
    parser.add_argument("--verification-total-timeout", type=float, default=7200)
    parser.add_argument("--direction-hard-timeout", type=float)
    parser.add_argument("--candidate-hard-timeout", type=float)
    parser.add_argument("--certificate-hard-timeout", type=float)
    parser.add_argument(
        "--hard-wall-termination-grace",
        type=float,
        default=DEFAULT_TERMINATION_GRACE_S,
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    # Candidate workers are fresh spawned interpreters.  Set this before any
    # of them starts so the configured worker budget counts real solver cores,
    # rather than hidden BLAS pools inside every process.
    native_thread_environment = enforce_sat_native_thread_budget()
    parser = build_parser()
    args = parser.parse_args(argv)
    args.target_mode = validate_target_mode(args.target_mode)
    if (
        args.top < 0
        or not math.isfinite(args.timeout)
        or args.timeout <= 0
    ):
        parser.error("top must be nonnegative and timeout must be positive")
    for name in (
        "certificate_timeout_per_logical",
        "certificate_total_timeout",
        "verification_timeout_per_logical",
        "verification_total_timeout",
        "hard_wall_termination_grace",
    ):
        value = getattr(args, name)
        if not math.isfinite(value) or value <= 0:
            parser.error(f"{name.replace('_', '-')} must be positive")
    for name in (
        "direction_hard_timeout",
        "candidate_hard_timeout",
        "certificate_hard_timeout",
    ):
        value = getattr(args, name)
        if value is not None and (not math.isfinite(value) or value <= 0):
            parser.error(f"{name.replace('_', '-')} must be positive")
    try:
        validate_worker_budget(
            args.candidate_workers,
            args.direction_workers,
            args.max_total_workers,
        )
        if args.certify:
            validate_worker_budget(
                args.certificate_workers,
                args.certificate_solver_workers,
                args.max_total_workers,
            )
        rows = read_ranked_jsonl(args.ranked_input)
        selection_top = (
            0 if args.resume and args.backend == "sat-sectors" else args.top
        )
        selected, counts = select_unresolved(
            rows,
            selection_top,
            target_mode=args.target_mode,
        )
        selected = prioritize_resume_candidates(
            selected,
            args.state_dir,
            backend=args.backend,
            resume=args.resume,
        )
        if args.top > 0 and len(selected) > args.top:
            newly_unselected = len(selected) - args.top
            selected = selected[: args.top]
            counts["selected_candidates"] = len(selected)
            counts["unselected_unresolved_candidates"] += newly_unselected
            counts["selection_exhausted"] = False
        solver_eligible_candidates = (
            sum(
                twobga_solver_eligible(candidate)
                for _, candidate in selected
            )
            if args.backend == TWOBGA_STAGE3_BACKEND
            else len(selected)
        )
    except (OSError, TypeError, ValueError) as exc:
        parser.error(str(exc))
    # Reserve the peak of the two non-overlapping solver phases.  Holding the
    # lease across their transition prevents another independently launched
    # campaign from filling the cgroup between Stage 3 and certification.
    stage3_solver_slots = (
        min(args.candidate_workers, solver_eligible_candidates)
        * args.direction_workers
    )
    certificate_solver_slots = (
        args.certificate_workers * args.certificate_solver_workers
        if args.certify and solver_eligible_candidates > 0 else 0
    )
    requested_solver_slots = max(
        stage3_solver_slots,
        (
            certificate_solver_slots
        ),
    )
    solver_budget_lease = None
    solver_budget_runtime: dict[str, Any] = {
        "enforced": False,
        "requested_slots": 0,
        "reason": "no selected candidates",
    }
    if requested_solver_slots > 0:
        try:
            solver_budget_lease = acquire_solver_budget(
                requested_solver_slots,
            )
        except SolverBudgetError as exc:
            parser.error(str(exc))
        solver_budget_runtime = solver_budget_lease.as_dict()
    elif selected:
        solver_budget_runtime["reason"] = (
            "all selected candidates failed the fail-closed 2BGA "
            "solver-eligibility preflight"
        )
    try:
        results = screen_selected_candidates(
            selected,
            args.state_dir,
            timeout=args.timeout,
            candidate_workers=args.candidate_workers,
            direction_workers=args.direction_workers,
            threshold_only=not args.exact,
            resume=args.resume,
            direction_hard_timeout=args.direction_hard_timeout,
            candidate_hard_timeout=args.candidate_hard_timeout,
            termination_grace=args.hard_wall_termination_grace,
            backend=args.backend,
            sat_cardinality_encoding=args.sat_cardinality_encoding,
        )
        atomic_write_jsonl(
            args.ranked_output,
            annotate_rows(rows, selected, results),
        )
        artifacts, artifact_failures = threshold_artifacts(results)
        if artifact_failures:
            results = [
                {
                    **result,
                    "status": "ERROR",
                    "error": artifact_failures[
                        str(result["canonical_digest"])
                    ],
                }
                if str(result["canonical_digest"]) in artifact_failures
                else result
                for result in results
            ]
        if args.stage4_manifest is not None:
            atomic_write_jsonl(args.stage4_manifest, artifacts)
        if args.certify and artifacts:
            from scripts.audit_candidate_pool import (
                AuditConfig,
                certify_selected_candidates,
                merge_certification_results,
            )
            config = AuditConfig(
                state_dir=args.state_dir,
                target_mode=args.target_mode,
                resume=args.resume,
                certify=True,
                known_answer_artifact=args.known_answer_artifact,
                certificate_timeout_per_logical_s=(
                    args.certificate_timeout_per_logical
                ),
                certificate_total_timeout_s=(
                    args.certificate_total_timeout
                ),
                certificate_solver_workers=(
                    args.certificate_solver_workers
                ),
                verification_timeout_per_logical_s=(
                    args.verification_timeout_per_logical
                ),
                verification_total_timeout_s=(
                    args.verification_total_timeout
                ),
                certificate_hard_timeout_s=args.certificate_hard_timeout,
                hard_wall_termination_grace_s=(
                    args.hard_wall_termination_grace
                ),
            )
            certifications = certify_selected_candidates(
                artifacts,
                config,
                certificate_workers=args.certificate_workers,
                max_total_workers=args.max_total_workers,
            )
            results = merge_certification_results(
                results, certifications, certify=True,
            )
    finally:
        if solver_budget_lease is not None:
            solver_budget_lease.release()
    annotated = annotate_rows(rows, selected, results)
    atomic_write_jsonl(args.ranked_output, annotated)
    status_counts: dict[str, int] = {}
    for result in results:
        status = str(result["status"])
        status_counts[status] = status_counts.get(status, 0) + 1
    operational_errors = (
        counts["malformed_unresolved_rows"]
        + status_counts.get("ERROR", 0)
        + sum(
            bool(result.get("certificate", {}).get("error"))
            for result in results
        )
    )
    retry_reasons = {
        "unresolved_candidates": status_counts.get("UNRESOLVED", 0),
        "unselected_unresolved_candidates": counts[
            "unselected_unresolved_candidates"
        ],
        "operational_errors": operational_errors,
    }
    retry_required = any(retry_reasons.values())
    summary = {
        "schema_version": 1,
        "gate": "qldpc-direction-candidate-pool",
        "target_mode": args.target_mode,
        "backend": args.backend,
        "sat_cardinality_encoding": (
            args.sat_cardinality_encoding
            if args.backend in {"sat-sectors", TWOBGA_STAGE3_BACKEND}
            else None
        ),
        "proof_unit_semantics": (
            "first-nonzero-sector-partitions-plus-xz-upper-witness"
            if args.backend == "sat-sectors"
            else (
                "rank-defect-gated-dressed-subsystem-xz-plus-original-upper"
                if args.backend == TWOBGA_STAGE3_BACKEND
                else "logical-basis-directions"
            )
        ),
        **counts,
        "threshold_only": (
            args.backend != "sat-sectors" and not args.exact
        ),
        "hard_wall_budget": {
            "direction_timeout_s": (
                args.direction_hard_timeout
                if args.direction_hard_timeout is not None
                else args.timeout + 5.0
            ),
            "candidate_timeout_s": args.candidate_hard_timeout,
            "certificate_timeout_s": args.certificate_hard_timeout,
            "termination_grace_s": args.hard_wall_termination_grace,
        },
        "worker_budget": {
            "phases_overlap": False,
            "stage3": {
                "candidate_workers": args.candidate_workers,
                "solver_eligible_candidates": solver_eligible_candidates,
                "direction_workers": args.direction_workers,
                "solver_workers_per_direction": 1,
                "configured_solver_workers": (
                    args.candidate_workers * args.direction_workers
                ),
                "admitted_solver_workers": stage3_solver_slots,
            },
            "certification": {
                "enabled": args.certify,
                "certificate_workers": args.certificate_workers,
                "solver_workers_per_certificate": (
                    args.certificate_solver_workers
                ),
                "configured_solver_workers": (
                    args.certificate_workers
                    * args.certificate_solver_workers
                ),
                "admitted_solver_workers": certificate_solver_slots,
            },
            "max_total_workers": args.max_total_workers,
            "native_thread_environment": native_thread_environment,
            "global_admission": solver_budget_runtime,
        },
        "status_counts": status_counts,
        # Exit 0 means that this invocation reached a terminal disposition for
        # every selected candidate *and* exhausted the requested selection.
        # A durable partial artifact remains useful for --resume, but it must
        # never look like a successfully completed Stage 3 to a shell/nohup
        # supervisor.  Exit 2 is the pipeline's recoverable-proof contract.
        "retry_required": retry_required,
        "retry_reasons": retry_reasons,
        "certify": args.certify,
        "stage4_candidates": len(artifacts),
        "certified_wins": sum(
            result.get("certificate", {}).get("certificate_passed") is True
            and result.get("certificate", {}).get("verification_passed") is True
            for result in results
        ),
        "operational_errors": operational_errors,
        "stage4_manifest": (
            None if args.stage4_manifest is None else str(args.stage4_manifest)
        ),
        "ranked_output": str(args.ranked_output),
        "state_dir": str(args.state_dir),
        "results": results,
    }
    atomic_write_json(args.summary_output, summary)
    print(json.dumps(summary, indent=2))
    return RECOVERABLE_INCOMPLETE_EXIT_CODE if retry_required else 0


if __name__ == "__main__":
    raise SystemExit(main())
