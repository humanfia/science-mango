"""Typed DistQLDPC lower-proof replay for sector exact certificates.

Stage 3 may prove the global CSS lower bound with one pinned DistQLDPC exact
decision instead of a collection of PySAT UNSAT sectors.  This module keeps
that evidence typed when it is handed to Stage 4/Final and gives certificate
verification a distinct, certificate-bound identity for its independent
rerun.

No result is inferred from progress output.  Stored and fresh decisions are
accepted only after both official DistQLDPC evidence verifiers replay them.
"""

from __future__ import annotations

import hashlib
import json
import math
import re
from pathlib import Path
from typing import Any, Callable, Mapping

import numpy as np

from evaluation.admissibility_policy import (
    validate_css_w6_admissibility_binding,
)
from evaluation.distance_distqldpc import (
    DEFAULT_DISTQLDPC_EXE,
    DISTQLDPC_CARDINALITY_MODES,
    solve_css_distance_distqldpc_lower,
    verify_distqldpc_exact_evidence,
    verify_distqldpc_lower_evidence,
)
from evaluation.target_policy import TARGET_MODE_SCALAR_13_INCLUSIVE


STAGE3_GATE = "qldpc-frontier-sat-sector-exact-screen"
DISTQLDPC_LOWER_BACKEND = "distqldpc"
DISTQLDPC_STAGE3_PHASE = "lower-distqldpc"
DISTQLDPC_CERTIFICATE_REPLAY_PHASE = "verify-lower-distqldpc"
SUPPORTED_COVERAGE_MODES = frozenset({"global", "first-nonzero"})
_SHA256_RE = re.compile(r"[0-9a-f]{64}")

DistQLDPCSolver = Callable[..., dict[str, Any]]


def _canonical_json(value: Any) -> Any:
    """Return the strict-JSON normalization used by DistQLDPC bindings."""

    return json.loads(
        json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ),
    )


def _canonical_sha256(value: Any) -> str:
    encoded = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def _sha256(value: Any, label: str) -> str:
    if not isinstance(value, str) or _SHA256_RE.fullmatch(value) is None:
        raise ValueError(f"{label} must be a lowercase SHA256 digest")
    return value


def _nonempty_string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{label} must be a non-empty string")
    return value


def _positive_int(value: Any, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        raise ValueError(f"{label} must be a positive integer")
    return value


def _report_sha256(report: Mapping[str, Any] | None, label: str) -> str | None:
    if report is None:
        return None
    if not isinstance(report, Mapping):
        raise ValueError(f"{label} must be a mapping or null")
    return _sha256(report.get("report_sha256"), f"{label}.report_sha256")


def _admissibility_checkpoint_fields(
    candidate: Mapping[str, Any],
) -> dict[str, str]:
    raw = candidate.get("admissibility")
    if raw is None:
        target = candidate.get("target")
        target_mode = candidate.get("target_mode")
        if target_mode is None and isinstance(target, Mapping):
            target_mode = target.get("mode")
        if target_mode == TARGET_MODE_SCALAR_13_INCLUSIVE:
            raise ValueError("FOM13 checkpoint lacks CSS weight-6 policy")
        return {}
    binding = validate_css_w6_admissibility_binding(raw)
    return {"admissibility_binding_sha256": binding["binding_sha256"]}


def stage3_distqldpc_checkpoint_identity(
    candidate: Mapping[str, Any],
    *,
    cardinality_mode: str,
    coverage_mode: str,
    logical_detector: Mapping[str, Any],
    translation_symmetry: Mapping[str, Any] | None,
    construction_symmetry: Mapping[str, Any] | None,
    xz_sector_isometry: Mapping[str, Any] | None,
) -> dict[str, Any]:
    """Strictly rebuild the identity emitted by the Stage-3 screen.

    This intentionally mirrors
    :func:`scripts.screen_frontier_sat.distqldpc_stage3_checkpoint_identity`
    without importing a CLI module into the evaluation package.
    """

    if cardinality_mode not in DISTQLDPC_CARDINALITY_MODES:
        raise ValueError("unsupported DistQLDPC cardinality mode")
    if coverage_mode not in SUPPORTED_COVERAGE_MODES:
        raise ValueError("unsupported Stage-3 coverage mode")
    if not isinstance(candidate, Mapping):
        raise ValueError("candidate must be a mapping")
    if not isinstance(logical_detector, Mapping):
        raise ValueError("logical_detector must be a mapping")
    candidate_digest = _nonempty_string(
        candidate.get("canonical_digest"), "candidate canonical digest",
    )
    detector_sha256 = _sha256(
        logical_detector.get("report_sha256"),
        "logical_detector.report_sha256",
    )
    target = candidate.get("target")
    if target is not None and not isinstance(target, Mapping):
        raise ValueError("candidate target must be a mapping or null")
    if translation_symmetry is not None and not isinstance(
        translation_symmetry, Mapping,
    ):
        raise ValueError("translation_symmetry must be a mapping or null")
    identity = {
        "stage3_gate": STAGE3_GATE,
        "candidate_digest": candidate_digest,
        "target_mode": candidate.get("target_mode"),
        "target_binding_sha256": (
            target.get("binding_sha256")
            if isinstance(target, Mapping)
            else None
        ),
        **_admissibility_checkpoint_fields(candidate),
        "phase": DISTQLDPC_STAGE3_PHASE,
        "lower_backend": DISTQLDPC_LOWER_BACKEND,
        "cardinality_mode": cardinality_mode,
        "coverage_mode": coverage_mode,
        "logical_detector_sha256": detector_sha256,
        "translation_symmetry": (
            None
            if translation_symmetry is None
            else dict(translation_symmetry)
        ),
        "construction_symmetry_sha256": _report_sha256(
            construction_symmetry, "construction_symmetry",
        ),
        "xz_sector_isometry_sha256": _report_sha256(
            xz_sector_isometry, "xz_sector_isometry",
        ),
    }
    return _canonical_json(identity)


def replay_stage3_distqldpc_decisions(
    records: Any,
    *,
    candidate: Mapping[str, Any],
    coverage_mode: str,
    logical_detector: Mapping[str, Any],
    translation_symmetry: Mapping[str, Any] | None,
    construction_symmetry: Mapping[str, Any] | None,
    xz_sector_isometry: Mapping[str, Any] | None,
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
    max_weight: int,
    require_lower: bool = True,
    allow_empty: bool = False,
) -> dict[str, Any]:
    """Replay stored Stage-3 XZ decisions and return a fail-closed report."""

    failures: list[str] = []
    recovered: list[dict[str, Any]] = []
    modes: list[str] = []
    distances: set[int] = set()
    if isinstance(max_weight, bool) or not isinstance(max_weight, int):
        failures.append("max_weight must be an integer")
    if not isinstance(records, list):
        failures.append("DistQLDPC decisions must be a list")
        records = []
    if not records and not allow_empty:
        failures.append("DistQLDPC decisions are empty")

    for index, raw in enumerate(records):
        prefix = f"decision[{index}]"
        if not isinstance(raw, Mapping):
            failures.append(f"{prefix} is not a mapping")
            continue
        wrapper = dict(raw)
        mode = wrapper.get("cardinality_mode")
        evidence = wrapper.get("solver_evidence")
        checkpoint_identity = wrapper.get("checkpoint_identity")
        if mode not in DISTQLDPC_CARDINALITY_MODES:
            failures.append(f"{prefix} has an unsupported cardinality mode")
            continue
        if mode in modes:
            failures.append(f"{prefix} duplicates cardinality mode {mode}")
            continue
        modes.append(mode)
        if (
            wrapper.get("sector") != "XZ"
            or wrapper.get("partition_index") is not None
            or wrapper.get("anchor_cube") is not None
        ):
            failures.append(f"{prefix} is not a global unanchored XZ decision")
            continue
        if not isinstance(evidence, Mapping):
            failures.append(f"{prefix} lacks solver evidence")
            continue
        if not isinstance(checkpoint_identity, Mapping):
            failures.append(f"{prefix} lacks a checkpoint identity")
            continue
        try:
            expected_identity = stage3_distqldpc_checkpoint_identity(
                candidate,
                cardinality_mode=mode,
                coverage_mode=coverage_mode,
                logical_detector=logical_detector,
                translation_symmetry=translation_symmetry,
                construction_symmetry=construction_symmetry,
                xz_sector_isometry=xz_sector_isometry,
            )
        except (KeyError, TypeError, ValueError) as exc:
            failures.append(f"{prefix} identity reconstruction failed: {exc}")
            continue
        if _canonical_json(checkpoint_identity) != expected_identity:
            failures.append(f"{prefix} checkpoint identity does not replay")
            continue
        verifier = (
            verify_distqldpc_lower_evidence
            if require_lower
            else verify_distqldpc_exact_evidence
        )
        try:
            evidence_failures = verifier(
                evidence,
                hx,
                hz,
                lx,
                lz,
                max_weight=max_weight,
                cardinality_mode=mode,
                expected_checkpoint_identity=expected_identity,
            )
        except (KeyError, TypeError, ValueError) as exc:
            failures.append(f"{prefix} official replay raised: {exc}")
            continue
        failures.extend(
            f"{prefix}: {failure}" for failure in evidence_failures
        )
        distance = evidence.get("exact_distance")
        if isinstance(distance, bool) or not isinstance(distance, int):
            failures.append(f"{prefix} lacks an integer exact distance")
            continue
        if not evidence_failures:
            distances.add(distance)
            recovered.append(wrapper)

    if len(distances) > 1:
        failures.append("DistQLDPC decisions disagree on exact distance")
    verified = not failures and (bool(recovered) or allow_empty)
    exact_distance = next(iter(distances)) if len(distances) == 1 else None
    return {
        "verified": verified,
        "failures": failures,
        "decisions": recovered if verified else [],
        "cardinality_modes": modes if verified else [],
        "exact_distance": exact_distance if verified else None,
    }


def certificate_bound_distqldpc_checkpoint_identity(
    *,
    certificate_type: str,
    certificate_sha256: str,
    candidate: Mapping[str, Any],
    cardinality_mode: str,
    required_distance: int,
    exact_distance: int,
    max_weight: int,
    logical_detector: Mapping[str, Any],
    translation_symmetry: Mapping[str, Any] | None,
    xz_sector_isometry: Mapping[str, Any] | None,
    source_stage3_checkpoint_identity: Mapping[str, Any],
) -> dict[str, Any]:
    """Construct the distinct identity used by a Stage-4/Final fresh rerun."""

    certificate_type = _nonempty_string(certificate_type, "certificate_type")
    certificate_sha256 = _sha256(
        certificate_sha256, "certificate_sha256",
    )
    if cardinality_mode not in DISTQLDPC_CARDINALITY_MODES:
        raise ValueError("unsupported DistQLDPC cardinality mode")
    required_distance = _positive_int(required_distance, "required_distance")
    exact_distance = _positive_int(exact_distance, "exact_distance")
    if exact_distance < required_distance:
        raise ValueError("exact_distance is below required_distance")
    if (
        isinstance(max_weight, bool)
        or not isinstance(max_weight, int)
        or max_weight != exact_distance - 1
    ):
        raise ValueError("max_weight must equal exact_distance - 1")
    if not isinstance(candidate, Mapping):
        raise ValueError("candidate must be a mapping")
    candidate_digest = _nonempty_string(
        candidate.get("canonical_digest"), "candidate canonical digest",
    )
    if not isinstance(logical_detector, Mapping):
        raise ValueError("logical_detector must be a mapping")
    detector_sha256 = _sha256(
        logical_detector.get("report_sha256"),
        "logical_detector.report_sha256",
    )
    if not isinstance(source_stage3_checkpoint_identity, Mapping):
        raise ValueError("source Stage-3 checkpoint identity must be a mapping")
    source_identity = _canonical_json(source_stage3_checkpoint_identity)
    if (
        source_identity.get("stage3_gate") != STAGE3_GATE
        or source_identity.get("phase") != DISTQLDPC_STAGE3_PHASE
        or source_identity.get("lower_backend") != DISTQLDPC_LOWER_BACKEND
        or source_identity.get("candidate_digest") != candidate_digest
        or source_identity.get("cardinality_mode") != cardinality_mode
        or source_identity.get("logical_detector_sha256") != detector_sha256
    ):
        raise ValueError("source Stage-3 checkpoint identity is inconsistent")
    target = candidate.get("target")
    if target is not None and not isinstance(target, Mapping):
        raise ValueError("candidate target must be a mapping or null")
    if translation_symmetry is not None and not isinstance(
        translation_symmetry, Mapping,
    ):
        raise ValueError("translation_symmetry must be a mapping or null")
    identity = {
        "certificate_type": certificate_type,
        "certificate_sha256": certificate_sha256,
        "candidate_digest": candidate_digest,
        "phase": DISTQLDPC_CERTIFICATE_REPLAY_PHASE,
        "lower_backend": DISTQLDPC_LOWER_BACKEND,
        "cardinality_mode": cardinality_mode,
        "target_mode": candidate.get("target_mode"),
        "target_binding_sha256": (
            target.get("binding_sha256")
            if isinstance(target, Mapping)
            else None
        ),
        **_admissibility_checkpoint_fields(candidate),
        "required_distance": required_distance,
        "exact_distance": exact_distance,
        "max_weight": max_weight,
        "logical_detector_sha256": detector_sha256,
        "translation_symmetry_sha256": (
            None
            if translation_symmetry is None
            else _canonical_sha256(translation_symmetry)
        ),
        "xz_sector_isometry_sha256": _report_sha256(
            xz_sector_isometry, "xz_sector_isometry",
        ),
        "source_stage3_checkpoint_identity_sha256": _canonical_sha256(
            source_identity,
        ),
    }
    normalized = _canonical_json(identity)
    if normalized == source_identity:
        raise ValueError("certificate replay reused the Stage-3 identity")
    return normalized


def rerun_certificate_bound_distqldpc_lower(
    source_decision: Mapping[str, Any],
    *,
    certificate_type: str,
    certificate_sha256: str,
    candidate: Mapping[str, Any],
    coverage_mode: str,
    required_distance: int,
    exact_distance: int,
    logical_detector: Mapping[str, Any],
    translation_symmetry: Mapping[str, Any] | None,
    construction_symmetry: Mapping[str, Any] | None,
    xz_sector_isometry: Mapping[str, Any] | None,
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
    timeout: float,
    binary: Path | str = DEFAULT_DISTQLDPC_EXE,
    checkpoint_path: Path | str | None = None,
    progress_path: Path | str | None = None,
    resume: bool = True,
    solver: DistQLDPCSolver | None = None,
) -> dict[str, Any]:
    """Independently rerun one stored lower proof under a certificate identity."""

    failures: list[str] = []
    if not isinstance(source_decision, Mapping):
        return {
            "verified": False,
            "failures": ["source decision is not a mapping"],
            "checkpoint_identity": None,
            "solver_evidence": None,
        }
    max_weight = exact_distance - 1 if isinstance(exact_distance, int) else -1
    stored = replay_stage3_distqldpc_decisions(
        [source_decision],
        candidate=candidate,
        coverage_mode=coverage_mode,
        logical_detector=logical_detector,
        translation_symmetry=translation_symmetry,
        construction_symmetry=construction_symmetry,
        xz_sector_isometry=xz_sector_isometry,
        hx=hx,
        hz=hz,
        lx=lx,
        lz=lz,
        max_weight=max_weight,
        require_lower=True,
    )
    if not stored["verified"]:
        return {
            "verified": False,
            "failures": [
                f"stored Stage-3 replay: {failure}"
                for failure in stored["failures"]
            ],
            "checkpoint_identity": None,
            "solver_evidence": None,
        }
    if stored["exact_distance"] != exact_distance:
        return {
            "verified": False,
            "failures": ["stored Stage-3 exact distance does not match certificate"],
            "checkpoint_identity": None,
            "solver_evidence": None,
        }
    cardinality_mode = source_decision.get("cardinality_mode")
    source_identity = source_decision.get("checkpoint_identity")
    try:
        replay_identity = certificate_bound_distqldpc_checkpoint_identity(
            certificate_type=certificate_type,
            certificate_sha256=certificate_sha256,
            candidate=candidate,
            cardinality_mode=cardinality_mode,
            required_distance=required_distance,
            exact_distance=exact_distance,
            max_weight=max_weight,
            logical_detector=logical_detector,
            translation_symmetry=translation_symmetry,
            xz_sector_isometry=xz_sector_isometry,
            source_stage3_checkpoint_identity=source_identity,
        )
    except (KeyError, TypeError, ValueError) as exc:
        return {
            "verified": False,
            "failures": [f"certificate replay identity is invalid: {exc}"],
            "checkpoint_identity": None,
            "solver_evidence": None,
        }
    try:
        hard_timeout = float(timeout)
        if not math.isfinite(hard_timeout) or hard_timeout <= 0:
            raise ValueError("timeout must be positive and finite")
        run_solver = solve_css_distance_distqldpc_lower if solver is None else solver
        evidence = run_solver(
            hx,
            hz,
            lx,
            lz,
            max_weight=max_weight,
            timeout=hard_timeout,
            binary=binary,
            cardinality_mode=cardinality_mode,
            checkpoint_path=checkpoint_path,
            progress_path=progress_path,
            checkpoint_identity=replay_identity,
            resume=resume,
        )
    except (OSError, RuntimeError, TypeError, ValueError) as exc:
        return {
            "verified": False,
            "failures": [f"fresh DistQLDPC rerun failed: {exc}"],
            "checkpoint_identity": replay_identity,
            "solver_evidence": None,
        }
    if not isinstance(evidence, Mapping):
        return {
            "verified": False,
            "failures": ["fresh DistQLDPC rerun returned no evidence"],
            "checkpoint_identity": replay_identity,
            "solver_evidence": None,
        }
    try:
        exact_failures = verify_distqldpc_exact_evidence(
            evidence,
            hx,
            hz,
            lx,
            lz,
            max_weight=max_weight,
            cardinality_mode=cardinality_mode,
            expected_checkpoint_identity=replay_identity,
        )
        lower_failures = verify_distqldpc_lower_evidence(
            evidence,
            hx,
            hz,
            lx,
            lz,
            max_weight=max_weight,
            cardinality_mode=cardinality_mode,
            expected_checkpoint_identity=replay_identity,
        )
    except (KeyError, TypeError, ValueError) as exc:
        exact_failures = [f"official fresh replay raised: {exc}"]
        lower_failures = []
    failures.extend(f"exact replay: {item}" for item in exact_failures)
    failures.extend(f"lower replay: {item}" for item in lower_failures)
    distance = evidence.get("exact_distance")
    if distance != exact_distance or isinstance(distance, bool):
        failures.append("fresh exact distance does not match certificate")
    return {
        "verified": not failures,
        "failures": failures,
        "lower_bound_backend": DISTQLDPC_LOWER_BACKEND,
        "cardinality_mode": cardinality_mode,
        "max_weight": max_weight,
        "exact_distance": distance if not isinstance(distance, bool) else None,
        "checkpoint_identity": replay_identity,
        "source_stage3_checkpoint_identity_sha256": _canonical_sha256(
            source_identity,
        ),
        "solver_evidence": dict(evidence),
    }


__all__ = [
    "DISTQLDPC_CERTIFICATE_REPLAY_PHASE",
    "DISTQLDPC_LOWER_BACKEND",
    "DISTQLDPC_STAGE3_PHASE",
    "STAGE3_GATE",
    "SUPPORTED_COVERAGE_MODES",
    "certificate_bound_distqldpc_checkpoint_identity",
    "replay_stage3_distqldpc_decisions",
    "rerun_certificate_bound_distqldpc_lower",
    "stage3_distqldpc_checkpoint_identity",
]
