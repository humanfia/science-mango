"""Exact CSS BB certificates with a typed DistQLDPC lower proof.

This certificate type is deliberately distinct from the sector-SAT type.  A
stored pinned DistQLDPC exact decision proves the global ``XZ`` lower bound;
an algebraically replayable anchored SAT witness proves the matching upper
bound.  Building is static.  Verification reruns DistQLDPC exactly once under
a new identity bound to the completed certificate.
"""

from __future__ import annotations

import math
import platform
import re
import time
from pathlib import Path
from typing import Any, Mapping

from evaluation import distqldpc_sector_adapter as _adapter
from evaluation import sector_certificate as _sector
from evaluation.certificate import (
    _certificate_sha256,
    _file_sha256,
    _package_version,
)
from evaluation.challenge_gate import evaluate_challenge_gate
from evaluation.distance_distqldpc import DEFAULT_DISTQLDPC_EXE
from evaluation.failure_disposition import incomplete_result_disposition
from evaluation.target_policy import classify_target_win


SCHEMA_VERSION = 1
CERTIFICATE_TYPE = "qldpc-css-bb-sector-distqldpc-exact"
FORMULATION = "css-bb-exact-distance-distqldpc-lower-sat-upper-v1"
PROOF_TYPE = "qldpc-css-sector-distqldpc-exact-proof-v1"
FINAL_GATE = "qldpc-challenge-final-distqldpc-extension"
LEGACY_PROOF_CHECK = "typed_exact_sector_sat_proof"
TYPED_PROOF_CHECK = "typed_exact_sector_distqldpc_proof"
_SHA256_RE = re.compile(r"[0-9a-f]{64}")


def _sha256(value: Any, label: str) -> str:
    if not isinstance(value, str) or _SHA256_RE.fullmatch(value) is None:
        raise ValueError(f"{label} must be a lowercase SHA256 digest")
    return value


def _candidate_context(claim: Mapping[str, Any]) -> dict[str, Any]:
    if not isinstance(claim, Mapping):
        raise ValueError("claim must be an object")
    if claim.get("C_terms") or claim.get("D_terms"):
        raise ValueError("typed DistQLDPC certificates support CSS claims only")
    if isinstance(claim.get("construction"), Mapping):
        raise ValueError("typed DistQLDPC certificates currently require CSS BB")
    clean_claim = _sector._clean_claim(claim)
    code, hx, hz, lx, lz = _sector._matrices(clean_claim)
    n = int(code.num_qudits)
    k = n - _sector._rank_f2(hx) - _sector._rank_f2(hz)
    if (
        k <= 0
        or int(code.dimension) != k
        or len(lx) != k
        or len(lz) != k
        or clean_claim.get("n") != n
        or clean_claim.get("k") != k
    ):
        raise ValueError("reconstructed CSS BB parameters do not match the claim")
    selected_mode, selected_target, required = _sector._claim_target_context(
        clean_claim,
        n=n,
        k=k,
    )
    if clean_claim.get("required_distance", required) != required:
        raise ValueError("required_distance does not match the target binding")
    admissibility_report = _sector._claim_admissibility_context(
        clean_claim,
        selected_mode=selected_mode,
        hx=hx,
        hz=hz,
    )
    clean_claim["required_distance"] = required
    if selected_target is not None:
        clean_claim.update(_sector._target_metadata(selected_target))
    return {
        "claim": clean_claim,
        "code": code,
        "hx": hx,
        "hz": hz,
        "lx": lx,
        "lz": lz,
        "n": n,
        "k": k,
        "target_mode": selected_mode,
        "target": selected_target,
        "required_distance": required,
        "admissibility_report": admissibility_report,
    }


def _fresh_reports(
    context: Mapping[str, Any],
    request: Mapping[str, Any],
) -> tuple[dict[str, Any], dict[str, Any], tuple[int, ...]]:
    xz_isometry, proof_sectors = _sector._xz_isometry_context(
        request,
        context["claim"],
        hx=context["hx"],
        hz=context["hz"],
    )
    if xz_isometry is None or proof_sectors != ("X",):
        raise ValueError("a fresh verified X/Z sector isometry is required")
    detector, translation, anchors = _sector._coverage_context(
        request,
        context["claim"],
        hx=context["hx"],
        hz=context["hz"],
        lx=context["lx"],
        lz=context["lz"],
    )
    if translation is None or not anchors:
        raise ValueError("a fresh verified translation anchor cover is required")
    if request.get("anchor_cover_cubes") is not None:
        raise ValueError("DistQLDPC global lower proof cannot carry anchor cubes")
    return detector, translation, anchors


def _replay_one_lower(
    wrapper: Mapping[str, Any],
    *,
    candidate: Mapping[str, Any],
    requested_coverage_mode: str,
    detector: Mapping[str, Any],
    translation: Mapping[str, Any],
    xz_isometry: Mapping[str, Any],
    context: Mapping[str, Any],
    max_weight: int,
) -> dict[str, Any]:
    kwargs = {
        "candidate": candidate,
        "coverage_mode": requested_coverage_mode,
        "logical_detector": detector,
        "translation_symmetry": translation,
        "construction_symmetry": None,
        "xz_sector_isometry": xz_isometry,
        "hx": context["hx"],
        "hz": context["hz"],
        "lx": context["lx"],
        "lz": context["lz"],
        "max_weight": max_weight,
    }
    exact = _adapter.replay_stage3_distqldpc_decisions(
        [wrapper],
        require_lower=False,
        **kwargs,
    )
    lower = _adapter.replay_stage3_distqldpc_decisions(
        [wrapper],
        require_lower=True,
        **kwargs,
    )
    if (
        exact.get("verified") is not True
        or lower.get("verified") is not True
        or exact.get("decisions") != lower.get("decisions")
        or exact.get("exact_distance") != lower.get("exact_distance")
        or exact.get("exact_distance") is None
    ):
        failures = [
            *[f"exact: {item}" for item in exact.get("failures", [])],
            *[f"lower: {item}" for item in lower.get("failures", [])],
        ]
        detail = "; ".join(failures) or "exact/lower replay mismatch"
        raise ValueError(f"stored DistQLDPC decision does not replay: {detail}")
    recovered = exact["decisions"][0]
    return {
        "wrapper": recovered,
        "distance": int(exact["exact_distance"]),
        "cardinality_mode": str(recovered["cardinality_mode"]),
        "stage3_checkpoint_identity": dict(recovered["checkpoint_identity"]),
        "stage3_checkpoint_identity_sha256": _sector._canonical_sha256(
            recovered["checkpoint_identity"],
        ),
    }


def _stage3_context(claim: Mapping[str, Any]) -> dict[str, Any]:
    request = _sector._request(claim)
    context = _candidate_context(claim)
    required = context["required_distance"]
    requested_mode = request.get("requested_coverage_mode")
    if (
        request.get("stage3_status") != "EXACT_PROVEN"
        or request.get("requested_lower_backend") != "distqldpc"
        or request.get("lower_bound_backend") != "distqldpc"
        or request.get("coverage_mode") != "global"
        or requested_mode not in _adapter.SUPPORTED_COVERAGE_MODES
        or request.get("lower_bound_threshold") != required - 1
        or request.get("distqldpc_conflict") is not False
        or request.get("distqldpc_conflict_details") not in (None, [])
        or request.get("low_witnesses") != []
    ):
        raise ValueError("Stage-3 DistQLDPC exact metadata is incomplete")
    stage3_artifact_sha256 = _sha256(
        request.get("stage3_artifact_sha256"),
        "stage3_artifact_sha256",
    )
    if not _sector._target_metadata_matches(request, context["target"]):
        raise ValueError("Stage-3 target metadata does not replay")
    if context["admissibility_report"] is not None and (
        request.get("admissibility") != context["claim"].get("admissibility")
        or request.get("admissibility_report")
        != context["admissibility_report"]
    ):
        raise ValueError("Stage-3 admissibility metadata does not replay")
    detector, translation, anchors = _fresh_reports(context, request)
    xz_isometry = dict(request["xz_sector_isometry"])
    selected = request.get("lower_bound_decisions")
    exact_records = request.get("distqldpc_exact_decisions")
    lower_records = request.get("distqldpc_lower_decisions")
    if (
        not isinstance(selected, list)
        or len(selected) != 1
        or not isinstance(selected[0], Mapping)
        or exact_records != selected
        or lower_records != selected
    ):
        raise ValueError("Stage-3 must select one identical XZ exact/lower wrapper")
    replay = _replay_one_lower(
        selected[0],
        candidate=context["claim"],
        requested_coverage_mode=str(requested_mode),
        detector=detector,
        translation=translation,
        xz_isometry=xz_isometry,
        context=context,
        max_weight=required - 1,
    )
    distance = replay["distance"]
    if (
        distance != required
        or request.get("distqldpc_exact_distances") != [distance]
    ):
        raise ValueError("Stage-3 exact distance does not match the target layer")
    witness = request.get("upper_witness")
    if (
        not isinstance(witness, Mapping)
        or witness.get("sector") != "X"
        or not _sector._valid_upper_witness(
            witness,
            distance=distance,
            hx=context["hx"],
            hz=context["hz"],
            lx=context["lx"],
            lz=context["lz"],
            expected_anchors=anchors,
        )
    ):
        raise ValueError("Stage-3 anchored weight-d SAT upper witness is invalid")
    return {
        **context,
        **replay,
        "requested_coverage_mode": str(requested_mode),
        "detector": detector,
        "translation": translation,
        "anchors": anchors,
        "xz_isometry": xz_isometry,
        "upper_witness": dict(witness),
        "stage3_artifact_sha256": stage3_artifact_sha256,
    }


def _proof_payload(context: Mapping[str, Any]) -> dict[str, Any]:
    distance = int(context["distance"])
    proof: dict[str, Any] = {
        "schema_version": 1,
        "proof_type": PROOF_TYPE,
        "exact": True,
        **_sector._target_metadata(context["target"]),
        "required_distance": int(context["required_distance"]),
        "lower_bound_backend": "distqldpc",
        "requested_lower_backend": "distqldpc",
        "coverage_mode": "global",
        "requested_coverage_mode": context["requested_coverage_mode"],
        "lower_bound_threshold": distance - 1,
        "lower_bound": distance,
        "upper_bound": distance,
        "distance": distance,
        "expected_lower_decisions": 1,
        "completed_lower_decisions": 1,
        "expected_lower_partitions": 1,
        "completed_lower_partitions": 1,
        "lower_bound_decisions": [dict(context["wrapper"])],
        "distqldpc_exact_distances": [distance],
        "cardinality_mode": context["cardinality_mode"],
        "source_stage3_status": "EXACT_PROVEN",
        "source_stage3_artifact_sha256": context["stage3_artifact_sha256"],
        "source_stage3_checkpoint_identity_sha256": (
            context["stage3_checkpoint_identity_sha256"]
        ),
        "upper_witness": dict(context["upper_witness"]),
        "logical_detector": dict(context["detector"]),
        "translation_symmetry": dict(context["translation"]),
        "construction_symmetry": None,
        "xz_sector_isometry": dict(context["xz_isometry"]),
        "anchor_indices": list(context["anchors"]),
        "anchor_cover_cubes": None,
    }
    if context["admissibility_report"] is not None:
        proof["admissibility"] = dict(context["claim"]["admissibility"])
        proof["admissibility_report"] = dict(
            context["admissibility_report"],
        )
    proof["proof_sha256"] = _sector._canonical_sha256(proof)
    return proof


def validate_distqldpc_exact_proof(row: Mapping[str, Any]) -> dict[str, Any]:
    """Strictly replay a packaged proof without launching DistQLDPC."""

    context = _candidate_context(row)
    proof = row.get("exact_distance_proof")
    if not isinstance(proof, Mapping):
        raise ValueError("exact_distance_proof is missing")
    unsigned = dict(proof)
    proof_sha256 = unsigned.pop("proof_sha256", None)
    if proof_sha256 != _sector._canonical_sha256(unsigned):
        raise ValueError("typed DistQLDPC proof hash is invalid")
    distance = row.get("d")
    required = context["required_distance"]
    if (
        isinstance(distance, bool)
        or not isinstance(distance, int)
        or distance < required
        or proof.get("schema_version") != 1
        or proof.get("proof_type") != PROOF_TYPE
        or proof.get("exact") is not True
        or proof.get("required_distance") != required
        or proof.get("lower_bound_backend") != "distqldpc"
        or proof.get("requested_lower_backend") != "distqldpc"
        or proof.get("coverage_mode") != "global"
        or proof.get("requested_coverage_mode")
        not in _adapter.SUPPORTED_COVERAGE_MODES
        or proof.get("lower_bound_threshold") != distance - 1
        or proof.get("lower_bound") != distance
        or proof.get("upper_bound") != distance
        or proof.get("distance") != distance
        or proof.get("distqldpc_exact_distances") != [distance]
        or proof.get("source_stage3_status") != "EXACT_PROVEN"
        or proof.get("construction_symmetry") is not None
        or proof.get("anchor_cover_cubes") is not None
        or any(
            proof.get(field) != 1
            for field in (
                "expected_lower_decisions",
                "completed_lower_decisions",
                "expected_lower_partitions",
                "completed_lower_partitions",
            )
        )
        or not _sector._target_metadata_matches(proof, context["target"])
    ):
        raise ValueError("typed DistQLDPC proof metadata is inconsistent")
    _sha256(
        proof.get("source_stage3_artifact_sha256"),
        "source_stage3_artifact_sha256",
    )
    if context["admissibility_report"] is not None and (
        proof.get("admissibility") != context["claim"].get("admissibility")
        or proof.get("admissibility_report") != context["admissibility_report"]
    ):
        raise ValueError("typed proof admissibility metadata does not replay")
    lower = proof.get("lower_bound_decisions")
    if (
        not isinstance(lower, list)
        or len(lower) != 1
        or not isinstance(lower[0], Mapping)
    ):
        raise ValueError("typed proof must contain one XZ lower decision")
    replay_request = {
        "coverage_mode": "global",
        "lower_bound_decisions": lower,
        "logical_detector": proof.get("logical_detector"),
        "translation_symmetry": proof.get("translation_symmetry"),
        "construction_symmetry": None,
        "use_translation_anchors": True,
        "use_construction_anchors": False,
        "xz_sector_isometry": proof.get("xz_sector_isometry"),
        "anchor_cover_cubes": None,
    }
    detector, translation, anchors = _fresh_reports(context, replay_request)
    xz_isometry = dict(replay_request["xz_sector_isometry"])
    if proof.get("anchor_indices") != list(anchors):
        raise ValueError("typed proof anchor indices do not replay")
    replay = _replay_one_lower(
        lower[0],
        candidate=context["claim"],
        requested_coverage_mode=str(proof["requested_coverage_mode"]),
        detector=detector,
        translation=translation,
        xz_isometry=xz_isometry,
        context=context,
        max_weight=distance - 1,
    )
    if (
        replay["distance"] != distance
        or replay["cardinality_mode"] != proof.get("cardinality_mode")
        or replay["stage3_checkpoint_identity_sha256"]
        != proof.get("source_stage3_checkpoint_identity_sha256")
    ):
        raise ValueError("typed proof lower decision binding is inconsistent")
    witness = proof.get("upper_witness")
    if (
        not isinstance(witness, Mapping)
        or witness.get("sector") != "X"
        or not _sector._valid_upper_witness(
            witness,
            distance=distance,
            hx=context["hx"],
            hz=context["hz"],
            lx=context["lx"],
            lz=context["lz"],
            expected_anchors=anchors,
        )
    ):
        raise ValueError("typed proof anchored SAT upper witness is invalid")
    target_win = classify_target_win(
        context["n"],
        context["k"],
        distance,
        context["target_mode"],
    )
    expected_fom = context["k"] * distance * distance / context["n"]
    if (
        target_win.get("passed") is not True
        or row.get("d_is_exact") is not True
        or not isinstance(row.get("fom"), (int, float))
        or not math.isclose(
            float(row["fom"]), expected_fom, rel_tol=0.0, abs_tol=1e-9,
        )
    ):
        raise ValueError("typed proof target/FOM metadata is inconsistent")
    return {
        **context,
        **replay,
        "proof": dict(proof),
        "distance": distance,
        "detector": detector,
        "translation": translation,
        "anchors": anchors,
        "xz_isometry": xz_isometry,
        "upper_witness": dict(witness),
        "target_win": target_win,
        "fom": expected_fom,
    }


def evaluate_distqldpc_final_gate(
    row: dict[str, Any],
    *,
    known_answer_artifact: Path | str,
) -> dict[str, Any]:
    """Reuse every base final-gate check, replacing only proof dispatch."""

    base = evaluate_challenge_gate(
        row,
        known_answer_artifact=known_answer_artifact,
    )
    checks = dict(base.get("checks") or {})
    failures = list(base.get("failures") or [])
    legacy_present = LEGACY_PROOF_CHECK in checks
    legacy_result = checks.pop(LEGACY_PROOF_CHECK, None)
    failures = [item for item in failures if item != LEGACY_PROOF_CHECK]
    typed_failure: str | None = None
    try:
        validate_distqldpc_exact_proof(row)
        typed_valid = True
    except (KeyError, TypeError, ValueError) as exc:
        typed_valid = False
        typed_failure = str(exc)
    transparent = bool(
        legacy_present
        and isinstance(row.get("exact_distance_proof"), Mapping)
        and row["exact_distance_proof"].get("proof_type") == PROOF_TYPE
    )
    checks[TYPED_PROOF_CHECK] = typed_valid
    checks["typed_proof_dispatch_transparent"] = transparent
    if not typed_valid:
        failures.append(TYPED_PROOF_CHECK)
    if not transparent:
        failures.append("typed_proof_dispatch_transparent")
    result = dict(base)
    result.update({
        "gate": FINAL_GATE,
        "accepted": not failures,
        "checks": checks,
        "failures": failures,
        "proof_dispatch": {
            "base_gate": base.get("gate"),
            "replaced_check": LEGACY_PROOF_CHECK,
            "base_check_result": legacy_result,
            "replacement_check": TYPED_PROOF_CHECK,
            "proof_type": PROOF_TYPE,
            "typed_failure": typed_failure,
        },
    })
    return result


def build_distqldpc_sector_certificate(
    claim: dict[str, Any],
    *,
    known_answer_artifact: Path | str,
) -> dict[str, Any]:
    """Statically seal an exact certificate; this function runs no solver."""

    context = _stage3_context(claim)
    proof = _proof_payload(context)
    distance = int(context["distance"])
    novelty = _sector.check_code_novelty(context["code"], code_type="css")
    normalized_claim = {
        **context["claim"],
        "n": context["n"],
        "k": context["k"],
        "d": distance,
        "fom": context["k"] * distance * distance / context["n"],
        "d_is_exact": True,
        "structural_novelty": novelty,
        "exact_distance_proof": proof,
    }
    final_gate = evaluate_distqldpc_final_gate(
        normalized_claim,
        known_answer_artifact=known_answer_artifact,
    )
    target_win = classify_target_win(
        context["n"],
        context["k"],
        distance,
        context["target_mode"],
    )
    passed = bool(
        target_win.get("passed") is True
        and final_gate.get("accepted") is True
    )
    certificate: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "certificate_type": CERTIFICATE_TYPE,
        "formulation": FORMULATION,
        "claim": normalized_claim,
        **_sector._target_metadata(context["target"]),
        "target_gate": {
            "mode": context["target_mode"],
            "required_distance": context["required_distance"],
            "binding_sha256": (
                None
                if context["target"] is None
                else context["target"]["binding_sha256"]
            ),
            "passed": target_win.get("passed") is True,
            "win": target_win,
        },
        "matrix_sha256": {
            "hx": _sector._matrix_sha256(context["hx"]),
            "hz": _sector._matrix_sha256(context["hz"]),
        },
        "known_answer": {
            "artifact_sha256": _file_sha256(known_answer_artifact),
        },
        "lower_proof_backend": {
            "backend": "distqldpc",
            "interface": "evaluation.distance_distqldpc",
            "cardinality_mode": context["cardinality_mode"],
            "build_solver_invocations": 0,
            "verification_replay_required": True,
        },
        "environment": {
            "python": platform.python_version(),
            "numpy": _package_version("numpy"),
            "qldpc": _package_version("qldpc"),
        },
        "distqldpc_exact": {
            "exact": True,
            "lower_bound_backend": "distqldpc",
            "coverage_mode": "global",
            "requested_coverage_mode": context["requested_coverage_mode"],
            "required_distance": context["required_distance"],
            "exact_lower_bound_threshold": distance - 1,
            "expected_lower_decisions": 1,
            "completed_lower_decisions": 1,
            "expected_lower_partitions": 1,
            "completed_lower_partitions": 1,
            "lower_bound": distance,
            "upper_bound": distance,
            "distance": distance,
            "cardinality_mode": context["cardinality_mode"],
            "proof": proof,
        },
        "source_stage3": {
            "gate": _adapter.STAGE3_GATE,
            "status": "EXACT_PROVEN",
            "artifact_sha256": context["stage3_artifact_sha256"],
            "checkpoint_identity_sha256": (
                context["stage3_checkpoint_identity_sha256"]
            ),
        },
        "build": {
            "mode": "static-no-rerun",
            "solver_invocations": 0,
            "independent_replay_complete": False,
        },
        "final_gate": final_gate,
        "passed": passed,
    }
    if not passed:
        certificate["failure_disposition"] = incomplete_result_disposition(
            domain="evidence",
            code="DISTQLDPC_STATIC_CERTIFICATE_REJECTED",
        )
    certificate["certificate_sha256"] = _certificate_sha256(certificate)
    return certificate


def verify_distqldpc_sector_certificate(
    certificate: Mapping[str, Any],
    *,
    known_answer_artifact: Path | str,
    rerun: bool = True,
    timeout: float = 21600,
    binary: Path | str = DEFAULT_DISTQLDPC_EXE,
    checkpoint_path: Path | str | None = None,
    progress_path: Path | str | None = None,
    resume: bool = True,
    distqldpc_solver: Any | None = None,
) -> dict[str, Any]:
    """Strictly replay a certificate and optionally run its fresh lower lane."""

    started = time.monotonic()
    checks: dict[str, bool] = {}
    failures: list[str] = []
    context: dict[str, Any] | None = None
    if not isinstance(certificate, Mapping):
        return {
            "passed": False,
            "replay_complete": False,
            "checks": {"schema": False},
            "failures": ["schema"],
        }
    checks["schema"] = bool(
        certificate.get("schema_version") == SCHEMA_VERSION
        and certificate.get("certificate_type") == CERTIFICATE_TYPE
        and certificate.get("formulation") == FORMULATION
    )
    try:
        checks["certificate_sha256"] = bool(
            certificate.get("certificate_sha256")
            == _certificate_sha256(dict(certificate))
        )
    except (TypeError, ValueError):
        checks["certificate_sha256"] = False
    try:
        checks["known_answer_sha256"] = bool(
            certificate.get("known_answer", {}).get("artifact_sha256")
            == _file_sha256(known_answer_artifact)
        )
    except (AttributeError, OSError, TypeError, ValueError):
        checks["known_answer_sha256"] = False
    claim = certificate.get("claim")
    if isinstance(claim, Mapping):
        try:
            context = validate_distqldpc_exact_proof(claim)
            checks["typed_lower_evidence"] = True
            checks["upper_witness"] = True
        except (KeyError, TypeError, ValueError):
            checks["typed_lower_evidence"] = False
            checks["upper_witness"] = False
    else:
        checks["typed_lower_evidence"] = False
        checks["upper_witness"] = False
    if context is not None:
        proof = context["proof"]
        stored_exact = certificate.get("distqldpc_exact")
        checks["matrix_sha256"] = certificate.get("matrix_sha256") == {
            "hx": _sector._matrix_sha256(context["hx"]),
            "hz": _sector._matrix_sha256(context["hz"]),
        }
        checks["typed_counts"] = bool(
            isinstance(stored_exact, Mapping)
            and stored_exact.get("proof") == proof
            and stored_exact.get("lower_bound_backend") == "distqldpc"
            and stored_exact.get("coverage_mode") == "global"
            and stored_exact.get("requested_coverage_mode")
            == context["proof"]["requested_coverage_mode"]
            and stored_exact.get("required_distance")
            == context["required_distance"]
            and stored_exact.get("exact_lower_bound_threshold")
            == context["distance"] - 1
            and stored_exact.get("cardinality_mode")
            == context["cardinality_mode"]
            and stored_exact.get("distance") == context["distance"]
            and stored_exact.get("lower_bound") == context["distance"]
            and stored_exact.get("upper_bound") == context["distance"]
            and all(
                stored_exact.get(field) == 1
                for field in (
                    "expected_lower_decisions",
                    "completed_lower_decisions",
                    "expected_lower_partitions",
                    "completed_lower_partitions",
                )
            )
        )
        checks["source_stage3_binding"] = certificate.get("source_stage3") == {
            "gate": _adapter.STAGE3_GATE,
            "status": "EXACT_PROVEN",
            "artifact_sha256": proof["source_stage3_artifact_sha256"],
            "checkpoint_identity_sha256": (
                proof["source_stage3_checkpoint_identity_sha256"]
            ),
        }
        checks["lower_backend_metadata"] = (
            certificate.get("lower_proof_backend") == {
                "backend": "distqldpc",
                "interface": "evaluation.distance_distqldpc",
                "cardinality_mode": context["cardinality_mode"],
                "build_solver_invocations": 0,
                "verification_replay_required": True,
            }
        )
        checks["static_build_metadata"] = certificate.get("build") == {
            "mode": "static-no-rerun",
            "solver_invocations": 0,
            "independent_replay_complete": False,
        }
        checks["certificate_target_binding"] = (
            _sector._target_metadata_matches(certificate, context["target"])
        )
        expected_target_gate = {
            "mode": context["target_mode"],
            "required_distance": context["required_distance"],
            "binding_sha256": (
                None
                if context["target"] is None
                else context["target"]["binding_sha256"]
            ),
            "passed": context["target_win"].get("passed") is True,
            "win": context["target_win"],
        }
        checks["target_and_fom"] = bool(
            certificate.get("target_gate") == expected_target_gate
            and math.isclose(
                float(claim.get("fom")),
                float(context["fom"]),
                rel_tol=0.0,
                abs_tol=1e-9,
            )
        )
        final_gate = evaluate_distqldpc_final_gate(
            dict(claim),
            known_answer_artifact=known_answer_artifact,
        )
        checks["final_gate"] = final_gate.get("accepted") is True
        checks["stored_final_gate"] = certificate.get("final_gate") == final_gate
        final_checks = final_gate.get("checks") or {}
        checks["novelty"] = all(
            final_checks.get(name) is True
            for name in (
                "structural_audit_present",
                "structural_audit_reproduced",
                "expanded_registry_novel",
            )
        )
    else:
        checks.update({
            "matrix_sha256": False,
            "typed_counts": False,
            "source_stage3_binding": False,
            "lower_backend_metadata": False,
            "static_build_metadata": False,
            "certificate_target_binding": False,
            "target_and_fom": False,
            "final_gate": False,
            "stored_final_gate": False,
            "novelty": False,
        })
        final_gate = None
    checks["certificate_passed_flag"] = certificate.get("passed") is True
    static_ready = all(value is True for value in checks.values())
    rerun_report: dict[str, Any] | None = None
    if rerun and static_ready and context is not None:
        rerun_report = _adapter.rerun_certificate_bound_distqldpc_lower(
            context["wrapper"],
            certificate_type=CERTIFICATE_TYPE,
            certificate_sha256=str(certificate["certificate_sha256"]),
            candidate=context["claim"],
            coverage_mode=str(context["proof"]["requested_coverage_mode"]),
            required_distance=int(context["required_distance"]),
            exact_distance=int(context["distance"]),
            logical_detector=context["detector"],
            translation_symmetry=context["translation"],
            construction_symmetry=None,
            xz_sector_isometry=context["xz_isometry"],
            hx=context["hx"],
            hz=context["hz"],
            lx=context["lx"],
            lz=context["lz"],
            timeout=timeout,
            binary=binary,
            checkpoint_path=checkpoint_path,
            progress_path=progress_path,
            resume=resume,
            solver=distqldpc_solver,
        )
    checks["distqldpc_rerun"] = bool(
        isinstance(rerun_report, Mapping)
        and rerun_report.get("verified") is True
    )
    replay_complete = checks["distqldpc_rerun"]
    for name, passed in checks.items():
        if passed is not True:
            failures.append(name)
    passed = not failures
    result: dict[str, Any] = {
        "passed": passed,
        "replay_complete": replay_complete,
        "checks": checks,
        "failures": failures,
        "distance": None if context is None else context["distance"],
        "lower_bound_backend": "distqldpc",
        "typed_lower": checks["typed_lower_evidence"],
        "upper": checks["upper_witness"],
        "novelty": checks["novelty"],
        "fom_target": checks["target_and_fom"],
        "distqldpc_decisions_verified": 1 if replay_complete else 0,
        "distqldpc_decisions_total": 1,
        "logical_partitions_verified": 1 if replay_complete else 0,
        "logical_partitions_total": 1,
        "distqldpc_rerun": rerun_report,
        "rerun_elapsed_s": time.monotonic() - started,
        "final_gate": final_gate,
    }
    if not passed:
        result["failure_disposition"] = incomplete_result_disposition(
            domain="solver" if not replay_complete else "evidence",
            code=(
                "DISTQLDPC_REPLAY_INCOMPLETE"
                if not replay_complete
                else "DISTQLDPC_REPLAY_MISMATCH"
            ),
        )
    return result


__all__ = [
    "CERTIFICATE_TYPE",
    "FINAL_GATE",
    "FORMULATION",
    "PROOF_TYPE",
    "TYPED_PROOF_CHECK",
    "build_distqldpc_sector_certificate",
    "evaluate_distqldpc_final_gate",
    "validate_distqldpc_exact_proof",
    "verify_distqldpc_sector_certificate",
]

