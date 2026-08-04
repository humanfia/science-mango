"""Typed exact BB certificates bridged by a dressed 2BGA subsystem bound."""

from __future__ import annotations

import math
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Any, Callable, Mapping

import numpy as np

from evaluation.certificate import (
    _certificate_sha256,
    _file_sha256,
    _validate_solver_workers,
)
from evaluation.challenge_gate import evaluate_challenge_gate
from evaluation.distance_sat import (
    solve_css_sector_sat,
    verify_css_threshold_sat_witness,
)
from evaluation.distance_milp import get_code_matrices
from evaluation.failure_disposition import (
    CANDIDATE_REJECTED,
    incomplete_result_disposition,
    make_failure_disposition,
    validate_failure_disposition,
)
from evaluation.geometry import candidate_geometry
from evaluation.registry import check_code_novelty
from evaluation.twobga_subsystem import (
    derive_twobga_subsystem_problem,
    matrix_sha256,
)
from scripts.screen_frontier_twobga import (
    TWOBGA_EXACT_PROOF_TYPE,
    TWOBGA_PROOF_SECTORS,
    TWOBGA_REQUEST_FIELD,
    _canonical_sha256,
    _complete_unsat,
    _instance_bound,
    _valid_auxiliary_lower,
    _valid_original_counterexample,
    _valid_original_upper,
    validate_twobga_stage3_artifact,
)
from scripts.screen_frontier_candidate import (
    build_candidate_code,
    validate_candidate_parameters,
)
from scripts.screen_frontier_xor import verify_bb_translation_symmetry


SCHEMA_VERSION = 1
CERTIFICATE_TYPE = "qldpc-css-bb-twobga-subsystem-exact"
FORMULATION = "css-bb-exact-via-dressed-twobga-subsystem-v1"
VERIFICATION_CARDINALITY_ENCODING = "seqcounter"
VERIFICATION_SOLVER = "glucose42"
SectorSolver = Callable[..., dict[str, Any]]


def _strict_timeout(value: float, name: str) -> float:
    timeout = float(value)
    if not math.isfinite(timeout) or timeout <= 0:
        raise ValueError(f"{name} must be positive and finite")
    return timeout


def _clean_claim(claim: Mapping[str, Any]) -> dict[str, Any]:
    value = dict(claim)
    value.pop(TWOBGA_REQUEST_FIELD, None)
    value.pop("exact_distance_proof", None)
    for key in (
        "d",
        "fom",
        "d_is_exact",
        "structural_novelty",
        "distance_status",
        "distance_trusted",
        "stage",
        "milp_attempted",
        "milp_details",
        "campaign_audit",
        "campaign_direction_audit",
    ):
        value.pop(key, None)
    return value


def _require_rectangular_twobga_domain(claim: Mapping[str, Any]) -> None:
    """Fail closed outside the rectangular theorem's proven domain."""

    if candidate_geometry(_clean_claim(claim)) is not None:
        raise ValueError(
            "2BGA subsystem certificates do not support twisted-torus geometry"
        )


def _request(claim: Mapping[str, Any]) -> Mapping[str, Any]:
    request = claim.get(TWOBGA_REQUEST_FIELD)
    if (
        not isinstance(request, Mapping)
        or request.get("schema_version") != 1
        or not isinstance(request.get("stage3_artifact"), Mapping)
        or request.get("stage3_artifact_sha256")
        != request["stage3_artifact"].get("artifact_sha256")
    ):
        raise ValueError("claim lacks a valid typed 2BGA certificate request")
    return request


def _checkpoint_for(
    checkpoint_path: Path | str | None,
    label: str,
) -> Path | None:
    if checkpoint_path is None:
        return None
    base = Path(checkpoint_path)
    return base.with_name(f"{base.name}.twobga-{label}.json")


def _upper_wrapper(
    evidence: Mapping[str, Any],
    *,
    anchors: tuple[int, ...],
    required_distance: int,
    hz: np.ndarray,
    lz: np.ndarray,
) -> dict[str, Any]:
    failures = (
        verify_css_threshold_sat_witness(evidence, hz, lz)
        if evidence.get("outcome") == "sat" else []
    )
    return {
        "unit_id": "original-upper-X",
        "domain": "original-code",
        "phase": "upper",
        "sector": "X",
        "max_weight": required_distance,
        "anchor_indices": list(anchors),
        "witness_verified": bool(
            evidence.get("outcome") == "sat" and not failures
        ),
        "witness_failures": failures,
        "solver_evidence": dict(evidence),
    }


def _proof(
    context: Mapping[str, Any],
    upper: Mapping[str, Any],
) -> dict[str, Any]:
    required = int(context["required_distance"])
    proof: dict[str, Any] = {
        "schema_version": 1,
        "proof_type": TWOBGA_EXACT_PROOF_TYPE,
        "exact": True,
        "required_distance": required,
        "distance": required,
        "lower_bound_threshold": required - 1,
        "lower_bound": required,
        "upper_bound": required,
        "theorem_eligibility": dict(context["problem"].report),
        "lower_bound_decisions": [
            dict(item) for item in context["lower_bound_decisions"]
        ],
        "upper_witness": dict(upper),
        "original_logical_detector": dict(
            context["original_logical_detector"],
        ),
        "original_translation_symmetry": dict(
            context["original_translation_symmetry"],
        ),
        "original_anchor_indices": list(context["original_anchor_indices"]),
        "subsystem_distance_semantics": "dressed-logical-center-quotient",
        "required_auxiliary_sectors": list(TWOBGA_PROOF_SECTORS),
    }
    proof["proof_sha256"] = _canonical_sha256(proof)
    return proof


def validate_twobga_exact_proof(
    claim: Mapping[str, Any],
) -> dict[str, Any]:
    """Reconstruct every matrix and replay the typed proof without a solver."""

    _require_rectangular_twobga_domain(claim)
    clean = _clean_claim(claim)
    # Reuse the Stage-3 validator by rebuilding its immutable envelope from
    # the proof.  This keeps the theorem, quotient, anchor, and SAT binding
    # checks identical at both handoff boundaries.
    proof = claim.get("exact_distance_proof")
    if not isinstance(proof, Mapping):
        raise ValueError("claim lacks a typed exact 2BGA proof")
    required = proof.get("required_distance")
    lower = proof.get("lower_bound_decisions")
    upper = proof.get("upper_witness")
    anchor_indices = proof.get("original_anchor_indices")
    if (
        proof.get("schema_version") != 1
        or proof.get("proof_type") != TWOBGA_EXACT_PROOF_TYPE
        or proof.get("exact") is not True
        or isinstance(required, bool)
        or not isinstance(required, int)
        or required <= 0
        or proof.get("distance") != required
        or proof.get("lower_bound_threshold") != required - 1
        or proof.get("lower_bound") != proof.get("distance")
        or proof.get("upper_bound") != proof.get("distance")
        or not isinstance(lower, list)
        or len(lower) != len(TWOBGA_PROOF_SECTORS)
        or not all(isinstance(item, Mapping) for item in lower)
        or not isinstance(upper, Mapping)
        or not isinstance(proof.get("theorem_eligibility"), Mapping)
        or not isinstance(proof.get("original_logical_detector"), Mapping)
        or not isinstance(proof.get("original_translation_symmetry"), Mapping)
        or not isinstance(anchor_indices, list)
        or any(
            isinstance(index, bool) or not isinstance(index, int)
            for index in anchor_indices
        )
        or proof.get("subsystem_distance_semantics")
        != "dressed-logical-center-quotient"
        or proof.get("required_auxiliary_sectors")
        != list(TWOBGA_PROOF_SECTORS)
        or proof.get("proof_sha256")
        != _canonical_sha256(proof, omit="proof_sha256")
    ):
        raise ValueError("typed exact 2BGA proof metadata is invalid")

    # Construct a terminal artifact and seal it afresh.  Its validator then
    # independently rebuilds the candidate and all matrix identities.
    artifact: dict[str, Any] = {
        "schema_version": 1,
        "gate": "qldpc-frontier-twobga-subsystem-screen",
        "backend": "twobga-aux",
        "status": "EXACT_PROVEN",
        "candidate": clean,
        "required_distance": proof["required_distance"],
        "threshold_only": False,
        "theorem_eligibility": proof.get("theorem_eligibility"),
        "proof_semantics": {
            "lower_bound": (
                "both dressed auxiliary X/Z decisions UNSAT through d-1"
            ),
            "auxiliary_sat_witness": "inconclusive-for-original-code",
            "original_sat_witness": "valid upper bound for original code",
        },
        "expected_units": 3,
        "attempted_units": 3,
        "terminal_units": 3,
        "lower_bound_decisions": proof.get("lower_bound_decisions"),
        "upper_witness": proof.get("upper_witness"),
        "auxiliary_witnesses": [],
        "units": sorted(
            [
                *lower,
                upper,
            ],
            key=lambda item: str(item.get("unit_id")),
        ),
        "original_logical_detector": proof.get("original_logical_detector"),
        "original_translation_symmetry": proof.get(
            "original_translation_symmetry",
        ),
        # Operational timing is excluded from the theorem/proof semantics but
        # remains a required numeric artifact field.
        "elapsed_s": 0.0,
    }
    artifact["artifact_sha256"] = _canonical_sha256(artifact)
    context = validate_twobga_stage3_artifact(artifact)
    if (
        required != context["required_distance"]
        or proof.get("theorem_eligibility") != context["problem"].report
        or proof.get("lower_bound_decisions")
        != context["lower_bound_decisions"]
        or proof.get("upper_witness") != context["upper_witness"]
        or anchor_indices != list(context["original_anchor_indices"])
        or isinstance(claim.get("d"), bool)
        or not isinstance(claim.get("d"), int)
        or claim.get("d") != context["required_distance"]
        or claim.get("d_is_exact") is not True
    ):
        raise ValueError("typed exact 2BGA claim metadata is inconsistent")
    return context


def build_twobga_certificate(
    claim: dict[str, Any],
    *,
    known_answer_artifact: Path | str,
    timeout_per_logical: float = 300,
    total_timeout: float = 7200,
    checkpoint_path: Path | str | None = None,
    resume: bool = False,
    solver_workers: int = 1,
    sector_solver: SectorSolver | None = None,
) -> dict[str, Any]:
    """Build an exact certificate from a theorem lower bound plus full witness."""

    _require_rectangular_twobga_domain(claim)
    workers = _validate_solver_workers(solver_workers)
    per_decision = _strict_timeout(timeout_per_logical, "timeout_per_logical")
    total = _strict_timeout(total_timeout, "total_timeout")
    request = _request(claim)
    context = validate_twobga_stage3_artifact(request["stage3_artifact"])
    clean = dict(context["claim"])
    required = int(context["required_distance"])
    upper = context["upper_witness"]
    started = time.monotonic()
    solve = solve_css_sector_sat if sector_solver is None else sector_solver
    upper_attempt: dict[str, Any] | None = None
    counterexample: dict[str, Any] | None = None
    if upper is None:
        remaining = max(0.001, total - (time.monotonic() - started))
        evidence = solve(
            context["hz"],
            context["lz"],
            max_weight=required,
            timeout=min(per_decision, remaining),
            workers=1,
            seed=0,
            partition_index=None,
            anchor_indices=context["original_anchor_indices"],
            sector="X",
            cardinality_encoding="kmtotalizer",
            solver="auto",
            checkpoint_path=_checkpoint_for(checkpoint_path, "build-upper-X"),
            resume=resume,
            checkpoint_identity={
                "certificate_type": CERTIFICATE_TYPE,
                "phase": "original-upper",
                "stage3_artifact_sha256": request["stage3_artifact_sha256"],
                "theorem_report_sha256": context["problem"].report[
                    "report_sha256"
                ],
            },
        )
        upper_attempt = _upper_wrapper(
            evidence,
            anchors=context["original_anchor_indices"],
            required_distance=required,
            hz=context["hz"],
            lz=context["lz"],
        )
        if _valid_original_upper(
            upper_attempt,
            hz=context["hz"],
            lz=context["lz"],
            required_distance=required,
            anchors=context["original_anchor_indices"],
        ):
            upper = upper_attempt
        elif _valid_original_counterexample(
            upper_attempt,
            hz=context["hz"],
            lz=context["lz"],
            required_distance=required,
            anchors=context["original_anchor_indices"],
        ):
            counterexample = upper_attempt

    exact = upper is not None
    proof = _proof(context, upper) if exact else None
    novelty = check_code_novelty(context["code"], code_type="css")
    normalized_claim = {
        **clean,
        "n": int(context["code"].num_qudits),
        "k": int(context["code"].dimension),
        "d": required if exact else 0,
        "fom": (
            int(context["code"].dimension) * required * required
            / int(context["code"].num_qudits)
            if exact else 0.0
        ),
        "d_is_exact": exact,
        "stage": (
            "twobga_exact"
            if exact else (
                "twobga_rejected" if counterexample else "twobga_incomplete"
            )
        ),
        "distance_status": (
            "exact"
            if exact else (
                "upper_bound_below_required"
                if counterexample else "unresolved"
            )
        ),
        "structural_novelty": novelty,
    }
    if proof is not None:
        normalized_claim["exact_distance_proof"] = proof
    final_gate = evaluate_challenge_gate(
        normalized_claim,
        known_answer_artifact=known_answer_artifact,
    )
    passed = bool(exact and final_gate.get("accepted") is True)
    certificate: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "certificate_type": CERTIFICATE_TYPE,
        "formulation": FORMULATION,
        "independent_verification_required": True,
        "build_assurance": "provisional-structural-replay",
        "claim": normalized_claim,
        "matrix_sha256": {
            "hx": matrix_sha256(context["hx"]),
            "hz": matrix_sha256(context["hz"]),
        },
        "known_answer": {
            "artifact_sha256": _file_sha256(known_answer_artifact),
        },
        "theorem_eligibility": dict(context["problem"].report),
        "solver": {
            "interface": "evaluation.distance_sat",
            "solver_workers": workers,
            "timeout_per_decision_s": per_decision,
            "total_timeout_s": total,
        },
        "twobga_exact": {
            "exact": exact,
            "required_distance": required,
            "distance": required if exact else 0,
            "lower_bound": required,
            "upper_bound": required if exact else None,
            "expected_lower_decisions": len(TWOBGA_PROOF_SECTORS),
            "completed_lower_decisions": len(
                context["lower_bound_decisions"],
            ),
            "lower_bound_decisions": context["lower_bound_decisions"],
            "upper_witness": upper,
            "upper_attempt": upper_attempt,
            "proof": proof,
            "elapsed_s": time.monotonic() - started,
        },
        "candidate_rejection": (
            None
            if counterexample is None
            else {
                "reason": "original-logical-below-required-distance",
                "required_distance": required,
                "witness": counterexample,
            }
        ),
        "final_gate": final_gate,
        "passed": passed,
    }
    if not passed:
        certificate["failure_disposition"] = (
            make_failure_disposition(
                CANDIDATE_REJECTED,
                "candidate",
                ["ORIGINAL_LOGICAL_BELOW_REQUIRED_DISTANCE"],
            )
            if counterexample is not None
            else incomplete_result_disposition(
                domain="solver" if not exact else "evidence",
                code=(
                    "TWOBGA_ORIGINAL_UPPER_WITNESS_INCOMPLETE"
                    if not exact else "TWOBGA_FINAL_GATE_REJECTED"
                ),
            )
        )
    certificate["certificate_sha256"] = _certificate_sha256(certificate)
    return certificate


def validate_twobga_candidate_rejection(
    certificate: Mapping[str, Any],
) -> bool:
    """Replay a terminal original-code witness below the required distance."""

    try:
        if (
            certificate.get("schema_version") != SCHEMA_VERSION
            or certificate.get("certificate_type") != CERTIFICATE_TYPE
            or certificate.get("formulation") != FORMULATION
            or certificate.get("passed") is not False
            or certificate.get("independent_verification_required") is not True
            or certificate.get("build_assurance")
            != "provisional-structural-replay"
            or certificate.get("certificate_sha256")
            != _certificate_sha256(dict(certificate))
        ):
            return False
        disposition = validate_failure_disposition(
            certificate.get("failure_disposition"),
        )
        expected_disposition = make_failure_disposition(
            CANDIDATE_REJECTED,
            "candidate",
            ["ORIGINAL_LOGICAL_BELOW_REQUIRED_DISTANCE"],
        )
        rejection = certificate.get("candidate_rejection")
        claim = certificate.get("claim")
        exact = certificate.get("twobga_exact")
        if (
            disposition != expected_disposition
            or not isinstance(rejection, Mapping)
            or not isinstance(claim, Mapping)
            or not isinstance(exact, Mapping)
            or rejection.get("reason")
            != "original-logical-below-required-distance"
        ):
            return False
        clean = _clean_claim(claim)
        _require_rectangular_twobga_domain(clean)
        code = build_candidate_code(clean)
        parameters = validate_candidate_parameters(clean, code)
        required = int(parameters["required_distance"])
        hx, hz, lx, lz = (
            np.asarray(value, dtype=np.uint8) & 1
            for value in get_code_matrices(code)
        )
        problem = derive_twobga_subsystem_problem(
            hx,
            hz,
            ell=int(clean["ell"]),
            m=int(clean["m"]),
            expected_n=int(clean["n"]),
            expected_k=int(clean["k"]),
        )
        symmetry = verify_bb_translation_symmetry(clean)
        anchors = (
            tuple(
                int(index)
                for index in symmetry["orbit_representatives"]
            )
            if symmetry.get("verified") is True else ()
        )
        witness = rejection.get("witness")
        lower = exact.get("lower_bound_decisions")
        by_sector = {
            str(item.get("sector")): item
            for item in lower
            if isinstance(item, Mapping)
        } if isinstance(lower, list) else {}
        return bool(
            problem.eligible
            and certificate.get("theorem_eligibility") == problem.report
            and certificate.get("matrix_sha256") == {
                "hx": matrix_sha256(hx),
                "hz": matrix_sha256(hz),
            }
            and rejection.get("required_distance") == required
            and isinstance(witness, Mapping)
            and _valid_original_counterexample(
                witness,
                hz=hz,
                lz=lz,
                required_distance=required,
                anchors=anchors,
            )
            and exact.get("exact") is False
            and exact.get("required_distance") == required
            and exact.get("distance") == 0
            and exact.get("lower_bound") == required
            and exact.get("upper_bound") is None
            and exact.get("expected_lower_decisions")
            == len(TWOBGA_PROOF_SECTORS)
            and exact.get("completed_lower_decisions")
            == len(TWOBGA_PROOF_SECTORS)
            and set(by_sector) == set(TWOBGA_PROOF_SECTORS)
            and all(
                _valid_auxiliary_lower(
                    by_sector[sector],
                    problem,
                    sector=sector,
                    required_distance=required,
                )
                for sector in TWOBGA_PROOF_SECTORS
            )
            and exact.get("upper_witness") is None
            and exact.get("upper_attempt") == witness
            and exact.get("proof") is None
            and claim.get("d_is_exact") is False
            and claim.get("d") == 0
            and claim.get("stage") == "twobga_rejected"
            and claim.get("distance_status")
            == "upper_bound_below_required"
        )
    except (
        AttributeError,
        KeyError,
        OSError,
        OverflowError,
        RuntimeError,
        TypeError,
        ValueError,
    ):
        return False


def verify_twobga_certificate(
    certificate: dict[str, Any],
    *,
    known_answer_artifact: Path | str,
    rerun_milp: bool = True,
    timeout_per_logical: float | None = None,
    checkpoint_path: Path | str | None = None,
    resume: bool = False,
    total_timeout: float | None = None,
    solver_workers: int = 1,
    sector_solver: SectorSolver | None = None,
) -> dict[str, Any]:
    """Independently rebuild the theorem bridge and rerun both lower lanes."""

    workers = _validate_solver_workers(solver_workers)
    started = time.monotonic()
    checks: dict[str, bool] = {}
    try:
        if not isinstance(certificate, Mapping):
            raise TypeError("certificate must be an object")
        known_answer = certificate.get("known_answer")
        solver_config = certificate.get("solver")
        if not isinstance(known_answer, Mapping):
            known_answer = {}
        if not isinstance(solver_config, Mapping):
            solver_config = {}
        actual_known_answer_sha256 = _file_sha256(known_answer_artifact)
        checks["schema"] = bool(
            certificate.get("schema_version") == SCHEMA_VERSION
            and certificate.get("certificate_type") == CERTIFICATE_TYPE
            and certificate.get("formulation") == FORMULATION
            and certificate.get("independent_verification_required") is True
            and certificate.get("build_assurance")
            == "provisional-structural-replay"
        )
        checks["certificate_sha256"] = bool(
            certificate.get("certificate_sha256")
            == _certificate_sha256(certificate)
        )
        checks["known_answer_sha256"] = bool(
            known_answer.get("artifact_sha256")
            == actual_known_answer_sha256
        )
    except (
        AttributeError,
        OSError,
        OverflowError,
        TypeError,
        ValueError,
    ) as exc:
        return {
            "passed": False,
            "replay_complete": False,
            "checks": checks,
            "failures": [f"certificate schema validation failed: {exc}"],
            "failure_disposition": incomplete_result_disposition(
                domain="schema",
                code="TWOBGA_CERTIFICATE_SCHEMA_INVALID",
            ),
        }
    failures: list[str] = []
    try:
        claim = certificate["claim"]
        if not isinstance(claim, Mapping):
            raise TypeError("certificate claim must be an object")
        _require_rectangular_twobga_domain(claim)
        context = validate_twobga_exact_proof(claim)
    except (
        AttributeError,
        KeyError,
        OverflowError,
        RuntimeError,
        TypeError,
        ValueError,
    ) as exc:
        return {
            "passed": False,
            "replay_complete": False,
            "checks": checks,
            "failures": [f"certificate reconstruction failed: {exc}"],
            "failure_disposition": incomplete_result_disposition(
                domain="schema",
                code="TWOBGA_CERTIFICATE_RECONSTRUCTION_FAILED",
            ),
        }
    checks["matrix_sha256"] = certificate.get("matrix_sha256") == {
        "hx": matrix_sha256(context["hx"]),
        "hz": matrix_sha256(context["hz"]),
    }
    checks["theorem_eligibility"] = bool(
        certificate.get("theorem_eligibility") == context["problem"].report
    )
    checks["typed_exact_proof"] = True
    proof = claim["exact_distance_proof"]
    stored_exact = certificate.get("twobga_exact")
    checks["twobga_exact_binding"] = bool(
        isinstance(stored_exact, Mapping)
        and certificate.get("candidate_rejection") is None
        and stored_exact.get("exact") is True
        and stored_exact.get("required_distance")
        == context["required_distance"]
        and stored_exact.get("distance") == context["required_distance"]
        and stored_exact.get("lower_bound") == context["required_distance"]
        and stored_exact.get("upper_bound") == context["required_distance"]
        and stored_exact.get("expected_lower_decisions")
        == len(TWOBGA_PROOF_SECTORS)
        and stored_exact.get("completed_lower_decisions")
        == len(TWOBGA_PROOF_SECTORS)
        and stored_exact.get("lower_bound_decisions")
        == context["lower_bound_decisions"]
        and stored_exact.get("upper_witness") == context["upper_witness"]
        and stored_exact.get("upper_attempt")
        in (None, context["upper_witness"])
        and stored_exact.get("proof") == proof
    )

    per_decision = timeout_per_logical
    if per_decision is None:
        per_decision = solver_config.get(
            "timeout_per_decision_s", 300,
        )
    try:
        per_decision = _strict_timeout(float(per_decision), "timeout_per_logical")
        total = (
            math.inf
            if total_timeout is None
            else _strict_timeout(total_timeout, "total_timeout")
        )
    except (TypeError, ValueError, OverflowError):
        per_decision = 0.0
        total = 0.0
    solve = solve_css_sector_sat if sector_solver is None else sector_solver
    rerun_results: dict[str, dict[str, Any]] = {}

    def rerun_sector(sector: str) -> tuple[str, dict[str, Any]]:
        matrices = context["problem"].sector_matrices(sector)
        symmetry = context["problem"].report["sectors"][sector][
            "translation_symmetry"
        ]
        anchors = (0,) if symmetry.get("verified") is True else ()
        remaining = max(0.001, total - (time.monotonic() - started))
        evidence = solve(
            matrices[0],
            matrices[1],
            max_weight=int(context["required_distance"]) - 1,
            timeout=min(per_decision, remaining),
            workers=1,
            seed=0,
            partition_index=None,
            anchor_indices=anchors,
            sector=sector,
            checkpoint_path=_checkpoint_for(
                checkpoint_path, f"verify-lower-{sector}",
            ),
            resume=resume,
            checkpoint_identity={
                "certificate_sha256": certificate.get("certificate_sha256"),
                "phase": "verify-auxiliary-lower",
                "sector": sector,
                "cardinality_encoding": VERIFICATION_CARDINALITY_ENCODING,
                "solver": VERIFICATION_SOLVER,
                "theorem_report_sha256": context["problem"].report[
                    "report_sha256"
                ],
            },
            cardinality_encoding=VERIFICATION_CARDINALITY_ENCODING,
            solver=VERIFICATION_SOLVER,
        )
        return sector, dict(evidence)

    if rerun_milp and per_decision > 0 and total > 0:
        with ThreadPoolExecutor(
            max_workers=min(workers, len(TWOBGA_PROOF_SECTORS)),
        ) as executor:
            futures = {
                executor.submit(rerun_sector, sector): sector
                for sector in TWOBGA_PROOF_SECTORS
            }
            for future in as_completed(futures):
                sector = futures[future]
                try:
                    returned_sector, evidence = future.result()
                except Exception as exc:
                    evidence = {
                        "outcome": "solver_error",
                        "message": f"{type(exc).__name__}: {exc}",
                    }
                    returned_sector = sector
                rerun_results[returned_sector] = evidence
    rerun_matches = bool(
        rerun_milp
        and set(rerun_results) == set(TWOBGA_PROOF_SECTORS)
        and all(
            _complete_unsat(
                rerun_results[sector],
                int(context["required_distance"]) - 1,
            )
            and _instance_bound(
                rerun_results[sector],
                context["problem"].sector_matrices(sector)[0],
                context["problem"].sector_matrices(sector)[1],
                sector=sector,
                max_weight=int(context["required_distance"]) - 1,
                anchors=(
                    (0,)
                    if context["problem"].report["sectors"][sector][
                        "translation_symmetry"
                    ].get("verified") is True
                    else ()
                ),
            )
            for sector in TWOBGA_PROOF_SECTORS
        )
    )
    checks["independent_auxiliary_rerun"] = rerun_matches
    gate = evaluate_challenge_gate(
        dict(claim),
        known_answer_artifact=known_answer_artifact,
    )
    checks["final_gate"] = gate.get("accepted") is True
    checks["stored_final_gate"] = certificate.get("final_gate") == gate
    checks["certificate_passed_flag"] = certificate.get("passed") is True
    for name, passed in checks.items():
        if not passed:
            failures.append(name)
    passed = not failures
    result: dict[str, Any] = {
        "passed": passed,
        "replay_complete": rerun_matches,
        "distance": int(context["required_distance"]),
        "checks": checks,
        "failures": failures,
        "rerun": {
            "requested": bool(rerun_milp),
            "cardinality_encoding": VERIFICATION_CARDINALITY_ENCODING,
            "solver": VERIFICATION_SOLVER,
            "completed_sectors": len(rerun_results),
            "expected_sectors": len(TWOBGA_PROOF_SECTORS),
            "matches": rerun_matches,
            "results": [
                {"sector": sector, "solver_evidence": rerun_results[sector]}
                for sector in TWOBGA_PROOF_SECTORS
                if sector in rerun_results
            ],
        },
        "final_gate": gate,
        "elapsed_s": time.monotonic() - started,
    }
    if not passed:
        result["failure_disposition"] = incomplete_result_disposition(
            domain="solver" if not rerun_matches else "evidence",
            code=(
                "TWOBGA_INDEPENDENT_RERUN_INCOMPLETE"
                if not rerun_matches else "TWOBGA_VERIFICATION_FAILED"
            ),
        )
    return result


__all__ = [
    "CERTIFICATE_TYPE",
    "FORMULATION",
    "SCHEMA_VERSION",
    "VERIFICATION_CARDINALITY_ENCODING",
    "VERIFICATION_SOLVER",
    "build_twobga_certificate",
    "validate_twobga_candidate_rejection",
    "validate_twobga_exact_proof",
    "verify_twobga_certificate",
]
