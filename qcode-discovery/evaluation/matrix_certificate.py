"""Replayable exact certificate for an arbitrary binary CSS matrix pair."""

from __future__ import annotations

import importlib.metadata
import hashlib
import json
import math
import platform
import time
from pathlib import Path
from typing import Any, Mapping

import numpy as np

from evaluation.certificate import (
    FORMULATION,
    _certificate_sha256,
    _direction_key,
    _direction_specs,
    _file_sha256,
    _highs_version,
    _json_sha256,
    _load_direction_checkpoint,
    _solver_environment,
    _validate_solver_workers,
    _write_direction_checkpoint,
    pack_vector,
    solve_css_direction,
    unpack_vector,
    verify_direction_evidence,
)
from evaluation.failure_disposition import (
    classify_build_failure,
    classify_replay_failure,
    incomplete_result_disposition,
)
from evaluation.final_gate import (
    _connected,
    _matrix_sha256,
    classify_win,
    validate_known_answer_artifact,
)
from evaluation.matrix_io import build_css_from_matrices, css_parameters, pack_matrix
from evaluation.registry import check_code_novelty
from evaluation.target_policy import (
    DEFAULT_TARGET_MODE,
    classify_target_win,
    target_binding,
    validate_target_binding,
    validate_target_mode,
)

SCHEMA_VERSION = 1
CERTIFICATE_TYPE = "qldpc-css-matrix-exact"
BUILD_CHECKPOINT_TYPE = "qldpc-css-matrix-build-checkpoint-v2"
VERIFY_CHECKPOINT_TYPE = "qldpc-css-matrix-verify-checkpoint-v2"


def _version(name: str) -> str | None:
    try:
        return importlib.metadata.version(name)
    except importlib.metadata.PackageNotFoundError:
        return None


def _normalized_construction_claim(
    claim: Mapping[str, Any],
) -> tuple[dict[str, Any], Any, Any]:
    """Normalize a compact construction and return its cache bindings."""

    from evaluation.construction import (
        construction_identity,
        construction_source_fingerprint,
        normalize_construction_claim,
    )

    normalized = normalize_construction_claim(dict(claim))
    normalized_claim = (
        dict(normalized)
        if isinstance(normalized, Mapping)
        and isinstance(normalized.get("construction"), Mapping)
        else {"construction": dict(normalized)}
    )
    return (
        normalized_claim,
        construction_identity(normalized_claim),
        construction_source_fingerprint(),
    )


def _rebuild_claim(
    claim: Mapping[str, Any],
) -> tuple[Any, np.ndarray, np.ndarray, dict[str, Any] | None, Any, Any]:
    """Rebuild matrices from the authoritative construction when available."""

    construction = claim.get("construction")
    if isinstance(construction, Mapping):
        from evaluation.construction import build_css_code_from_claim

        normalized, identity, source_fingerprint = (
            _normalized_construction_claim(claim)
        )
        code = build_css_code_from_claim(normalized)
        hx = np.asarray(
            code.matrix_x.toarray()
            if hasattr(code.matrix_x, "toarray")
            else code.matrix_x,
            dtype=np.uint8,
        ) & 1
        hz = np.asarray(
            code.matrix_z.toarray()
            if hasattr(code.matrix_z, "toarray")
            else code.matrix_z,
            dtype=np.uint8,
        ) & 1
        # Packed matrices are witnesses, never the authority for a compact
        # construction.  If supplied, require byte-exact agreement.
        hx_value = claim.get("H_X", claim.get("hx"))
        hz_value = claim.get("H_Z", claim.get("hz"))
        if hx_value is not None or hz_value is not None:
            if hx_value is None or hz_value is None:
                raise ValueError("H_X and H_Z must be supplied together")
            _, claimed_hx, claimed_hz = build_css_from_matrices(
                hx_value, hz_value,
            )
            if not (
                np.array_equal(hx, claimed_hx)
                and np.array_equal(hz, claimed_hz)
            ):
                raise ValueError(
                    "packed matrices do not match reconstructed construction"
                )
        return code, hx, hz, normalized, identity, source_fingerprint

    hx_value = claim.get("H_X", claim.get("hx"))
    hz_value = claim.get("H_Z", claim.get("hz"))
    if hx_value is None or hz_value is None:
        raise ValueError("generic CSS claim requires H_X and H_Z")
    code, hx, hz = build_css_from_matrices(hx_value, hz_value)
    return code, hx, hz, None, None, None


def _implementation_binding() -> dict[str, Any]:
    sources = {}
    for path in (
        Path(__file__),
        Path(__file__).with_name("construction.py"),
        Path(__file__).with_name("matrix_io.py"),
        Path(__file__).with_name("target_policy.py"),
    ):
        sources[path.name] = (
            hashlib.sha256(path.read_bytes()).hexdigest()
            if path.is_file()
            else None
        )
    return {"sources": sources, "sha256": _json_sha256(sources)}


def _claim_target_binding(
    claim: Mapping[str, Any],
    *,
    n: int,
    k: int,
) -> dict[str, Any]:
    """Resolve a claim target, defaulting only an absent field to legacy gist."""

    supplied_mode = claim.get("target_mode")
    if "target" not in claim:
        if (
            supplied_mode is not None
            and validate_target_mode(supplied_mode) != DEFAULT_TARGET_MODE
        ):
            raise ValueError("non-legacy target mode requires a target binding")
        return target_binding(n, k, DEFAULT_TARGET_MODE)
    return validate_target_binding(
        claim["target"],
        n=n,
        k=k,
        mode=supplied_mode,
    )


def _static_gate(
    code,
    hx: np.ndarray,
    hz: np.ndarray,
    *,
    distance: int,
    exact: bool,
    known_answer_artifact: Path | str,
    target: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    baseline = validate_known_answer_artifact(known_answer_artifact)
    n, k = css_parameters(hx, hz)
    stacked = np.vstack((hx, hz))
    connected, components = _connected(stacked)
    novelty = check_code_novelty(code, code_type="css")
    selected_target = (
        target_binding(n, k, DEFAULT_TARGET_MODE)
        if target is None
        else validate_target_binding(target, n=n, k=k)
    )
    selected_win = classify_target_win(
        n,
        k,
        distance,
        selected_target["mode"],
    )
    challenge_compatibility = classify_win(n, k, distance)
    checks = {
        "known_answer_gate": baseline["passed"],
        "css_commutation": not np.any((hx @ hz.T) & 1),
        "positive_dimension": k > 0,
        "weight_and_degree_at_most_6": (
            int(stacked.sum(axis=1).max(initial=0)) <= 6
            and int(stacked.sum(axis=0).max(initial=0)) <= 6
        ),
        "connected_tanner_graph": connected,
        "all_2k_milp_directions_optimal": exact,
        "expanded_registry_novel": novelty["novel"],
        # This legacy check name is part of the sealed terminal-gate shape.
        # Its value is the selected target decision; the historical gist
        # decision is reported separately as ``challenge_compatibility``.
        "challenge_win": selected_win["passed"],
    }
    return {
        "accepted": all(checks.values()),
        "checks": checks,
        "failures": [name for name, passed in checks.items() if not passed],
        "known_answer": baseline,
        "structural_novelty": novelty,
        "win": selected_win,
        "selected_target": selected_target,
        "selected_target_win": selected_win,
        "target_gate": {
            "passed": selected_win["passed"],
            "mode": selected_target["mode"],
            "observed_distance": distance,
            "required_distance": selected_target["required_distance"],
            "rejection_cutoff": selected_target["rejection_cutoff"],
            "binding_sha256": selected_target["binding_sha256"],
        },
        "challenge_compatibility": challenge_compatibility,
        "candidate": {
            "n": n,
            "k": k,
            "d": distance,
            "fom": selected_win["fom"],
            "tanner_components": components,
            "matrix_sha256": {
                "hx": _matrix_sha256(hx),
                "hz": _matrix_sha256(hz),
            },
        },
    }


def build_matrix_css_certificate(
    claim: dict[str, Any],
    *,
    known_answer_artifact: Path | str,
    timeout_per_logical: float = 300,
    total_timeout: float = 7200,
    checkpoint_path: Path | str | None = None,
    resume: bool = False,
    solver_workers: int = 1,
) -> dict[str, Any]:
    workers = _validate_solver_workers(solver_workers)
    timeout_per_logical = float(timeout_per_logical)
    total_timeout = float(total_timeout)
    if not math.isfinite(timeout_per_logical) or timeout_per_logical <= 0:
        raise ValueError("timeout_per_logical must be a positive finite number")
    if not math.isfinite(total_timeout) or total_timeout <= 0:
        raise ValueError("total_timeout must be a positive finite number")
    (
        code,
        hx,
        hz,
        normalized_construction,
        construction_identity_value,
        construction_source,
    ) = _rebuild_claim(claim)
    n, k = css_parameters(hx, hz)
    if k <= 0:
        raise ValueError("generic CSS claim must encode at least one logical qubit")
    selected_target = _claim_target_binding(claim, n=n, k=k)

    specs = _direction_specs(code)
    matrix_sha256 = {
        "hx": _matrix_sha256(hx),
        "hz": _matrix_sha256(hz),
    }
    checkpoint_binding = {
        "claim_sha256": _json_sha256(
            normalized_construction
            if normalized_construction is not None
            else {"H_X": pack_matrix(hx), "H_Z": pack_matrix(hz)}
        ),
        "construction_identity": construction_identity_value,
        "canonical_digest": claim.get("canonical_digest"),
        "construction_source_fingerprint": construction_source,
        "matrix_sha256": matrix_sha256,
        "target": selected_target,
        "target_binding_sha256": selected_target["binding_sha256"],
        "known_answer_sha256": _file_sha256(known_answer_artifact),
        "solver": _solver_environment(),
        "implementation": _implementation_binding(),
    }
    reusable: dict[str, dict[str, Any]] = {}
    if checkpoint_path is not None:
        checkpoint = Path(checkpoint_path)
        if resume and checkpoint.exists():
            reusable = _load_direction_checkpoint(
                checkpoint,
                checkpoint_type=BUILD_CHECKPOINT_TYPE,
                binding=checkpoint_binding,
                specs=specs,
            )
        _write_direction_checkpoint(
            checkpoint,
            checkpoint_type=BUILD_CHECKPOINT_TYPE,
            binding=checkpoint_binding,
            directions=reusable,
            specs=specs,
        )

    directions: list[dict[str, Any]] = []
    reused_directions = 0
    started = time.monotonic()
    for logical_type, index, check_name, checks, target in specs:
        key = _direction_key(logical_type, index, check_name)
        cached = reusable.get(key)
        if cached is not None:
            directions.append(cached)
            reused_directions += 1
            continue
        remaining = total_timeout - (time.monotonic() - started)
        if remaining <= 0:
            break
        evidence = solve_css_direction(
            checks,
            target,
            timeout=min(float(timeout_per_logical), remaining),
            solver_workers=workers,
        )
        evidence.update(
            {
                "logical_type": logical_type,
                "logical_index": index,
                "check_matrix": check_name,
                "target_logical": pack_vector(target),
            }
        )
        directions.append(evidence)
        if not verify_direction_evidence(evidence, checks, target):
            reusable[key] = evidence
            if checkpoint_path is not None:
                _write_direction_checkpoint(
                    checkpoint_path,
                    checkpoint_type=BUILD_CHECKPOINT_TYPE,
                    binding=checkpoint_binding,
                    directions=reusable,
                    specs=specs,
                )

    exact = len(directions) == 2 * k and all(
        not verify_direction_evidence(
            item,
            hx if item["check_matrix"] == "hx" else hz,
            unpack_vector(item["target_logical"]),
        )
        for item in directions
    )
    objectives = [
        int(item["objective"])
        for item in directions
        if item.get("objective") is not None
    ]
    distance = min(objectives) if objectives else 0
    gate = _static_gate(
        code,
        hx,
        hz,
        distance=distance,
        exact=exact,
        known_answer_artifact=known_answer_artifact,
        target=selected_target,
    )
    best = min(
        (item for item in directions if item.get("objective") is not None),
        key=lambda item: int(item["objective"]),
        default=None,
    )
    passed = bool(exact and gate["accepted"])
    certificate = {
        "schema_version": SCHEMA_VERSION,
        "certificate_type": CERTIFICATE_TYPE,
        "formulation": FORMULATION,
        "claim": {
            "source": claim.get("source"),
            "canonical_digest": claim.get("canonical_digest"),
            "H_X": pack_matrix(hx),
            "H_Z": pack_matrix(hz),
            "n": n,
            "k": k,
            "d": distance,
            "fom": gate["win"]["fom"],
            "target_mode": selected_target["mode"],
            "target": selected_target,
        },
        "construction_identity": construction_identity_value,
        "canonical_digest": claim.get("canonical_digest"),
        "construction_source_fingerprint": construction_source,
        "implementation": _implementation_binding(),
        "matrix_sha256": matrix_sha256,
        "target_mode": selected_target["mode"],
        "target": selected_target,
        "target_binding_sha256": selected_target["binding_sha256"],
        "known_answer": {"artifact_sha256": _file_sha256(known_answer_artifact)},
        "solver": {
            "interface": "scipy.optimize.milp",
            "backend": "HiGHS",
            "scipy_version": _version("scipy"),
            "highs_version": _highs_version(),
            "presolve": True,
            "solver_workers": workers,
            "timeout_per_logical_s": timeout_per_logical,
            "total_timeout_s": total_timeout,
        },
        "environment": {
            "python": platform.python_version(),
            "numpy": _version("numpy"),
            "qldpc": _version("qldpc"),
        },
        "milp": {
            "exact": exact,
            "expected_directions": 2 * k,
            "completed_directions": len(directions),
            "distance": distance,
            "elapsed_s": time.monotonic() - started,
            "resumed_directions": reused_directions,
            "directions": directions,
        },
        "upper_witness": None
        if best is None
        else {
            "logical_type": best["logical_type"],
            "logical_index": best["logical_index"],
            "weight": best["objective"],
            "operator": best["operator"],
            "target_logical": best["target_logical"],
        },
        "final_gate": gate,
        "passed": passed,
    }
    if normalized_construction is not None:
        certificate["claim"]["construction"] = dict(
            normalized_construction["construction"]
        )
    failure_disposition = classify_build_failure(
        exact=exact,
        passed=passed,
        final_gate=gate,
    )
    if failure_disposition is not None:
        certificate["failure_disposition"] = failure_disposition
    certificate["certificate_sha256"] = _certificate_sha256(certificate)
    return certificate


def verify_matrix_css_certificate(
    certificate: dict[str, Any],
    *,
    known_answer_artifact: Path | str,
    rerun_milp: bool = True,
    timeout_per_logical: float | None = None,
    checkpoint_path: Path | str | None = None,
    resume: bool = False,
    total_timeout: float | None = None,
    solver_workers: int = 1,
) -> dict[str, Any]:
    workers = _validate_solver_workers(solver_workers)
    if timeout_per_logical is not None:
        timeout_per_logical = float(timeout_per_logical)
        if not math.isfinite(timeout_per_logical) or timeout_per_logical <= 0:
            raise ValueError("timeout_per_logical must be a positive finite number")
    if total_timeout is not None:
        total_timeout = float(total_timeout)
        if not math.isfinite(total_timeout) or total_timeout <= 0:
            raise ValueError("total_timeout must be a positive finite number")
    verify_started = time.monotonic()
    failures: list[str] = []
    checks = {
        "schema": (
            certificate.get("schema_version") == SCHEMA_VERSION
            and certificate.get("certificate_type") == CERTIFICATE_TYPE
            and certificate.get("formulation") == FORMULATION
        ),
        "certificate_sha256": (
            certificate.get("certificate_sha256") == _certificate_sha256(certificate)
        ),
    }
    try:
        claim = certificate["claim"]
        (
            code,
            hx,
            hz,
            normalized_construction,
            construction_identity_value,
            construction_source,
        ) = _rebuild_claim(claim)
        n, k = css_parameters(hx, hz)
        selected_target = _claim_target_binding(claim, n=n, k=k)
        has_certificate_target = bool(
            "target" in certificate
            or "target_mode" in certificate
            or "target_binding_sha256" in certificate
        )
        checks["target_binding"] = True
        if has_certificate_target or "target" in claim:
            checks["target_binding"] = bool(
                certificate.get("target_mode") == selected_target["mode"]
                and certificate.get("target") == selected_target
                and certificate.get("target_binding_sha256")
                == selected_target["binding_sha256"]
            )
        checks["known_answer_sha256"] = certificate["known_answer"][
            "artifact_sha256"
        ] == _file_sha256(known_answer_artifact)
        checks["matrix_sha256"] = certificate.get("matrix_sha256") == {
            "hx": _matrix_sha256(hx),
            "hz": _matrix_sha256(hz),
        }
        checks["construction_identity"] = (
            certificate.get("construction_identity")
            == construction_identity_value
        )
        checks["canonical_digest_binding"] = (
            certificate.get("canonical_digest")
            == claim.get("canonical_digest")
        )
        checks["construction_source_fingerprint"] = (
            certificate.get("construction_source_fingerprint")
            == construction_source
        )
        checks["implementation_binding"] = (
            certificate.get("implementation") == _implementation_binding()
        )
        specs = _direction_specs(code)
        directions = certificate["milp"]["directions"]
    except (KeyError, TypeError, ValueError, OSError) as exc:
        domain = "io" if isinstance(exc, OSError) else "schema"
        code = (
            "CERTIFICATE_RECONSTRUCTION_IO_ERROR"
            if isinstance(exc, OSError)
            else "CERTIFICATE_RECONSTRUCTION_INCOMPLETE"
        )
        return {
            "passed": False,
            "replay_complete": False,
            "checks": checks,
            "failures": [f"certificate reconstruction failed: {exc}"],
            "failure_disposition": incomplete_result_disposition(
                domain=domain,
                code=code,
            ),
        }

    checks["claim_parameters"] = (
        int(claim.get("n", -1)) == n and int(claim.get("k", -1)) == k
    )
    checks["direction_count"] = len(directions) == len(specs) == 2 * k
    expected_objectives = {
        _direction_key(logical_type, index, check_name): (
            directions[position].get("objective")
            if position < len(directions)
            and isinstance(directions[position], Mapping)
            else None
        )
        for position, (
            logical_type, index, check_name, _matrix, _target,
        ) in enumerate(specs)
    }
    checkpoint_binding = {
        "certificate_sha256": _json_sha256(certificate),
        "claim_sha256": _json_sha256(
            normalized_construction
            if normalized_construction is not None
            else {"H_X": pack_matrix(hx), "H_Z": pack_matrix(hz)}
        ),
        "construction_identity": construction_identity_value,
        "canonical_digest": claim.get("canonical_digest"),
        "construction_source_fingerprint": construction_source,
        "matrix_sha256": certificate.get("matrix_sha256"),
        "target": selected_target,
        "target_binding_sha256": selected_target["binding_sha256"],
        "known_answer_sha256": _file_sha256(known_answer_artifact),
        "solver": _solver_environment(),
        "implementation": _implementation_binding(),
    }
    reusable: dict[str, dict[str, Any]] = {}
    if rerun_milp and checkpoint_path is not None:
        checkpoint = Path(checkpoint_path)
        if resume and checkpoint.exists():
            reusable = _load_direction_checkpoint(
                checkpoint,
                checkpoint_type=VERIFY_CHECKPOINT_TYPE,
                binding=checkpoint_binding,
                specs=specs,
                expected_objectives=expected_objectives,
            )
        _write_direction_checkpoint(
            checkpoint,
            checkpoint_type=VERIFY_CHECKPOINT_TYPE,
            binding=checkpoint_binding,
            directions=reusable,
            specs=specs,
        )
    direction_failures: list[str] = []
    replay_complete = True
    reused_directions = 0
    for position, (logical_type, index, check_name, matrix, target) in enumerate(specs):
        if position >= len(directions):
            direction_failures.append(f"{logical_type}[{index}]: missing")
            continue
        evidence = directions[position]
        local = []
        if (
            evidence.get("logical_type") != logical_type
            or int(evidence.get("logical_index", -1)) != index
            or evidence.get("check_matrix") != check_name
        ):
            local.append("identity/order mismatch")
        local.extend(verify_direction_evidence(evidence, matrix, target))
        if rerun_milp:
            key = _direction_key(logical_type, index, check_name)
            rerun = reusable.get(key)
            if rerun is not None:
                reused_directions += 1
            remaining = None
            if rerun is None and total_timeout is not None:
                remaining = total_timeout - (time.monotonic() - verify_started)
            if rerun is not None:
                pass
            elif remaining is not None and remaining <= 0:
                local.append("rerun total timeout exhausted")
                replay_complete = False
                rerun = None
            else:
                raw_timeout = timeout_per_logical
                if raw_timeout is None:
                    raw_timeout = certificate.get("solver", {}).get(
                        "timeout_per_logical_s", 300
                    )
                try:
                    timeout = float(raw_timeout)
                except (TypeError, ValueError, OverflowError):
                    timeout = math.nan
                if not math.isfinite(timeout) or timeout <= 0:
                    local.append("invalid rerun timeout")
                    replay_complete = False
                    rerun = None
                else:
                    effective_timeout = timeout
                    if remaining is not None:
                        effective_timeout = min(timeout, remaining)
                    rerun = solve_css_direction(
                        matrix,
                        target,
                        timeout=effective_timeout,
                        solver_workers=workers,
                    )
                    rerun.update(
                        {
                            "logical_type": logical_type,
                            "logical_index": index,
                            "check_matrix": check_name,
                            "target_logical": pack_vector(target),
                        }
                    )
            rerun_valid = (
                rerun is not None
                and not verify_direction_evidence(rerun, matrix, target)
                and rerun.get("objective") == evidence.get("objective")
            )
            if rerun_valid and key not in reusable:
                reusable[key] = rerun
                if checkpoint_path is not None:
                    _write_direction_checkpoint(
                        checkpoint_path,
                        checkpoint_type=VERIFY_CHECKPOINT_TYPE,
                        binding=checkpoint_binding,
                        directions=reusable,
                        specs=specs,
                    )
            if rerun is not None and not rerun_valid:
                replay_complete = False
                local.append("rerun optimum mismatch")
        if local:
            direction_failures.append(f"{logical_type}[{index}]: " + "; ".join(local))
    checks["stored_direction_evidence"] = not direction_failures
    checks["milp_rerun"] = rerun_milp and not direction_failures
    objectives = [
        int(item["objective"])
        for item in directions
        if item.get("objective") is not None
    ]
    distance = min(objectives) if objectives else 0
    checks["distance_recomputed"] = (
        distance > 0
        and certificate["milp"].get("distance") == distance
        and int(claim.get("d", -1)) == distance
    )
    gate = _static_gate(
        code,
        hx,
        hz,
        distance=distance,
        exact=all(
            (
                checks["direction_count"],
                checks["stored_direction_evidence"],
                checks["milp_rerun"],
            )
        ),
        known_answer_artifact=known_answer_artifact,
        target=selected_target,
    )
    checks["stored_final_gate"] = certificate.get("final_gate") == gate
    checks["final_gate"] = gate["accepted"]
    checks["certificate_passed_flag"] = certificate.get("passed") is True
    failures.extend(name for name, passed in checks.items() if not passed)
    failures.extend(direction_failures)
    passed = not failures
    result = {
        "passed": passed,
        "replay_complete": replay_complete,
        "checks": checks,
        "failures": failures,
        "distance": distance,
        "directions_verified": len(specs) - len(direction_failures),
        "directions_total": len(specs),
        "resumed_directions": reused_directions,
        "target": selected_target,
        "final_gate": gate,
    }
    failure_disposition = classify_replay_failure(
        passed=passed,
        replay_complete=replay_complete,
    )
    if failure_disposition is not None:
        result["failure_disposition"] = failure_disposition
    return result
