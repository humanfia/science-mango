import copy
import json
from pathlib import Path

import pytest

import evaluation.matrix_certificate as matrix_certificate_module
from evaluation.admissibility_policy import (
    css_w6_admissibility_binding,
)
import evaluation.noncss_certificate as noncss_certificate_module
from evaluation.failure_disposition import (
    _TERMINAL_GATE_SHAPES,
    terminal_candidate_rejection,
)
from evaluation.matrix_certificate import (
    _rebuild_claim,
    build_matrix_css_certificate,
    verify_matrix_css_certificate,
)
from evaluation.noncss_certificate import (
    build_noncss_certificate,
    verify_noncss_certificate,
)
from evaluation.target_policy import (
    TARGET_MODE_GIST,
    TARGET_MODE_SCALAR,
    TARGET_MODE_SCALAR_13_INCLUSIVE,
    target_binding,
)


KNOWN_ANSWER = Path(__file__).resolve().parent.parent / "results" / "known_answer_gate.json"


def _generic_css_claim():
    return {
        "source": "test [[4,1,2]]",
        "H_X": ["1111"],
        "H_Z": ["1100", "0011"],
    }


def test_fom13_top_level_bb_rebuilds_as_authoritative_construction():
    claim = {
        "ell": 2,
        "m": 3,
        "A_terms": [[1, 0], [0, 0]],
        "B_terms": [[1, 1], [0, 1]],
        "geometry": {
            "schema_version": 1,
            "family": "twisted_torus",
            "twist": 1,
        },
        "target_mode": TARGET_MODE_SCALAR_13_INCLUSIVE,
    }
    code, hx, hz, normalized, identity, source = _rebuild_claim(claim)

    assert normalized == {
        "construction": {
            "ell": 2,
            "m": 3,
            "A_terms": [[0, 0], [1, 0]],
            "B_terms": [[0, 1], [1, 1]],
            "geometry": {
                "schema_version": 1,
                "family": "twisted_torus",
                "twist": 1,
            },
        },
    }
    assert identity == {"kind": "bb-v1", **normalized["construction"]}
    assert int(code.num_qudits) == hx.shape[1] == hz.shape[1]
    assert isinstance(source, str) and len(source) == 64


def test_fom13_top_level_bb_conflicts_stop_before_direction_planning(
    monkeypatch,
):
    seed = {
        "ell": 6,
        "m": 6,
        "A_terms": [[0, 0], [1, 0], [0, 1]],
        "B_terms": [[0, 0], [2, 0], [0, 2]],
        "target_mode": TARGET_MODE_SCALAR_13_INCLUSIVE,
    }
    code, hx, hz, _, _, _ = _rebuild_claim(seed)
    selected_target = target_binding(
        int(code.num_qudits),
        int(code.dimension),
        TARGET_MODE_SCALAR_13_INCLUSIVE,
    )
    planned = False

    def record_planning(_code):
        nonlocal planned
        planned = True
        raise AssertionError("direction planning reached")

    monkeypatch.setattr(
        matrix_certificate_module,
        "_direction_specs",
        record_planning,
    )

    conflicting_aliases = {
        **seed,
        "target_mode": TARGET_MODE_GIST,
        "target": selected_target,
        "admissibility": css_w6_admissibility_binding(),
    }
    with pytest.raises(ValueError, match="mode does not match"):
        build_matrix_css_certificate(
            conflicting_aliases,
            known_answer_artifact=KNOWN_ANSWER,
        )
    assert planned is False

    claimed_hx = hx.tolist()
    claimed_hx.append(hx[0].tolist())
    forged_witness = {
        **seed,
        "target": selected_target,
        "admissibility": css_w6_admissibility_binding(),
        "H_X": claimed_hx,
        "H_Z": hz.tolist(),
    }
    with pytest.raises(
        ValueError,
        match="packed matrices do not match reconstructed construction",
    ):
        build_matrix_css_certificate(
            forged_witness,
            known_answer_artifact=KNOWN_ANSWER,
        )
    assert planned is False


def _five_qubit_claim():
    # Standard cyclic [[5,1,3]] stabilizers: XZZXI and shifts.
    paulies = ["XZZXI", "IXZZX", "XIXZZ", "ZXIXZ"]
    rows = []
    for pauli in paulies:
        x = [int(item in "XY") for item in pauli]
        z = [int(item in "ZY") for item in pauli]
        rows.append(x + z)
    return {
        "source": "test [[5,1,3]]",
        "symplectic_stabilizer": rows,
    }


def _contradictory_result(status: int) -> dict:
    return {
        "success": False,
        "status": status,
        "message": "contradicts stored feasible optimum",
        "objective": None,
        "mip_dual_bound": None,
        "mip_gap": None,
        "mip_node_count": 0,
        "elapsed_s": 0.0,
        "operator": None,
    }


def test_generic_css_certificate_exports_all_2k_directions():
    certificate = build_matrix_css_certificate(
        _generic_css_claim(),
        known_answer_artifact=KNOWN_ANSWER,
        timeout_per_logical=10,
        total_timeout=30,
    )
    assert certificate["claim"]["n"] == 4
    assert certificate["claim"]["k"] == 1
    assert certificate["milp"]["exact"] is True
    assert certificate["milp"]["completed_directions"] == 2
    assert certificate["milp"]["distance"] == 2
    assert certificate["upper_witness"]["weight"] == 2
    expected_target = target_binding(4, 1, TARGET_MODE_GIST)
    assert certificate["claim"]["target"] == expected_target
    assert certificate["claim"]["target_mode"] == TARGET_MODE_GIST
    assert certificate["target"] == expected_target
    assert certificate["target_mode"] == TARGET_MODE_GIST
    assert certificate["target_binding_sha256"] == expected_target["binding_sha256"]
    assert certificate["final_gate"]["selected_target"] == expected_target
    # It is a complete exact certificate, but intentionally not a challenge win.
    assert certificate["passed"] is False
    assert certificate["failure_disposition"]["status"] == "CANDIDATE_REJECTED"
    assert "challenge_win" in certificate["final_gate"]["failures"]
    assert set(certificate["final_gate"]["checks"]) == (
        _TERMINAL_GATE_SHAPES["qldpc-css-matrix-exact"][1]
    )
    assert terminal_candidate_rejection(certificate) is True


def test_matrix_checkpoint_and_certificate_bind_explicit_target(tmp_path):
    checkpoint = tmp_path / "matrix-build-checkpoint.json"
    claim = _generic_css_claim()
    claim["target"] = target_binding(4, 1, TARGET_MODE_SCALAR)

    certificate = build_matrix_css_certificate(
        claim,
        known_answer_artifact=KNOWN_ANSWER,
        timeout_per_logical=10,
        total_timeout=30,
        checkpoint_path=checkpoint,
    )

    saved = json.loads(checkpoint.read_text())
    binding_sha256 = claim["target"]["binding_sha256"]
    assert saved["binding"]["target"] == claim["target"]
    assert saved["binding"]["target_binding_sha256"] == binding_sha256
    assert certificate["claim"]["target"] == claim["target"]
    assert certificate["target_binding_sha256"] == binding_sha256
    assert certificate["final_gate"]["target_gate"]["mode"] == TARGET_MODE_SCALAR


def test_matrix_fom13_policy_is_checked_before_direction_planning(
    monkeypatch,
):
    claim = {
        **_generic_css_claim(),
        "target_mode": TARGET_MODE_SCALAR_13_INCLUSIVE,
        "target": target_binding(
            4,
            1,
            TARGET_MODE_SCALAR_13_INCLUSIVE,
        ),
    }

    planned = False

    def record_planning(_code):
        nonlocal planned
        planned = True
        raise AssertionError("direction planning reached")

    monkeypatch.setattr(
        matrix_certificate_module,
        "_direction_specs",
        record_planning,
    )
    with pytest.raises(ValueError, match="admissibility binding"):
        build_matrix_css_certificate(
            claim,
            known_answer_artifact=KNOWN_ANSWER,
        )
    assert planned is False

    claim["admissibility"] = css_w6_admissibility_binding()
    with pytest.raises(AssertionError, match="direction planning reached"):
        build_matrix_css_certificate(
            claim,
            known_answer_artifact=KNOWN_ANSWER,
        )
    assert planned is True


@pytest.mark.parametrize(
    ("hx_rows", "error"),
    [
        (["1111111"], "row weight exceeds"),
        (["1000000"] * 7, "qubit check degree exceeds"),
    ],
)
def test_matrix_fom13_locality_violation_stops_before_planning(
    monkeypatch,
    hx_rows,
    error,
):
    claim = {
        "source": "invalid-locality [[7,6]]",
        "H_X": hx_rows,
        "H_Z": ["0000000"],
        "target_mode": TARGET_MODE_SCALAR_13_INCLUSIVE,
        "target": target_binding(
            7,
            6,
            TARGET_MODE_SCALAR_13_INCLUSIVE,
        ),
        "admissibility": css_w6_admissibility_binding(),
    }
    planned = False

    def record_planning(_code):
        nonlocal planned
        planned = True
        raise AssertionError("direction planning reached")

    monkeypatch.setattr(
        matrix_certificate_module,
        "_direction_specs",
        record_planning,
    )
    with pytest.raises(ValueError, match=error):
        build_matrix_css_certificate(
            claim,
            known_answer_artifact=KNOWN_ANSWER,
        )
    assert planned is False


def test_matrix_fom13_verifier_rejects_missing_policy_context_before_planning(
    monkeypatch,
):
    selected_target = target_binding(
        4,
        1,
        TARGET_MODE_SCALAR_13_INCLUSIVE,
    )
    certificate = {
        "schema_version": matrix_certificate_module.SCHEMA_VERSION,
        "certificate_type": matrix_certificate_module.CERTIFICATE_TYPE,
        "formulation": matrix_certificate_module.FORMULATION,
        "claim": {
            **_generic_css_claim(),
            "target_mode": TARGET_MODE_SCALAR_13_INCLUSIVE,
            "target": selected_target,
            "admissibility": css_w6_admissibility_binding(),
        },
    }
    planned = False

    def record_planning(_code):
        nonlocal planned
        planned = True
        raise AssertionError("direction planning reached")

    monkeypatch.setattr(
        matrix_certificate_module,
        "_direction_specs",
        record_planning,
    )
    replay = verify_matrix_css_certificate(
        certificate,
        known_answer_artifact=KNOWN_ANSWER,
        rerun_milp=True,
    )

    assert replay["passed"] is False
    assert replay["replay_complete"] is False
    assert "policy context does not replay" in replay["failures"][0]
    assert planned is False


def test_scalar_certificate_uses_selected_target_and_reports_gist_compatibility(
    monkeypatch,
):
    claim = _generic_css_claim()
    claim["target"] = target_binding(4, 1, TARGET_MODE_SCALAR)
    monkeypatch.setattr(
        matrix_certificate_module,
        "classify_win",
        lambda _n, _k, _d: {
            "passed": True,
            "fom": 999.0,
            "reasons": ["synthetic_gist_compatibility"],
        },
    )

    certificate = build_matrix_css_certificate(
        claim,
        known_answer_artifact=KNOWN_ANSWER,
        timeout_per_logical=10,
        total_timeout=30,
    )

    gate = certificate["final_gate"]
    assert gate["challenge_compatibility"]["passed"] is True
    assert gate["selected_target_win"]["passed"] is False
    assert gate["target_gate"]["passed"] is False
    assert gate["checks"]["challenge_win"] is False
    assert gate["accepted"] is False
    assert certificate["passed"] is False


def test_matrix_builder_and_verifier_recompute_claim_target():
    mismatched_claim = _generic_css_claim()
    mismatched_claim["target"] = target_binding(5, 1, TARGET_MODE_SCALAR)
    with pytest.raises(ValueError, match="recomputed parameters"):
        build_matrix_css_certificate(
            mismatched_claim,
            known_answer_artifact=KNOWN_ANSWER,
            timeout_per_logical=10,
            total_timeout=30,
        )

    conflicting_mode_claim = {
        **_generic_css_claim(),
        "target_mode": TARGET_MODE_GIST,
        "target": target_binding(4, 1, TARGET_MODE_SCALAR),
    }
    with pytest.raises(ValueError, match="mode does not match"):
        build_matrix_css_certificate(
            conflicting_mode_claim,
            known_answer_artifact=KNOWN_ANSWER,
            timeout_per_logical=10,
            total_timeout=30,
        )

    certificate = build_matrix_css_certificate(
        {
            **_generic_css_claim(),
            "target": target_binding(4, 1, TARGET_MODE_SCALAR),
        },
        known_answer_artifact=KNOWN_ANSWER,
        timeout_per_logical=10,
        total_timeout=30,
    )
    forged = copy.deepcopy(certificate)
    forged_target = target_binding(5, 1, TARGET_MODE_SCALAR)
    forged["claim"]["target"] = forged_target
    forged["target"] = forged_target
    forged["target_binding_sha256"] = forged_target["binding_sha256"]
    forged["certificate_sha256"] = matrix_certificate_module._certificate_sha256(
        forged
    )

    result = verify_matrix_css_certificate(
        forged,
        known_answer_artifact=KNOWN_ANSWER,
        rerun_milp=False,
    )
    assert result["passed"] is False
    assert result["replay_complete"] is False
    assert "recomputed parameters" in result["failures"][0]


def test_generic_noncss_five_qubit_certificate_exports_symplectic_witness():
    certificate = build_noncss_certificate(
        _five_qubit_claim(),
        known_answer_artifact=KNOWN_ANSWER,
        timeout_per_logical=10,
        total_timeout=30,
    )
    assert certificate["claim"]["n"] == 5
    assert certificate["claim"]["k"] == 1
    assert certificate["milp"]["exact"] is True
    assert certificate["milp"]["completed_directions"] == 2
    assert certificate["milp"]["distance"] == 3
    assert certificate["upper_witness"]["weight"] == 3
    assert certificate["passed"] is False
    assert certificate["failure_disposition"]["status"] == "CANDIDATE_REJECTED"
    observed_checks = set(certificate["final_gate"]["checks"])
    assert observed_checks == (
        _TERMINAL_GATE_SHAPES["qldpc-noncss-matrix-exact"][1]
    )
    # Both non-CSS certificate kinds call the same _static_gate producer.
    assert observed_checks == (
        _TERMINAL_GATE_SHAPES["qldpc-pbb-noncss-exact"][1]
    )
    assert terminal_candidate_rejection(certificate) is True


def test_exact_build_with_unverified_known_answer_is_incomplete(tmp_path):
    unavailable_baseline = tmp_path / "invalid-known-answer.json"
    unavailable_baseline.write_text("{}\n")

    certificate = build_matrix_css_certificate(
        _generic_css_claim(),
        known_answer_artifact=unavailable_baseline,
        timeout_per_logical=10,
        total_timeout=30,
    )

    assert certificate["milp"]["exact"] is True
    assert certificate["passed"] is False
    assert certificate["failure_disposition"] == {
        "schema_version": 1,
        "status": "INCOMPLETE",
        "domain": "known_answer",
        "codes": ["KNOWN_ANSWER_GATE_UNVERIFIED"],
    }


@pytest.mark.parametrize("solver_status", [2, 3])
def test_generic_css_verifier_retries_contradictory_terminal_status(
    monkeypatch, solver_status,
):
    certificate = build_matrix_css_certificate(
        _generic_css_claim(),
        known_answer_artifact=KNOWN_ANSWER,
        timeout_per_logical=10,
        total_timeout=30,
    )
    monkeypatch.setattr(
        matrix_certificate_module,
        "solve_css_direction",
        lambda *_args, **_kwargs: _contradictory_result(solver_status),
    )

    result = verify_matrix_css_certificate(
        certificate,
        known_answer_artifact=KNOWN_ANSWER,
        timeout_per_logical=10,
        total_timeout=30,
    )

    assert result["passed"] is False
    assert result["replay_complete"] is False


@pytest.mark.parametrize("solver_status", [2, 3])
def test_noncss_verifier_retries_contradictory_terminal_status(
    monkeypatch, solver_status,
):
    certificate = build_noncss_certificate(
        _five_qubit_claim(),
        known_answer_artifact=KNOWN_ANSWER,
        timeout_per_logical=10,
        total_timeout=30,
    )
    monkeypatch.setattr(
        noncss_certificate_module,
        "solve_symplectic_direction",
        lambda *_args, **_kwargs: _contradictory_result(solver_status),
    )

    result = verify_noncss_certificate(
        certificate,
        known_answer_artifact=KNOWN_ANSWER,
        timeout_per_logical=10,
        total_timeout=30,
    )

    assert result["passed"] is False
    assert result["replay_complete"] is False


@pytest.mark.parametrize(
    ("builder", "verifier", "module", "claim"),
    [
        (
            build_matrix_css_certificate,
            verify_matrix_css_certificate,
            matrix_certificate_module,
            _generic_css_claim,
        ),
        (
            build_noncss_certificate,
            verify_noncss_certificate,
            noncss_certificate_module,
            _five_qubit_claim,
        ),
    ],
)
def test_universal_reconstruction_io_error_is_retryable(
    monkeypatch,
    builder,
    verifier,
    module,
    claim,
):
    certificate = builder(
        claim(),
        known_answer_artifact=KNOWN_ANSWER,
        timeout_per_logical=10,
        total_timeout=30,
    )
    monkeypatch.setattr(
        module,
        "_file_sha256",
        lambda _path: (_ for _ in ()).throw(OSError("storage unavailable")),
    )

    result = verifier(
        certificate,
        known_answer_artifact=KNOWN_ANSWER,
        rerun_milp=False,
    )

    assert result["passed"] is False
    assert result["replay_complete"] is False
    assert result["failure_disposition"]["status"] == "INCOMPLETE"
    assert result["failure_disposition"]["domain"] == "io"
