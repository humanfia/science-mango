import evaluation.certificate_dispatch as dispatch
import pytest
from evaluation.certificate import build_css_certificate
from evaluation.certificate_dispatch import (
    BB_CSS_TYPE,
    EXACT_ANCHOR_CSS_TYPE,
    SUPPORTED_CERTIFICATE_TYPES,
    builder_for_claim,
    verifier_for_certificate,
)
from evaluation.matrix_certificate import build_matrix_css_certificate
from evaluation.noncss_certificate import build_noncss_certificate
from evaluation.sector_certificate import (
    REQUEST_FIELD as SECTOR_SAT_REQUEST_FIELD,
    build_sector_sat_certificate,
)
from evaluation.target_policy import (
    TARGET_MODE_SCALAR_13_INCLUSIVE,
    TARGET_MODE_SCALAR_INCLUSIVE,
)
from evaluation.twobga_certificate import build_twobga_certificate
from scripts.screen_frontier_twobga import TWOBGA_REQUEST_FIELD


def test_builder_dispatches_every_claim_shape():
    assert builder_for_claim({"ell": 6, "m": 6}) is build_css_certificate
    assert (
        builder_for_claim({"H_X": [[1]], "H_Z": [[0]]}) is build_matrix_css_certificate
    )
    assert (
        builder_for_claim({"construction": {"kind": "fixture"}})
        is build_matrix_css_certificate
    )
    assert builder_for_claim({"C_terms": [[0, 0]]}) is build_noncss_certificate
    assert (
        builder_for_claim({"symplectic_stabilizer": [[1, 0]]})
        is build_noncss_certificate
    )
    assert builder_for_claim({TWOBGA_REQUEST_FIELD: {}}) is build_twobga_certificate


def test_fom13_plain_bb_dispatches_to_policy_aware_matrix_certificate():
    claim = {
        "ell": 2,
        "m": 3,
        "A_terms": [[0, 0], [1, 0]],
        "B_terms": [[0, 1], [1, 1]],
        "target_mode": TARGET_MODE_SCALAR_13_INCLUSIVE,
    }
    assert builder_for_claim(claim) is build_matrix_css_certificate
    assert builder_for_claim({
        **claim,
        "target_mode": TARGET_MODE_SCALAR_INCLUSIVE,
    }) is build_css_certificate
    assert builder_for_claim({
        **claim,
        SECTOR_SAT_REQUEST_FIELD: {},
    }) is build_sector_sat_certificate
    assert builder_for_claim({
        **claim,
        TWOBGA_REQUEST_FIELD: {},
    }) is build_twobga_certificate

    nested_target_only = dict(claim)
    nested_target_only.pop("target_mode")
    nested_target_only["target"] = {
        "target_mode": TARGET_MODE_SCALAR_13_INCLUSIVE,
    }
    assert builder_for_claim(nested_target_only) is build_matrix_css_certificate

    conflicting_aliases = {
        **claim,
        "target_mode": TARGET_MODE_SCALAR_INCLUSIVE,
        "target": {"mode": TARGET_MODE_SCALAR_13_INCLUSIVE},
    }
    assert builder_for_claim(conflicting_aliases) is build_matrix_css_certificate
    assert builder_for_claim({
        **claim,
        "C_terms": [[0, 0]],
    }) is build_noncss_certificate
    assert builder_for_claim({
        **claim,
        "symplectic_stabilizer": [],
    }) is build_noncss_certificate


def test_verifier_dispatch_is_fail_closed():
    assert len(SUPPORTED_CERTIFICATE_TYPES) == 7
    assert SUPPORTED_CERTIFICATE_TYPES[-1] == EXACT_ANCHOR_CSS_TYPE
    assert tuple(value.encode("ascii") for value in SUPPORTED_CERTIFICATE_TYPES[:6]) == (
        b"qldpc-css-bb-exact",
        b"qldpc-css-matrix-exact",
        b"qldpc-pbb-noncss-exact",
        b"qldpc-noncss-matrix-exact",
        b"qldpc-css-bb-sector-sat-exact",
        b"qldpc-css-bb-twobga-subsystem-exact",
    )
    assert verifier_for_certificate({"certificate_type": BB_CSS_TYPE})
    with pytest.raises(ValueError, match="unsupported certificate_type"):
        verifier_for_certificate({"certificate_type": "untrusted"})


def test_css_checkpoint_controls_reach_bb_and_matrix_schemas(monkeypatch):
    calls = {}

    def css_builder(claim, **kwargs):
        calls["css_build"] = kwargs
        return {"certificate_type": BB_CSS_TYPE}

    def matrix_builder(
        claim,
        *,
        known_answer_artifact,
        timeout_per_logical,
        total_timeout,
        checkpoint_path,
        resume,
        solver_workers,
    ):
        calls["matrix_build"] = {
            "known_answer_artifact": known_answer_artifact,
            "timeout_per_logical": timeout_per_logical,
            "total_timeout": total_timeout,
            "checkpoint_path": checkpoint_path,
            "resume": resume,
            "solver_workers": solver_workers,
        }
        return {"certificate_type": "qldpc-css-matrix-exact"}

    monkeypatch.setattr(dispatch, "build_css_certificate", css_builder)
    monkeypatch.setattr(dispatch, "build_matrix_css_certificate", matrix_builder)
    controls = {
        "known_answer_artifact": "known.json",
        "timeout_per_logical": 11,
        "total_timeout": 22,
        "checkpoint_path": "checkpoint.json",
        "resume": True,
        "solver_workers": 3,
    }
    dispatch.build_certificate({"ell": 2, "m": 2}, **controls)
    dispatch.build_certificate({"H_X": [[1]], "H_Z": [[0]]}, **controls)

    assert calls["css_build"]["checkpoint_path"] == "checkpoint.json"
    assert calls["css_build"]["resume"] is True
    assert calls["css_build"]["solver_workers"] == 3
    assert calls["matrix_build"]["checkpoint_path"] == "checkpoint.json"
    assert calls["matrix_build"]["resume"] is True
    assert calls["matrix_build"]["solver_workers"] == 3

    def css_verifier(certificate, **kwargs):
        calls["css_verify"] = kwargs
        return {"passed": True}

    def matrix_verifier(
        certificate,
        *,
        known_answer_artifact,
        rerun_milp,
        timeout_per_logical,
        total_timeout,
        solver_workers,
        checkpoint_path,
        resume,
    ):
        calls["matrix_verify"] = {
            "known_answer_artifact": known_answer_artifact,
            "rerun_milp": rerun_milp,
            "timeout_per_logical": timeout_per_logical,
            "total_timeout": total_timeout,
            "solver_workers": solver_workers,
            "checkpoint_path": checkpoint_path,
            "resume": resume,
        }
        return {"passed": True}

    monkeypatch.setattr(dispatch, "verify_css_certificate", css_verifier)
    monkeypatch.setitem(dispatch.VERIFIERS, BB_CSS_TYPE, css_verifier)
    monkeypatch.setitem(
        dispatch.VERIFIERS,
        "qldpc-css-matrix-exact",
        matrix_verifier,
    )
    verify_controls = {
        "known_answer_artifact": "known.json",
        "rerun_milp": True,
        "timeout_per_logical": 11,
        "checkpoint_path": "verify.json",
        "resume": True,
        "total_timeout": 22,
        "solver_workers": 3,
        "artifact_root": "unused-artifacts",
        "trusted_checkers": {"unused": {}},
        "checker_timeout_s": 9,
    }
    dispatch.verify_certificate(
        {"certificate_type": BB_CSS_TYPE},
        **verify_controls,
    )
    dispatch.verify_certificate(
        {"certificate_type": "qldpc-css-matrix-exact"},
        **verify_controls,
    )

    assert calls["css_verify"]["total_timeout"] == 22
    assert calls["css_verify"]["solver_workers"] == 3
    assert calls["matrix_verify"]["checkpoint_path"] == "verify.json"
    assert calls["matrix_verify"]["resume"] is True
