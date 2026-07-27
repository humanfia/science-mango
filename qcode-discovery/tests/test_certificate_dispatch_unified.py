import pytest

import evaluation.certificate_dispatch as dispatch
from evaluation.certificate import build_css_certificate
from evaluation.certificate_dispatch import (
    BB_CSS_TYPE,
    SUPPORTED_CERTIFICATE_TYPES,
    builder_for_claim,
    verifier_for_certificate,
)
from evaluation.matrix_certificate import build_matrix_css_certificate
from evaluation.noncss_certificate import build_noncss_certificate


def test_builder_dispatches_every_claim_shape():
    assert builder_for_claim({"ell": 6, "m": 6}) is build_css_certificate
    assert builder_for_claim({"H_X": [[1]], "H_Z": [[0]]}) is build_matrix_css_certificate
    assert builder_for_claim({"C_terms": [[0, 0]]}) is build_noncss_certificate
    assert builder_for_claim({"symplectic_stabilizer": [[1, 0]]}) is build_noncss_certificate


def test_verifier_dispatch_is_fail_closed():
    assert len(SUPPORTED_CERTIFICATE_TYPES) == 4
    assert verifier_for_certificate({"certificate_type": BB_CSS_TYPE})
    with pytest.raises(ValueError, match="unsupported certificate_type"):
        verifier_for_certificate({"certificate_type": "untrusted"})


def test_bb_checkpoint_controls_do_not_leak_to_other_schemas(monkeypatch):
    calls = {}

    def css_builder(claim, **kwargs):
        calls["css_build"] = kwargs
        return {"certificate_type": BB_CSS_TYPE}

    def matrix_builder(
        claim, *, known_answer_artifact, timeout_per_logical, total_timeout,
    ):
        calls["matrix_build"] = {
            "known_answer_artifact": known_answer_artifact,
            "timeout_per_logical": timeout_per_logical,
            "total_timeout": total_timeout,
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
    assert set(calls["matrix_build"]) == {
        "known_answer_artifact",
        "timeout_per_logical",
        "total_timeout",
    }

    def css_verifier(certificate, **kwargs):
        calls["css_verify"] = kwargs
        return {"passed": True}

    def matrix_verifier(
        certificate, *, known_answer_artifact, rerun_milp,
        timeout_per_logical,
    ):
        calls["matrix_verify"] = {
            "known_answer_artifact": known_answer_artifact,
            "rerun_milp": rerun_milp,
            "timeout_per_logical": timeout_per_logical,
        }
        return {"passed": True}

    monkeypatch.setattr(dispatch, "verify_css_certificate", css_verifier)
    monkeypatch.setitem(dispatch.VERIFIERS, BB_CSS_TYPE, css_verifier)
    monkeypatch.setitem(
        dispatch.VERIFIERS, "qldpc-css-matrix-exact", matrix_verifier,
    )
    verify_controls = {
        "known_answer_artifact": "known.json",
        "rerun_milp": True,
        "timeout_per_logical": 11,
        "checkpoint_path": "verify.json",
        "resume": True,
        "total_timeout": 22,
        "solver_workers": 3,
    }
    dispatch.verify_certificate(
        {"certificate_type": BB_CSS_TYPE}, **verify_controls,
    )
    dispatch.verify_certificate(
        {"certificate_type": "qldpc-css-matrix-exact"}, **verify_controls,
    )

    assert calls["css_verify"]["total_timeout"] == 22
    assert calls["css_verify"]["solver_workers"] == 3
    assert set(calls["matrix_verify"]) == {
        "known_answer_artifact",
        "rerun_milp",
        "timeout_per_logical",
    }
