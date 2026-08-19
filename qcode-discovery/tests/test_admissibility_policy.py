from __future__ import annotations

import numpy as np
import pytest

from evaluation.admissibility_policy import (
    css_w6_admissibility_binding,
    evaluate_css_w6_admissibility,
    require_css_w6_admissibility,
    validate_css_w6_admissibility_binding,
)


def test_css_w6_binding_is_versioned_and_self_hashed():
    binding = css_w6_admissibility_binding()
    assert binding == {
        "schema_version": 1,
        "mode": "css-stabilizer-check-row-weight-at-most-6-v1",
        "code_type": "css",
        "matrix_scope": ["H_X", "H_Z"],
        "metric": "binary-hamming-support-per-row",
        "maximum": 6,
        "matrix_authority": "fresh-rebuild-from-construction",
        "reported_weight_fields_authoritative": False,
        "row_reduction_allowed": False,
        "binding_sha256": (
            "c8b9f4d817ab9e88ec2f396f03a2b0bc163d0761656f7374"
            "c7f5880e3402bdb5"
        ),
    }
    assert validate_css_w6_admissibility_binding(binding) == binding
    with pytest.raises(ValueError, match="missing or stale"):
        validate_css_w6_admissibility_binding({**binding, "maximum": 7})


def test_css_w6_report_checks_original_rows_and_separate_degree_gate():
    hx = np.asarray([[1, 1, 1, 1, 1, 1, 0, 0]], dtype=np.uint8)
    hz = np.asarray([[0, 0, 1, 1, 1, 1, 1, 1]], dtype=np.uint8)
    report = require_css_w6_admissibility(hx, hz)
    assert report["passed"] is True
    assert report["max_x_check_weight"] == 6
    assert report["max_z_check_weight"] == 6
    assert report["max_check_row_weight"] == 6
    assert report["additional_existing_gate"] == {
        "mode": "combined-qubit-check-degree-at-most-6-v1",
        "maximum": 6,
        "observed": 2,
        "passed": True,
    }


def test_css_w6_rejects_a_seven_body_stabilizer_check():
    hx = np.ones((1, 7), dtype=np.uint8)
    hz = np.zeros((1, 7), dtype=np.uint8)
    report = evaluate_css_w6_admissibility(hx, hz)
    assert report["max_check_row_weight"] == 7
    assert report["passed"] is False
    with pytest.raises(ValueError, match="row weight exceeds"):
        require_css_w6_admissibility(hx, hz)


def test_css_w6_keeps_existing_qubit_degree_gate_separate_and_fail_closed():
    hx = np.ones((4, 1), dtype=np.uint8)
    hz = np.ones((3, 1), dtype=np.uint8)
    report = evaluate_css_w6_admissibility(hx, hz)
    assert report["max_check_row_weight"] == 1
    assert report["all_x_rows_within_limit"] is True
    assert report["all_z_rows_within_limit"] is True
    assert report["additional_existing_gate"]["observed"] == 7
    assert report["passed"] is False
    with pytest.raises(ValueError, match="qubit check degree exceeds"):
        require_css_w6_admissibility(hx, hz)


def test_css_w6_rejects_nonbinary_or_mismatched_matrices():
    with pytest.raises(ValueError, match="non-binary"):
        evaluate_css_w6_admissibility([[2]], [[0]])
    with pytest.raises(ValueError, match="same number of qubits"):
        evaluate_css_w6_admissibility([[1, 0]], [[1]])
