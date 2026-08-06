"""Proof semantics for the two-block sparse-kernel prefilter."""

from __future__ import annotations

import copy

import numpy as np
import pytest
from qldpc import codes

from evaluation.coset_two_block import build_coset_candidate
from evaluation.distance_milp import get_code_matrices
from evaluation.low_weight_oracle import evaluate_css_low_weight_oracle
import evaluation.two_block_sparse_kernel_oracle as sparse_kernel
from evolve.coset_search_contract import (
    COSET_CANDIDATE_SCHEMA_VERSION_V3,
    COSET_RENDERER_V3_ID,
    COSET_REPRESENTATION_ID_V3,
    action_search_views,
)


def _single_block_d2_code():
    checks = np.array([[1, 1, 1, 1]], dtype=np.uint8)
    lx = np.array([[1, 1, 0, 0], [1, 0, 1, 0]], dtype=np.uint8)
    lz = np.array([[0, 1, 0, 1], [0, 0, 1, 1]], dtype=np.uint8)
    return checks, checks.copy(), lx, lz


def _cross_block_only_d2_code():
    # Every nonzero vector in the kernel of either three-column restriction
    # has weight three.  Equal columns across the two coordinate blocks still
    # create a full-code weight-two logical, so restricted UNSAT must not be
    # confused with a distance lower bound.
    checks = np.array(
        [
            [1, 1, 0, 1, 1, 0],
            [0, 1, 1, 0, 1, 1],
        ],
        dtype=np.uint8,
    )
    code = codes.CSSCode(
        checks,
        checks,
        field=2,
        promise_equal_distance_xz=False,
    )
    return get_code_matrices(code)


def _real_two_block_code():
    view = action_search_views()[0]
    left = [view.left_identity_id, *(
        item for item in view.left_element_ids
        if item != view.left_identity_id
    )][:3]
    right = [view.right_identity_id, *(
        item for item in view.right_element_ids
        if item != view.right_identity_id
    )][:3]
    return build_coset_candidate({
        "schema_version": COSET_CANDIDATE_SCHEMA_VERSION_V3,
        "representation_id": COSET_REPRESENTATION_ID_V3,
        "renderer_descriptor_id": COSET_RENDERER_V3_ID,
        "action_id": view.action_id,
        "support_split": [3, 3],
        "left_support": left,
        "right_support": right,
    })


def test_single_block_witness_lifts_and_replays_against_full_code():
    hx, hz, lx, lz = _single_block_d2_code()
    evidence = sparse_kernel.evaluate_two_block_sparse_kernel_oracle(
        hx, hz, lx, lz, max_weight=2
    )

    assert evidence["outcome"] == "SAT"
    assert evidence["distance_lower_bound"] is None
    assert evidence["distance_upper_bound"] == 2
    assert evidence["witness"]["query_id"] == "X:A"
    assert evidence["witness"]["block"] == "A"
    assert evidence["witness"]["kernel_component"] == "B^T"
    assert evidence["witness"]["support"] == [0, 1]
    assert {
        item["kernel_component"] for item in evidence["query_plan"]
    } == {"A", "B", "A^T", "B^T"}
    assert sparse_kernel.verify_two_block_sparse_kernel_oracle(
        evidence, hx, hz, lx, lz
    ) == []


@pytest.mark.parametrize(
    ("sector", "block", "component"),
    (("X", "A", "B^T"), ("X", "B", "A^T"),
     ("Z", "A", "A"), ("Z", "B", "B")),
)
def test_real_coset_builder_uses_the_declared_four_kernel_components(
    sector,
    block,
    component,
):
    code = _real_two_block_code()
    hx, hz, lx, lz = get_code_matrices(code)
    block_size = int(code.matrix_a.shape[0])
    checks, _logicals, _start = sparse_kernel._query_problem(
        hx,
        hz,
        lx,
        lz,
        sector=sector,
        block=block,
        block_size=block_size,
    )
    expected = {
        "A": code.matrix_a,
        "B": code.matrix_b,
        "A^T": code.matrix_a.T,
        "B^T": code.matrix_b.T,
    }[component]
    assert sparse_kernel._KERNEL_COMPONENT[(sector, block)] == component
    assert np.array_equal(checks, expected)


def test_restricted_unsat_never_claims_a_full_distance_lower_bound():
    hx, hz, lx, lz = _cross_block_only_d2_code()
    restricted = sparse_kernel.evaluate_two_block_sparse_kernel_oracle(
        hx, hz, lx, lz, max_weight=2
    )
    unrestricted = evaluate_css_low_weight_oracle(
        hx, hz, lx, lz, max_weight=2
    )

    assert restricted["outcome"] == "NO_SINGLE_BLOCK_WITNESS"
    assert restricted["distance_lower_bound"] is None
    assert restricted["single_block_minimum_weight_lower_bound"] == 3
    assert set(restricted["queries"]) == {"X:A", "X:B", "Z:A", "Z:B"}
    assert all(
        query["outcome"] == "UNSAT"
        for query in restricted["queries"].values()
    )
    assert sparse_kernel.verify_two_block_sparse_kernel_oracle(
        restricted, hx, hz, lx, lz
    ) == []
    assert unrestricted["outcome"] == "SAT"
    assert unrestricted["witness"]["support"] in ([0, 3], [1, 4], [2, 5])


@pytest.mark.parametrize("field", ("block", "support", "bits"))
def test_tampered_lifted_witness_is_rejected(field):
    hx, hz, lx, lz = _single_block_d2_code()
    evidence = sparse_kernel.evaluate_two_block_sparse_kernel_oracle(
        hx, hz, lx, lz, max_weight=2
    )
    tampered = copy.deepcopy(evidence)
    if field == "block":
        tampered["witness"]["block"] = "B"
    elif field == "support":
        tampered["witness"]["support"] = [2, 3]
    else:
        tampered["witness"]["bits"][0] ^= 1

    failures = sparse_kernel.verify_two_block_sparse_kernel_oracle(
        tampered, hx, hz, lx, lz
    )
    assert "single-block oracle evidence self-hash mismatch" in failures
    assert any("SAT summary does not replay" in failure for failure in failures)


def test_matrix_and_block_layout_are_bound_into_evidence():
    hx, hz, lx, lz = _single_block_d2_code()
    evidence = sparse_kernel.evaluate_two_block_sparse_kernel_oracle(
        hx, hz, lx, lz, max_weight=2
    )
    changed_hx = hx.copy()
    changed_hx[0, 0] ^= 1

    assert "single-block oracle matrix/source binding mismatch" in (
        sparse_kernel.verify_two_block_sparse_kernel_oracle(
            evidence, changed_hx, hz, lx, lz
        )
    )
    with pytest.raises(ValueError, match="equal-size two-block"):
        sparse_kernel.evaluate_two_block_sparse_kernel_oracle(
            hx[:, :3], hz[:, :3], lx[:, :3], lz[:, :3], max_weight=2
        )

    forged_source = copy.deepcopy(evidence)
    forged_source["source_sha256"] = "0" * 64
    sparse_kernel._seal(forged_source)
    assert "single-block oracle source binding mismatch" in (
        sparse_kernel.verify_two_block_sparse_kernel_oracle(
            forged_source, hx, hz, lx, lz
        )
    )


def test_unknown_query_stays_retryable_and_gets_no_bound(monkeypatch):
    hx, hz, lx, lz = _single_block_d2_code()

    def unknown(checks, logicals, *, max_weight, sector, hard_timeout_s):
        return sparse_kernel._sector_oracle._timeout_sector_evidence(
            checks,
            logicals,
            max_weight=max_weight,
            sector=sector,
        )

    monkeypatch.setattr(
        sparse_kernel._sector_oracle, "evaluate_low_weight_sector", unknown
    )
    evidence = sparse_kernel.evaluate_two_block_sparse_kernel_oracle(
        hx, hz, lx, lz, max_weight=2, hard_timeout_s=1.0
    )

    assert evidence["outcome"] == "UNKNOWN"
    assert evidence["retryable"] is True
    assert evidence["distance_lower_bound"] is None
    assert evidence["distance_upper_bound"] is None
    assert sparse_kernel.verify_two_block_sparse_kernel_oracle(
        evidence, hx, hz, lx, lz
    ) == []
