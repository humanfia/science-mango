"""Tests for the central negative-only structural witness replay gate."""

from __future__ import annotations

import copy
import hashlib
import json

import numpy as np

import humanize.negative_evidence as negative_evidence
from evaluation.target_policy import TARGET_MODE_SCALAR
from humanize.negative_evidence import (
    StructuralLogicalBasisRejection,
    replay_structural_logical_basis_rejection,
)


def _sealed_report(witness):
    payload = {
        "schema_version": 1,
        "kind": "qcode-logical-basis-upper-bound-v1",
        "method": "replayed-minimum-symplectic-basis-row",
        "available": True,
        "upper_bound": witness["weight"],
        "witness": witness,
    }
    encoded = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode()
    return {**payload, "report_sha256": hashlib.sha256(encoded).hexdigest()}


def _row(n, k, witness):
    return {
        "ell": 2,
        "m": 1,
        "A_terms": [[0, 0]],
        "B_terms": [[1, 0]],
        "n": n,
        "k": k,
        "static_eligibility": {
            "checked": True,
            "eligible": True,
            "n": n,
            "k": k,
            "logical_basis_upper_bound": _sealed_report(witness),
        },
    }


def _install_fake_code(monkeypatch, *, n=4, k=1, witness=None):
    if witness is None:
        witness = {
            "side": "X",
            "index": 0,
            "dual_side": "Z",
            "dual_index": 0,
            "weight": 1,
            "bits": [1] + [0] * (n - 1),
        }

    class Code:
        num_qudits = n
        dimension = k

    bits = np.asarray(witness["bits"], dtype=np.uint8)
    dual_bits = np.zeros(n, dtype=np.uint8)
    dual_bits[int(np.flatnonzero(bits)[0])] = 1
    zero_checks = np.zeros((1, n), dtype=np.uint8)
    side_logicals = bits.reshape(1, n)
    dual_logicals = dual_bits.reshape(1, n)
    lx = side_logicals if witness["side"] == "X" else dual_logicals
    lz = dual_logicals if witness["side"] == "X" else side_logicals
    monkeypatch.setattr(
        negative_evidence,
        "build_css_code_from_claim",
        lambda _row: Code(),
    )
    monkeypatch.setattr(
        negative_evidence,
        "symplectic_weight_witness",
        lambda _code: copy.deepcopy(witness),
    )
    monkeypatch.setattr(
        negative_evidence,
        "get_code_matrices",
        lambda _code: (
            zero_checks,
            zero_checks,
            lx,
            lz,
        ),
    )
    return witness


def test_replayed_operator_strictly_below_target_can_skip_audit(monkeypatch):
    witness = _install_fake_code(monkeypatch)

    rejection = replay_structural_logical_basis_rejection(
        _row(4, 1, witness),
        target_mode=TARGET_MODE_SCALAR,
    )

    assert rejection == StructuralLogicalBasisRejection(
        target_mode=TARGET_MODE_SCALAR,
        n=4,
        k=1,
        upper_bound=1,
        required_distance=7,
    )


def test_valid_self_hash_does_not_make_forged_operator_authoritative(
    monkeypatch,
):
    authentic = _install_fake_code(monkeypatch)
    forged = copy.deepcopy(authentic)
    forged["bits"] = [0, 1, 0, 0]
    row = _row(4, 1, forged)

    assert replay_structural_logical_basis_rejection(
        row,
        target_mode=TARGET_MODE_SCALAR,
    ) is None


def test_fresh_scalar_without_replayable_operator_keeps_audit_slot(
    monkeypatch,
):
    witness = _install_fake_code(monkeypatch)
    monkeypatch.setattr(
        negative_evidence,
        "get_code_matrices",
        lambda _code: (
            np.ones((1, 4), dtype=np.uint8),
            np.ones((1, 4), dtype=np.uint8),
            np.asarray([witness["bits"]], dtype=np.uint8),
            np.asarray([witness["bits"]], dtype=np.uint8),
        ),
    )

    assert replay_structural_logical_basis_rejection(
        _row(4, 1, witness),
        target_mode=TARGET_MODE_SCALAR,
    ) is None


def test_rebuilt_parameter_mismatch_keeps_audit_slot(monkeypatch):
    witness = _install_fake_code(monkeypatch)
    row = _row(4, 1, witness)
    row["n"] = 5

    assert replay_structural_logical_basis_rejection(
        row,
        target_mode=TARGET_MODE_SCALAR,
    ) is None


def test_upper_bound_equal_to_required_distance_does_not_reject(monkeypatch):
    bits = [1, 1, 1, 1] + [0] * 68
    witness = {
        "side": "X",
        "index": 0,
        "dual_side": "Z",
        "dual_index": 0,
        "weight": 4,
        "bits": bits,
    }
    _install_fake_code(monkeypatch, n=72, k=72, witness=witness)

    assert replay_structural_logical_basis_rejection(
        _row(72, 72, witness),
        target_mode=TARGET_MODE_SCALAR,
    ) is None


def test_bp_scalar_without_structural_operator_never_skips(monkeypatch):
    witness = _install_fake_code(monkeypatch)
    row = _row(4, 1, witness)
    row["static_eligibility"].pop("logical_basis_upper_bound")
    row.update({"bp_osd_d": 1, "distance_upper_bound": 1, "fom": 0.25})

    assert replay_structural_logical_basis_rejection(
        row,
        target_mode=TARGET_MODE_SCALAR,
    ) is None


def test_actual_twisted_torus_row_rebuilds_and_replays():
    bits = [int(index in {36, 39}) for index in range(72)]
    witness = {
        "side": "X",
        "index": 3,
        "dual_side": "Z",
        "dual_index": 3,
        "weight": 2,
        "bits": bits,
    }
    row = {
        "ell": 6,
        "m": 6,
        "A_terms": [[0, 0], [0, 3]],
        "B_terms": [[0, 2], [0, 5], [1, 0], [1, 3]],
        "geometry": {
            "schema_version": 1,
            "family": "twisted_torus",
            "twist": 1,
        },
        "n": 72,
        "k": 36,
        "static_eligibility": {
            "checked": True,
            "eligible": True,
            "n": 72,
            "k": 36,
            "logical_basis_upper_bound": _sealed_report(witness),
        },
    }

    rejection = replay_structural_logical_basis_rejection(
        row,
        target_mode=TARGET_MODE_SCALAR,
    )

    assert rejection is not None
    assert rejection.upper_bound == 2
    assert rejection.required_distance == 5
