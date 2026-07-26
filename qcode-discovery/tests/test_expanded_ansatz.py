import argparse

import numpy as np
import pytest

import scripts.search_expanded_ansatz as expanded

from evaluation.bb_code import build_bb_code
from evaluation.certificate import solve_css_direction, verify_css_witness
from evaluation.distance_milp import get_code_matrices
from scripts.search_expanded_ansatz import (
    _resume_config,
    _screen_code,
    _xor_prefilter,
    candidate_key,
    parse_shapes,
    parse_term_splits,
    sample_css_claim,
)


def test_expanded_sampler_covers_weight_four_to_six():
    rng = np.random.default_rng(9)
    splits = parse_term_splits("2+2,2+3,3+3,4+2")
    weights = set()
    for trial in range(100):
        claim = sample_css_claim(
            rng, ((6, 6),), splits, seed=9, trial=trial,
        )
        weights.add(len(claim["A_terms"]) + len(claim["B_terms"]))
        assert len(set(map(tuple, claim["A_terms"]))) == len(claim["A_terms"])
        assert len(set(map(tuple, claim["B_terms"]))) == len(claim["B_terms"])
        code = build_bb_code(
            claim["ell"], claim["m"], claim["A_terms"], claim["B_terms"],
        )
        hx, hz, _, _ = get_code_matrices(code)
        assert max(np.asarray(hx).sum(axis=1)) <= 6
        assert max(np.asarray(hz).sum(axis=1)) <= 6
    assert weights == {4, 5, 6}


def test_expanded_key_ignores_term_order_but_binds_shape():
    claim = {
        "ell": 6, "m": 6,
        "A_terms": [[0, 0], [1, 0]],
        "B_terms": [[0, 1], [2, 0]],
    }
    reordered = {**claim, "A_terms": list(reversed(claim["A_terms"]))}
    reshaped = {**claim, "ell": 9}
    assert candidate_key(claim) == candidate_key(reordered)
    assert candidate_key(claim) != candidate_key(reshaped)


def test_expanded_parser_rejects_overweight_checks():
    assert parse_shapes("6x6,12x6") == ((6, 6), (12, 6))
    with pytest.raises(Exception):
        parse_term_splits("3+4")


def test_css_solver_objective_matches_saved_incumbent_weight():
    checks = np.zeros((0, 3), dtype=np.uint8)
    target = np.asarray([1, 0, 0], dtype=np.uint8)
    result = solve_css_direction(checks, target, timeout=10)
    assert result["success"] is True
    assert result["objective"] == result["operator"]["weight"] == 1
    assert verify_css_witness(result, checks, target) == []


def test_threshold_screen_marks_only_complete_infeasibility_as_proven(monkeypatch):
    checks = np.zeros((0, 3), dtype=np.uint8)
    targets = [
        np.asarray([1, 0, 0], dtype=np.uint8),
        np.asarray([0, 1, 0], dtype=np.uint8),
    ]
    monkeypatch.setattr(
        expanded,
        "_direction_specs",
        lambda code: [
            ("Z", index, "hx", checks, target)
            for index, target in enumerate(targets)
        ],
    )
    monkeypatch.setattr(
        expanded,
        "solve_css_below_threshold",
        lambda checks, target, *, max_weight, timeout: {
            "success": False,
            "status": 2,
            "message": "infeasible",
            "threshold_infeasible": True,
            "max_weight": max_weight,
            "objective": None,
            "mip_dual_bound": None,
            "mip_gap": None,
            "operator": None,
        },
    )
    status, directions, exact = _screen_code(
        object(),
        required_distance=2,
        screen_mode="threshold",
        timeout_per_logical=1,
        total_timeout_per_code=10,
    )
    assert status == "THRESHOLD_PROVEN"
    assert len(directions) == 2
    assert all(item["witness_verified"] is False for item in directions)
    assert exact is False


def test_timeout_incumbent_is_not_promoted_to_exact_distance(monkeypatch):
    checks = np.zeros((0, 3), dtype=np.uint8)
    target = np.asarray([1, 0, 0], dtype=np.uint8)
    monkeypatch.setattr(
        expanded,
        "_direction_specs",
        lambda code: [("Z", 0, "hx", checks, target)],
    )
    monkeypatch.setattr(
        expanded,
        "solve_css_direction",
        lambda checks, target, *, timeout: {
            "success": False,
            "status": 1,
            "message": "timeout",
            "objective": 8,
            "mip_dual_bound": 3.0,
            "mip_gap": 0.625,
            "operator": None,
        },
    )
    status, directions, exact = _screen_code(
        object(),
        required_distance=6,
        screen_mode="exact",
        timeout_per_logical=1,
        total_timeout_per_code=10,
    )
    assert status == "UNRESOLVED"
    assert directions[0]["objective"] == 8
    assert directions[0]["mip_dual_bound"] == 3.0
    assert exact is False


def test_resume_config_allows_extending_total_trials():
    base = dict(
        seed=1,
        trials=100,
        shapes=((6, 6),),
        term_splits=((3, 3),),
        sampler="mixed",
        structured_probability=0.5,
        structured_max_mutations=1,
        mutation_radius=1,
        template_labels=None,
        screen_mode="exact",
        shard_count=4,
        shard_index=2,
    )
    first = _resume_config(argparse.Namespace(**base))
    second = _resume_config(argparse.Namespace(**{**base, "trials": 200}))
    assert first == second


def test_xor_prefilter_rejects_global_sector_witness(monkeypatch):
    matrix = np.zeros((1, 4), dtype=np.uint8)
    targets = np.eye(2, 4, dtype=np.uint8)
    calls = []

    def solve(checks, logicals, **kwargs):
        calls.append(kwargs)
        return {
            "operator": {"weight": 2},
            "objective": 2,
            "threshold_infeasible": False,
            "max_weight": kwargs["max_weight"],
        }

    monkeypatch.setattr(expanded, "solve_css_sector_xor", solve)
    monkeypatch.setattr(
        expanded,
        "verify_css_sector_witness",
        lambda evidence, checks, targets: [],
    )
    status, sectors = _xor_prefilter(
        matrix,
        matrix,
        targets,
        targets,
        required_distance=6,
        timeout_per_sector=0.5,
        workers=1,
        seed=4,
    )
    assert status == "REJECTED"
    assert len(sectors) == 1
    assert sectors[0]["sector"] == "X"
    assert sectors[0]["witness_verified"] is True
    assert calls[0]["max_weight"] == 5


def test_xor_prefilter_can_prove_both_sectors(monkeypatch):
    matrix = np.zeros((1, 4), dtype=np.uint8)
    targets = np.eye(2, 4, dtype=np.uint8)
    monkeypatch.setattr(
        expanded,
        "solve_css_sector_xor",
        lambda checks, logicals, **kwargs: {
            "operator": None,
            "objective": None,
            "threshold_infeasible": True,
            "max_weight": kwargs["max_weight"],
        },
    )
    status, sectors = _xor_prefilter(
        matrix,
        matrix,
        targets,
        targets,
        required_distance=6,
        timeout_per_sector=0.5,
        workers=1,
        seed=4,
    )
    assert status == "THRESHOLD_PROVEN"
    assert [item["sector"] for item in sectors] == ["X", "Z"]


def test_persist_record_is_fsynced_before_dedup_completion(tmp_path, monkeypatch):
    events = []

    class FakeDedup:
        def complete(self, digest):
            events.append(("complete", digest))
            return True

    monkeypatch.setattr(expanded.os, "fsync", lambda descriptor: events.append(("fsync", descriptor)))
    record = {"canonical_digest": "digest", "status": "REJECTED"}
    stats = {"dedup_completion_lost": 0}
    with (tmp_path / "results.jsonl").open("w") as stream:
        expanded._persist_and_complete(stream, record, FakeDedup(), stats)

    assert events[0][0] == "fsync"
    assert events[1] == ("complete", "digest")
    assert stats["dedup_completion_lost"] == 0
