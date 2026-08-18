"""Tests for the disjoint SAT Stage-3 screen."""

from __future__ import annotations

import json
import time
from itertools import product

import numpy as np

from evaluation.distance_sat import (
    SAT_EVIDENCE_KIND,
    SAT_EVIDENCE_SCHEMA_VERSION,
)
from scripts import screen_frontier_sat as sat_screen


def _evidence(
    outcome: str,
    *,
    threshold: int,
    objective: int | None = None,
    anchor_cube: dict | None = None,
):
    value = {
        "schema_version": SAT_EVIDENCE_SCHEMA_VERSION,
        "evidence_kind": SAT_EVIDENCE_KIND,
        "outcome": outcome,
        "decision_complete": True,
        "threshold_infeasible": outcome == "unsat",
        "max_weight": threshold,
        "operator": None if outcome == "unsat" else {"test": True},
        "objective": objective,
        "zero_anchor_indices": (
            [] if anchor_cube is None else anchor_cube["zero_anchor_indices"]
        ),
        "one_anchor_index": (
            None if anchor_cube is None else anchor_cube["one_anchor_index"]
        ),
        "anchor_cube_sha256": (
            None if anchor_cube is None else anchor_cube["cube_sha256"]
        ),
    }
    if anchor_cube is not None:
        clauses = [
            [-(index + 1)] for index in anchor_cube["zero_anchor_indices"]
        ] + [[anchor_cube["one_anchor_index"] + 1]]
        instance = {
            "anchor_constraint_formulation": (
                "anchor-or-first-nonzero-unit-clauses-v1"
            ),
            "anchor_indices": anchor_cube["anchor_indices"],
            "zero_anchor_indices": anchor_cube["zero_anchor_indices"],
            "one_anchor_index": anchor_cube["one_anchor_index"],
            "anchor_cube_sha256": anchor_cube["cube_sha256"],
            "anchor_unit_clauses": clauses,
            "anchor_unit_clauses_sha256": sat_screen._canonical_sha256(clauses),
        }
        instance["binding_sha256"] = sat_screen._canonical_sha256(instance)
        value["instance"] = instance
        value["cnf"] = {
            "anchor_unit_clauses_sha256": sat_screen._canonical_sha256(
                clauses,
            ),
        }
    value["evidence_sha256"] = sat_screen._canonical_sha256(value)
    return value


def _unit(
    phase: str,
    sector: str,
    evidence: dict,
    *,
    partition: int | None = None,
    anchor_cube: dict | None = None,
):
    key = (
        f"{phase}-{sector}"
        if anchor_cube is None and partition is None
        else sat_screen._unit_key(phase, sector, partition, anchor_cube)
    )
    return key, {
        "unit_id": key,
        "phase": phase,
        "sector": sector,
        "partition_index": partition,
        "anchor_cube": anchor_cube,
        "solver_evidence": evidence,
    }


def test_css_logical_detector_dimension_replay():
    hx = np.array([[1, 1]], dtype=np.uint8)
    hz = np.zeros((0, 2), dtype=np.uint8)
    lx = np.array([[1, 0]], dtype=np.uint8)
    lz = np.array([[1, 1]], dtype=np.uint8)
    report = sat_screen.verify_css_logical_detectors(hx, hz, lx, lz)
    assert report["verified"] is True
    assert report["logical_duality"] is True

    invalid = sat_screen.verify_css_logical_detectors(
        hx, hz, lx, np.zeros_like(lz),
    )
    assert invalid["verified"] is False


def test_artifact_requires_two_lower_sectors_and_equal_weight_witness():
    units = dict([
        _unit("lower", "X", _evidence("unsat", threshold=1)),
        _unit("lower", "Z", _evidence("unsat", threshold=1)),
        _unit("upper", "X", _evidence("sat", threshold=2, objective=2)),
    ])
    common = {
        "candidate": {"k": 1, "required_distance": 2},
        "mode": "global",
        "translation_symmetry": {"verified": True},
        "logical_detector": {"verified": True},
        "expected_units": 4,
        "started": time.monotonic(),
    }
    exact = sat_screen._artifact(units=units, **common)
    assert exact["status"] == "EXACT_PROVEN"
    assert exact["completed_lower_decisions"] == 2
    assert exact["upper_witness"]["sector"] == "X"

    incomplete = sat_screen._artifact(
        units={key: value for key, value in units.items() if key != "lower-Z"},
        **common,
    )
    assert incomplete["status"] == "UNRESOLVED"

    low_key, low = _unit(
        "upper", "Z", _evidence("sat", threshold=2, objective=1),
    )
    rejected = sat_screen._artifact(
        units={**units, low_key: low},
        **common,
    )
    assert rejected["status"] == "REJECTED"
    assert rejected["low_witnesses"]


def test_upper_unsat_pair_promotes_stronger_global_threshold():
    units = dict([
        _unit("upper", "X", _evidence("unsat", threshold=2)),
        _unit("upper", "Z", _evidence("unsat", threshold=2)),
        # Deliberately omit all first-nonzero lower units: the two global
        # decisions at the stronger threshold already cover every logical.
    ])
    artifact = sat_screen._artifact(
        candidate={"k": 3, "required_distance": 2},
        mode="first-nonzero",
        translation_symmetry={"verified": True},
        logical_detector={"verified": True},
        units=units,
        expected_units=8,
        started=time.monotonic(),
    )

    assert artifact["status"] == "THRESHOLD_PROVEN"
    assert artifact["requested_coverage_mode"] == "first-nonzero"
    assert artifact["coverage_mode"] == "global"
    assert artifact["lower_bound_threshold"] == 2
    assert artifact["expected_lower_decisions"] == 2
    assert artifact["completed_lower_decisions"] == 2
    assert {item["sector"] for item in artifact["lower_bound_decisions"]} == {
        "X",
        "Z",
    }


def test_proof_plan_prioritizes_fair_interleaved_lower_units():
    assert sat_screen._proof_plan("first-nonzero", 2) == [
        ("lower", "X", 0, None),
        ("lower", "Z", 0, None),
        ("lower", "X", 1, None),
        ("lower", "Z", 1, None),
        ("upper", "X", None, None),
        ("upper", "Z", None, None),
    ]
    cubes = sat_screen.build_anchor_cover_cubes((0, 2))
    assert sat_screen._proof_plan(
        "first-nonzero", 1, ("X",), cubes,
    ) == [
        ("lower-global", "X", None, None),
        ("lower", "X", 0, 0),
        ("lower", "X", 0, 1),
        ("upper", "X", None, None),
    ]


def _timeout_attempt(
    config,
    attempt_index,
    *,
    budget=3600.0,
    outcome="hard_timeout",
    policy=sat_screen.SAT_PORTFOLIO_POLICY,
):
    evidence = {
        "outcome": outcome,
        "decision_complete": False,
        "hard_timeout_s": budget,
        "backend": {"solver": config["solver"]},
        "cardinality_encoding": config["cardinality_encoding"],
        "elapsed_s": budget,
    }
    return sat_screen._attempt_record(
        evidence,
        attempt_index=attempt_index,
        requested_solver=config["solver"],
        requested_encoding=config["cardinality_encoding"],
        portfolio_policy=policy,
    )


def test_auto_portfolio_starts_with_four_heterogeneous_lanes():
    seqcounter = sat_screen._portfolio_configs("auto", "seqcounter")
    assert seqcounter[:4] == [
        {"solver": "cadical195", "cardinality_encoding": "seqcounter"},
        {"solver": "kissat404", "cardinality_encoding": "totalizer"},
        {"solver": "glucose42", "cardinality_encoding": "kmtotalizer"},
        {"solver": "minicard", "cardinality_encoding": "native-minicard"},
    ]
    kmtotalizer = sat_screen._portfolio_configs("auto", "kmtotalizer")
    assert kmtotalizer[:4] == [
        {"solver": "cadical195", "cardinality_encoding": "kmtotalizer"},
        {"solver": "kissat404", "cardinality_encoding": "seqcounter"},
        {"solver": "glucose42", "cardinality_encoding": "totalizer"},
        {"solver": "minicard", "cardinality_encoding": "native-minicard"},
    ]


def test_lower_units_rotate_only_the_bounded_diversity_warmup():
    portfolio = sat_screen._portfolio_configs("auto", "kmtotalizer")
    rotated = [
        sat_screen._portfolio_for_lower_unit(portfolio, ordinal)
        for ordinal in range(4)
    ]
    assert [lane[0] for lane in rotated] == portfolio[:4]
    assert all(lane[4:] == portfolio[4:] for lane in rotated)


def test_current_v1_history_uses_new_solver_before_larger_budget_retry():
    portfolio = sat_screen._portfolio_configs("auto", "kmtotalizer")
    old_seqcounter = {
        "solver": "cadical195",
        "cardinality_encoding": "seqcounter",
    }
    attempts = [
        _timeout_attempt(
            portfolio[0],
            0,
            policy=sat_screen.SAT_PORTFOLIO_POLICY_V1,
        ),
        _timeout_attempt(
            old_seqcounter,
            1,
            policy=sat_screen.SAT_PORTFOLIO_POLICY_V1,
        ),
    ]
    unit = {
        "solver_evidence": {"outcome": "hard_timeout"},
        "attempts": attempts,
    }
    selected = sat_screen._next_attempt(
        unit,
        portfolio=portfolio,
        hard_timeout_s=7200.0,
    )
    assert selected == (2, portfolio[1], False)


def test_diversity_warmup_precedes_budget_upgrade_and_ignores_cancelled():
    portfolio = sat_screen._portfolio_configs("auto", "seqcounter")
    first_attempt = _timeout_attempt(portfolio[0], 0)
    unit = {
        "solver_evidence": {"outcome": "hard_timeout"},
        "attempts": [first_attempt],
    }
    assert sat_screen._next_attempt(
        unit,
        portfolio=portfolio,
        hard_timeout_s=3600.0,
    ) == (1, portfolio[1], False)
    assert sat_screen._next_attempt(
        unit,
        portfolio=portfolio,
        hard_timeout_s=7200.0,
    ) == (1, portfolio[1], False)

    warmup_attempts = [
        _timeout_attempt(config, index)
        for index, config in enumerate(portfolio[:4])
    ]
    warmup_unit = {
        "solver_evidence": {"outcome": "hard_timeout"},
        "attempts": warmup_attempts,
    }
    assert sat_screen._next_attempt(
        warmup_unit,
        portfolio=portfolio,
        hard_timeout_s=7200.0,
    ) == (4, portfolio[0], False)
    assert sat_screen._next_attempt(
        warmup_unit,
        portfolio=portfolio,
        hard_timeout_s=3600.0,
    ) == (4, portfolio[4], False)

    cancelled_unit = {
        "solver_evidence": {"outcome": "cancelled"},
        "attempts": [
            _timeout_attempt(portfolio[0], 0, outcome="cancelled"),
        ],
    }
    assert sat_screen._next_attempt(
        cancelled_unit,
        portfolio=portfolio,
        hard_timeout_s=3600.0,
    ) == (1, portfolio[0], False)


def test_isometry_reduces_complete_proof_to_canonical_sector():
    units = dict([
        _unit("lower", "X", _evidence("unsat", threshold=1)),
        _unit("upper", "X", _evidence("sat", threshold=2, objective=2)),
    ])
    artifact = sat_screen._artifact(
        candidate={"k": 1, "required_distance": 2},
        mode="global",
        translation_symmetry={"verified": True},
        logical_detector={"verified": True},
        xz_sector_isometry={
            "verified": True,
            "canonical_sector": "X",
            "covered_sectors": ["X", "Z"],
        },
        proof_sectors=("X",),
        units=units,
        expected_units=2,
        started=time.monotonic(),
    )
    assert artifact["status"] == "EXACT_PROVEN"
    assert artifact["expected_lower_decisions"] == 1
    assert artifact["completed_lower_decisions"] == 1


def test_attempt_record_is_self_hashed_policy_compatible_and_tamper_evident():
    evidence = {
        "outcome": "hard_timeout",
        "hard_timeout_s": 1.0,
        "backend": {"solver": "cadical195"},
        "cardinality_encoding": "totalizer",
        "elapsed_s": 1.0,
    }
    record = sat_screen._attempt_record(
        evidence,
        attempt_index=3,
        requested_solver="cadical195",
        requested_encoding="totalizer",
    )
    assert record["portfolio_policy"] == sat_screen.SAT_PORTFOLIO_POLICY
    assert sat_screen._attempt_valid(record)

    v1 = dict(record)
    v1["portfolio_policy"] = sat_screen.SAT_PORTFOLIO_POLICY_V1
    v1["attempt_sha256"] = sat_screen._canonical_sha256(
        v1,
        omit="attempt_sha256",
    )
    assert sat_screen._attempt_valid(v1)

    legacy = sat_screen._legacy_attempt(evidence)
    assert legacy["portfolio_policy"] == sat_screen.SAT_PORTFOLIO_POLICY_V1
    assert sat_screen._attempt_valid(legacy)

    tampered = dict(record)
    tampered["outcome"] = "unsat"
    assert not sat_screen._attempt_valid(tampered)

    unknown = dict(record)
    unknown["portfolio_policy"] = "untrusted-portfolio-v999"
    unknown["attempt_sha256"] = sat_screen._canonical_sha256(
        unknown,
        omit="attempt_sha256",
    )
    assert not sat_screen._attempt_valid(unknown)


def test_anchor_cover_cube_schema_is_disjoint_and_exhaustive():
    anchors = (0, 180, 271)
    cubes = sat_screen.build_anchor_cover_cubes(anchors)
    assert len(cubes) == len(anchors)
    for assignment in product((0, 1), repeat=len(anchors)):
        covered = [
            cube
            for cube in cubes
            if all(
                assignment[anchors.index(index)] == 0
                for index in cube["zero_anchor_indices"]
            )
            and assignment[anchors.index(cube["one_anchor_index"])] == 1
        ]
        assert len(covered) == int(any(assignment))
    assert all(
        cube["cube_sha256"]
        == sat_screen._canonical_sha256(cube, omit="cube_sha256")
        for cube in cubes
    )


def test_anchor_bound_timeout_resumes_without_relaxing_terminal_cnf_gate():
    cube = sat_screen.build_anchor_cover_cubes((0, 105))[0]
    clauses = [[cube["one_anchor_index"] + 1]]
    instance = {
        "anchor_constraint_formulation": (
            "anchor-or-first-nonzero-unit-clauses-v1"
        ),
        "anchor_indices": cube["anchor_indices"],
        "zero_anchor_indices": cube["zero_anchor_indices"],
        "one_anchor_index": cube["one_anchor_index"],
        "anchor_cube_sha256": cube["cube_sha256"],
        "anchor_unit_clauses": clauses,
        "anchor_unit_clauses_sha256": sat_screen._canonical_sha256(clauses),
    }
    instance["binding_sha256"] = sat_screen._canonical_sha256(instance)
    timeout = {
        "outcome": "hard_timeout",
        "decision_complete": False,
        "zero_anchor_indices": cube["zero_anchor_indices"],
        "one_anchor_index": cube["one_anchor_index"],
        "anchor_cube_sha256": cube["cube_sha256"],
        "instance": instance,
        "cnf": None,
    }
    assert sat_screen._evidence_matches_anchor_cube(timeout, cube)

    terminal_without_cnf = {
        **timeout,
        "outcome": "unsat",
        "decision_complete": True,
    }
    assert not sat_screen._evidence_matches_anchor_cube(
        terminal_without_cnf,
        cube,
    )

    tampered = {**timeout, "instance": {**instance, "one_anchor_index": 105}}
    assert not sat_screen._evidence_matches_anchor_cube(tampered, cube)


def test_artifact_only_completes_partition_after_every_cube_unsat():
    cubes = sat_screen.build_anchor_cover_cubes((0, 2))
    cube0_key, cube0_unit = _unit(
        "lower",
        "X",
        _evidence("unsat", threshold=1, anchor_cube=cubes[0]),
        partition=0,
        anchor_cube=cubes[0],
    )
    cube1_key, cube1_unit = _unit(
        "lower",
        "X",
        _evidence("unsat", threshold=1, anchor_cube=cubes[1]),
        partition=0,
        anchor_cube=cubes[1],
    )
    upper_key, upper_unit = _unit(
        "upper", "X", _evidence("sat", threshold=2, objective=2),
    )
    common = {
        "candidate": {"k": 1, "required_distance": 2},
        "mode": "first-nonzero",
        "translation_symmetry": {"verified": True},
        "logical_detector": {"verified": True},
        "xz_sector_isometry": {
            "verified": True,
            "canonical_sector": "X",
            "covered_sectors": ["X", "Z"],
        },
        "proof_sectors": ("X",),
        "anchor_cover_cubes": cubes,
        "expected_units": 3,
        "started": time.monotonic(),
    }
    partial = sat_screen._artifact(
        units={cube0_key: cube0_unit, upper_key: upper_unit},
        **common,
    )
    assert partial["status"] == "UNRESOLVED"
    assert partial["completed_lower_decisions"] == 1
    assert partial["completed_lower_partitions"] == 0

    complete = sat_screen._artifact(
        units={
            cube0_key: cube0_unit,
            cube1_key: cube1_unit,
            upper_key: upper_unit,
        },
        **common,
    )
    assert complete["status"] == "EXACT_PROVEN"
    assert complete["expected_lower_decisions"] == 2
    assert complete["completed_lower_decisions"] == 2
    assert complete["expected_lower_partitions"] == 1
    assert complete["completed_lower_partitions"] == 1
    assert complete["anchor_cover_cubes"] == cubes

    tampered = dict(cube1_unit)
    tampered["anchor_cube"] = cubes[0]
    fail_closed = sat_screen._artifact(
        units={cube0_key: cube0_unit, cube1_key: tampered, upper_key: upper_unit},
        **common,
    )
    assert fail_closed["status"] == "UNRESOLVED"
    assert fail_closed["completed_lower_partitions"] == 0


def test_global_lower_lane_is_an_independent_complete_proof_path():
    cubes = sat_screen.build_anchor_cover_cubes((0, 2))
    global_key, global_unit = _unit(
        "lower-global", "X", _evidence("unsat", threshold=1),
    )
    upper_key, upper_unit = _unit(
        "upper", "X", _evidence("sat", threshold=2, objective=2),
    )
    artifact = sat_screen._artifact(
        candidate={"k": 3, "required_distance": 2},
        mode="first-nonzero",
        translation_symmetry={"verified": True},
        logical_detector={"verified": True},
        xz_sector_isometry={
            "verified": True,
            "canonical_sector": "X",
            "covered_sectors": ["X", "Z"],
        },
        proof_sectors=("X",),
        anchor_cover_cubes=cubes,
        units={global_key: global_unit, upper_key: upper_unit},
        expected_units=8,
        started=time.monotonic(),
    )
    assert artifact["status"] == "EXACT_PROVEN"
    assert artifact["coverage_mode"] == "global"
    assert artifact["anchor_cover_cubes"] is None
    assert artifact["requested_anchor_cover_cubes"] == cubes
    assert artifact["lower_bound_threshold"] == 1
    assert artifact["expected_lower_decisions"] == 1
    assert artifact["completed_lower_partitions"] == 1
    assert artifact["lower_bound_decisions"][0]["anchor_cube"] is None


def test_resume_keeps_legacy_upper_but_never_promotes_old_anchor_or_lower(
    tmp_path,
):
    candidate = {"k": 1, "required_distance": 2, "canonical_digest": "resume"}
    symmetry = {"verified": True, "orbit_representatives": [0, 2]}
    detector = {"verified": True, "report_sha256": "d" * 64}
    isometry = {
        "verified": True,
        "canonical_sector": "X",
        "covered_sectors": ["X", "Z"],
        "report_sha256": "i" * 64,
    }
    legacy_lower = {
        "unit_id": "lower-X-p000",
        "phase": "lower",
        "sector": "X",
        "partition_index": 0,
        "solver_evidence": _evidence("unsat", threshold=1),
    }
    legacy_upper = {
        "unit_id": "upper-X-global",
        "phase": "upper",
        "sector": "X",
        "partition_index": None,
        "solver_evidence": _evidence("sat", threshold=2, objective=2),
    }
    old = {
        "schema_version": sat_screen.SAT_STAGE3_SCHEMA_VERSION,
        "gate": sat_screen.SAT_STAGE3_GATE,
        "candidate": candidate,
        "coverage_mode": "first-nonzero",
        "requested_coverage_mode": "first-nonzero",
        "translation_symmetry": symmetry,
        "logical_detector": detector,
        "xz_sector_isometry": isometry,
        "units": [legacy_lower, legacy_upper],
    }
    old["artifact_sha256"] = sat_screen._canonical_sha256(old)
    output = tmp_path / "old.json"
    output.write_text(json.dumps(old), encoding="utf-8")

    cubes = sat_screen.build_anchor_cover_cubes((0, 2))
    plan = sat_screen._proof_plan("first-nonzero", 1, ("X",), cubes)
    resumed = sat_screen._resume_units(
        output,
        candidate=candidate,
        mode="first-nonzero",
        plan=plan,
        anchor_cover_cubes=cubes,
        translation_symmetry=symmetry,
        logical_detector=detector,
        xz_sector_isometry=isometry,
    )
    assert set(resumed) == {"upper-X-global"}
    assert resumed["upper-X-global"]["checkpoint_replay_pending"] is True


def test_screen_resume_rotates_hard_timeout_portfolio_end_to_end(
    tmp_path,
    monkeypatch,
):
    candidate = {
        "ell": 1,
        "m": 1,
        "n": 2,
        "k": 1,
        "required_distance": 2,
        "canonical_digest": "portfolio-resume",
    }
    hx = np.array([[1, 1]], dtype=np.uint8)
    hz = np.zeros((0, 2), dtype=np.uint8)
    lx = np.array([[1, 0]], dtype=np.uint8)
    lz = np.array([[1, 1]], dtype=np.uint8)
    isometry = {
        "verified": True,
        "canonical_sector": "X",
        "covered_sectors": ["X", "Z"],
        "report_sha256": "a" * 64,
    }
    symmetry = {
        "verified": True,
        "orbit_representatives": [0],
        "report_sha256": "b" * 64,
    }
    calls = []

    monkeypatch.setattr(sat_screen, "build_candidate_code", lambda _claim: object())
    monkeypatch.setattr(
        sat_screen,
        "validate_candidate_parameters",
        lambda _claim, _code: {"n": 2, "k": 1, "required_distance": 2},
    )
    monkeypatch.setattr(
        sat_screen,
        "get_code_matrices",
        lambda _code: (hx, hz, lx, lz),
    )
    monkeypatch.setattr(
        sat_screen,
        "verify_bb_translation_symmetry",
        lambda _claim: symmetry,
    )
    monkeypatch.setattr(
        sat_screen,
        "verify_bb_xz_sector_isometry",
        lambda *_args, **_kwargs: isometry,
    )

    def hard_timeout_solver(_checks, _logicals, **kwargs):
        calls.append((kwargs["solver"], kwargs["cardinality_encoding"]))
        zero_anchors = list(kwargs.get("zero_anchor_indices") or ())
        one_anchor = kwargs.get("one_anchor_index")
        cube_sha256 = kwargs.get("anchor_cube_sha256")
        evidence = {
            "schema_version": SAT_EVIDENCE_SCHEMA_VERSION,
            "evidence_kind": SAT_EVIDENCE_KIND,
            "outcome": "hard_timeout",
            "decision_complete": False,
            "threshold_infeasible": False,
            "retryable": True,
            "success": False,
            "operator": None,
            "objective": None,
            "max_weight": kwargs["max_weight"],
            "hard_timeout_s": kwargs["timeout"],
            "elapsed_s": 0.01,
            "backend": {"solver": kwargs["solver"]},
            "cardinality_encoding": kwargs["cardinality_encoding"],
            "zero_anchor_indices": zero_anchors,
            "one_anchor_index": one_anchor,
            "anchor_cube_sha256": cube_sha256,
        }
        if cube_sha256 is not None:
            clauses = [[-(index + 1)] for index in zero_anchors]
            clauses.append([one_anchor + 1])
            instance = {
                "anchor_constraint_formulation": (
                    "anchor-or-first-nonzero-unit-clauses-v1"
                ),
                "anchor_indices": symmetry["orbit_representatives"],
                "zero_anchor_indices": zero_anchors,
                "one_anchor_index": one_anchor,
                "anchor_cube_sha256": cube_sha256,
                "anchor_unit_clauses": clauses,
                "anchor_unit_clauses_sha256": (
                    sat_screen._canonical_sha256(clauses)
                ),
            }
            instance["binding_sha256"] = sat_screen._canonical_sha256(instance)
            evidence["instance"] = instance
            evidence["cnf"] = {
                "anchor_unit_clauses_sha256": (
                    sat_screen._canonical_sha256(clauses)
                ),
            }
        evidence["evidence_sha256"] = sat_screen._canonical_sha256(evidence)
        return evidence

    monkeypatch.setattr(
        sat_screen,
        "solve_css_sector_sat",
        hard_timeout_solver,
    )
    output = tmp_path / "candidate.json"
    first = sat_screen.screen_sat_candidate(
        candidate,
        output=output,
        timeout=1,
        workers=1,
        resume=False,
    )
    assert calls == [
        ("cadical195", "seqcounter"),
        ("cadical195", "seqcounter"),
    ]
    assert first["expected_units"] == 2

    calls.clear()
    second = sat_screen.screen_sat_candidate(
        candidate,
        output=output,
        timeout=1,
        workers=1,
        resume=True,
    )
    assert calls == [
        ("kissat404", "totalizer"),
        ("kissat404", "totalizer"),
    ]
    assert second["portfolio_attempts"] == 4
    assert all(len(unit["attempts"]) == 2 for unit in second["units"])


def test_screen_candidate_deadline_cancels_active_unit(tmp_path, monkeypatch):
    candidate = {
        "ell": 1,
        "m": 1,
        "n": 2,
        "k": 1,
        "required_distance": 2,
        "canonical_digest": "candidate-deadline",
    }
    hx = np.array([[1, 1]], dtype=np.uint8)
    hz = np.zeros((0, 2), dtype=np.uint8)
    lx = np.array([[1, 0]], dtype=np.uint8)
    lz = np.array([[1, 1]], dtype=np.uint8)
    monkeypatch.setattr(sat_screen, "build_candidate_code", lambda _claim: object())
    monkeypatch.setattr(
        sat_screen,
        "validate_candidate_parameters",
        lambda _claim, _code: {"n": 2, "k": 1, "required_distance": 2},
    )
    monkeypatch.setattr(
        sat_screen,
        "get_code_matrices",
        lambda _code: (hx, hz, lx, lz),
    )
    monkeypatch.setattr(
        sat_screen,
        "verify_bb_translation_symmetry",
        lambda _claim: {
            "verified": True,
            "orbit_representatives": [0],
            "report_sha256": "b" * 64,
        },
    )
    monkeypatch.setattr(
        sat_screen,
        "verify_bb_xz_sector_isometry",
        lambda *_args, **_kwargs: {
            "verified": True,
            "canonical_sector": "X",
            "covered_sectors": ["X", "Z"],
            "report_sha256": "a" * 64,
        },
    )

    def cancellable_solver(_checks, _logicals, **kwargs):
        cancellation = kwargs["cancel_event"]
        while not cancellation.is_set():
            time.sleep(0.005)
        evidence = {
            "schema_version": SAT_EVIDENCE_SCHEMA_VERSION,
            "evidence_kind": SAT_EVIDENCE_KIND,
            "outcome": "cancelled",
            "decision_complete": False,
            "threshold_infeasible": False,
            "retryable": True,
            "success": False,
            "operator": None,
            "objective": None,
            "max_weight": kwargs["max_weight"],
            "hard_timeout_s": kwargs["timeout"],
            "elapsed_s": 0.1,
            "backend": {"solver": kwargs["solver"]},
            "cardinality_encoding": kwargs["cardinality_encoding"],
            "zero_anchor_indices": list(
                kwargs.get("zero_anchor_indices") or (),
            ),
            "one_anchor_index": kwargs.get("one_anchor_index"),
            "anchor_cube_sha256": kwargs.get("anchor_cube_sha256"),
        }
        evidence["evidence_sha256"] = sat_screen._canonical_sha256(evidence)
        return evidence

    monkeypatch.setattr(sat_screen, "solve_css_sector_sat", cancellable_solver)
    artifact = sat_screen.screen_sat_candidate(
        candidate,
        output=tmp_path / "deadline.json",
        timeout=5,
        workers=1,
        candidate_timeout=0.25,
        termination_grace=0.05,
        resume=False,
    )
    assert artifact["status"] == "UNRESOLVED"
    assert artifact["termination"]["reason"] == "candidate_timeout"
    assert artifact["units"][0]["solver_evidence"]["outcome"] == "cancelled"
