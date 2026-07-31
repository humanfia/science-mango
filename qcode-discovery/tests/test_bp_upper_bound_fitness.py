"""Regression tests for fail-closed BP/OSD distance-bound semantics.

BP-OSD and OSD-CS find logical operators, so their outputs are upper bounds
on distance.  These tests deliberately keep that mathematical distinction
separate from exact/lower-bound evidence and from OpenEvolve parent fitness.
"""

from __future__ import annotations

from dataclasses import dataclass

import pytest

from evaluation import evaluator as distance_evaluator
from evaluation.bb_code import build_bb_code
from evaluation.distance_milp import symplectic_weight_bound
from evolve import openevolve_evaluator as search_evaluator


@dataclass
class _DummyCode:
    num_qudits: int = 288
    dimension: int = 144


_A_TERMS = [(0, 0), (1, 0), (0, 1)]
_B_TERMS = [(0, 0), (2, 0), (0, 2)]


def _bp_only_row(distance_upper_bound: int) -> dict:
    """Return one unresolved result whose only distance evidence is BP."""

    n = 288
    k = 12
    return {
        "ell": 12,
        "m": 12,
        "A_terms": _A_TERMS,
        "B_terms": _B_TERMS,
        "n": n,
        "k": k,
        "d": distance_upper_bound,
        "d_is_exact": False,
        "distance_status": "upper_bound",
        "search_status": "unresolved",
        "distance_upper_bound": distance_upper_bound,
        "bp_distance_upper_bound": distance_upper_bound,
        "fom_upper_bound": k * distance_upper_bound**2 / n,
        "fitness_distance_credit": 0.0,
        "threshold_rejection_proven": False,
        "pattern_type": 4.0,
    }


def test_bp_only_d5_and_d86_have_identical_distance_and_parent_fitness():
    """A looser BP upper bound must never look like stronger distance proof."""

    d5 = _bp_only_row(5)
    d86 = _bp_only_row(86)

    score_d5 = search_evaluator._score_stage2_upper_bound_safe([d5])
    score_d86 = search_evaluator._score_stage2_upper_bound_safe([d86])

    assert d5["fom_upper_bound"] < d86["fom_upper_bound"]
    assert score_d5["fitness_distance_credit"] == 0.0
    assert score_d86["fitness_distance_credit"] == 0.0
    assert score_d5["combined_score"] == score_d86["combined_score"]
    assert score_d5["per_lattice_credit"] == score_d86["per_lattice_credit"]
    assert score_d5["survivor_count"] == score_d86["survivor_count"] == 1
    assert search_evaluator._verified_distance_persistence_rows([d5, d86]) == []


def test_exact_credit_and_persistence_recompute_fom_from_consistent_evidence():
    """Self-reported exact FOM/credit fields must not influence selection."""

    row = {
        "ell": 12,
        "m": 6,
        "A_terms": _A_TERMS,
        "B_terms": _B_TERMS,
        "n": 144,
        "k": 12,
        "d": 6,
        "exact_distance": 6,
        "d_is_exact": True,
        "distance_status": "exact",
        "search_status": "exact",
        "fom": 999_999.0,
        "exact_fom": 999_999.0,
        "fitness_distance_credit": 999_999.0,
    }

    score = search_evaluator._score_stage2_upper_bound_safe([row])
    verified = search_evaluator._verified_distance_persistence_rows([row])

    assert score["fitness_distance_credit"] == pytest.approx(3.0)
    assert score["fitness_survivor_credit"] == 0.0
    assert len(verified) == 1
    assert verified[0]["d"] == verified[0]["exact_distance"] == 6
    assert verified[0]["fom"] == verified[0]["exact_fom"] == pytest.approx(3.0)
    assert verified[0]["fitness_distance_credit"] == pytest.approx(3.0)
    # Normalization is copy-on-write: telemetry input retains its raw fields.
    assert row["exact_fom"] == 999_999.0


@pytest.mark.parametrize(
    "updates",
    [
        {"exact_distance": 7},
        {"d": 145, "exact_distance": 145},
        {"d": 6.5, "exact_distance": 6.5},
        {"n": 72},
        {"k": 145},
    ],
)
def test_inconsistent_exact_evidence_gets_no_credit_or_persistence(updates):
    """Contradictory or out-of-domain exact rows must fail closed."""

    row = {
        "ell": 12,
        "m": 6,
        "A_terms": _A_TERMS,
        "B_terms": _B_TERMS,
        "n": 144,
        "k": 12,
        "d": 6,
        "exact_distance": 6,
        "d_is_exact": True,
        "distance_status": "exact",
        "search_status": "exact",
        "fom": 999_999.0,
        "exact_fom": 999_999.0,
        "fitness_distance_credit": 999_999.0,
        **updates,
    }

    score = search_evaluator._score_stage2_upper_bound_safe([row])

    assert score["fitness_distance_credit"] == 0.0
    assert search_evaluator._verified_distance_persistence_rows([row]) == []


def test_tightening_an_upper_bound_is_monotone_nonincreasing_for_fitness():
    """Finding a shorter logical may keep or reduce, but never raise, fitness."""

    loose = _bp_only_row(86)
    tighter = _bp_only_row(5)
    rejected = {
        **_bp_only_row(4),
        "search_status": "terminal_negative",
        "threshold_rejection_proven": True,
    }

    loose_score = search_evaluator._score_stage2_upper_bound_safe([loose])
    tighter_score = search_evaluator._score_stage2_upper_bound_safe([tighter])
    rejected_score = search_evaluator._score_stage2_upper_bound_safe([rejected])

    assert tighter_score["combined_score"] <= loose_score["combined_score"]
    assert rejected_score["combined_score"] <= tighter_score["combined_score"]
    assert rejected_score["fitness_distance_credit"] == 0.0
    assert rejected_score["survivor_count"] == 0
    assert rejected_score["terminal_negative_count"] == 1


def test_challenge_symplectic_rejection_short_circuits_before_bp(monkeypatch):
    """A replayable low-weight logical must reject before any BP work starts."""

    dummy = _DummyCode()
    bp_calls = 0

    monkeypatch.setattr(
        distance_evaluator,
        "_validate_and_build",
        lambda *_args, **_kwargs: (
            dummy,
            dummy.num_qudits,
            dummy.dimension,
        ),
    )
    monkeypatch.setattr(
        distance_evaluator,
        "symplectic_weight_bound",
        lambda _code: (3, 3, 7),
    )
    monkeypatch.setattr(
        distance_evaluator,
        "symplectic_weight_witness",
        lambda _code, _distance: {
            "side": "X",
            "index": 0,
            "dual_side": "Z",
            "dual_index": 0,
            "weight": 3,
            "bits": [1, 1, 1],
        },
    )
    monkeypatch.setattr(
        distance_evaluator,
        "_validate_replayable_symplectic_witness",
        lambda _code, witness, *, distance: {
            **witness,
            "weight": distance,
        },
    )

    def fail_if_bp_runs(*_args, **_kwargs):
        nonlocal bp_calls
        bp_calls += 1
        raise AssertionError("BP must not run after formal threshold rejection")

    monkeypatch.setattr(distance_evaluator, "estimate_distance", fail_if_bp_runs)
    monkeypatch.setattr(
        distance_evaluator,
        "estimate_distance_osd_cs",
        fail_if_bp_runs,
    )

    result = distance_evaluator.evaluate_candidate(
        12,
        12,
        _A_TERMS,
        _B_TERMS,
        challenge_target_fom=12.0,
    )

    assert bp_calls == 0
    assert result["stage"] == "challenge_symplectic_rejected"
    assert result["search_status"] == "terminal_negative"
    assert result["distance_status"] == "upper_bound"
    assert result["distance_upper_bound"] == 3
    assert result["fom_upper_bound"] == pytest.approx(4.5)
    assert result["fitness_distance_credit"] == 0.0
    assert result["threshold_rejection_proven"] is True
    assert result["score"] == 0.0


def test_skip_exact_still_runs_osd_cs(monkeypatch):
    """The exact-distance switch and OSD-CS switch are independent."""

    dummy = _DummyCode()
    calls = {"bp": 0, "osd_cs": 0, "exact": 0}

    monkeypatch.setattr(
        distance_evaluator,
        "_validate_and_build",
        lambda *_args, **_kwargs: (
            dummy,
            dummy.num_qudits,
            dummy.dimension,
        ),
    )
    monkeypatch.setattr(
        distance_evaluator,
        "symplectic_weight_bound",
        lambda _code: (100, 100, 100),
    )

    def bp(*_args, **_kwargs):
        calls["bp"] += 1
        return 20

    def osd_cs(*_args, **_kwargs):
        calls["osd_cs"] += 1
        return 7

    def exact(*_args, **_kwargs):
        calls["exact"] += 1
        raise AssertionError("skip_exact=True must suppress exact distance")

    monkeypatch.setattr(distance_evaluator, "estimate_distance", bp)
    monkeypatch.setattr(distance_evaluator, "estimate_distance_osd_cs", osd_cs)
    monkeypatch.setattr(distance_evaluator, "compute_distance_exact", exact)

    result = distance_evaluator.evaluate_candidate(
        12,
        12,
        _A_TERMS,
        _B_TERMS,
        fom_threshold_refine=float("inf"),
        fom_threshold_osd_cs=0.0,
        osd_cs_trials=17,
        skip_exact=True,
    )

    assert calls == {"bp": 1, "osd_cs": 1, "exact": 0}
    assert result["stage"] == "osd_cs_upper_bound"
    assert result["d"] == 7
    assert result["distance_upper_bound"] == 7
    assert result["distance_status"] == "upper_bound"
    assert result["distance_trusted"] is False
    assert result["fitness_distance_credit"] == 0.0


def test_four_round_false_positives_never_enter_positive_distance_elite():
    """Compact replay of the 12 audited BP false positives from rounds 1-4."""

    # (BP estimate, sealed upper/exact distance, exact?)
    audited = [
        (15, 3, False),
        (0, 2, True),
        (86, 2, True),
        (20, 2, True),
        (0, 5, False),
        (70, 2, True),
        (22, 6, False),
        (0, 6, False),
        (72, 4, False),
        (24, 4, False),
        (0, 4, False),
        (60, 2, True),
    ]
    rows = []
    for bp_distance, sealed_distance, exact in audited:
        row = {
            **_bp_only_row(sealed_distance),
            # Keep every compact fixture on a contracted fitness lattice; the
            # test concerns evidence admission, not lattice routing.
            "ell": 12,
            "m": 12,
            "n": 288,
            "bp_distance_upper_bound": bp_distance,
            "search_status": "terminal_negative",
            "threshold_rejection_proven": True,
            "d_is_exact": exact,
            "distance_status": "exact" if exact else "upper_bound",
        }
        if exact:
            row["exact_distance"] = sealed_distance
            row["exact_fom"] = (
                row["k"] * sealed_distance**2 / row["n"]
            )
        rows.append(row)

    scored = search_evaluator._score_stage2_upper_bound_safe(rows)

    assert scored["survivor_count"] == 0
    assert scored["terminal_negative_count"] == len(rows)
    assert scored["fitness_distance_credit"] == 0.0
    assert scored["combined_score"] == 0.0
    assert search_evaluator._verified_distance_persistence_rows(rows) == []


def test_openevolve_deep_batch_enables_bound_safe_cascade(
    tmp_path, monkeypatch
):
    """The production adapter must enable every fail-closed cascade control."""

    monkeypatch.setattr(search_evaluator, "_PROJECT_ROOT", str(tmp_path))
    monkeypatch.setattr(
        search_evaluator,
        "_filter_static_eligible",
        lambda rows: (rows, []),
    )
    monkeypatch.setattr(
        search_evaluator,
        "deduplicate_css_results",
        lambda rows: (rows, []),
    )
    candidate = (
        [[0, 0], [0, 1], [1, 0]],
        [[0, 0], [0, 2], [2, 0]],
    )
    deep_kwargs = []

    def fake_batch(ell, m, rows, **kwargs):
        quick = kwargs.get("quick") is True
        if not quick:
            deep_kwargs.append(dict(kwargs))
        return [
            {
                "ell": ell,
                "m": m,
                "A_terms": a_terms,
                "B_terms": b_terms,
                "n": 2 * ell * m,
                "k": 12,
                "d": 0 if quick else 20,
                "d_is_exact": False,
                "distance_status": "unknown" if quick else "upper_bound",
                "distance_upper_bound": None if quick else 20,
                "search_status": "unresolved",
                "threshold_rejection_proven": False,
                "fitness_distance_credit": 0.0,
                "fom": 0.0 if quick else 12 * 20**2 / (2 * ell * m),
                "fom_upper_bound": (
                    None if quick else 12 * 20**2 / (2 * ell * m)
                ),
                "score": 12 / (2 * ell * m),
                "stage": "quick_k_only" if quick else "bp_upper_bound",
                "encoding_rate": 12 / (2 * ell * m),
            }
            for a_terms, b_terms in rows
        ]

    monkeypatch.setattr(search_evaluator, "evaluate_batch", fake_batch)

    search_evaluator._run_evaluation(
        lambda _ell, _m: [candidate],
        [(12, 12)],
        quick=False,
        max_distance_per_lattice=1,
        run_name="bound-safe-adapter",
        sampling_salt="bound-safe-adapter",
    )

    assert len(deep_kwargs) == 1
    assert deep_kwargs[0]["fom_threshold_osd_cs"] == 8.0
    assert deep_kwargs[0]["skip_exact"] is True
    assert deep_kwargs[0]["challenge_target_fom"] == 12.0


def test_terminal_negative_wave_refills_until_a_survivor_is_found(
    tmp_path, monkeypatch
):
    """Cheap formal rejections must not consume the BP/OSD survivor budget."""

    monkeypatch.setattr(search_evaluator, "_PROJECT_ROOT", str(tmp_path))
    monkeypatch.setattr(
        search_evaluator,
        "_filter_static_eligible",
        lambda rows: (rows, []),
    )
    monkeypatch.setattr(
        search_evaluator,
        "deduplicate_css_results",
        lambda rows: (rows, []),
    )
    candidates = [
        (
            [[0, 0], [0, 1], [index + 1, 0]],
            [[0, 0], [0, 2], [index + 2, 0]],
        )
        for index in range(4)
    ]
    k_by_marker = {1: 16, 2: 12, 3: 8, 4: 4}
    deep_waves = []

    def fake_batch(ell, m, rows, **kwargs):
        quick = kwargs.get("quick") is True
        if not quick:
            deep_waves.append([
                max(x for x, _y in a_terms)
                for a_terms, _b_terms in rows
            ])
        results = []
        for a_terms, b_terms in rows:
            marker = max(x for x, _y in a_terms)
            k = k_by_marker[marker]
            terminal = not quick and marker <= 3
            results.append({
                "ell": ell,
                "m": m,
                "A_terms": a_terms,
                "B_terms": b_terms,
                "n": 2 * ell * m,
                "k": k,
                "d": 0 if quick else (3 if terminal else 20),
                "d_is_exact": False,
                "distance_status": (
                    "unknown" if quick else "upper_bound"
                ),
                "distance_upper_bound": (
                    None if quick else (3 if terminal else 20)
                ),
                "search_status": (
                    "terminal_negative" if terminal else "unresolved"
                ),
                "threshold_rejection_proven": terminal,
                "fitness_distance_credit": 0.0,
                "fom": 0.0,
                "fom_upper_bound": None,
                "score": k / (2 * ell * m),
                "stage": (
                    "quick_k_only"
                    if quick
                    else (
                        "challenge_symplectic_rejected"
                        if terminal
                        else "bp_upper_bound"
                    )
                ),
                "encoding_rate": k / (2 * ell * m),
            })
        return results

    monkeypatch.setattr(search_evaluator, "evaluate_batch", fake_batch)

    metrics = search_evaluator._run_evaluation(
        lambda _ell, _m: candidates,
        [(12, 12)],
        quick=False,
        max_distance_per_lattice=3,
        run_name="bound-safe-refill",
        sampling_salt="bound-safe-refill",
    )
    score = search_evaluator._score_stage2_upper_bound_safe(
        metrics["all_results"]
    )

    assert deep_waves == [[1, 2, 3], [4]]
    assert metrics["winner_capable_distance_pending_persisted"] == 4
    assert score["terminal_negative_count"] == 3
    assert score["survivor_count"] == 1
    assert any(
        max(x for x, _y in row["A_terms"]) == 4
        and row["search_status"] == "unresolved"
        for row in metrics["all_results"]
    )


@pytest.mark.parametrize(
    ("ell", "m", "a_terms", "b_terms", "expected"),
    [
        (
            6,
            6,
            [(3, 0), (0, 1), (0, 2)],
            [(0, 3), (1, 0), (2, 0)],
            (72, 12, (6, 6, 10)),
        ),
        (
            15,
            3,
            [(9, 0), (0, 1), (0, 2)],
            [(0, 0), (2, 0), (7, 0)],
            (90, 8, (10, 10, 12)),
        ),
        (
            12,
            6,
            [(3, 0), (0, 1), (0, 2)],
            [(0, 3), (1, 0), (2, 0)],
            (144, 12, (12, 12, 16)),
        ),
    ],
)
def test_ibm_baselines_have_stable_cheap_symplectic_bounds(
    ell, m, a_terms, b_terms, expected
):
    """The cheap screen preserves the three pinned IBM known answers."""

    expected_n, expected_k, expected_bounds = expected
    code = build_bb_code(ell, m, a_terms, b_terms)

    assert (int(code.num_qudits), int(code.dimension)) == (
        expected_n,
        expected_k,
    )
    assert symplectic_weight_bound(code) == expected_bounds
