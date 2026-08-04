import copy
import json
import math

import evaluation.evaluator as candidate_evaluator
import evaluation.low_weight_oracle as low_weight_oracle
import evaluation.bb_code as bb_code
from evolve.openevolve_evaluator import _candidate_jsonl_record
from humanize.flow import select_for_milp
from humanize.reviewer import build_review_prompt
from humanize.state import (
    EliteArchive,
    candidate_proven_fom,
    code_key,
)


def _candidate(*, shift: int, d: int, fom: float) -> dict:
    return {
        "ell": 6,
        "m": 6,
        "n": 72,
        "k": 8,
        "d": d,
        "fom": fom,
        "score": fom,
        "d_is_exact": False,
        "distance_trusted": False,
        "distance_status": "upper_bound",
        "distance_upper_bound": d,
        "fom_upper_bound": fom,
        "fitness_distance_credit": 0.0,
        "search_status": "unresolved",
        "stage": "bp_upper_bound",
        "A_terms": [[0, 0], [0, 1 + shift], [1, 0]],
        "B_terms": [[0, 0], [0, 2 + shift], [2, 0]],
    }


def _archive_winner(tmp_path, rows: list[dict], name: str) -> str:
    archive = EliteArchive(tmp_path / name)
    archive.replace(rows)
    return code_key(archive.ranked()[0])


def _review_evidence(prompt: str) -> dict:
    body = prompt.split("Round evidence JSON:\n", 1)[1]
    encoded = body.split("\n\nReturn only the JSON object", 1)[0]
    return json.loads(encoded)


def test_archive_winner_is_invariant_to_swapped_bp_upper_bounds(tmp_path):
    first = _candidate(shift=0, d=5, fom=2.8)
    second = _candidate(shift=1, d=86, fom=821.8)

    original = _archive_winner(
        tmp_path,
        [first, second],
        "original.json",
    )
    first_swapped = dict(first, d=86, fom=821.8, score=821.8)
    second_swapped = dict(second, d=5, fom=2.8, score=2.8)
    swapped = _archive_winner(
        tmp_path,
        [first_swapped, second_swapped],
        "swapped.json",
    )

    assert original == swapped


def test_exact_can_beat_large_bp_upper_bound(tmp_path):
    bp = _candidate(shift=0, d=86, fom=821.8)
    exact = _candidate(shift=1, d=3, fom=1.0)
    exact.update({
        "d_is_exact": True,
        "distance_trusted": True,
        "distance_status": "exact",
        "exact_distance": 3,
        "exact_fom": 1.0,
        "fitness_distance_credit": 1.0,
        "search_status": "exact",
    })

    assert candidate_proven_fom(bp) == 0.0
    assert candidate_proven_fom(exact) == 1.0
    assert _archive_winner(tmp_path, [bp, exact], "exact.json") == code_key(
        exact
    )


def test_milp_lane_is_invariant_to_bp_fom_and_rejects_terminal_negative():
    first = _candidate(shift=0, d=5, fom=2.8)
    second = _candidate(shift=1, d=86, fom=821.8)
    selected = select_for_milp([first, second], None, set(), 1)

    first_swapped = dict(first, d=86, fom=821.8, score=821.8)
    second_swapped = dict(second, d=5, fom=2.8, score=2.8)
    selected_swapped = select_for_milp(
        [first_swapped, second_swapped],
        None,
        set(),
        1,
    )
    assert code_key(selected[0]) == code_key(selected_swapped[0])

    terminal = dict(first)
    terminal.update({
        "search_status": "terminal_negative",
        "d_is_exact": True,
        "distance_trusted": True,
        "distance_status": "exact",
        "exact_distance": 5,
        "threshold_rejection_proven": True,
        "final_gate_excluded_by_upper_bound": True,
    })
    assert select_for_milp([terminal], None, set(), 1) == []


def test_reviewer_withholds_unresolved_upper_magnitudes_but_keeps_exact():
    upper = _candidate(shift=0, d=86, fom=821.8)
    terminal = dict(upper)
    terminal.update({
        "search_status": "terminal_negative",
        "threshold_rejection_proven": True,
        "threshold_proof_source": "symplectic_upper_bound",
        "threshold_proof_distance": 3,
        "final_gate_excluded_by_upper_bound": True,
    })
    exact = dict(upper)
    exact.update({
        "d": 3,
        "fom": 1.0,
        "d_is_exact": True,
        "distance_trusted": True,
        "distance_status": "exact",
    })

    evidence = _review_evidence(build_review_prompt(
        round_number=1,
        contract={},
        candidates=[upper],
        audited=[terminal],
        archive_top=[upper],
        memory="",
        trusted_exact_history=[exact],
        trusted_exact_wins=[],
    ))

    for name in ("new_candidates", "archive_top"):
        [projected] = evidence[name]
        assert "d" not in projected
        assert "fom" not in projected
        assert "score" not in projected
        assert "distance_upper_bound" not in projected
        assert "fom_upper_bound" not in projected
    [audited] = evidence["milp_audited"]
    assert "negative_only_upper_bound_evidence" not in audited
    assert "proof_backed_terminal_negative" not in audited
    assert evidence["trusted_exact_history"][0]["d"] == 3
    assert evidence["trusted_exact_history"][0]["fom"] == 1.0


def test_reviewer_receives_formally_audited_negative_witness_geometry():
    audited = candidate_evaluator.evaluate_candidate(
        12,
        6,
        [(0, 3), (6, 0)],
        [(1, 1), (2, 0), (6, 0), (9, 1)],
        skip_exact=True,
        skip_osd_cs=True,
        challenge_target_fom=12.0,
    )
    witness = copy.deepcopy(audited["threshold_proof_witness"])
    audited.update({
        "threshold_rejection_proven": True,
        "final_gate_excluded_by_upper_bound": True,
        "audit_attempt": {"schema_version": 2, "evidence": {}},
        "milp_details": {
            "minimum_direction_witness": witness,
        },
    })

    evidence = _review_evidence(build_review_prompt(
        round_number=1,
        contract={},
        candidates=[],
        audited=[audited],
        archive_top=[],
        memory="",
    ))

    [projected] = evidence["milp_audited"]
    geometry = projected["replayed_low_weight_witness"]
    assert geometry["semantics"] == "negative_upper_bound_witness"
    expected_support = [
        index for index, bit in enumerate(witness["bits"]) if bit
    ]
    assert geometry["support"] == expected_support
    assert [item["qubit"] for item in geometry["block_support"]] == (
        expected_support
    )


def test_reviewer_replays_stage2_oracle_witness_before_exposing(
    monkeypatch,
):
    monkeypatch.setattr(
        candidate_evaluator,
        "symplectic_weight_bound",
        lambda code: (code.num_qudits, code.num_qudits, code.num_qudits),
    )
    row = candidate_evaluator.evaluate_candidate(
        12,
        6,
        [(0, 3), (6, 0)],
        [(1, 1), (2, 0), (6, 0), (9, 1)],
        skip_exact=True,
        skip_osd_cs=True,
        challenge_target_fom=12.0,
        low_weight_oracle_max_weight=4,
    )
    evidence = _review_evidence(build_review_prompt(
        round_number=1,
        contract={},
        candidates=[row],
        audited=[],
        archive_top=[],
        memory="",
    ))

    [projected] = evidence["new_candidates"]
    geometry = projected["replayed_low_weight_witness"]
    assert geometry["semantics"] == "negative_upper_bound_witness"
    assert geometry["support"] == row["low_weight_oracle"]["witness"][
        "support"
    ]

    tampered = copy.deepcopy(row)
    tampered["low_weight_oracle"]["witness"]["bits"][0] ^= 1
    tampered_evidence = _review_evidence(build_review_prompt(
        round_number=1,
        contract={},
        candidates=[tampered],
        audited=[],
        archive_top=[],
        memory="",
    ))
    assert "replayed_low_weight_witness" not in (
        tampered_evidence["new_candidates"][0]
    )


def test_reviewer_replays_historical_stage2_sat_after_source_upgrade(
    monkeypatch,
):
    monkeypatch.setattr(
        candidate_evaluator,
        "symplectic_weight_bound",
        lambda code: (code.num_qudits, code.num_qudits, code.num_qudits),
    )
    row = candidate_evaluator.evaluate_candidate(
        12,
        6,
        [(0, 3), (6, 0)],
        [(1, 1), (2, 0), (6, 0), (9, 1)],
        skip_exact=True,
        skip_osd_cs=True,
        challenge_target_fom=12.0,
        low_weight_oracle_max_weight=4,
    )
    historical_source = row["low_weight_oracle"]["source_sha256"]
    replacement_source = (
        "f" * 64 if historical_source != "f" * 64 else "e" * 64
    )
    monkeypatch.setattr(
        low_weight_oracle, "_SOURCE_SHA256", replacement_source
    )

    evidence = _review_evidence(build_review_prompt(
        round_number=2,
        contract={},
        candidates=[row],
        audited=[],
        archive_top=[],
        memory="",
    ))
    [projected] = evidence["new_candidates"]
    assert projected["replayed_low_weight_witness"]["support"] == row[
        "low_weight_oracle"
    ]["witness"]["support"]


def test_reviewer_rejects_noncampaign_lattice_before_dense_bb_build(
    monkeypatch,
):
    row = _candidate(shift=0, d=2, fom=1.0)
    row.update({
        "ell": 7,
        "m": 7,
        "n": 98,
        "k": 2,
        "search_status": "terminal_negative",
        "threshold_rejection_proven": True,
        "threshold_proof_source": "low_weight_oracle",
        "final_gate_excluded_by_upper_bound": True,
        "low_weight_oracle": {
            "outcome": "SAT",
            "witness": {
                "side": "X",
                "weight": 1,
                "bits": [1] + [0] * 97,
            },
        },
    })
    calls = 0

    def forbidden_build(*args, **kwargs):
        nonlocal calls
        calls += 1
        raise AssertionError("dense BB build must not run")

    monkeypatch.setattr(bb_code, "build_bb_code", forbidden_build)
    evidence = _review_evidence(build_review_prompt(
        round_number=1,
        contract={},
        candidates=[row],
        audited=[],
        archive_top=[],
        memory="",
    ))
    assert calls == 0
    assert "replayed_low_weight_witness" not in evidence["new_candidates"][0]


def test_self_declared_lower_bound_is_withheld_from_reviewer_and_fitness():
    row = _candidate(shift=0, d=86, fom=821.8)
    row.update({
        "distance_lower_bound": 1000,
        "fom_lower_bound": 100000.0,
        "distance_lower_bound_status": "certified",
        "distance_lower_bound_proven": True,
    })

    evidence = _review_evidence(build_review_prompt(
        round_number=1,
        contract={},
        candidates=[row],
        audited=[],
        archive_top=[row],
        memory="",
        trusted_exact_history=[],
        trusted_exact_wins=[],
    ))

    assert candidate_proven_fom(row) == 0.0
    [projected] = evidence["new_candidates"]
    assert projected["unverified_lower_bound_claim_withheld"] is True
    assert "distance_lower_bound" not in projected
    assert "fom_lower_bound" not in projected


def test_exact_distance_requires_strict_consistent_physical_integer():
    exact = _candidate(shift=0, d=3, fom=1.0)
    exact.update({
        "d_is_exact": True,
        "distance_trusted": True,
        "distance_status": "exact",
        "exact_distance": 3,
    })
    assert candidate_proven_fom(exact) == 1.0

    for invalid in (3.5, math.inf, "3", True, 73):
        malformed = dict(exact, exact_distance=invalid)
        assert candidate_proven_fom(malformed) == 0.0

    contradictory = dict(exact, exact_distance=4)
    assert candidate_proven_fom(contradictory) == 0.0

    fallback = dict(exact, exact_distance=None)
    assert candidate_proven_fom(fallback) == 1.0


def test_candidate_log_preserves_bound_semantics_for_humanize():
    upper = _candidate(shift=0, d=5, fom=2.8)
    upper.update({
        "distance_upper_bound_source": "bp_osd",
        "fitness_survivor_credit": 1.0,
    })

    record = _candidate_jsonl_record(upper)

    assert record is not None
    assert record["distance_status"] == "upper_bound"
    assert record["distance_upper_bound"] == 5
    assert record["fom_upper_bound"] == 2.8
    assert record["fitness_distance_credit"] == 0.0
    assert record["fitness_survivor_credit"] == 1.0
    assert record["search_status"] == "unresolved"
