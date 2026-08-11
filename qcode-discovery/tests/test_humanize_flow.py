import copy
import json

import pytest

import evaluation.evaluator as candidate_evaluator
from evaluation.coset_action_catalog import V2_CATALOG_ID, get_catalog
from evaluation.coset_two_block import (
    ACTION_CATALOG_SHA256,
    ACTION_CATALOG_V2_SHA256,
    CONSTRUCTION_REPRESENTATION_V2,
)
from evolve import coset_policy_dsl_v3 as policy_v3
from evolve.coset_search_contract import (
    COSET_SUPPORT_ORBIT_BINS,
    TRUSTED_COSET_SUPPORT_SPLITS,
    canonical_json_sha256,
    coset_support_orbit_bin,
)
from humanize.audit_state import (
    authoritative_candidate_digest,
    create_unresolved_entry,
)
from humanize.flow import (
    CANDIDATE_BATCH_POLICY_COMPOSITE_PROVENANCE_VERSION,
    CANDIDATE_BATCH_POLICY_EVIDENCE_MERGE_VERSION,
    CANDIDATE_BATCH_POLICY_LEGACY_VERSION,
    FlowConfig,
    HumanizeFlow,
    RoundTransactionError,
    UnresolvedAuditError,
    _canonical_payload_sha256,
    _deduplicate,
    _merge_duplicate_search_evidence,
    _milp_is_fully_exact,
    select_for_milp,
)
from humanize.reviewer import validate_review
from humanize.state import (
    EliteArchive,
    RunStore,
    archive_cell,
    candidate_structural_features,
    code_key,
    read_jsonl_since,
)


def candidate(*, ell=6, m=6, k=12, d=6, fom=6.0, shift=0):
    return {
        "ell": ell,
        "m": m,
        "n": 2 * ell * m,
        "k": k,
        "d": d,
        "fom": fom,
        "score": fom,
        "stage": "refined_estimate",
        "A_terms": [[0, 0], [0, 1 + shift], [1, 0]],
        "B_terms": [[0, 0], [0, 2 + shift], [2, 0]],
        "pattern_type": "swap",
        "term_count": 6,
    }


def _v3_archive_row(candidate_row, *, n=240, k=12):
    return {
        **copy.deepcopy(candidate_row),
        "construction": {
            "kind": "coset-two-block-v2",
            "representation_id": CONSTRUCTION_REPRESENTATION_V2,
            "action_id": candidate_row["action_id"],
            "action_catalog_id": V2_CATALOG_ID,
            "action_catalog_sha256": ACTION_CATALOG_V2_SHA256,
            "left_support": copy.deepcopy(candidate_row["left_support"]),
            "right_support": copy.deepcopy(candidate_row["right_support"]),
        },
        "n": n,
        "k": k,
    }


def _legacy_support_orbit_bin(row):
    digest = canonical_json_sha256({
        "left_support": sorted(row["construction"]["left_support"]),
        "right_support": sorted(row["construction"]["right_support"]),
    })
    return int(digest[:8], 16) % COSET_SUPPORT_ORBIT_BINS


def test_elite_archive_replaces_cell_winner_and_selects_diverse(tmp_path):
    archive = EliteArchive(tmp_path / "archive.json")
    weak = candidate(fom=5.0)
    strong = candidate(fom=8.0, shift=1)
    other_cell = candidate(ell=12, m=6, d=8, fom=7.0, shift=2)
    archive.update([weak, strong, other_cell], 1)

    ranked = archive.ranked()
    assert len(ranked) == 2
    assert ranked[0]["fom"] == 8.0
    selected = select_for_milp(ranked, archive, set(), 2)
    assert len(selected) == 2
    assert len({row["archive_cell"] for row in selected}) == 2


def test_candidate_archive_cell_ignores_forged_structural_metadata():
    row = candidate()
    variants = []
    for pattern, term_count, version in (
        ("forged", 999, 2),
        (3.0, 1, 1),
        (None, None, None),
    ):
        variant = dict(row)
        variant["pattern_type"] = pattern
        variant["term_count"] = term_count
        variant["pattern_classifier_version"] = version
        variants.append(variant)

    assert len({archive_cell(variant) for variant in variants}) == 1
    assert candidate_structural_features(variants[0]) == {
        "pattern_type": 5.0,
        "term_count": 3.0,
        "pattern_classifier_version": 2,
    }


def test_candidate_archive_uses_v2_mixed_and_max_term_semantics():
    multi_term_mixed = {
        "A_terms": [[0, 0], [1, 0]],
        "B_terms": [[0, 1], [1, 1], [2, 0], [0, 2]],
    }
    compact_mixed = {
        "A_terms": [[0, 0], [1, 1], [2, 0]],
        "B_terms": [[0, 1], [1, 0], [2, 2]],
    }

    assert candidate_structural_features(multi_term_mixed) == {
        "pattern_type": 4.0,
        "term_count": 4.0,
        "pattern_classifier_version": 2,
    }
    assert candidate_structural_features(compact_mixed) == {
        "pattern_type": 3.0,
        "term_count": 3.0,
        "pattern_classifier_version": 2,
    }


def test_candidate_archive_replays_catalog_version_from_coset_construction():
    legacy = {
        "construction": {
            "kind": "coset-two-block-v1",
            "action_id": "coset2bga-l224-m53-s1-degree112-v1",
            "action_catalog_sha256": ACTION_CATALOG_SHA256,
            "left_support": ["L000", "L104", "L207"],
            "right_support": ["R000", "R009", "R024"],
        }
    }
    catalog = get_catalog(catalog_id=V2_CATALOG_ID)
    action = next(
        action for action in catalog.actions.values()
        if action.published_support is not None
    )
    published = action.published_support
    assert published is not None
    current = {
        "construction": {
            "kind": "coset-two-block-v2",
            "representation_id": CONSTRUCTION_REPRESENTATION_V2,
            "action_id": action.action_id,
            "action_catalog_id": V2_CATALOG_ID,
            "action_catalog_sha256": ACTION_CATALOG_V2_SHA256,
            "left_support": list(published["left_support"]),
            "right_support": list(published["right_support"]),
        }
    }

    legacy_features = candidate_structural_features(legacy)
    current_features = candidate_structural_features(current)
    assert legacy_features["term_count"] == 6
    assert current_features["term_count"] == 6
    assert legacy_features["subgroup_normal"] == 0
    assert current_features["subgroup_normal"] == 0
    assert legacy_features["support_orbit_bin"] == (
        _legacy_support_orbit_bin(legacy)
    )
    assert current_features["support_orbit_bin"] == (
        _legacy_support_orbit_bin(current)
    )
    assert archive_cell({**legacy, "n": 224, "k": 12}).startswith("n=224|")
    assert archive_cell({**current, "n": published["reported_n"], "k": published["reported_k"]}).startswith(
        f"n={published['reported_n']}|"
    )


@pytest.mark.parametrize("support_split", TRUSTED_COSET_SUPPORT_SPLITS)
def test_renderer_v3_archive_orbit_matches_authoritative_batch(
    support_split,
):
    rendered = policy_v3.render_candidates(
        policy_v3.default_policy(support_split=support_split)
    )

    # Exercise the full renderer batch, not a single 3+3 fixture.  Humanize's
    # archive projection must be exactly the evaluator coordinate for every
    # whitelisted split.
    assert len(rendered) == 384
    for candidate_row in rendered:
        row = _v3_archive_row(candidate_row)
        assert candidate_structural_features(row)[
            "support_orbit_bin"
        ] == coset_support_orbit_bin(candidate_row)


def test_renderer_v3_archive_ignores_forged_stale_orbit_metadata(tmp_path):
    candidate_row = policy_v3.render_candidates(
        policy_v3.default_policy(support_split=(2, 4))
    )[0]
    row = _v3_archive_row(candidate_row)
    authoritative = coset_support_orbit_bin(candidate_row)
    row.update({
        "support_orbit_bin": (authoritative + 1) % COSET_SUPPORT_ORBIT_BINS,
        "archive_cell": "forged-stale-cell",
    })

    archive = EliteArchive(tmp_path / "v3-forged.json")
    archive.replace([row])
    [stored] = archive.ranked()

    assert stored["support_orbit_bin"] == authoritative
    assert stored["archive_cell"] == archive_cell(row)
    assert stored["archive_cell"] != "forged-stale-cell"


@pytest.mark.parametrize("missing", ("renderer_descriptor_id", "support_split"))
def test_partial_renderer_v3_identity_fails_closed(missing):
    candidate_row = policy_v3.render_candidates(
        policy_v3.default_policy(support_split=(3, 2))
    )[0]
    row = _v3_archive_row(candidate_row)
    del row[missing]

    with pytest.raises(ValueError):
        candidate_structural_features(row)


def test_elite_archive_migrates_renderer_v3_cells_and_evidence_winner(
    tmp_path,
):
    rendered = policy_v3.render_candidates(
        policy_v3.default_policy(support_split=(4, 2))
    )
    by_new_cell = {}
    pair = None
    for candidate_row in rendered:
        row = _v3_archive_row(candidate_row)
        new_cell = archive_cell(row)
        old_bin = _legacy_support_orbit_bin(row)
        previous = by_new_cell.get(new_cell)
        if previous is not None and previous[1] != old_bin:
            pair = (previous[0], row)
            break
        by_new_cell[new_cell] = (row, old_bin)
    assert pair is not None
    unresolved, exact = pair
    exact.update({
        "d": 3,
        "exact_distance": 3,
        "d_is_exact": True,
        "distance_trusted": True,
        "distance_status": "exact",
    })
    path = tmp_path / "schema3-v3.json"
    path.write_text(json.dumps({
        "schema_version": 3,
        "cells": {
            "old-false-cell-a": {
                **unresolved,
                "support_orbit_bin": _legacy_support_orbit_bin(unresolved),
                "archive_cell": "old-false-cell-a",
            },
            "old-false-cell-b": {
                **exact,
                "support_orbit_bin": _legacy_support_orbit_bin(exact),
                "archive_cell": "old-false-cell-b",
            },
        },
    }))

    migrated = EliteArchive(path)

    assert json.loads(path.read_text())["schema_version"] == 4
    assert len(migrated.cells) == 1
    [winner] = migrated.ranked()
    assert winner["candidate_key"] == code_key(exact)
    assert winner["support_orbit_bin"] == coset_support_orbit_bin({
        name: exact[name]
        for name in (
            "schema_version",
            "representation_id",
            "renderer_descriptor_id",
            "action_id",
            "support_split",
            "left_support",
            "right_support",
        )
    })

    # Replacement and a second process load preserve the same canonical cell
    # collapse and proof-priority winner under schema v4.
    migrated.replace([unresolved, exact])
    reloaded = EliteArchive(path)
    assert len(reloaded.cells) == 1
    assert reloaded.ranked()[0]["candidate_key"] == code_key(exact)


def test_elite_archive_migrates_metadata_without_trusting_upper_fom(tmp_path):
    path = tmp_path / "archive.json"
    weak = candidate(fom=5.0)
    strong = candidate(fom=8.0)
    weak.update({"pattern_type": "weak-forgery", "term_count": 100})
    strong.update({"pattern_type": "strong-forgery", "term_count": 200})
    path.write_text(json.dumps({
        "schema_version": 1,
        "cells": {
            "legacy-cell-a": weak,
            "legacy-cell-b": strong,
        },
    }))

    archive = EliteArchive(path)

    assert len(archive.cells) == 1
    [stored] = archive.ranked()
    # Both legacy rows describe the same unresolved definition.  A larger
    # reported BP/OSD FOM is not stronger evidence and cannot replace it.
    assert stored["fom"] == 5.0
    assert stored["pattern_type"] == 5.0
    assert stored["term_count"] == 3.0
    assert stored["pattern_classifier_version"] == 2
    assert stored["archive_cell"] == archive_cell(stored)


def test_duplicate_bp_upper_bounds_keep_tightest_observation():
    loose = candidate(k=8, d=30, fom=100.0)
    tight = candidate(k=8, d=12, fom=16.0)

    [selected] = _deduplicate([loose, tight])

    assert selected["d"] == 12
    assert selected["fom"] == 16.0
    assert selected["bp_upper_bound_observations"] == {
        "count": 2,
        "minimum_distance": 12,
        "maximum_distance": 30,
        "selected_distance": 12,
        "selection_policy": "tightest_observed_upper_bound",
    }


def test_unknown_quick_duplicate_never_overwrites_positive_upper_bound():
    unknown = candidate(k=4, d=0, fom=0.0)
    unknown.update({
        "stage": "quick_k_only",
        "candidate_persistence_lane": "winner_capable_quick_exploration",
        "winner_capable_parameters": True,
        "minimum_winning_distance": 15,
        "singleton_distance_upper_bound": 35,
    })
    observed = candidate(k=4, d=18, fom=18.0)

    [selected] = _deduplicate([unknown, observed])

    assert selected["d"] == 18
    assert selected["stage"] == "refined_estimate"
    assert selected["bp_upper_bound_observations"]["count"] == 1


def test_milp_selection_reserves_one_bounded_quick_exploration_lane():
    credible = candidate(k=8, d=8, fom=7.0, shift=1)
    outlier = candidate(k=8, d=40, fom=120.0, shift=2)
    quick = candidate(k=4, d=0, fom=0.0, shift=3)
    quick.update({
        "stage": "quick_k_only",
        "candidate_persistence_lane": "winner_capable_quick_exploration",
        "winner_capable_parameters": True,
        "minimum_winning_distance": 15,
        "singleton_distance_upper_bound": 35,
    })

    selected = select_for_milp(
        [credible, outlier, quick],
        None,
        set(),
        3,
    )

    assert {code_key(row) for row in selected} == {
        code_key(credible),
        code_key(outlier),
        code_key(quick),
    }
    assert sum(
        row.get("candidate_persistence_lane")
        == "winner_capable_quick_exploration"
        for row in selected
    ) == 1


def test_milp_selection_never_takes_more_than_one_quick_exploration():
    quick_rows = []
    for shift in range(5):
        quick = candidate(k=4, d=0, fom=0.0, shift=shift)
        quick.update({
            "stage": "quick_k_only",
            "candidate_persistence_lane": "winner_capable_quick_exploration",
            "winner_capable_parameters": True,
            "minimum_winning_distance": 15,
            "singleton_distance_upper_bound": 35,
        })
        quick_rows.append(quick)

    selected = select_for_milp(quick_rows, None, set(), 3)

    assert len(selected) == 1
    assert selected[0]["candidate_persistence_lane"] == (
        "winner_capable_quick_exploration"
    )


def test_unresolved_distance_selection_precedes_arbitrary_quick_lane():
    quick = candidate(k=4, d=0, fom=0.0, shift=1)
    unresolved = candidate(k=4, d=0, fom=0.0, shift=2)
    for row in (quick, unresolved):
        row.update({
            "stage": "quick_k_only",
            "candidate_persistence_lane": (
                "winner_capable_quick_exploration"
            ),
            "winner_capable_parameters": True,
            "minimum_winning_distance": 15,
            "singleton_distance_upper_bound": 35,
        })
    quick["candidate_persistence_reason"] = "quick_distance_budget"
    unresolved["candidate_persistence_reason"] = (
        "selected_distance_unresolved"
    )

    selected = select_for_milp([quick, unresolved], None, set(), 3)

    assert selected == [unresolved]


def test_duplicate_zero_distance_rows_preserve_unresolved_provenance():
    quick = candidate(k=4, d=0, fom=0.0)
    quick.update({
        "stage": "quick_k_only",
        "candidate_persistence_lane": "winner_capable_quick_exploration",
        "candidate_persistence_reason": "quick_distance_budget",
        "winner_capable_parameters": True,
        "minimum_winning_distance": 15,
        "singleton_distance_upper_bound": 35,
    })
    unresolved = dict(quick)
    unresolved["candidate_persistence_reason"] = (
        "selected_distance_unresolved"
    )

    [selected] = _deduplicate([quick, unresolved])

    assert selected["candidate_persistence_reason"] == (
        "selected_distance_unresolved"
    )


def test_duplicate_search_lower_bounds_keep_stronger_complete_ledger():
    def sealed_lower_bound(lower_bound: int, *, complete: bool) -> dict:
        row = candidate(k=8, d=0, fom=0.0)
        row.pop("d")
        row["candidate_sha256"] = "a" * 64
        threshold = lower_bound - 1
        evidence = {
            "schema_version": 1,
            "kind": "qcode-css-low-weight-oracle",
            "outcome": "UNSAT",
            "decision_complete": True,
            "retryable": False,
            "max_weight": threshold,
            "distance_lower_bound": lower_bound,
            "witness": None,
        }
        evidence["evidence_sha256"] = _canonical_payload_sha256(evidence)
        ledger = {
            "kind": "qcode-coset-stage1-proof-ledger-v1",
            "schema_version": 1,
            "proof_ladder_version": 2,
            "candidate_sha256": row["candidate_sha256"],
            "entries": [{
                "threshold": threshold,
                "outcome": "UNSAT",
                "evidence_sha256": evidence["evidence_sha256"],
                "cache_sha256": "b" * 64,
            }],
        }
        ledger["root_sha256"] = _canonical_payload_sha256(ledger)
        row.update({
            "distance_lower_bound": lower_bound,
            "distance_lower_bound_proven": True,
            "distance_lower_bound_status": "search_oracle_proven",
            "distance_lower_bound_evidence": evidence,
            "distance_lower_bound_evidence_sha256": evidence[
                "evidence_sha256"
            ],
            "proof_ledger": ledger,
            "oracle_ladder_complete": complete,
            "challenge_target_lower_bound_proven": complete,
            "search_status": (
                "challenge_threshold_survivor"
                if complete else "partial_lower_bound_retry"
            ),
        })
        return row

    partial = sealed_lower_bound(5, complete=False)
    survivor = sealed_lower_bound(6, complete=True)

    # Historical transaction policy v1 retained the first rank-zero row.  It
    # must remain replayable after later policies start preferring sealed lower
    # bounds, otherwise a code upgrade invalidates an already committed batch.
    legacy = _deduplicate(
        [partial, survivor],
        policy_version=CANDIDATE_BATCH_POLICY_LEGACY_VERSION,
    )
    assert legacy[0]["distance_lower_bound"] == 5
    assert _deduplicate([partial, survivor])[0]["distance_lower_bound"] == 6
    assert _deduplicate([survivor, partial])[0]["distance_lower_bound"] == 6

    tampered = json.loads(json.dumps(survivor))
    tampered["distance_lower_bound_evidence"]["max_weight"] = 1
    [selected] = _deduplicate([partial, tampered])
    assert selected["distance_lower_bound"] == 5

    with pytest.raises(ValueError, match="unsupported candidate batch policy"):
        _deduplicate([partial, survivor], policy_version=True)


def test_duplicate_occurrences_merge_replayed_lb_and_ub_into_exact_interval(
    monkeypatch,
):
    """A 2f2-style split LB/UB pair must survive canonicalization intact."""

    monkeypatch.setattr(
        candidate_evaluator,
        "symplectic_weight_bound",
        lambda code: (code.num_qudits, code.num_qudits, code.num_qudits),
    )
    upper = candidate_evaluator.evaluate_candidate(
        12,
        6,
        [(0, 3), (6, 0)],
        [(1, 1), (2, 0), (6, 0), (9, 1)],
        skip_exact=True,
        skip_osd_cs=True,
        challenge_target_fom=12.0,
        low_weight_oracle_max_weight=4,
    )
    candidate_sha256 = "c" * 64
    upper["candidate_sha256"] = candidate_sha256
    witness = upper["low_weight_oracle"]["witness"]
    exact_distance = witness["weight"]
    # Canonicalization must derive the UB from the replayed witness, not from
    # status strings or scalar fields carried by this occurrence.
    upper.update({
        "d": exact_distance + 97,
        "distance_upper_bound": exact_distance + 97,
        "search_status": "partial_lower_bound_retry",
        "threshold_rejection_proven": False,
        "final_gate_excluded_by_upper_bound": False,
        "search_final_gate_excluded_by_upper_bound": False,
        "stage": "low_weight_oracle_rejected",
        "score": 0.0,
        "fitness": 0.0,
        "fitness_distance_credit": 0.0,
        "negative_archive_match_counts": {
            "exact_construction": 3,
            "action_support_split": 2,
            "action": 1,
        },
        "negative_archive_coordinate_sha256": {
            "exact_construction": "1" * 64,
            "action_support_split": "2" * 64,
            "action": "3" * 64,
        },
        "negative_archive_penalty": 0.036,
        "negative_archive_penalty_components": {
            "construction_proxy": 0.008,
            "verified_witness_mechanism": 0.028,
        },
        "negative_archive_witness_match_counts": {
            "block": 1,
            "action": 2,
            "orbit": 3,
            "support": 4,
        },
        "negative_archive_witness_motif_sha256": "4" * 64,
        "oracle_ladder_history": [{
            "threshold": exact_distance,
            "outcome": "SAT",
        }],
        "oracle_last_attempt": {
            "outcome": "SAT",
            "strategy_id": "upper-authority",
        },
        "oracle_last_attempt_outcome": "SAT",
        "oracle_last_attempt_threshold": exact_distance,
        "oracle_frontier_selected": True,
        "oracle_batch_budget_exhausted": False,
        # Policy v4 must normalize this redundant scalar from the oracle it
        # actually replayed, not trust even the chosen upper occurrence.
        "oracle_evidence_sha256": "5" * 64,
    })

    lower = {
        field: copy.deepcopy(upper[field])
        for field in (
            "ell",
            "m",
            "n",
            "k",
            "A_terms",
            "B_terms",
            "geometry",
        )
        if field in upper
    }
    lower["candidate_sha256"] = candidate_sha256
    threshold = exact_distance - 1
    lower_evidence = {
        "schema_version": 1,
        "kind": "qcode-css-low-weight-oracle",
        "outcome": "UNSAT",
        "decision_complete": True,
        "retryable": False,
        "max_weight": threshold,
        "distance_lower_bound": exact_distance,
        "witness": None,
    }
    lower_evidence["evidence_sha256"] = _canonical_payload_sha256(
        lower_evidence
    )
    ledger = {
        "kind": "qcode-coset-stage1-proof-ledger-v1",
        "schema_version": 1,
        "proof_ladder_version": 2,
        "candidate_sha256": candidate_sha256,
        "entries": [{
            "threshold": threshold,
            "outcome": "UNSAT",
            "evidence_sha256": lower_evidence["evidence_sha256"],
            "cache_sha256": "d" * 64,
        }],
    }
    ledger["root_sha256"] = _canonical_payload_sha256(ledger)
    lower.update({
        "distance_lower_bound": exact_distance,
        "distance_lower_bound_proven": True,
        "distance_lower_bound_status": "search_oracle_proven",
        "distance_lower_bound_evidence": lower_evidence,
        "distance_lower_bound_evidence_sha256": lower_evidence[
            "evidence_sha256"
        ],
        "proof_ledger": ledger,
        "oracle_ladder_complete": False,
        "oracle_ladder_next_threshold": exact_distance,
        "oracle_deferred": True,
        "challenge_target_lower_bound_proven": False,
        "search_status": "partial_lower_bound_retry",
        "candidate_persistence_lane": (
            "global_scalar_fom_proof_frontier"
        ),
        "candidate_persistence_reason": (
            "target_aware_cross_program_proof_continuation"
        ),
        "global_proof_frontier_injected": True,
        "global_proof_frontier_first_seen_sequence": 17,
        # These values model the stale LB-selected metadata observed in Round
        # 4.  They must remain frozen under historical policy v3 but must not
        # leak into a newly canonicalized policy-v4 terminal SAT row.
        "score": 0.91,
        "fitness": 0.91,
        "fitness_distance_credit": 9.5,
        "stage": "low_weight_oracle_lower_bound",
        "negative_archive_match_counts": {
            "exact_construction": 0,
            "action_support_split": 0,
            "action": 0,
        },
        "negative_archive_coordinate_sha256": {
            "exact_construction": "a" * 64,
            "action_support_split": "b" * 64,
            "action": "c" * 64,
        },
        "negative_archive_penalty": 0.0,
        "negative_archive_penalty_components": {
            "construction_proxy": 0.0,
            "verified_witness_mechanism": 0.0,
        },
        "negative_archive_witness_match_counts": {
            "block": 0,
            "action": 0,
            "orbit": 0,
            "support": 0,
        },
        "negative_archive_witness_motif_sha256": None,
        "oracle_ladder_history": [{
            "threshold": threshold,
            "outcome": "UNSAT",
        }],
        "oracle_last_attempt": {
            "outcome": "UNSAT",
            "strategy_id": "lower-stale",
        },
        "oracle_last_attempt_outcome": "UNSAT",
        "oracle_last_attempt_threshold": threshold,
        "oracle_frontier_selected": False,
        "oracle_batch_budget_exhausted": True,
        "oracle_evidence_sha256": "f" * 64,
    })
    assert code_key(lower) == code_key(upper)
    original_lower = copy.deepcopy(lower)
    original_upper = copy.deepcopy(upper)

    # Historical v2 still chooses one row and therefore cannot synthesize the
    # split interval.  Policy v4 produces the same canonical row independent
    # of occurrence order and remains idempotent after persistence/replay.
    [historical] = _deduplicate([lower, upper], policy_version=2)
    assert "search_distance_interval_proof" not in historical
    assert historical["distance_lower_bound"] == exact_distance

    # Candidate-batch policies are immutable transaction contracts.  Policy
    # v3 must retain its pre-fix byte semantics so committed v3 rounds remain
    # replayable after v4 becomes the default.
    [historical_v3] = _deduplicate(
        [lower, upper],
        policy_version=CANDIDATE_BATCH_POLICY_EVIDENCE_MERGE_VERSION,
    )
    assert historical_v3 == _deduplicate(
        [upper, lower],
        policy_version=CANDIDATE_BATCH_POLICY_EVIDENCE_MERGE_VERSION,
    )[0]
    assert _deduplicate(
        [historical_v3],
        policy_version=CANDIDATE_BATCH_POLICY_EVIDENCE_MERGE_VERSION,
    ) == [historical_v3]
    assert historical_v3["negative_archive_penalty"] == 0.0
    assert historical_v3["negative_archive_witness_motif_sha256"] is None
    assert historical_v3["fitness"] == 0.91
    assert historical_v3["fitness_distance_credit"] == 9.5
    assert historical_v3["oracle_last_attempt_outcome"] == "UNSAT"

    [merged] = _deduplicate([lower, upper])
    [reverse] = _deduplicate([upper, lower])
    assert reverse == merged
    assert _deduplicate([merged]) == [merged]
    assert merged["distance_lower_bound"] == exact_distance
    assert merged["distance_upper_bound"] == exact_distance
    assert merged["search_exact_distance"] == exact_distance
    assert merged["search_distance_interval_status"] == "exact"
    assert merged["search_distance_interval_exact"] is True
    assert merged["search_status"] == "terminal_negative"
    assert merged["candidate_persistence_lane"] == (
        "negative_search_feedback"
    )
    assert merged["candidate_persistence_reason"] == (
        "replayed_scalar_fom_excluding_logical_witness"
    )
    assert merged["oracle_deferred"] is False
    assert merged["oracle_ladder_complete"] is True
    assert merged["oracle_ladder_next_threshold"] is None
    assert merged["global_proof_frontier_injected"] is True
    assert merged["global_proof_frontier_first_seen_sequence"] == 17
    assert merged["final_gate_excluded_by_upper_bound"] is True
    assert merged["search_final_gate_excluded_by_upper_bound"] is True
    for field in (
        "negative_archive_match_counts",
        "negative_archive_coordinate_sha256",
        "negative_archive_penalty",
        "negative_archive_penalty_components",
        "negative_archive_witness_match_counts",
        "negative_archive_witness_motif_sha256",
    ):
        assert merged[field] == upper[field]
    assert merged["oracle_ladder_history"] == upper[
        "oracle_ladder_history"
    ]
    assert merged["oracle_last_attempt"] == upper["oracle_last_attempt"]
    assert merged["oracle_last_attempt_outcome"] == "SAT"
    assert merged["oracle_last_attempt_threshold"] == exact_distance
    assert merged["oracle_frontier_selected"] is True
    assert merged["oracle_batch_budget_exhausted"] is False
    assert merged["oracle_evidence_sha256"] == upper[
        "low_weight_oracle"
    ]["evidence_sha256"]
    assert merged["stage"] == "low_weight_oracle_rejected"
    assert merged["score"] == 0.0
    assert merged["fitness"] == 0.0
    assert merged["fitness_distance_credit"] == 0.0
    assert lower == original_lower
    assert upper == original_upper
    # Search exactness never masquerades as a release/MILP exact result.
    assert merged["d_is_exact"] is False
    assert merged["distance_trusted"] is False
    proof = merged["search_distance_interval_proof"]
    unsigned_proof = dict(proof)
    proof_sha256 = unsigned_proof.pop("proof_sha256")
    assert proof_sha256 == _canonical_payload_sha256(unsigned_proof)
    assert proof["candidate_sha256"] == candidate_sha256
    assert proof["lower_bound_evidence_sha256"] == lower_evidence[
        "evidence_sha256"
    ]
    assert proof["upper_bound_oracle_evidence_sha256"] == upper[
        "low_weight_oracle"
    ]["evidence_sha256"]

    metadata_free_upper = copy.deepcopy(upper)
    for field in (
        "negative_archive_match_counts",
        "negative_archive_coordinate_sha256",
        "negative_archive_penalty",
        "negative_archive_penalty_components",
        "negative_archive_witness_match_counts",
        "negative_archive_witness_motif_sha256",
        "oracle_ladder_history",
        "oracle_last_attempt",
        "oracle_last_attempt_outcome",
        "oracle_last_attempt_threshold",
        "oracle_frontier_selected",
        "oracle_batch_budget_exhausted",
    ):
        metadata_free_upper.pop(field)
    [metadata_cleared] = _deduplicate([lower, metadata_free_upper])
    for field in (
        "negative_archive_match_counts",
        "negative_archive_coordinate_sha256",
        "negative_archive_penalty",
        "negative_archive_penalty_components",
        "negative_archive_witness_match_counts",
        "negative_archive_witness_motif_sha256",
        "oracle_ladder_history",
        "oracle_last_attempt",
        "oracle_last_attempt_outcome",
        "oracle_last_attempt_threshold",
        "oracle_frontier_selected",
        "oracle_batch_budget_exhausted",
    ):
        assert field not in metadata_cleared
    assert metadata_cleared["oracle_evidence_sha256"] == upper[
        "low_weight_oracle"
    ]["evidence_sha256"]
    assert metadata_cleared["fitness"] == 0.0
    assert metadata_cleared["fitness_distance_credit"] == 0.0

    tampered_upper = copy.deepcopy(upper)
    tampered_upper["low_weight_oracle"]["witness"]["bits"][0] ^= 1
    [not_merged] = _deduplicate([lower, tampered_upper])
    assert "distance_upper_bound" not in not_merged
    assert not_merged["search_distance_interval_status"] == (
        "lower_bound_only"
    )

    different_sha = copy.deepcopy(upper)
    different_sha["candidate_sha256"] = "e" * 64
    [sha_isolated] = _deduplicate([lower, different_sha])
    assert "distance_upper_bound" not in sha_isolated
    assert sha_isolated["search_distance_interval_status"] == (
        "lower_bound_only"
    )

    scalar_lower = copy.deepcopy(lower)
    scalar_lower["target_mode"] = "scalar-fom-strict-v1"
    gist_upper = copy.deepcopy(upper)
    gist_upper["target_mode"] = "gist-pareto-challenge-v1"
    [target_conflict] = _deduplicate([scalar_lower, gist_upper])
    assert target_conflict["target_binding_status"] == "conflict"
    assert target_conflict["target_mode_conflict"] == [
        "gist-pareto-challenge-v1",
        "scalar-fom-strict-v1",
    ]
    assert target_conflict["search_status"] == (
        "unresolved_target_conflict"
    )
    assert target_conflict["search_distance_interval_exact"] is False
    assert "search_exact_distance" not in target_conflict
    assert "threshold_rejection_proven" not in target_conflict
    assert _deduplicate([target_conflict]) == [target_conflict]


def _v5_ledger(candidate_sha256, history):
    ledger = {
        "kind": "qcode-coset-stage1-proof-ledger-v1",
        "schema_version": 1,
        "proof_ladder_version": 3,
        "candidate_sha256": candidate_sha256,
        "entries": [{
            field: copy.deepcopy(entry.get(field))
            for field in (
                "threshold",
                "outcome",
                "evidence_sha256",
                "attempt_sha256",
                "cache_sha256",
            )
        } for entry in history],
    }
    ledger["root_sha256"] = _canonical_payload_sha256(ledger)
    return ledger


def _v5_source_row(*, final_outcome, final_attempts, cache_digit):
    row = candidate(ell=3, m=6, k=4, d=0, fom=0.0)
    row.pop("d")
    row["candidate_sha256"] = "a" * 64
    lower_evidence = {
        "schema_version": 1,
        "kind": "qcode-css-low-weight-oracle",
        "outcome": "UNSAT",
        "decision_complete": True,
        "retryable": False,
        "max_weight": 4,
        "distance_lower_bound": 5,
        "witness": None,
    }
    lower_evidence["evidence_sha256"] = _canonical_payload_sha256(
        lower_evidence
    )
    lower_attempt = "1" * 64
    history = [{
        "threshold": 4,
        "outcome": "UNSAT",
        "attempts": 1,
        "cache_hit": True,
        "evidence_sha256": lower_evidence["evidence_sha256"],
        "attempt_sha256": lower_attempt,
        "cache_sha256": "2" * 64,
    }]
    final_evidence_sha256 = (
        "3" * 64 if final_outcome in {"SAT", "UNSAT"} else None
    )
    last_attempt = {
        "outcome": final_outcome,
        "strategy_id": "test-v5",
        "test_generation": f"{final_attempts}:{cache_digit}",
    }
    final_attempt = _canonical_payload_sha256(last_attempt)
    last_attempt["attempt_sha256"] = final_attempt
    history.append({
        "threshold": 6,
        "outcome": final_outcome,
        "attempts": final_attempts,
        "cache_hit": False,
        "evidence_sha256": final_evidence_sha256,
        "attempt_sha256": final_attempt,
        "cache_sha256": cache_digit * 64,
    })
    row.update({
        "distance_lower_bound": 5,
        "distance_lower_bound_proven": True,
        "distance_lower_bound_status": "search_oracle_proven",
        "distance_lower_bound_evidence": lower_evidence,
        "distance_lower_bound_evidence_sha256": lower_evidence[
            "evidence_sha256"
        ],
        "oracle_ladder_schema_version": 3,
        "oracle_ladder_cutoff": 8,
        "oracle_ladder_thresholds": [4, 6, 8],
        "oracle_ladder_history": history,
        "oracle_ladder_complete": False,
        "oracle_ladder_next_threshold": 6,
        "oracle_last_attempt": last_attempt,
        "oracle_last_attempt_outcome": final_outcome,
        "oracle_last_attempt_threshold": 6,
        "oracle_deferred": False,
        "oracle_retryable": True,
        "distance_retry_required": True,
        "search_status": "partial_lower_bound_retry",
    })
    row["proof_ledger"] = _v5_ledger(row["candidate_sha256"], history)
    if final_outcome == "SAT":
        row.update({
            "stub_upper": True,
            "low_weight_oracle": {
                "outcome": "SAT",
                "max_weight": 6,
                "evidence_sha256": final_evidence_sha256,
                "witness": {"weight": 6, "bits": [1]},
            },
        })
    return row


def _v5_unknown_only_source_row(*, cache_hit, cache_digit="7"):
    row = candidate(ell=3, m=6, k=4, d=0, fom=0.0)
    row.pop("d")
    row["candidate_sha256"] = "a" * 64
    last_attempt = {
        "outcome": "UNKNOWN",
        "strategy_id": "test-v5-unknown-only",
    }
    attempt_sha256 = _canonical_payload_sha256(last_attempt)
    last_attempt["attempt_sha256"] = attempt_sha256
    history = [{
        "threshold": 4,
        "outcome": "UNKNOWN",
        "attempts": 2,
        "cache_hit": cache_hit,
        "evidence_sha256": None,
        "attempt_sha256": attempt_sha256,
        "cache_sha256": "8" * 64,
    }]
    row.update({
        "static_legal": True,
        "oracle_ladder_schema_version": 3,
        "oracle_ladder_cutoff": 6,
        "oracle_ladder_thresholds": [4, 6],
        "oracle_ladder_history": history,
        "oracle_ladder_complete": False,
        "oracle_ladder_next_threshold": 4,
        "oracle_last_attempt": last_attempt,
        "oracle_last_attempt_outcome": "UNKNOWN",
        "oracle_last_attempt_threshold": 4,
        "oracle_batch_budget_exhausted": False,
        "low_weight_oracle_outcome": "UNKNOWN",
        "oracle_deferred": cache_hit,
        "oracle_retryable": True,
        "distance_retry_required": True,
        "search_status": (
            "unresolved_budget" if cache_hit else "unresolved"
        ),
    })
    row["proof_ledger"] = _v5_ledger(row["candidate_sha256"], history)
    return row


def test_policy_v5_composes_terminal_generation_and_is_canonical(monkeypatch):
    unknown = _v5_source_row(
        final_outcome="UNKNOWN", final_attempts=2, cache_digit="4"
    )
    sat = _v5_source_row(
        final_outcome="SAT", final_attempts=3, cache_digit="5"
    )

    def trusted(row):
        oracle = row.get("low_weight_oracle")
        if not isinstance(oracle, dict) or oracle.get("outcome") != "SAT":
            return None
        return 6, copy.deepcopy(oracle), copy.deepcopy(oracle["witness"])

    monkeypatch.setattr("humanize.flow._trusted_search_upper_bound", trusted)
    [forward] = _deduplicate(
        [unknown, sat],
        policy_version=CANDIDATE_BATCH_POLICY_COMPOSITE_PROVENANCE_VERSION,
    )
    [reverse] = _deduplicate(
        [sat, unknown],
        policy_version=CANDIDATE_BATCH_POLICY_COMPOSITE_PROVENANCE_VERSION,
    )
    assert forward == reverse
    assert _deduplicate(
        [forward],
        policy_version=CANDIDATE_BATCH_POLICY_COMPOSITE_PROVENANCE_VERSION,
    ) == [forward]
    assert [entry["outcome"] for entry in forward["oracle_ladder_history"]] == [
        "UNSAT",
        "SAT",
    ]
    assert forward["oracle_last_attempt_outcome"] == "SAT"
    assert forward["oracle_last_attempt_threshold"] == 6
    assert forward["oracle_last_attempt"]["attempt_sha256"] == sat[
        "oracle_last_attempt"
    ]["attempt_sha256"]
    assert forward["proof_ledger"] == _v5_ledger(
        forward["candidate_sha256"], forward["oracle_ladder_history"]
    )
    proof = forward["search_distance_interval_proof"]
    assert proof["lower_bound_ledger_root_sha256"] == forward[
        "proof_ledger"
    ]["root_sha256"]
    unsigned = dict(proof)
    assert unsigned.pop("proof_sha256") == _canonical_payload_sha256(unsigned)


def test_policy_v5_uses_latest_unknown_generation_and_preserves_lane():
    earlier = _v5_source_row(
        final_outcome="UNKNOWN", final_attempts=2, cache_digit="4"
    )
    later = _v5_source_row(
        final_outcome="UNKNOWN", final_attempts=3, cache_digit="6"
    )
    earlier.update({
        "candidate_persistence_lane": "global_scalar_fom_proof_frontier",
        "candidate_persistence_reason": (
            "target_aware_cross_program_proof_continuation"
        ),
    })
    [forward] = _deduplicate([earlier, later], policy_version=5)
    [reverse] = _deduplicate([later, earlier], policy_version=5)
    assert forward == reverse
    assert forward["oracle_ladder_history"][-1]["attempts"] == 3
    assert forward["oracle_ladder_history"][-1]["cache_sha256"] == "6" * 64
    assert forward["oracle_last_attempt"]["attempt_sha256"] == later[
        "oracle_last_attempt"
    ]["attempt_sha256"]
    assert forward["candidate_persistence_lane"] == (
        "global_scalar_fom_proof_frontier"
    )


def test_policy_v5_unknown_only_cache_hit_normalizes_lifecycle():
    fresh = _v5_unknown_only_source_row(cache_hit=False)
    cached = _v5_unknown_only_source_row(cache_hit=True)
    [forward] = _deduplicate([fresh, cached], policy_version=5)
    [reverse] = _deduplicate([cached, fresh], policy_version=5)
    assert forward == reverse
    assert _deduplicate([forward], policy_version=5) == [forward]
    assert forward["oracle_ladder_history"][-1]["cache_hit"] is True
    assert forward["low_weight_oracle_outcome"] == "UNKNOWN"
    assert forward["oracle_deferred"] is True
    assert forward["oracle_retryable"] is True
    assert forward["distance_retry_required"] is True
    assert forward["oracle_ladder_next_threshold"] == 4
    assert forward["search_status"] == "unresolved_budget"


def test_policy_v5_target_conflict_preserves_fail_closed_lifecycle():
    scalar = _v5_source_row(
        final_outcome="UNKNOWN", final_attempts=2, cache_digit="4"
    )
    gist = copy.deepcopy(scalar)
    scalar["target_mode"] = "scalar-fom-strict-v1"
    gist["target_mode"] = "gist-pareto-challenge-v1"
    [forward] = _deduplicate([scalar, gist], policy_version=5)
    [reverse] = _deduplicate([gist, scalar], policy_version=5)
    assert forward == reverse
    assert _deduplicate([forward], policy_version=5) == [forward]
    assert forward["target_binding_status"] == "conflict"
    assert forward["target_mode_conflict"] == [
        "gist-pareto-challenge-v1",
        "scalar-fom-strict-v1",
    ]
    assert forward["search_status"] == "unresolved_target_conflict"
    assert forward["search_distance_interval_status"] == (
        "target_mode_conflict"
    )
    assert forward["oracle_retryable"] is False
    assert forward["distance_retry_required"] is False
    assert forward["proof_ledger"] == _v5_ledger(
        forward["candidate_sha256"], forward["oracle_ladder_history"]
    )


def test_policy_v5_invalid_dimensions_and_static_rejection_preserve_lifecycle():
    invalid = _v5_source_row(
        final_outcome="UNKNOWN", final_attempts=2, cache_digit="4"
    )
    invalid.update({
        "n": 0,
        "search_status": "invalid",
        "low_weight_oracle_outcome": "NOT_RUN",
        "oracle_deferred": False,
        "oracle_retryable": False,
        "distance_retry_required": False,
    })
    [invalid_result] = _deduplicate([invalid], policy_version=5)
    assert invalid_result["search_status"] == "invalid"
    assert invalid_result["low_weight_oracle_outcome"] == "NOT_RUN"
    assert invalid_result["oracle_deferred"] is False
    assert invalid_result["oracle_retryable"] is False
    assert invalid_result["distance_retry_required"] is False

    static = _v5_unknown_only_source_row(cache_hit=True)
    static.update({
        "static_legal": False,
        "search_status": "unresolved",
        "low_weight_oracle_outcome": "NOT_RUN",
        "oracle_deferred": False,
        "oracle_retryable": False,
        "distance_retry_required": False,
    })
    [static_result] = _deduplicate([static], policy_version=5)
    assert static_result["search_status"] == "unresolved"
    assert static_result["low_weight_oracle_outcome"] == "NOT_RUN"
    assert static_result["oracle_deferred"] is False
    assert static_result["oracle_retryable"] is False
    assert static_result["distance_retry_required"] is False
    assert static_result["oracle_ladder_history"][-1]["cache_hit"] is True


@pytest.mark.parametrize("evidence_kind", ["exact", "milp", "bp"])
def test_policy_v5_non_stage1_distance_rows_preserve_lifecycle(evidence_kind):
    row = _v5_unknown_only_source_row(cache_hit=True)
    row.update({
        "d": 7,
        "d_is_exact": evidence_kind == "exact",
        "distance_status": (
            "exact" if evidence_kind == "exact" else "upper_bound"
        ),
        "stage": "exact" if evidence_kind == "exact" else evidence_kind,
        "search_status": (
            "exact" if evidence_kind == "exact" else "unresolved"
        ),
        "low_weight_oracle_outcome": "NOT_APPLICABLE",
        "oracle_ladder_complete": True,
        "oracle_ladder_next_threshold": None,
        "oracle_deferred": False,
        "oracle_retryable": False,
        "distance_retry_required": False,
    })
    if evidence_kind == "milp":
        row["milp_attempted"] = True
    [result] = _deduplicate([row], policy_version=5)
    assert result["search_status"] == row["search_status"]
    assert result["low_weight_oracle_outcome"] == "NOT_APPLICABLE"
    assert result["oracle_ladder_complete"] is True
    assert result["oracle_ladder_next_threshold"] is None
    assert result["oracle_deferred"] is False
    assert result["oracle_retryable"] is False
    assert result["distance_retry_required"] is False
    assert result["oracle_ladder_history"][-1]["cache_hit"] is True


def test_policy_v5_mixed_formal_primary_is_idempotent():
    source = _v5_unknown_only_source_row(cache_hit=True)
    formal = copy.deepcopy(source)
    for field in (
        "oracle_ladder_schema_version",
        "oracle_ladder_cutoff",
        "oracle_ladder_thresholds",
        "oracle_ladder_history",
        "proof_ledger",
        "oracle_last_attempt",
        "oracle_last_attempt_outcome",
        "oracle_last_attempt_threshold",
        "oracle_frontier_selected",
        "oracle_batch_budget_exhausted",
    ):
        formal.pop(field, None)
    formal.update({
        "d": 7,
        "d_is_exact": True,
        "distance_status": "exact",
        "stage": "exact",
        "search_status": "exact",
        "low_weight_oracle_outcome": "NOT_APPLICABLE",
        "oracle_ladder_complete": True,
        "oracle_ladder_next_threshold": None,
        "oracle_deferred": False,
        "oracle_retryable": False,
        "distance_retry_required": False,
    })
    [forward] = _deduplicate([formal, source], policy_version=5)
    [reverse] = _deduplicate([source, formal], policy_version=5)
    assert forward == reverse
    assert forward["oracle_ladder_schema_version"] == 3
    assert forward["oracle_ladder_cutoff"] == 6
    assert forward["oracle_ladder_thresholds"] == [4, 6]
    assert forward["search_status"] == "exact"
    assert forward["oracle_retryable"] is False
    assert _deduplicate([forward], policy_version=5) == [forward]


def test_policy_v5_rejects_conflicting_or_malformed_v3_provenance(monkeypatch):
    sat = _v5_source_row(
        final_outcome="SAT", final_attempts=3, cache_digit="5"
    )
    unsat = _v5_source_row(
        final_outcome="UNSAT", final_attempts=4, cache_digit="6"
    )
    monkeypatch.setattr(
        "humanize.flow._trusted_search_upper_bound",
        lambda row: (
            (6, copy.deepcopy(row["low_weight_oracle"]), {"weight": 6})
            if row.get("stub_upper") is True else None
        ),
    )
    with pytest.raises(RoundTransactionError, match="conflicting SAT/UNSAT"):
        _deduplicate([sat, unsat], policy_version=5)

    malformed = copy.deepcopy(sat)
    malformed["proof_ledger"]["entries"][-1]["cache_sha256"] = "7" * 64
    malformed["proof_ledger"]["root_sha256"] = _canonical_payload_sha256({
        key: value
        for key, value in malformed["proof_ledger"].items()
        if key != "root_sha256"
    })
    with pytest.raises(RoundTransactionError, match="disagrees"):
        _deduplicate([sat, malformed], policy_version=5)

    tampered_attempt = copy.deepcopy(sat)
    tampered_attempt["oracle_last_attempt"]["elapsed_s"] = 1.0
    with pytest.raises(RoundTransactionError, match="last-attempt"):
        _deduplicate([tampered_attempt], policy_version=5)

    extra_history_field = copy.deepcopy(sat)
    extra_history_field["oracle_ladder_history"][-1][
        "unbound_extra"
    ] = "input-order-dependent"
    with pytest.raises(RoundTransactionError, match="history fields"):
        _deduplicate([extra_history_field], policy_version=5)

    wrong_unknown = _v5_source_row(
        final_outcome="UNKNOWN", final_attempts=2, cache_digit="4"
    )
    wrong_unknown["oracle_ladder_history"][-1]["evidence_sha256"] = "8" * 64
    wrong_unknown["proof_ledger"] = _v5_ledger(
        wrong_unknown["candidate_sha256"],
        wrong_unknown["oracle_ladder_history"],
    )
    with pytest.raises(RoundTransactionError, match="outcome/evidence"):
        _deduplicate([wrong_unknown], policy_version=5)

    monkeypatch.setattr(
        "humanize.flow._trusted_search_upper_bound", lambda _row: None
    )
    with pytest.raises(RoundTransactionError, match="no replayed upper"):
        _deduplicate([sat], policy_version=5)

    missing_lower = _v5_source_row(
        final_outcome="UNKNOWN", final_attempts=2, cache_digit="4"
    )
    for field in (
        "distance_lower_bound",
        "distance_lower_bound_proven",
        "distance_lower_bound_status",
        "distance_lower_bound_evidence",
        "distance_lower_bound_evidence_sha256",
    ):
        missing_lower.pop(field, None)
    with pytest.raises(RoundTransactionError, match="no selected lower"):
        _deduplicate([missing_lower], policy_version=5)

    # A terminal SAT row may carry a valid UNSAT prefix, but that prefix must
    # still be backed by the full producer-owned lower-bound artifact.  This
    # is the exact singleton/global-frontier shape that exposed the producer
    # clearing the artifact before policy-v5 materialization.
    missing_terminal_lower = copy.deepcopy(sat)
    for field in (
        "distance_lower_bound",
        "distance_lower_bound_proven",
        "distance_lower_bound_status",
        "distance_lower_bound_evidence",
        "distance_lower_bound_evidence_sha256",
        "fom_lower_bound",
    ):
        missing_terminal_lower.pop(field, None)
    monkeypatch.setattr(
        "humanize.flow._trusted_search_upper_bound",
        lambda row: (
            (6, copy.deepcopy(row["low_weight_oracle"]), {"weight": 6})
            if row.get("stub_upper") is True else None
        ),
    )
    with pytest.raises(RoundTransactionError, match="no selected lower"):
        _deduplicate([missing_terminal_lower], policy_version=5)

    phantom = _v5_source_row(
        final_outcome="UNKNOWN", final_attempts=2, cache_digit="4"
    )
    phantom["oracle_ladder_history"] = []
    phantom["proof_ledger"] = _v5_ledger(phantom["candidate_sha256"], [])
    phantom["oracle_last_attempt"] = None
    phantom.pop("oracle_last_attempt_outcome")
    # Leaving just the threshold is the original deferred-no-attempt bug.
    with pytest.raises(RoundTransactionError, match="phantom"):
        _deduplicate([phantom], policy_version=5)


@pytest.mark.parametrize(
    ("forgery", "value"),
    [
        ("ledger_schema", True),
        ("ledger_schema", 1.0),
        ("proof_ladder_version", 3.0),
        ("row_ladder_version", 3.0),
        ("row_ladder_version", True),
        ("ladder_cutoff", 8.0),
        ("last_threshold", 6.0),
        ("history_threshold", True),
        ("ledger_entry_threshold", True),
        ("ledger_entry_threshold", 4.0),
    ],
)
def test_policy_v5_rejects_bool_or_float_integer_forgery(forgery, value):
    row = _v5_source_row(
        final_outcome="UNKNOWN", final_attempts=2, cache_digit="4"
    )
    if forgery == "ledger_schema":
        row["proof_ledger"]["schema_version"] = value
    elif forgery == "proof_ladder_version":
        row["proof_ledger"]["proof_ladder_version"] = value
    elif forgery == "row_ladder_version":
        row["oracle_ladder_schema_version"] = value
    elif forgery == "ladder_cutoff":
        row["oracle_ladder_cutoff"] = value
    elif forgery == "last_threshold":
        row["oracle_last_attempt_threshold"] = value
    elif forgery == "ledger_entry_threshold":
        row["proof_ledger"]["entries"][0]["threshold"] = value
        unsigned_ledger = dict(row["proof_ledger"])
        unsigned_ledger.pop("root_sha256")
        row["proof_ledger"]["root_sha256"] = _canonical_payload_sha256(
            unsigned_ledger
        )
    else:
        assert forgery == "history_threshold"
        row["oracle_ladder_history"][0]["threshold"] = value
    with pytest.raises(RoundTransactionError):
        _deduplicate([row], policy_version=5)


@pytest.mark.parametrize(
    "forgery",
    [
        "cache_attempts",
        "cache_outcome",
        "cache_evidence",
        "cache_attempt",
    ],
)
def test_policy_v5_content_digests_bind_full_generation_metadata(forgery):
    outcome = "UNSAT" if forgery == "cache_evidence" else "UNKNOWN"
    left = _v5_source_row(
        final_outcome=outcome, final_attempts=2, cache_digit="4"
    )
    right = copy.deepcopy(left)
    entry = right["oracle_ladder_history"][-1]
    if forgery == "cache_attempts":
        entry["attempts"] += 1
    elif forgery == "cache_outcome":
        entry["outcome"] = "SAT"
        entry["evidence_sha256"] = "9" * 64
        unsigned_attempt = dict(right["oracle_last_attempt"])
        unsigned_attempt.pop("attempt_sha256")
        unsigned_attempt["outcome"] = "SAT"
        entry["attempt_sha256"] = _canonical_payload_sha256(
            unsigned_attempt
        )
        right["oracle_last_attempt"] = {
            **unsigned_attempt,
            "attempt_sha256": entry["attempt_sha256"],
        }
        right["oracle_last_attempt_outcome"] = "SAT"
    elif forgery == "cache_evidence":
        entry["evidence_sha256"] = "9" * 64
    elif forgery == "cache_attempt":
        unsigned_attempt = dict(right["oracle_last_attempt"])
        unsigned_attempt.pop("attempt_sha256")
        unsigned_attempt["strategy_id"] = "forged-alternate-strategy"
        entry["attempt_sha256"] = _canonical_payload_sha256(
            unsigned_attempt
        )
        right["oracle_last_attempt"] = {
            **unsigned_attempt,
            "attempt_sha256": entry["attempt_sha256"],
        }
    else:
        raise AssertionError(f"unhandled forgery: {forgery}")
    right["proof_ledger"] = _v5_ledger(
        right["candidate_sha256"], right["oracle_ladder_history"]
    )
    for rows in ([left, right], [right, left]):
        with pytest.raises(RoundTransactionError, match="cache SHA"):
            _deduplicate(rows, policy_version=5)


def test_policy_v5_attempt_may_be_referenced_by_distinct_cache_parents():
    left = _v5_source_row(
        final_outcome="UNKNOWN", final_attempts=2, cache_digit="4"
    )
    right = copy.deepcopy(left)
    right["oracle_ladder_history"][-1]["cache_sha256"] = "9" * 64
    right["proof_ledger"] = _v5_ledger(
        right["candidate_sha256"], right["oracle_ladder_history"]
    )
    [forward] = _deduplicate([left, right], policy_version=5)
    [reverse] = _deduplicate([right, left], policy_version=5)
    assert forward == reverse
    assert forward["oracle_ladder_history"][-1]["cache_sha256"] == "9" * 64
    assert _deduplicate([forward], policy_version=5) == [forward]


def test_policy_v4_split_provenance_bytes_remain_frozen(monkeypatch):
    unknown = _v5_source_row(
        final_outcome="UNKNOWN", final_attempts=2, cache_digit="4"
    )
    sat = _v5_source_row(
        final_outcome="SAT", final_attempts=3, cache_digit="5"
    )
    # The historical fixture predates the v5 source-cutoff contract.
    for row, digit in ((unknown, "4"), (sat, "5")):
        row.pop("oracle_ladder_cutoff")
        row["oracle_ladder_history"][-1]["attempt_sha256"] = digit * 64
        row["oracle_last_attempt"].pop("test_generation")
        row["oracle_last_attempt"]["attempt_sha256"] = digit * 64
        row["proof_ledger"] = _v5_ledger(
            row["candidate_sha256"], row["oracle_ladder_history"]
        )
    monkeypatch.setattr(
        "humanize.flow._trusted_search_upper_bound",
        lambda row: (
            (6, copy.deepcopy(row["low_weight_oracle"]), {"weight": 6})
            if row.get("stub_upper") is True else None
        ),
    )
    [historical] = _deduplicate([unknown, sat], policy_version=4)
    assert _canonical_payload_sha256(historical) == (
        "882e6743b9b4d2e9f2c47af8f1d9e8fc"
        "57e591811426d4c61ffbc32873c7ab27"
    )


def test_candidate_batch_policy_v3_output_bytes_remain_frozen(monkeypatch):
    """Policy v4 must not rewrite a committed policy-v3 transaction."""

    candidate_sha256 = "8" * 64
    lower = candidate(k=6, d=0, fom=0.0)
    lower.pop("d")
    lower["candidate_sha256"] = candidate_sha256
    evidence = {
        "schema_version": 1,
        "kind": "qcode-css-low-weight-oracle",
        "outcome": "UNSAT",
        "decision_complete": True,
        "retryable": False,
        "max_weight": 0,
        "distance_lower_bound": 1,
        "witness": None,
    }
    evidence["evidence_sha256"] = _canonical_payload_sha256(evidence)
    ledger = {
        "kind": "qcode-coset-stage1-proof-ledger-v1",
        "schema_version": 1,
        "proof_ladder_version": 2,
        "candidate_sha256": candidate_sha256,
        "entries": [{
            "threshold": 0,
            "outcome": "UNSAT",
            "evidence_sha256": evidence["evidence_sha256"],
            "cache_sha256": "9" * 64,
        }],
    }
    ledger["root_sha256"] = _canonical_payload_sha256(ledger)
    lower.update({
        "distance_lower_bound": 1,
        "distance_lower_bound_proven": True,
        "distance_lower_bound_status": "search_oracle_proven",
        "distance_lower_bound_evidence": evidence,
        "distance_lower_bound_evidence_sha256": evidence[
            "evidence_sha256"
        ],
        "proof_ledger": ledger,
        "oracle_ladder_complete": False,
        "challenge_target_lower_bound_proven": False,
        "fitness": 0.75,
        "fitness_distance_credit": 0.5,
        "negative_archive_penalty": 0.01,
        "negative_archive_witness_motif_sha256": None,
        "oracle_last_attempt_outcome": "UNSAT",
    })
    upper = candidate(k=6, d=0, fom=0.0, shift=1)
    upper["candidate_sha256"] = candidate_sha256
    upper["stub_trusted_upper"] = True
    upper.update({
        "negative_archive_penalty": 0.04,
        "negative_archive_witness_motif_sha256": "a" * 64,
        "oracle_last_attempt_outcome": "SAT",
    })
    oracle = {
        "max_weight": 1,
        "evidence_sha256": "b" * 64,
    }
    witness = {"weight": 1, "bits": [1]}
    monkeypatch.setattr(
        "humanize.flow._trusted_search_upper_bound",
        lambda row: (
            (1, copy.deepcopy(oracle), copy.deepcopy(witness))
            if row.get("stub_trusted_upper") is True
            else None
        ),
    )

    merged_v3 = _merge_duplicate_search_evidence(
        lower,
        [lower, upper],
        policy_version=CANDIDATE_BATCH_POLICY_EVIDENCE_MERGE_VERSION,
    )
    assert _canonical_payload_sha256(merged_v3) == (
        "b211683790fc60f647aaa0173eed64c4"
        "3bbc6c9f059bcd6b14a2e326f7d35620"
    )
    with pytest.raises(ValueError, match="candidate batch policy"):
        _merge_duplicate_search_evidence(
            lower,
            [lower, upper],
            policy_version=True,
        )


def test_distance_error_precedes_unresolved_pending_and_quick_lanes():
    reasons = [
        "quick_distance_budget",
        "selected_distance_pending",
        "selected_distance_unresolved",
        "selected_distance_error",
    ]
    rows = []
    for shift, reason in enumerate(reasons):
        row = candidate(k=4, d=0, fom=0.0, shift=shift)
        row.update({
            "stage": reason,
            "candidate_persistence_lane": (
                "winner_capable_quick_exploration"
            ),
            "candidate_persistence_reason": reason,
            "winner_capable_parameters": True,
            "minimum_winning_distance": 15,
            "singleton_distance_upper_bound": 35,
        })
        rows.append(row)

    selected = select_for_milp(rows, None, set(), 3)

    assert len(selected) == 1
    assert selected[0]["candidate_persistence_reason"] == (
        "selected_distance_error"
    )


def test_duplicate_write_ahead_rows_keep_error_then_later_positive_evidence():
    quick = candidate(k=4, d=0, fom=0.0)
    quick.update({
        "stage": "quick_k_only",
        "candidate_persistence_lane": "winner_capable_quick_exploration",
        "candidate_persistence_reason": "quick_distance_budget",
        "winner_capable_parameters": True,
        "minimum_winning_distance": 15,
        "singleton_distance_upper_bound": 35,
    })
    pending = dict(quick)
    pending["candidate_persistence_reason"] = "selected_distance_pending"
    unresolved = dict(quick)
    unresolved["candidate_persistence_reason"] = (
        "selected_distance_unresolved"
    )
    failed = dict(quick)
    failed["candidate_persistence_reason"] = "selected_distance_error"

    [selected_without_distance] = _deduplicate(
        [quick, pending, unresolved, failed]
    )
    assert selected_without_distance["candidate_persistence_reason"] == (
        "selected_distance_error"
    )

    positive = candidate(k=4, d=16, fom=4 * 16 * 16 / 72)
    [selected_with_distance] = _deduplicate(
        [quick, pending, unresolved, failed, positive]
    )
    assert selected_with_distance["d"] == 16
    assert selected_with_distance["stage"] == "refined_estimate"


def test_milp_selection_rejects_forged_or_malformed_quick_lane_marker():
    malformed = candidate(k=4, d=0, fom=0.0)
    malformed.update({
        "stage": "quick_k_only",
        "candidate_persistence_lane": "winner_capable_quick_exploration",
        "winner_capable_parameters": True,
        "minimum_winning_distance": "15",
        "singleton_distance_upper_bound": 35,
    })

    assert select_for_milp([malformed], None, set(), 3) == []


def test_structural_digest_prevents_cross_round_reaudit(tmp_path):
    archive = EliteArchive(tmp_path / "archive.json")
    row = candidate(k=8)
    row["static_eligibility"] = {"eligible": True}
    row["structural_novelty"] = {
        "checked": True,
        "novel": True,
        "canonical_digest": "same-tanner-graph",
    }
    archive.update([row], 1)
    digest = authoritative_candidate_digest(row)
    assert select_for_milp(
        [row], archive, set(), 1, {digest}
    ) == []


def test_unresolved_queue_reserves_one_lane_for_fresh_candidate(tmp_path):
    repo = tmp_path / "qcode"
    repo.mkdir()
    source = repo / "offline.jsonl"
    source.write_text("")
    flow = HumanizeFlow(
        FlowConfig(
            repo_dir=repo,
            run_id="retry-drain",
            max_rounds=1,
            milp_top=3,
            candidate_file=source,
        ),
        reviewer=FakeReviewer(),
    )
    unresolved_rows = [
        candidate(k=8, shift=shift) for shift in range(3)
    ]
    entries = [
        create_unresolved_entry(row, round_number=1)
        for row in unresolved_rows
    ]
    state = {
        "unresolved_candidates": {
            entry["candidate_key"]: entry for entry in entries
        },
        "audited_keys": [],
        "audited_structural_digests": [],
    }

    fresh = candidate(k=8, shift=3)
    selected = flow._select_audit_candidates(
        [fresh],
        state,
        screened_history=[fresh],
    )

    selected_keys = {code_key(row) for row in selected}
    assert code_key(fresh) in selected_keys
    assert len(selected_keys & set(state["unresolved_candidates"])) == 2
    assert len(selected) == 3


def test_unresolved_queue_fills_idle_fresh_lane_with_retry(tmp_path):
    repo = tmp_path / "qcode"
    repo.mkdir()
    source = repo / "offline.jsonl"
    source.write_text("")
    flow = HumanizeFlow(
        FlowConfig(
            repo_dir=repo,
            run_id="retry-fill",
            max_rounds=1,
            milp_top=3,
            candidate_file=source,
        ),
        reviewer=FakeReviewer(),
    )
    entries = [
        create_unresolved_entry(
            candidate(k=8, shift=shift),
            round_number=1,
        )
        for shift in range(3)
    ]
    state = {
        "current_round": 1,
        "unresolved_candidates": {
            entry["candidate_key"]: entry for entry in entries
        },
        "audited_keys": [],
        "audited_structural_digests": [],
    }

    selected = flow._select_audit_candidates(
        [],
        state,
        screened_history=[],
    )

    assert {code_key(row) for row in selected} == set(
        state["unresolved_candidates"]
    )
    assert len(selected) == 3


def test_single_milp_lane_alternates_fresh_and_retry_turns(tmp_path):
    repo = tmp_path / "qcode"
    repo.mkdir()
    source = repo / "offline.jsonl"
    source.write_text("")
    flow = HumanizeFlow(
        FlowConfig(
            repo_dir=repo,
            run_id="retry-alternation",
            max_rounds=3,
            milp_top=1,
            candidate_file=source,
        ),
        reviewer=FakeReviewer(),
    )
    unresolved = create_unresolved_entry(
        candidate(k=8, shift=0),
        round_number=1,
    )
    fresh = candidate(k=8, shift=1)
    state = {
        "current_round": 1,
        "unresolved_candidates": {
            unresolved["candidate_key"]: unresolved,
        },
        "audited_keys": [],
        "audited_structural_digests": [],
    }

    fresh_turn = flow._select_audit_candidates(
        [fresh],
        state,
        screened_history=[fresh],
    )
    state["current_round"] = 2
    retry_turn = flow._select_audit_candidates(
        [fresh],
        state,
        screened_history=[fresh],
    )

    assert [code_key(row) for row in fresh_turn] == [code_key(fresh)]
    assert [code_key(row) for row in retry_turn] == [
        unresolved["candidate_key"]
    ]


def test_forged_structural_digest_cannot_hide_candidate_before_audit(tmp_path):
    archive = EliteArchive(tmp_path / "archive.json")
    row = candidate(k=8)
    row["static_eligibility"] = {"eligible": True}
    row["structural_novelty"] = {
        "checked": True,
        "novel": True,
        "canonical_digest": "forged-terminal-digest",
    }

    assert select_for_milp(
        [row],
        archive,
        set(),
        1,
        {"forged-terminal-digest"},
    ) == [row]


def test_partial_milp_never_becomes_exact():
    partial = {
        "d": 18,
        "d_is_exact": True,
        "stage": "milp_exact",
        "milp_details": {
            "exact": True,
            "total_logicals": 24,
            "num_logicals_checked": 7,
            "logicals_optimal": 7,
        },
    }
    assert not _milp_is_fully_exact(partial)
    partial["milp_details"].update(
        num_logicals_checked=24, logicals_optimal=24
    )
    assert _milp_is_fully_exact(partial)


def test_jsonl_offset_is_resumable(tmp_path):
    path = tmp_path / "codes.jsonl"
    first = candidate()
    path.write_text(json.dumps(first) + "\n")
    rows, offset = read_jsonl_since(path, 0)
    assert [code_key(row) for row in rows] == [code_key(first)]
    assert read_jsonl_since(path, offset) == ([], offset)
    second = candidate(ell=12, m=6, shift=2)
    with path.open("a") as stream:
        stream.write(json.dumps(second) + "\n")
    rows, new_offset = read_jsonl_since(path, offset)
    assert [code_key(row) for row in rows] == [code_key(second)]
    assert new_offset > offset


class FakeReviewer:
    def review(self, prompt, round_dir):
        assert "BP-OSD returns an upper bound" in prompt
        return validate_review({
            "verdict": "promote",
            "summary": "The complete MILP audit is suitable for Lean promotion.",
            "risks": [],
            "recommended_focus": ["Try a second lattice cell."],
            "lessons": [{
                "insight": "Require complete logical-direction coverage.",
                "evidence": "The exact candidate has checked=optimal=total.",
                "action": "Keep partial MILP results as upper bounds.",
            }],
        })


def fake_milp(row, _config, **_invocation):
    result = dict(row)
    result.update({
        "milp_attempted": True,
        "stage": "milp_exact",
        "d_is_exact": True,
        "distance_source": "milp_exact",
        "milp_details": {
            "exact": True,
            "total_logicals": 2 * row["k"],
            "num_logicals_checked": 2 * row["k"],
            "logicals_optimal": 2 * row["k"],
        },
    })
    return result


def test_debug_exact_results_remain_unresolved_but_persist_review_memory(
    tmp_path,
):
    repo = tmp_path / "qcode"
    repo.mkdir()
    source = repo / "offline.jsonl"
    rows = [
        candidate(k=8),
        candidate(ell=12, m=6, k=8, d=8, fom=7.0, shift=0),
    ]
    source.write_text("".join(json.dumps(row) + "\n" for row in rows))
    config = FlowConfig(
        repo_dir=repo,
        run_id="test-humanize",
        max_rounds=1,
        milp_top=2,
        candidate_file=source,
        allow_debug_audit_evaluator=True,
    )
    flow = HumanizeFlow(config, reviewer=FakeReviewer(), milp_evaluator=fake_milp)
    with pytest.raises(UnresolvedAuditError):
        flow.run()
    state = flow.store.load_state()
    assert state is not None

    assert state["status"] == "incomplete-unresolved"
    assert state["current_round"] == 1
    evaluations = (repo / "results/runs/test-humanize/evaluations.jsonl").read_text().splitlines()
    assert len(evaluations) == 2
    assert all(
        json.loads(line)["audit_attempt"]["schema_version"] == 1
        for line in evaluations
    )
    assert state["audited_keys"] == []
    assert len(state["unresolved_candidates"]) == 2
    assert state["trusted_exact_count"] == 0
    assert state["trusted_win_count"] == 0
    memory = (repo / "results/humanize/test-humanize/bitlesson.md").read_text()
    assert "Require complete logical-direction coverage" in memory

    # A resumed debug run stays unresolved and does not append duplicates.
    with pytest.raises(UnresolvedAuditError):
        flow.run()
    assert len((repo / "results/runs/test-humanize/evaluations.jsonl").read_text().splitlines()) == 2
