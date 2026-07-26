from evaluation.proof_triage import (
    candidate_identity,
    deduplicate_ranked,
    evidence_score,
    normalize_record,
    rank_record,
    stable_sort_key,
)


def direction(index, *, objective=None, dual=None, verified=False, **extra):
    return {
        "logical_type": "X" if index % 2 == 0 else "Z",
        "logical_index": index,
        "objective": objective,
        "mip_dual_bound": dual,
        "witness_verified": verified,
        **extra,
    }


def candidate(*, trial, directions, fom=0.0, digest=None, k=2):
    row = {
        "trial": trial,
        "ell": 6,
        "m": 6,
        "A_terms": [[0, 0], [1, 0], [0, 1]],
        "B_terms": [[0, 0], [2, 0], [0, 2]],
        "n": 72,
        "k": k,
        "required_distance": 10,
        "fom": fom,
        "directions": directions,
    }
    if digest is not None:
        row["novelty"] = {"canonical_digest": digest, "novel": True}
    return row


def test_normalize_expanded_claim_and_frontier_flat_rows():
    expanded = {
        "trial": 7,
        "claim": {
            "source": "expanded seed=3 trial=7",
            "ell": 9,
            "m": 6,
            "A_terms": [[0, 0]],
            "B_terms": [[1, 1]],
        },
        "n": 108,
        "k": 2,
        "required_distance": 26,
        "directions": [],
    }
    normalized = normalize_record(
        expanded, source="expanded.jsonl", line_number=8,
    )
    assert normalized["ell"] == 9
    assert normalized["n"] == 108
    assert normalized["trial"] == 7
    assert normalized["_triage_source"] == "expanded.jsonl"
    assert normalized["_triage_line_number"] == 8
    assert "claim" not in normalized

    frontier = {
        **expanded["claim"],
        "trial": 9,
        "n": 108,
        "k": 2,
        "required_distance": 26,
        "direction": {"objective": 29},
    }
    flat = normalize_record(frontier)
    assert flat["trial"] == 9
    assert flat["direction"]["objective"] == 29


def test_verified_low_witness_is_rejected_but_unverified_one_is_not():
    rejected = candidate(
        trial=1,
        directions=[direction(0, objective=9, dual=9, verified=True)],
    )
    score = evidence_score(rejected)
    assert score["status"] == "REJECTED"
    assert score["rejected"] is True
    assert score["threshold_safe_directions"] == 0

    unresolved = candidate(
        trial=2,
        directions=[direction(0, objective=9, dual=9, verified=False)],
    )
    assert evidence_score(unresolved)["rejected"] is False


def test_threshold_infeasibility_and_dual_bound_count_as_safe_progress():
    row = candidate(
        trial=1,
        k=1,
        directions=[
            direction(
                0,
                objective=None,
                dual=None,
                max_weight=9,
                operator=None,
                threshold_infeasible=True,
            ),
            direction(1, objective=13, dual=10.0, verified=True),
        ],
    )
    score = evidence_score(row)
    assert score["status"] == "THRESHOLD_PROVEN"
    assert score["threshold_safe_directions"] == 2
    assert score["coverage"] == 1.0
    assert score["min_dual_ratio"] == 1.0
    assert score["terminal_dual_ratio"] == 1.0


def test_rank_prefers_proof_progress_over_raw_fom():
    incumbent_only = rank_record(candidate(
        trial=1,
        fom=1000.0,
        digest="incumbent",
        directions=[direction(0, objective=40, dual=6.0, verified=True)],
    ))
    proof_progress = rank_record(candidate(
        trial=2,
        fom=1.0,
        digest="proof",
        directions=[direction(0, objective=40, dual=10.0, verified=True)],
    ))
    assert stable_sort_key(proof_progress) < stable_sort_key(incumbent_only)
    assert len(proof_progress["proof_score"]["rank_vector"]) == 5


def test_min_then_terminal_dual_ratio_precede_coverage():
    higher_coverage_weaker_floor = rank_record(candidate(
        trial=1,
        digest="wide",
        directions=[
            direction(0, objective=20, dual=10.0, verified=True),
            direction(1, objective=20, dual=9.5, verified=True),
        ],
    ))
    lower_coverage_stronger_floor = rank_record(candidate(
        trial=2,
        digest="deep",
        directions=[direction(0, objective=20, dual=10.0, verified=True)],
    ))
    assert (
        higher_coverage_weaker_floor["proof_score"]
        ["threshold_safe_directions"]
        == 1
    )
    assert (
        lower_coverage_stronger_floor["proof_score"]
        ["threshold_safe_directions"]
        == 1
    )
    assert (
        higher_coverage_weaker_floor["proof_score"]["coverage"]
        > lower_coverage_stronger_floor["proof_score"]["coverage"]
    )
    assert (
        stable_sort_key(lower_coverage_stronger_floor)
        < stable_sort_key(higher_coverage_weaker_floor)
    )


def test_structural_fallback_identity_matches_nested_and_flat_claims():
    expanded = candidate(trial=1, directions=[])
    expanded = {
        "claim": {
            key: expanded[key]
            for key in ("ell", "m", "A_terms", "B_terms")
        },
        **{
            key: value
            for key, value in expanded.items()
            if key not in ("ell", "m", "A_terms", "B_terms")
        },
    }
    flat = candidate(trial=99, directions=[])
    flat["A_terms"] = list(reversed(flat["A_terms"]))
    assert (
        candidate_identity(expanded)["canonical_digest"]
        == candidate_identity(flat)["canonical_digest"]
    )
    assert candidate_identity(expanded)["digest_kind"] == "structural-claim"


def test_digest_dedup_keeps_best_evidence_and_aggregates_sources():
    weak = candidate(
        trial=1,
        digest="same-code",
        fom=500.0,
        directions=[direction(0, objective=30, dual=7.0, verified=True)],
    )
    strong = candidate(
        trial=2,
        digest="same-code",
        fom=1.0,
        directions=[direction(0, objective=30, dual=10.0, verified=True)],
    )
    other = candidate(
        trial=3,
        digest="other-code",
        directions=[],
    )
    ranked = deduplicate_ranked(
        [weak, strong, other],
        sources=[
            "expanded-a.jsonl", "frontier-b.jsonl", "expanded-c.jsonl",
        ],
    )
    assert len(ranked) == 2
    assert ranked[0]["trial"] == 2
    identity = ranked[0]["triage_identity"]
    assert identity["canonical_digest"] == "same-code"
    assert identity["merged_record_count"] == 2
    assert identity["duplicate_count"] == 1
    assert identity["source_identities"] == [
        "expanded-a.jsonl#trial=1#line=1",
        "frontier-b.jsonl#trial=2#line=2",
    ]


def test_wrapped_audit_artifact_promotes_candidate_and_evidence():
    wrapped = {
        "status": "UNRESOLVED",
        "candidate": candidate(trial=4, directions=[]),
        "expected_directions": 4,
        "directions": [
            direction(0, objective=20, dual=10, verified=True),
        ],
    }
    normalized = normalize_record(wrapped)
    assert normalized["trial"] == 4
    assert normalized["directions"][0]["mip_dual_bound"] == 10
    assert evidence_score(wrapped)["threshold_safe_directions"] == 1


def test_digest_dedup_never_hides_a_verified_rejection():
    stale_unresolved = candidate(
        trial=1,
        digest="rejected-code",
        directions=[direction(0, objective=30, dual=9.9, verified=True)],
    )
    conclusive_rejection = candidate(
        trial=2,
        digest="rejected-code",
        directions=[direction(0, objective=9, dual=9, verified=True)],
    )
    [merged] = deduplicate_ranked(
        [stale_unresolved, conclusive_rejection],
        sources=["old.jsonl", "new.jsonl"],
    )
    assert merged["trial"] == 2
    assert merged["proof_score"]["status"] == "REJECTED"
    assert merged["triage_identity"]["merged_record_count"] == 2


def _schema2_xor_record(*, status, sectors):
    row = candidate(trial=8, directions=[], k=2)
    claim = {
        name: row.pop(name)
        for name in ("ell", "m", "A_terms", "B_terms")
    }
    row.update({
        "schema_version": 2,
        "claim": claim,
        "status": status,
        "expected_directions": 4,
        "completed_directions": 0,
        "completed_sectors": len(sectors),
        "sectors": sectors,
    })
    return row


def test_schema2_empty_directions_uses_xor_rejection():
    row = _schema2_xor_record(
        status="REJECTED",
        sectors=[{
            "sector": "X",
            "objective": 2,
            "witness_verified": True,
            "operator": {"weight": 2},
        }],
    )
    score = evidence_score(row)
    assert score["status"] == "REJECTED"
    assert score["rejected"] is True
    assert score["expected_directions"] == 2
    assert score["completed_directions"] == 1


def test_schema2_empty_directions_uses_xor_threshold_proof():
    row = _schema2_xor_record(
        status="THRESHOLD_PROVEN",
        sectors=[
            {
                "sector": "X",
                "threshold_infeasible": True,
                "status_name": "INFEASIBLE",
                "max_weight": 9,
                "operator": None,
            },
            {
                "sector": "Z",
                "threshold_infeasible": True,
                "status_name": "INFEASIBLE",
                "max_weight": 9,
                "operator": None,
            },
        ],
    )
    score = evidence_score(row)
    assert score["status"] == "THRESHOLD_PROVEN"
    assert score["rejected"] is False
    assert score["expected_directions"] == 2
    assert score["completed_directions"] == 2
    assert score["threshold_safe_directions"] == 2
    assert score["coverage"] == 1.0
