from archon.commands.qcode_formalize import prepare_catalogs


def _row(*, novel: bool, score: float, ell: int) -> dict:
    return {
        "ell": ell,
        "m": 6,
        "A_terms": [[3, 0], [0, 1], [0, 2]],
        "B_terms": [[0, 3], [1, 0], [2, 0]],
        "n": 2 * ell * 6,
        "k": 12,
        "d": 12,
        "score": score,
        "stage": "milp_exact",
        "d_is_exact": True,
        "milp_attempted": True,
        "milp_details": {
            "exact": True,
            "total_logicals": 24,
            "num_logicals_checked": 24,
            "logicals_optimal": 24,
        },
        "structural_novelty": {
            "checked": True,
            "novel": novel,
            "matched_reference": None if novel else "Gross [[144,12,12]]",
        },
    }


def test_formalization_rejects_higher_scoring_structural_duplicate():
    duplicate = _row(novel=False, score=100.0, ell=12)
    novel = _row(novel=True, score=1.0, ell=6)
    exact, upper = prepare_catalogs([duplicate, novel], 10)
    selected = exact["archon-qcode-exact"]
    assert len(selected) == 1
    assert selected[0]["ell"] == 6
    assert selected[0]["structural_novelty"]["novel"] is True
    assert not upper["archon-qcode-upper"]


def test_formalization_keeps_one_representative_per_structural_digest():
    first = _row(novel=True, score=10.0, ell=12)
    second = _row(novel=True, score=9.0, ell=6)
    second["n"] = first["n"]
    second["k"] = first["k"]
    first["structural_novelty"]["canonical_digest"] = "same-structure"
    second["structural_novelty"]["canonical_digest"] = "same-structure"
    exact, upper = prepare_catalogs([first, second], 10)
    selected = exact["archon-qcode-exact"]
    assert len(selected) == 1
    assert selected[0]["score"] == 10.0
    assert not upper["archon-qcode-upper"]
