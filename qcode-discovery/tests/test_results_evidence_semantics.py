import json

import pytest

from evaluation.results import load_codes, save_code, update_pareto_front


def _row(
    *,
    marker: int,
    distance: int,
    status: str = "exact",
    exact: bool = True,
) -> dict:
    n = 144
    k = 12
    row = {
        "ell": 12,
        "m": 6,
        "A_terms": [[0, 0], [marker, 0], [0, 1]],
        "B_terms": [[0, 0], [0, 2], [1, 0]],
        "n": n,
        "k": k,
        "d": distance,
        "d_is_exact": exact,
        "distance_status": status,
        "exact_distance": distance if exact else None,
        "search_status": "exact" if exact else "unresolved",
        "fom": k * distance * distance / n,
    }
    if not exact:
        row.update({
            "distance_upper_bound": distance,
            "fom_upper_bound": row["fom"],
            "fitness_distance_credit": 0.0,
        })
    return row


def test_later_exact_replaces_same_key_legacy_upper_bound(tmp_path):
    path = tmp_path / "discovered.json"
    upper = _row(marker=3, distance=30, status="upper_bound", exact=False)
    path.write_text(json.dumps([upper]))

    exact = _row(marker=3, distance=8)
    save_code(exact, path)

    stored = load_codes(path)
    assert stored == [{
        **exact,
        "exact_fom": 12 * 8 * 8 / 144,
    }]


def test_save_code_rejects_upper_and_certified_lower(tmp_path):
    path = tmp_path / "discovered.json"
    upper = _row(marker=3, distance=30, status="upper_bound", exact=False)
    with pytest.raises(ValueError, match="explicit exact-distance"):
        save_code(upper, path)
    assert not path.exists()

    # Stale exact-looking fields must not upgrade a certified lower bound.
    lower = _row(marker=4, distance=14)
    lower.update({
        "distance_lower_bound": 14,
        "distance_lower_bound_status": "certified",
        "d_represents_certified_lower_bound": True,
    })
    with pytest.raises(ValueError, match="explicit exact-distance"):
        save_code(lower, path)
    assert not path.exists()


def test_pareto_update_cleans_upper_unresolved_and_lower_rows(tmp_path):
    path = tmp_path / "pareto.json"
    old_upper = _row(marker=1, distance=100, status="upper_bound", exact=False)
    old_unresolved = _row(
        marker=2,
        distance=80,
        status="unknown_no_incumbent",
        exact=False,
    )
    # Exercise contradictory legacy data: exact markers plus lower-only proof.
    old_lower = _row(marker=3, distance=40)
    old_lower.update({
        "distance_lower_bound": 40,
        "distance_lower_bound_status": "certified",
        "d_represents_certified_lower_bound": True,
    })
    path.write_text(json.dumps([old_upper, old_unresolved, old_lower]))

    exact = _row(marker=4, distance=6)
    front = update_pareto_front([exact], path)

    assert len(front) == 1
    assert front[0]["A_terms"] == exact["A_terms"]
    assert front[0]["distance_status"] == "exact"
    assert json.loads(path.read_text()) == front


def test_pareto_exact_cannot_be_downgraded_by_later_upper(tmp_path):
    path = tmp_path / "pareto.json"
    exact = _row(marker=3, distance=8)
    assert len(update_pareto_front([exact], path)) == 1

    upper = _row(marker=3, distance=100, status="upper_bound", exact=False)
    front = update_pareto_front([upper], path)

    assert len(front) == 1
    assert front[0]["d"] == 8
    assert front[0]["distance_status"] == "exact"


def test_exact_markers_must_be_consistent_and_physically_bounded(tmp_path):
    path = tmp_path / "pareto.json"
    contradictory = _row(marker=3, distance=8)
    contradictory["exact_distance"] = 9
    impossible = _row(marker=4, distance=145)

    assert update_pareto_front([contradictory, impossible], path) == []
    assert json.loads(path.read_text()) == []


def test_updates_fail_closed_on_corrupt_existing_store(tmp_path):
    path = tmp_path / "results.json"
    path.write_text("{not valid json")
    exact = _row(marker=3, distance=8)

    with pytest.raises(ValueError, match="unavailable or invalid"):
        save_code(exact, path)
    with pytest.raises(ValueError, match="unavailable or invalid"):
        update_pareto_front([exact], path)

    assert path.read_text() == "{not valid json"
