import json

import pytest

from scripts.verify_deep_milp import (
    load_bliss_hash_filter,
    select_codes_for_verification,
)


def code(bliss_hash, *, trust="TRUSTED", fom=8.0, ell=15, shift=0):
    return {
        "bliss_hash": bliss_hash,
        "trust_level": trust,
        "fom": fom,
        "ell": ell,
        "m": 6,
        "n": 2 * ell * 6,
        "k": 6,
        "d": 10,
        "A_terms": [[0, 0], [1 + shift, 0]],
        "B_terms": [[0, 0], [0, 1 + shift]],
        "C_terms": [[0, 0], [2 + shift, 0]],
        "D_terms": [[0, 0], [0, 2 + shift]],
    }


def test_automatic_selection_remains_trusted_and_above_threshold():
    rows = [
        code("trusted", fom=6.0),
        code("partial", trust="PARTIAL", fom=20.0, shift=1),
        code("low", fom=4.0, shift=2),
    ]
    selected = select_codes_for_verification(rows, min_fom=5.0)
    assert [row["bliss_hash"] for row in selected] == ["trusted"]


def test_explicit_worklist_overrides_trust_and_fom_and_preserves_order():
    rows = [
        code("trusted", fom=8.0),
        code("partial", trust="PARTIAL", fom=1.0, shift=1),
    ]
    selected = select_codes_for_verification(
        rows, min_fom=99.0, hash_filter=["partial", "trusted"]
    )
    assert [row["bliss_hash"] for row in selected] == ["partial", "trusted"]
    assert selected[0]["trust_level"] == "PARTIAL"


def test_worklist_parser_is_strict_and_ordered(tmp_path):
    path = tmp_path / "worklist.json"
    path.write_text(json.dumps({
        "codes": [{"bliss_hash": "second"}, {"bliss_hash": "first"}],
    }))
    assert load_bliss_hash_filter(str(path)) == ["second", "first"]

    path.write_text(json.dumps(["same", "same"]))
    with pytest.raises(ValueError, match="duplicate"):
        load_bliss_hash_filter(str(path))

    path.write_text(json.dumps({"codes": [{}]}))
    with pytest.raises(ValueError, match="non-empty"):
        load_bliss_hash_filter(str(path))

    path.write_text("")
    with pytest.raises(ValueError, match="empty"):
        load_bliss_hash_filter(str(path))


def test_explicit_missing_ambiguous_and_lattice_exclusion_fail_closed():
    one = code("one")
    with pytest.raises(ValueError, match="not found"):
        select_codes_for_verification(
            [one], min_fom=0, hash_filter=["missing"]
        )
    with pytest.raises(ValueError, match="multiple"):
        select_codes_for_verification(
            [one, dict(one)], min_fom=0, hash_filter=["one"]
        )
    with pytest.raises(ValueError, match="excluded"):
        select_codes_for_verification(
            [one], min_fom=0, lat_filter={(12, 6)}, hash_filter=["one"]
        )


def test_tier3_partial_candidate_is_reachable_from_real_worklist():
    with open("results/campaign7_publication_merged.jsonl", encoding="utf-8") as stream:
        rows = [json.loads(line) for line in stream if line.strip()]
    hashes = load_bliss_hash_filter("results/deep_milp_tier3_n180_hashes.json")
    selected = select_codes_for_verification(
        rows, min_fom=5.0, hash_filter=hashes
    )
    by_hash = {row["bliss_hash"]: row for row in selected}
    assert "70c03e15fe2839e4" in by_hash
    assert by_hash["70c03e15fe2839e4"]["trust_level"] == "PARTIAL"
    assert len(selected) == len(hashes)
