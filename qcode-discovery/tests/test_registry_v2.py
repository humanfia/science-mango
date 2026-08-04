from collections import Counter

from evaluation.coset_two_block import build_coset_two_block
from evaluation.registry import check_code_novelty
from evaluation.registry import load_registry


def test_registry_v2_pins_all_verified_catalog_sources():
    registry = load_registry()
    assert registry["registry_version"] == (
        "2026-08-04.qcode-coset-two-block-v1"
    )
    assert registry["summary"] == {
        "raw_entries": 1864,
        "deduplicated_entries": 1150,
        "css": 782,
        "noncss": 368,
    }
    kinds = Counter(
        provenance["kind"]
        for entry in registry["entries"]
        for provenance in entry["provenance"]
    )
    assert kinds["literature"] == 7
    assert kinds["qcode-discovery-css-milp-verified"] == 1188
    assert kinds["qcode-discovery-css-ensemble-verified"] == 145
    assert kinds["qcode-discovery-pbb-publication"] == 368
    assert len(registry["sources"]) == 7

    coset = next(
        entry for entry in registry["entries"]
        if entry["id"] == "literature-aydin-tamo-barg-224-12-16"
    )
    assert (coset["n"], coset["k"]) == (224, 12)
    assert coset["distance_evidence"] == {
        "d": 16,
        "status": "published",
        "locally_exact_proven": False,
        "source_file_sha256": (
            "1797447d6bea96ffda61b4ce6a91b560b6d52fe2784983c01df6166c5ed69734"
        ),
    }
    assert coset["canonical_digest"] == (
        "0305b690d57d72928d0b2770ce4389162d114fe189b58731f335ae1e229870ff"
    )


def test_published_coset_fixture_is_rebuilt_and_rejected_as_known():
    registry = load_registry()
    entry = next(
        row for row in registry["entries"]
        if row["id"] == "literature-aydin-tamo-barg-224-12-16"
    )
    construction = entry["construction"]
    code = build_coset_two_block(
        construction["action_id"],
        construction["left_support"],
        construction["right_support"],
    )
    novelty = check_code_novelty(code, code_type="css")
    assert novelty["status"] == "COMPLETE"
    assert novelty["novel"] is False
    matched = next(
        item for item in novelty["matched_entries"]
        if item["id"] == entry["id"]
    )
    assert matched["replay"]["verified"] is True
    assert matched["replay"]["matrix_x_replayed"] is True
    assert matched["replay"]["matrix_z_replayed"] is True
