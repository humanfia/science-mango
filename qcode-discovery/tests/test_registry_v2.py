from collections import Counter

from evaluation.registry import load_registry


def test_registry_v2_pins_all_verified_catalog_sources():
    registry = load_registry()
    assert registry["registry_version"] == "2026-07-23.qcode-publication-v2"
    assert registry["summary"] == {
        "raw_entries": 1863,
        "deduplicated_entries": 1149,
        "css": 781,
        "noncss": 368,
    }
    kinds = Counter(
        provenance["kind"]
        for entry in registry["entries"]
        for provenance in entry["provenance"]
    )
    assert kinds["literature"] == 6
    assert kinds["qcode-discovery-css-milp-verified"] == 1188
    assert kinds["qcode-discovery-css-ensemble-verified"] == 145
    assert kinds["qcode-discovery-pbb-publication"] == 368
    assert len(registry["sources"]) == 5
