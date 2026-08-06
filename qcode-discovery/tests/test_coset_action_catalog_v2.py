from __future__ import annotations

from copy import deepcopy
from hashlib import sha256
import json

import numpy as np
import pytest

from evaluation import coset_action_catalog as catalog_module
from evaluation.construction import (
    build_css_code_from_claim,
    construction_identity,
)
from evaluation.coset_action_catalog import (
    CATALOG_V2_PATH,
    LEGACY_CATALOG_ID,
    V2_CATALOG_ID,
    V2_CATALOG_SHA256,
    action_catalog_identity,
    get_catalog,
    list_action_descriptors,
    load_action_catalog,
)
from evaluation.coset_two_block import (
    ACTION_CATALOG_V2_SHA256,
    CONSTRUCTION_KIND_V2,
    CONSTRUCTION_REPRESENTATION,
    CONSTRUCTION_REPRESENTATION_V2,
    build_coset_candidate,
    build_coset_two_block,
    build_coset_two_block_v2,
    normalize_coset_two_block_construction,
)


LEGACY_PAPER_ACTION = "coset2bga-l224-m53-s1-degree112-v1"
V2_PAPER_ACTION = "coset2bga-l224-m53-s1-degree112-v2"
V2_CONTROL_ACTION = "dihedral-d36-regular-degree72-v2"


def _descriptor(action_id: str, *, catalog_id: str) -> dict:
    return next(
        item
        for item in list_action_descriptors(catalog_id=catalog_id)
        if item["action_id"] == action_id
    )


def test_v2_is_an_explicit_46_action_geometry_superset():
    legacy = list_action_descriptors(catalog_id=LEGACY_CATALOG_ID)
    v2 = list_action_descriptors(catalog_id=V2_CATALOG_ID)
    assert len(legacy) == 2
    assert len(v2) == 46
    assert sum(not item["subgroup_normal"] for item in v2) == 45
    assert [
        item["action_id"] for item in v2 if item["subgroup_normal"]
    ] == [V2_CONTROL_ACTION]

    official_keys = {
        (
            tuple(item["provenance"]["gap_group_id"]),
            item["provenance"]["gap_nonnormal_subgroup_index"],
            item["block_size"],
        )
        for item in v2
        if not item["subgroup_normal"]
    }
    assert len(official_keys) == 45
    assert ((224, 53), 1, 112) in official_keys
    assert sum(item["published_support"] is not None for item in v2) == 24
    assert sum(item["published_support"] is None for item in v2) == 22
    assert sum(
        item["published_support"] is not None
        and not item["published_support"]["reported_distance_exact"]
        for item in v2
    ) == 1
    upper_bound_anchor = next(
        item
        for item in v2
        if item["action_id"] == "coset2bga-l248-m9-s1-degree124-v2"
    )
    assert upper_bound_anchor["published_support"]["reported_distance_exact"] is False
    assert upper_bound_anchor["published_support"]["distance_evidence_status"] == (
        "published-upper-bound-metadata-not-locally-proven"
    )
    for lane_index, descriptor in enumerate(v2):
        assert descriptor["action_catalog_id"] == V2_CATALOG_ID
        assert descriptor["action_catalog_schema_version"] == 2
        assert descriptor["action_catalog_sha256"] == ACTION_CATALOG_V2_SHA256
        assert descriptor["action_lane_index"] == lane_index
        assert descriptor["action_family_bin"] == int(
            descriptor["subgroup_normal"]
        )
        assert descriptor["source_bindings"]
        assert descriptor["validation"]["source_bindings_verified"] is True


def test_v2_catalog_identity_is_independent_from_legacy_identity():
    legacy = action_catalog_identity(LEGACY_CATALOG_ID)
    v2 = action_catalog_identity(V2_CATALOG_ID)
    assert legacy == {
        "catalog_id": LEGACY_CATALOG_ID,
        "schema_version": 1,
        "kind": "qcode-coset-two-block-action-catalog",
        "sha256": "7599be34679075de6fba8675f8b7c1d8f21b6eae56061418012ef796eafdb323",
    }
    assert v2["catalog_id"] == V2_CATALOG_ID
    assert v2["schema_version"] == 2
    assert v2["sha256"] == ACTION_CATALOG_V2_SHA256
    assert v2["sha256"] == V2_CATALOG_SHA256
    assert v2["sha256"] == (
        "2e06bd808426f3f2c6c7eb05db331f8649e43b7784050f44bb1572aaeea6772a"
    )
    assert v2["sha256"] != legacy["sha256"]
    assert get_catalog(catalog_sha256=v2["sha256"]).catalog_id == V2_CATALOG_ID
    with pytest.raises(ValueError, match="different catalogs"):
        get_catalog(
            catalog_id=LEGACY_CATALOG_ID,
            catalog_sha256=v2["sha256"],
        )


def test_v2_every_official_anchor_replays_published_n_and_k():
    for descriptor in list_action_descriptors(catalog_id=V2_CATALOG_ID):
        published = descriptor["published_support"]
        if published is None:
            continue
        code = build_coset_two_block_v2(
            descriptor["action_id"],
            descriptor["published_left_support"],
            descriptor["published_right_support"],
        )
        assert (code.num_qudits, code.dimension) == (
            published["reported_n"],
            published["reported_k"],
        )
        assert code.construction["kind"] == CONSTRUCTION_KIND_V2
        assert code.construction["representation_id"] == (
            CONSTRUCTION_REPRESENTATION_V2
        )
        assert code.construction["action_catalog_id"] == V2_CATALOG_ID
        assert code.construction["action_catalog_sha256"] == (
            ACTION_CATALOG_V2_SHA256
        )
        assert code.coset_two_block_validation["css_commutation_verified"] is True
        assert code.coset_two_block_validation["support_weight_total"] == 6


def test_v2_and_v1_published_224_action_rebuild_identical_matrices():
    legacy = _descriptor(LEGACY_PAPER_ACTION, catalog_id=LEGACY_CATALOG_ID)
    v2 = _descriptor(V2_PAPER_ACTION, catalog_id=V2_CATALOG_ID)
    legacy_code = build_coset_two_block(
        LEGACY_PAPER_ACTION,
        legacy["published_left_support"],
        legacy["published_right_support"],
    )
    v2_code = build_coset_two_block_v2(
        V2_PAPER_ACTION,
        v2["published_left_support"],
        v2["published_right_support"],
    )
    assert np.array_equal(legacy_code.matrix_x, v2_code.matrix_x)
    assert np.array_equal(legacy_code.matrix_z, v2_code.matrix_z)

    replayed = build_css_code_from_claim({"construction": v2_code.construction})
    assert np.array_equal(replayed.matrix_x, v2_code.matrix_x)
    assert construction_identity({"construction": v2_code.construction}) == (
        v2_code.construction
    )


def test_explicit_legacy_representation_still_routes_to_v1_catalog():
    descriptor = _descriptor(LEGACY_PAPER_ACTION, catalog_id=LEGACY_CATALOG_ID)
    compact = {
        "representation_id": CONSTRUCTION_REPRESENTATION,
        "action_id": LEGACY_PAPER_ACTION,
        "left_support": descriptor["published_left_support"],
        "right_support": descriptor["published_right_support"],
    }
    explicit = build_coset_candidate(compact)
    implicit = build_coset_candidate({
        key: value for key, value in compact.items() if key != "representation_id"
    })
    assert explicit.construction["kind"] == "coset-two-block-v1"
    assert explicit.construction["action_catalog_sha256"] == (
        action_catalog_identity(LEGACY_CATALOG_ID)["sha256"]
    )
    assert np.array_equal(explicit.matrix_x, implicit.matrix_x)
    assert np.array_equal(explicit.matrix_z, implicit.matrix_z)


def test_v2_construction_rejects_catalog_confusion():
    descriptor = _descriptor(V2_PAPER_ACTION, catalog_id=V2_CATALOG_ID)
    claim = {
        "kind": CONSTRUCTION_KIND_V2,
        "representation_id": CONSTRUCTION_REPRESENTATION_V2,
        "action_id": V2_PAPER_ACTION,
        "action_catalog_id": V2_CATALOG_ID,
        "action_catalog_sha256": ACTION_CATALOG_V2_SHA256,
        "left_support": descriptor["published_left_support"],
        "right_support": descriptor["published_right_support"],
    }
    normalized = normalize_coset_two_block_construction(claim)
    assert normalize_coset_two_block_construction(normalized) == normalized
    wrong_id = {**claim, "action_catalog_id": LEGACY_CATALOG_ID}
    with pytest.raises(ValueError, match="action_catalog_id changed"):
        normalize_coset_two_block_construction(wrong_id)
    wrong_sha = {**claim, "action_catalog_sha256": "0" * 64}
    with pytest.raises(ValueError, match="unknown frozen action catalog"):
        normalize_coset_two_block_construction(wrong_sha)
    wrong_representation = {**claim, "representation_id": "v1"}
    with pytest.raises(ValueError, match="representation_id changed"):
        normalize_coset_two_block_construction(wrong_representation)


def test_v2_loader_fails_closed_on_source_binding_and_generator_path(
    tmp_path,
    monkeypatch,
):
    def write_reviewed(path, document):
        payload = json.dumps(document).encode()
        path.write_bytes(payload)
        monkeypatch.setattr(
            catalog_module,
            "V2_CATALOG_SHA256",
            sha256(payload).hexdigest(),
        )

    raw = json.loads(CATALOG_V2_PATH.read_text())
    corrupt_binding = deepcopy(raw)
    corrupt_binding["actions"][0]["source_bindings"][0]["sha256"] = "0" * 64
    binding_path = tmp_path / "bad-binding.json"
    write_reviewed(binding_path, corrupt_binding)
    with pytest.raises(ValueError, match="does not exactly join"):
        load_action_catalog(binding_path)

    corrupt_generator = deepcopy(raw)
    action = corrupt_generator["actions"][0]
    other_path = corrupt_generator["actions"][1]["source_bindings"][0]["path"]
    action["left"]["generators"][0]["upstream_block_alias"] = (
        f"{other_path}#A2"
    )
    generator_path = tmp_path / "bad-generator.json"
    write_reviewed(generator_path, corrupt_generator)
    with pytest.raises(ValueError, match="outside source_bindings"):
        load_action_catalog(generator_path)

    wrong_identity = deepcopy(raw)
    wrong_identity["catalog_id"] = "unreviewed-catalog"
    identity_path = tmp_path / "bad-id.json"
    write_reviewed(identity_path, wrong_identity)
    with pytest.raises(RuntimeError, match="unexpected catalog v2 identity"):
        load_action_catalog(identity_path)
