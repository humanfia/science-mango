from __future__ import annotations

import hashlib
import json

import numpy as np
import pytest

from evaluation.construction import (
    build_css_code_from_claim,
    candidate_symmetry_generators,
    construction_identity,
    construction_source_fingerprint,
    normalize_construction_claim,
)
from evaluation.coset_action_catalog import (
    action_catalog_sha256,
    list_action_descriptors,
)
from evaluation.coset_two_block import (
    ACTION_CATALOG_SHA256,
    CONSTRUCTION_KIND,
    build_coset_two_block,
    matrix_sha256,
    normalize_coset_two_block_construction,
)
from evaluation.final_gate import _connected
from evaluation.matrix_certificate import _rebuild_claim
from evaluation.matrix_io import pack_matrix


PAPER_ACTION_ID = "coset2bga-l224-m53-s1-degree112-v1"
CONTROL_ACTION_ID = "dihedral-d36-regular-degree72-v1"
PAPER_HX_SHA256 = "a449fa1905d45becbc32a77544bc73b60acfdd4e598aba6dde10ff19098b7eea"
PAPER_HZ_SHA256 = "39267ddb41b624e7791fecf4008b8c3367222a4e2dd28d632ad5474f02e6efc5"
PAPER_IDENTITY_SHA256 = "8fc4b6bdb1b0c9430019ef87800afba3eceef1ab529bcb019e63cc24bebae6b5"


def _descriptor(action_id: str) -> dict:
    return next(
        item for item in list_action_descriptors()
        if item["action_id"] == action_id
    )


def _paper_code():
    descriptor = _descriptor(PAPER_ACTION_ID)
    return build_coset_two_block(
        PAPER_ACTION_ID,
        descriptor["published_left_support"],
        descriptor["published_right_support"],
    )


def test_catalog_closures_and_search_descriptors_are_validated_and_independent():
    first = list_action_descriptors()
    second = list_action_descriptors()
    assert len(first) == 2
    assert first == second
    assert first is not second

    paper = _descriptor(PAPER_ACTION_ID)
    assert paper["block_size"] == 112
    assert paper["subgroup_normal"] is False
    assert paper["action_family_bin"] == 0
    assert paper["left_closure_size"] == len(paper["left_element_ids"]) == 224
    assert paper["right_closure_size"] == len(paper["right_element_ids"]) == 28
    assert paper["left_abelian"] is False
    assert paper["right_abelian"] is True
    assert paper["validation"] == {
        "closure_sizes_verified": True,
        "faithful_permutation_closures_verified": True,
        "left_right_commutation_verified": True,
    }
    assert paper["published_support_aliases"] == {
        "left_support": ["a:1", "a:81", "a:186"],
        "right_support": ["b:1", "b:16", "b:47"],
    }
    assert paper["provenance"] == {
        "paper": "arXiv:2606.17268",
        "upstream_repository": "https://github.com/aaydinnnn/Coset2BGACodes",
        "upstream_commit": "a828dc43c55982e0212febea634775d36bf6e968",
        "upstream_path": (
            "code_dict/"
            "code_n224_k12_d16_l224_m53_s1_a1_81_186_b1_16_47.json"
        ),
        "upstream_file_sha256": (
            "1797447d6bea96ffda61b4ce6a91b560b6d52fe2784983c01d"
            "f6166c5ed69734"
        ),
    }

    control = _descriptor(CONTROL_ACTION_ID)
    assert control["block_size"] == 72
    assert control["subgroup_normal"] is True
    assert control["action_family_bin"] == 1
    assert control["left_closure_size"] == 72
    assert control["right_closure_size"] == 72
    assert control["left_abelian"] is False
    assert control["right_abelian"] is False

    first[0]["left_element_ids"].clear()
    assert len(list_action_descriptors()[0]["left_element_ids"]) == 224


def test_catalog_sha_is_exact_and_source_bound():
    assert ACTION_CATALOG_SHA256 == action_catalog_sha256()
    assert len(ACTION_CATALOG_SHA256) == 64
    int(ACTION_CATALOG_SHA256, 16)


def test_published_fixture_rebuilds_exact_matrices_without_claiming_distance():
    descriptor = _descriptor(PAPER_ACTION_ID)
    code = _paper_code()
    hx = np.asarray(code.matrix_x, dtype=np.uint8) & 1
    hz = np.asarray(code.matrix_z, dtype=np.uint8) & 1

    assert (code.num_qudits, code.dimension) == (224, 12)
    assert hx.shape == hz.shape == (112, 224)
    assert not np.any((hx.astype(np.uint16) @ hz.T.astype(np.uint16)) & 1)
    assert matrix_sha256(hx) == code.matrix_sha256_x == PAPER_HX_SHA256
    assert matrix_sha256(hz) == code.matrix_sha256_z == PAPER_HZ_SHA256
    assert _connected(np.vstack((hx, hz))) == (True, 1)
    assert set(hx.sum(axis=1).tolist()) == {6}
    assert set(hz.sum(axis=1).tolist()) == {6}
    assert set(hx.sum(axis=0).tolist()) == {3}
    assert set(hz.sum(axis=0).tolist()) == {3}
    assert set((hx.sum(axis=0) + hz.sum(axis=0)).tolist()) == {6}

    published = descriptor["published_support"]
    assert published["reported_distance"] == 16
    assert published["distance_evidence_status"] == (
        "published-metadata-not-locally-proven"
    )
    assert "reported_distance" not in code.construction
    assert not hasattr(code, "reported_distance")


def test_published_aliases_normalize_to_stable_order_independent_identity():
    descriptor = _descriptor(PAPER_ACTION_ID)
    aliases = descriptor["published_support_aliases"]
    alias_claim = {
        "kind": CONSTRUCTION_KIND,
        "action_id": PAPER_ACTION_ID,
        "action_catalog_sha256": ACTION_CATALOG_SHA256,
        "left_support": list(reversed(aliases["left_support"])),
        "right_support": list(reversed(aliases["right_support"])),
    }
    stable_claim = {
        **alias_claim,
        "left_support": descriptor["published_left_support"],
        "right_support": descriptor["published_right_support"],
    }
    alias_identity = construction_identity(alias_claim)
    stable_identity = construction_identity({"construction": stable_claim})
    assert alias_identity == stable_identity
    digest = hashlib.sha256(json.dumps(
        alias_identity,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode()).hexdigest()
    assert digest == PAPER_IDENTITY_SHA256


@pytest.mark.parametrize(
    "mutation, match",
    [
        ({"action_catalog_sha256": "0" * 64}, "does not match"),
        ({"left_support": ["does-not-exist"]}, "unknown left"),
        ({"right_support": ["does-not-exist"]}, "unknown right"),
        ({"left_support": []}, "must not be empty"),
        (
            {
                "left_support": ["L000", "L001", "L002", "L003"],
                "right_support": ["R000", "R001", "R002"],
            },
            "exceeds",
        ),
    ],
)
def test_invalid_coset_claims_fail_closed(mutation, match):
    descriptor = _descriptor(PAPER_ACTION_ID)
    claim = {
        "kind": CONSTRUCTION_KIND,
        "action_id": PAPER_ACTION_ID,
        "action_catalog_sha256": ACTION_CATALOG_SHA256,
        "left_support": descriptor["published_left_support"],
        "right_support": descriptor["published_right_support"],
    }
    claim.update(mutation)
    with pytest.raises(ValueError, match=match):
        normalize_coset_two_block_construction(claim)


def test_alias_and_stable_id_for_same_element_are_rejected_as_duplicate():
    descriptor = _descriptor(PAPER_ACTION_ID)
    claim = {
        "kind": CONSTRUCTION_KIND,
        "action_id": PAPER_ACTION_ID,
        "action_catalog_sha256": ACTION_CATALOG_SHA256,
        "left_support": ["a:1", descriptor["left_identity_id"]],
        "right_support": [descriptor["right_identity_id"]],
    }
    with pytest.raises(ValueError, match="duplicate"):
        normalize_coset_two_block_construction(claim)


def test_dihedral_regular_nonabelian_control_builds_css_code():
    descriptor = _descriptor(CONTROL_ACTION_ID)
    code = build_coset_two_block(
        CONTROL_ACTION_ID,
        [descriptor["left_identity_id"], descriptor["left_aliases"]["s"]],
        [descriptor["right_identity_id"], descriptor["right_aliases"]["r"]],
    )
    hx = np.asarray(code.matrix_x, dtype=np.uint8) & 1
    hz = np.asarray(code.matrix_z, dtype=np.uint8) & 1
    assert (code.num_qudits, code.dimension) == (144, 2)
    assert hx.shape == hz.shape == (72, 144)
    assert not np.any((hx.astype(np.uint16) @ hz.T.astype(np.uint16)) & 1)
    assert _connected(np.vstack((hx, hz))) == (True, 1)


def test_generic_dispatch_rebuilds_coset_and_legacy_bb_claims():
    paper = _paper_code()
    replayed = build_css_code_from_claim({"construction": paper.construction})
    assert np.array_equal(replayed.matrix_x, paper.matrix_x)
    assert np.array_equal(replayed.matrix_z, paper.matrix_z)

    legacy = {
        "ell": 6,
        "m": 6,
        "A_terms": [(3, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 3), (1, 0), (2, 0)],
    }
    normalized = normalize_construction_claim(legacy)
    legacy_code = build_css_code_from_claim({"construction": normalized})
    assert (legacy_code.num_qudits, legacy_code.dimension) == (72, 12)
    assert construction_identity(legacy)["kind"] == "bb-v1"


def test_packed_matrices_are_witnesses_and_must_match_authoritative_rebuild():
    code = _paper_code()
    hx = np.asarray(code.matrix_x, dtype=np.uint8) & 1
    hz = np.asarray(code.matrix_z, dtype=np.uint8) & 1
    claim = {
        "construction": code.construction,
        "H_X": pack_matrix(hx),
        "H_Z": pack_matrix(hz),
    }
    _, replayed_hx, replayed_hz, normalized, identity, source = _rebuild_claim(
        claim
    )
    assert np.array_equal(replayed_hx, hx)
    assert np.array_equal(replayed_hz, hz)
    assert normalized == {"construction": code.construction}
    assert identity == construction_identity(claim)
    assert source == construction_source_fingerprint()

    with pytest.raises(ValueError, match="do not match reconstructed"):
        _rebuild_claim({
            "construction": code.construction,
            "H_X": pack_matrix(hz),
            "H_Z": pack_matrix(hx),
        })


def test_nested_coset_claim_rejects_competing_top_level_definition():
    code = _paper_code()
    with pytest.raises(ValueError, match="ambiguous"):
        normalize_construction_claim({
            "construction": code.construction,
            "ell": 6,
        })


def test_source_fingerprint_is_stable_hex_digest():
    first = construction_source_fingerprint()
    assert first == construction_source_fingerprint()
    assert len(first) == 64
    int(first, 16)


def test_symmetry_generators_are_unverified_fresh_proposals():
    code = _paper_code()
    proposals = candidate_symmetry_generators({"construction": code.construction})
    assert len(proposals) == 4
    assert len({item["id"] for item in proposals}) == 4
    for proposal in proposals:
        assert proposal["verified"] is False
        assert proposal["verification_required"] is True
        assert proposal["permutation_convention"] == "source_to_destination"
        assert len(proposal["block_permutation"]) == 112
        assert len(proposal["qubit_permutation"]) == 224
        assert len(proposal["x_check_permutation"]) == 112
        assert len(proposal["z_check_permutation"]) == 112

    proposals[0]["qubit_permutation"].clear()
    assert len(
        candidate_symmetry_generators({"construction": code.construction})[0][
            "qubit_permutation"
        ]
    ) == 224
