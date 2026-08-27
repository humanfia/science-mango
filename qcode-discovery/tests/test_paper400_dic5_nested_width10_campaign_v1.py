from __future__ import annotations

import ast
import copy
import hashlib
from itertools import product
from pathlib import Path

import numpy as np
import pytest

from evaluation import paper400_dic5_optimized_cnf_final_v13 as optimized
from investigations import paper400_dic5_cube16 as cube16
from investigations import paper400_dic5_nested_width10_campaign_v1 as campaign
from investigations import paper400_dic5_widened_parent_campaign_v1 as width6


PARENT_INDEX = 0


def _synthetic_instance() -> optimized.OptimizedInstance:
    hx = np.zeros((200, 400), dtype=np.uint8)
    hz = np.zeros_like(hx)
    lx = np.zeros((16, 400), dtype=np.uint8)
    lx[0, 0] = 1
    lz = np.zeros_like(lx)
    cnf = {
        "num_variables": 400,
        "num_clauses": 1,
        "operator_variables": list(range(1, 401)),
        "logical_variables": [1],
        "native_atmost": None,
        "clauses": [[1]],
    }
    cnf["cnf_sha256"] = optimized.canonical_sha256({
        "num_variables": cnf["num_variables"],
        "clauses": cnf["clauses"],
        "native_atmost": None,
    })
    report = optimized.seal({
        "schema_version": 1,
        "solver_invoked": False,
        "baseline": {"preflight_sha256": "a" * 64},
    }, "report_sha256")
    return optimized.OptimizedInstance(
        hx=hx,
        hz=hz,
        lx=lx,
        lz=lz,
        basis_checks=hx[:192].copy(),
        active_logical=lx[:1].copy(),
        cnf=cnf,
        dimacs=optimized.render_dimacs(cnf),
        report=report,
    )


@pytest.fixture(scope="module")
def synthetic_material() -> tuple[
    optimized.OptimizedInstance, dict, dict, dict, dict,
]:
    instance = _synthetic_instance()
    parent = cube16.build_coverage_manifest(
        instance,
        strict_base=False,
        split_variables=(1, 2, 3, 4),
    )
    old_campaign = width6.build_campaign_manifest(
        parent,
        instance,
        parent_cube_index=PARENT_INDEX,
        strict_base=False,
    )
    preview = campaign.preview_extension_variables(
        old_campaign,
        parent,
        instance,
        parent_cube_index=PARENT_INDEX,
        strict_base=False,
    )
    manifest = campaign.build_campaign_manifest(
        old_campaign,
        parent,
        instance,
        confirmed_extension_variables=preview[
            "proposed_extension_variables_dimacs"
        ],
        parent_cube_index=PARENT_INDEX,
        strict_base=False,
    )
    return instance, parent, old_campaign, preview, manifest


@pytest.fixture(scope="module")
def verified_synthetic_material(
    synthetic_material: tuple[
        optimized.OptimizedInstance, dict, dict, dict, dict,
    ],
) -> tuple[
    optimized.OptimizedInstance, dict, dict, dict, dict, dict,
]:
    instance, parent, old_campaign, preview, manifest = synthetic_material
    verification = campaign.verify_campaign_manifest(
        manifest,
        old_campaign,
        parent,
        instance,
        parent_cube_index=PARENT_INDEX,
        strict_base=False,
    )
    assert verification["valid"] is True
    return instance, parent, old_campaign, preview, manifest, verification


def _reseal(manifest: dict) -> dict:
    changed = copy.deepcopy(manifest)
    changed.pop("manifest_sha256", None)
    return campaign.seal(changed)


def test_module_is_solver_and_execution_free() -> None:
    source = Path(campaign.__file__).read_text(encoding="utf-8")
    tree = ast.parse(source)
    imports: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imports.update(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            imports.add(node.module)
    assert "subprocess" not in imports
    assert "multiprocessing" not in imports
    assert "pysat" not in imports
    assert "Popen(" not in source
    assert '"solver_invoked": False' in source


def test_widths_counts_and_production_selection_are_frozen() -> None:
    assert campaign.WIDTH6_SPLIT_WIDTH == 6
    assert campaign.EXTENSION_WIDTH == 4
    assert campaign.SPLIT_WIDTH == 10
    assert campaign.WIDTH6_LEAF_COUNT == 64
    assert campaign.LOCAL_CHILD_COUNT == 16
    assert campaign.LEAF_COUNT == 1024
    assert campaign.LOCAL_PAIR_COUNT == 120
    assert campaign.WITHIN_PREFIX_PAIR_COUNT == 7680
    assert campaign.CROSS_PREFIX_PAIR_COUNT == 516096
    assert campaign.GLOBAL_PAIR_COUNT == 523776
    assert campaign.EXPECTED_PARENT000_WIDTH6_VARIABLES == (
        236, 254, 271, 274, 280, 321,
    )
    assert campaign.EXPECTED_PARENT000_EXTENSION_VARIABLES == (
        324, 342, 345, 352,
    )
    assert campaign.EXPECTED_PARENT000_WIDTH10_VARIABLES == (
        236, 254, 271, 274, 280, 321, 324, 342, 345, 352,
    )


def test_independent_preview_replays_exact_width6_prefix(
    synthetic_material: tuple[
        optimized.OptimizedInstance, dict, dict, dict, dict,
    ],
) -> None:
    _, _, old_campaign, preview, _ = synthetic_material
    assert preview["width6_variables_dimacs"] == [5, 6, 7, 8, 9, 10]
    assert preview["proposed_extension_variables_dimacs"] == [11, 12, 13, 14]
    assert preview["proposed_width10_variables_dimacs"] == list(range(5, 15))
    assert preview["width6_prefix_exact"] is True
    assert preview["candidate_ranking_sha256"] == old_campaign[
        "refinement"
    ]["refinement"]["selection_certificate"]["candidate_ranking_sha256"]
    assert preview["production_ranking_required"] is False
    assert preview["production_ranking_matches"] is False
    assert preview["solver_invoked"] is False


def test_nested_1024_cover_and_nonzero_prefix_are_exact(
    synthetic_material: tuple[
        optimized.OptimizedInstance, dict, dict, dict, dict,
    ],
) -> None:
    _, _, _, _, manifest = synthetic_material
    assert manifest["authority"] == campaign.AUTHORITY_TEST_ONLY
    assert manifest["test_only"] is True
    assert manifest["production_eligible"] is False
    assert len(manifest["leaves"]) == 1024
    assert [leaf["global_leaf_index"] for leaf in manifest["leaves"]] == list(
        range(1024)
    )
    assert [leaf["assignment_bits"] for leaf in manifest["leaves"]] == [
        list(bits) for bits in product((0, 1), repeat=10)
    ]
    assert len(manifest["local_covers"]) == 64
    assert manifest["local_covers"][0]["global_leaf_indices"] == list(
        range(0, 16)
    )
    assert manifest["local_covers"][1]["global_leaf_indices"] == list(
        range(16, 32)
    )
    assert manifest["local_covers"][63]["global_leaf_indices"] == list(
        range(1008, 1024)
    )
    assert all(
        cover["pair_count_checked"] == 120
        and cover["mutually_exclusive"] is True
        and cover["exhaustive"] is True
        for cover in manifest["local_covers"]
    )
    coverage = manifest["global_coverage"]
    assert coverage["within_width6_prefix_pair_count"] == 7680
    assert coverage["cross_width6_prefix_pair_count"] == 516096
    assert coverage["hierarchically_accounted_pair_count"] == 523776
    assert coverage["global_pair_records_materialized"] is False
    assert coverage["mutually_exclusive"] is True
    assert coverage["exhaustive"] is True


def test_leaf_parent_child_cnf_and_hash_bindings_are_exact(
    synthetic_material: tuple[
        optimized.OptimizedInstance, dict, dict, dict, dict,
    ],
) -> None:
    _, _, old_campaign, _, manifest = synthetic_material
    for global_index in (0, 15, 16, 31, 1023):
        leaf = manifest["leaves"][global_index]
        prefix, suffix = divmod(global_index, 16)
        old_leaf = old_campaign["leaves"][prefix]
        assert leaf["width6_leaf_index"] == prefix
        assert leaf["local_child_index"] == suffix
        assert leaf["width6_leaf_sha256"] == old_leaf["leaf_sha256"]
        assert leaf["width6_child_sha256"] == old_leaf["child_sha256"]
        assert leaf["width6_assignment_bits"] == campaign._bits(prefix, 6)
        assert leaf["extension_assignment_bits"] == campaign._bits(suffix, 4)
        assert leaf["assignment_bits"] == campaign._bits(global_index, 10)
        assert leaf["combined_unit_clauses"] == (
            leaf["width6_combined_unit_clauses"]
            + leaf["extension_unit_clauses"]
        )
        assert campaign.selfhash_valid(leaf, "leaf_sha256")


def test_full_fresh_verifier_accepts_only_the_canonical_campaign(
    verified_synthetic_material: tuple[
        optimized.OptimizedInstance, dict, dict, dict, dict, dict,
    ],
) -> None:
    _, _, _, _, manifest, replay = verified_synthetic_material
    assert replay["valid"] is True
    assert replay["mutually_exclusive"] is True
    assert replay["exhaustive"] is True
    assert replay["parent000_formula_equivalence_certified"] is True
    assert replay["leaf_count"] == 1024
    assert replay["width6_prefix_count"] == 64
    assert replay["expected_manifest_sha256"] == manifest["manifest_sha256"]
    assert set(replay) == campaign.VERIFICATION_FIELDS
    assert campaign.selfhash_valid(replay, "record_sha256")


def test_explicit_confirmation_and_parent_scope_fail_closed(
    synthetic_material: tuple[
        optimized.OptimizedInstance, dict, dict, dict, dict,
    ],
) -> None:
    instance, parent, old_campaign, preview, _ = synthetic_material
    wrong = list(preview["proposed_extension_variables_dimacs"])
    wrong[-1] += 1
    with pytest.raises(campaign.NestedWidth10CampaignError):
        campaign.build_campaign_manifest(
            old_campaign,
            parent,
            instance,
            confirmed_extension_variables=wrong,
            parent_cube_index=PARENT_INDEX,
            strict_base=False,
        )
    with pytest.raises(campaign.NestedWidth10CampaignError):
        campaign.build_campaign_manifest(
            old_campaign,
            parent,
            instance,
            confirmed_extension_variables=preview[
                "proposed_extension_variables_dimacs"
            ],
            parent_cube_index=True,
            strict_base=False,
        )


@pytest.mark.parametrize("tamper", ["leaf", "local_cover", "source"])
def test_resealed_tampering_fails_closed_without_large_rebuild(
    synthetic_material: tuple[
        optimized.OptimizedInstance, dict, dict, dict, dict,
    ],
    monkeypatch: pytest.MonkeyPatch,
    tamper: str,
) -> None:
    instance, parent, old_campaign, _, original = synthetic_material
    changed = copy.deepcopy(original)
    if tamper == "leaf":
        changed["leaves"][16], changed["leaves"][17] = (
            changed["leaves"][17], changed["leaves"][16],
        )
    elif tamper == "local_cover":
        changed["local_covers"][1]["global_leaf_indices"][-1] = 32
    elif tamper == "source":
        changed["source_binding"]["sources"][0]["sha256"] = "f" * 64
    changed = _reseal(changed)
    monkeypatch.setattr(
        campaign,
        "build_campaign_manifest",
        lambda *args, **kwargs: original,
    )
    replay = campaign.verify_campaign_manifest(
        changed,
        old_campaign,
        parent,
        instance,
        parent_cube_index=PARENT_INDEX,
        strict_base=False,
    )
    assert replay["valid"] is False
    assert replay["binding_failures"]


def test_fast_boundary_rebuilds_four_leaves_without_full_replay(
    verified_synthetic_material: tuple[
        optimized.OptimizedInstance, dict, dict, dict, dict, dict,
    ],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    (
        instance,
        parent,
        old_campaign,
        _,
        manifest,
        verification,
    ) = verified_synthetic_material

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("fast boundary called a full campaign rebuild")

    monkeypatch.setattr(campaign, "verify_campaign_manifest", forbidden)
    monkeypatch.setattr(campaign, "build_campaign_manifest", forbidden)
    for global_leaf_index in (16, 17, 18, 19):
        payload = campaign.verified_child_dimacs_from_verification(
            manifest,
            old_campaign,
            parent,
            instance,
            verification_record=verification,
            global_leaf_index=global_leaf_index,
            parent_cube_index=PARENT_INDEX,
            strict_base=False,
        )
        leaf = manifest["leaves"][global_leaf_index]
        assert len(payload) == leaf["child_dimacs_bytes"]
        assert hashlib.sha256(payload).hexdigest() == leaf[
            "child_dimacs_sha256"
        ]


@pytest.mark.parametrize(
    "tamper",
    [
        "valid_false",
        "campaign_sha256",
        "expected_sha256",
        "launch_authorized",
        "missing_field",
    ],
)
def test_fast_boundary_rejects_resealed_forged_success_records(
    verified_synthetic_material: tuple[
        optimized.OptimizedInstance, dict, dict, dict, dict, dict,
    ],
    tamper: str,
) -> None:
    (
        instance,
        parent,
        old_campaign,
        _,
        manifest,
        verification,
    ) = verified_synthetic_material
    changed = copy.deepcopy(verification)
    changed.pop("record_sha256")
    if tamper == "valid_false":
        changed["valid"] = False
    elif tamper == "campaign_sha256":
        changed["campaign_manifest_sha256"] = "f" * 64
    elif tamper == "expected_sha256":
        changed["expected_manifest_sha256"] = "e" * 64
    elif tamper == "launch_authorized":
        changed["launch_authorized_by_this_record"] = True
    elif tamper == "missing_field":
        changed.pop("binding_failures")
    changed = campaign.seal(changed, "record_sha256")
    with pytest.raises(campaign.NestedWidth10CampaignError):
        campaign.verified_child_dimacs_from_verification(
            manifest,
            old_campaign,
            parent,
            instance,
            verification_record=changed,
            global_leaf_index=16,
            parent_cube_index=PARENT_INDEX,
            strict_base=False,
        )


def test_fast_boundary_rejects_resealed_non_target_prefix_tamper(
    verified_synthetic_material: tuple[
        optimized.OptimizedInstance, dict, dict, dict, dict, dict,
    ],
) -> None:
    (
        instance,
        parent,
        old_campaign,
        _,
        original,
        verification,
    ) = verified_synthetic_material
    changed = copy.deepcopy(original)
    changed["leaves"][1008]["global_leaf_id"] += "-tampered"
    changed = _reseal(changed)
    assert campaign.selfhash_valid(changed)
    with pytest.raises(campaign.NestedWidth10CampaignError):
        campaign.verified_child_dimacs_from_verification(
            changed,
            old_campaign,
            parent,
            instance,
            verification_record=verification,
            global_leaf_index=16,
            parent_cube_index=PARENT_INDEX,
            strict_base=False,
        )


def test_forged_matching_record_cannot_replace_non_target_full_replay(
    verified_synthetic_material: tuple[
        optimized.OptimizedInstance, dict, dict, dict, dict, dict,
    ],
) -> None:
    (
        instance,
        parent,
        old_campaign,
        _,
        original,
        verification,
    ) = verified_synthetic_material
    changed = copy.deepcopy(original)
    changed["leaves"][1008]["global_leaf_id"] += "-tampered-and-resealed"
    changed = _reseal(changed)

    forged = copy.deepcopy(verification)
    forged.pop("record_sha256")
    forged["campaign_manifest_sha256"] = changed["manifest_sha256"]
    forged["expected_manifest_sha256"] = changed["manifest_sha256"]
    forged = campaign.seal(forged, "record_sha256")
    assert campaign.selfhash_valid(forged, "record_sha256")
    assert forged["valid"] is True
    assert forged["launch_authorized_by_this_record"] is False
    assert forged["publication_certificate"] is False

    replay = campaign.verify_campaign_manifest(
        changed,
        old_campaign,
        parent,
        instance,
        parent_cube_index=PARENT_INDEX,
        strict_base=False,
    )
    assert replay["valid"] is False
    assert "manifest is not exact current-source canonical replay" in replay[
        "binding_failures"
    ]


def test_fast_boundary_rebuild_rejects_fully_resealed_target_leaf(
    verified_synthetic_material: tuple[
        optimized.OptimizedInstance, dict, dict, dict, dict, dict,
    ],
) -> None:
    (
        instance,
        parent,
        old_campaign,
        _,
        original,
        verification,
    ) = verified_synthetic_material
    changed = copy.deepcopy(original)
    leaf = changed["leaves"][19]
    leaf.pop("leaf_sha256")
    leaf["extension_assignment_bits"][0] ^= 1
    leaf["assignment_bits"][6] ^= 1
    changed["leaves"][19] = campaign.seal(leaf, "leaf_sha256")
    changed = _reseal(changed)

    forged = copy.deepcopy(verification)
    forged.pop("record_sha256")
    forged["campaign_manifest_sha256"] = changed["manifest_sha256"]
    forged["expected_manifest_sha256"] = changed["manifest_sha256"]
    forged = campaign.seal(forged, "record_sha256")
    assert set(forged) == campaign.VERIFICATION_FIELDS
    with pytest.raises(campaign.NestedWidth10CampaignError):
        campaign.verified_child_dimacs_from_verification(
            changed,
            old_campaign,
            parent,
            instance,
            verification_record=forged,
            global_leaf_index=19,
            parent_cube_index=PARENT_INDEX,
            strict_base=False,
        )


def test_on_demand_dimacs_checks_selected_leaf_binding(
    verified_synthetic_material: tuple[
        optimized.OptimizedInstance, dict, dict, dict, dict, dict,
    ],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    (
        instance,
        parent,
        old_campaign,
        _,
        manifest,
        verification,
    ) = verified_synthetic_material
    monkeypatch.setattr(
        campaign,
        "verify_campaign_manifest",
        lambda *args, **kwargs: verification,
    )
    payload = campaign.verified_child_dimacs(
        manifest,
        old_campaign,
        parent,
        instance,
        global_leaf_index=1023,
        parent_cube_index=PARENT_INDEX,
        strict_base=False,
    )
    assert payload.startswith(b"p cnf 400 15\n")
    with pytest.raises(campaign.NestedWidth10CampaignError):
        campaign.verified_child_dimacs(
            manifest,
            old_campaign,
            parent,
            instance,
            global_leaf_index=1024,
            parent_cube_index=PARENT_INDEX,
            strict_base=False,
        )
