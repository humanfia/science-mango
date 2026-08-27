from __future__ import annotations

import ast
import copy
from itertools import product
from pathlib import Path

import numpy as np
import pytest

from evaluation import paper400_dic5_optimized_cnf_final_v13 as optimized
from investigations import paper400_dic5_cube16 as cube16
from investigations import paper400_dic5_widened_parent_campaign_v1 as campaign


PARENT_INDEX = 5


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
def synthetic_material() -> tuple[optimized.OptimizedInstance, dict, dict]:
    instance = _synthetic_instance()
    parent = cube16.build_coverage_manifest(
        instance,
        strict_base=False,
        split_variables=(1, 2, 3, 4),
    )
    manifest = campaign.build_campaign_manifest(
        parent,
        instance,
        parent_cube_index=PARENT_INDEX,
        strict_base=False,
    )
    return instance, parent, manifest


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


def test_width6_cover_and_width4_prefix_extension_are_exact(
    synthetic_material: tuple[optimized.OptimizedInstance, dict, dict],
) -> None:
    instance, parent, manifest = synthetic_material
    replay = campaign.verify_campaign_manifest(
        manifest,
        parent,
        instance,
        parent_cube_index=PARENT_INDEX,
        strict_base=False,
    )
    assert replay["valid"] is True
    assert replay["mutually_exclusive"] is True
    assert replay["exhaustive"] is True
    assert replay["width4_prefix_compatible"] is True
    assert manifest["authority"] == campaign.AUTHORITY_TEST_ONLY
    assert manifest["test_only"] is True
    assert manifest["production_eligible"] is False
    assert manifest["selected_parent"]["parent_cube_index"] == PARENT_INDEX
    assert manifest["refinement"]["refinement"]["variable_count"] == 6
    assert len(manifest["leaves"]) == 64
    assert [leaf["leaf_index"] for leaf in manifest["leaves"]] == list(
        range(64)
    )
    assert [leaf["assignment_bits"] for leaf in manifest["leaves"]] == [
        list(bits) for bits in product((0, 1), repeat=6)
    ]
    assert manifest["coverage"]["expected_pair_count"] == 2016
    compatibility = manifest["prefix_compatibility"]
    assert compatibility["selected_variable_prefix_equal"] is True
    assert compatibility["all_old_leaves_exactly_refined"] is True
    assert len(compatibility["mappings"]) == 16
    assert all(
        mapping["widened_child_indices"]
        == list(range(4 * old_index, 4 * old_index + 4))
        for old_index, mapping in enumerate(compatibility["mappings"])
    )


def test_interleaved_four_lane_schedule_is_exact_and_canonical(
    synthetic_material: tuple[optimized.OptimizedInstance, dict, dict],
) -> None:
    _, _, manifest = synthetic_material
    batches = manifest["batches"]
    assert len(batches) == 16
    assert [batch["leaf_indices"] for batch in batches[:4]] == [
        [0, 4, 8, 12],
        [1, 5, 9, 13],
        [2, 6, 10, 14],
        [3, 7, 11, 15],
    ]
    assert [batch["leaf_indices"] for batch in batches[4:8]] == [
        [16, 20, 24, 28],
        [17, 21, 25, 29],
        [18, 22, 26, 30],
        [19, 23, 27, 31],
    ]
    flat = [
        leaf_index
        for batch in batches
        for leaf_index in batch["leaf_indices"]
    ]
    assert len(flat) == 64
    assert len(set(flat)) == 64
    assert sorted(flat) == list(range(64))
    assert all(len(batch["lanes"]) == 4 for batch in batches)
    assert all(
        len({lane["suffix_index"] for lane in batch["lanes"]}) == 1
        for batch in batches
    )


def test_on_demand_dimacs_and_plan_are_freshly_bound(
    tmp_path: Path,
    synthetic_material: tuple[optimized.OptimizedInstance, dict, dict],
) -> None:
    instance, parent, manifest = synthetic_material
    payload = campaign.verified_child_dimacs(
        manifest,
        parent,
        instance,
        parent_cube_index=PARENT_INDEX,
        leaf_index=63,
        strict_base=False,
    )
    assert payload.startswith(b"p cnf 400 11\n")
    plan = campaign.verified_four_lane_batch_plan(
        manifest,
        parent,
        instance,
        parent_cube_index=PARENT_INDEX,
        strict_base=False,
    )
    assert plan["batch_count"] == 16
    assert plan["lane_count"] == 4
    assert plan["all_64_leaves_scheduled_exactly_once"] is True
    assert list(tmp_path.iterdir()) == []


@pytest.mark.parametrize(
    "tamper",
    [
        "leaf_missing",
        "leaf_duplicate",
        "leaf_reordered",
        "refinement",
        "prefix_mapping",
        "source",
        "batch_missing",
        "batch_duplicate",
        "batch_reordered",
        "batch_unhashable_index",
        "refinement_wrong_json_type",
    ],
)
def test_manifest_tampering_fails_closed_after_top_level_reseal(
    synthetic_material: tuple[optimized.OptimizedInstance, dict, dict],
    tamper: str,
) -> None:
    instance, parent, original = synthetic_material
    changed = copy.deepcopy(original)
    if tamper == "leaf_missing":
        changed["leaves"].pop(17)
    elif tamper == "leaf_duplicate":
        changed["leaves"][17] = copy.deepcopy(changed["leaves"][16])
    elif tamper == "leaf_reordered":
        changed["leaves"][16], changed["leaves"][17] = (
            changed["leaves"][17],
            changed["leaves"][16],
        )
    elif tamper == "refinement":
        changed["refinement"]["refinement"]["variables_dimacs"][0] += 1
    elif tamper == "prefix_mapping":
        compatibility = changed["prefix_compatibility"]
        compatibility.pop("prefix_compatibility_sha256")
        compatibility["mappings"][0]["widened_child_indices"] = [0, 1, 2, 4]
        changed["prefix_compatibility"] = campaign.seal(
            compatibility, "prefix_compatibility_sha256"
        )
    elif tamper == "source":
        source_binding = changed["source_binding"]
        source_binding.pop("source_binding_sha256")
        source_binding["sources"][0]["sha256"] = "f" * 64
        changed["source_binding"] = campaign.seal(
            source_binding, "source_binding_sha256"
        )
    elif tamper == "batch_missing":
        changed["batches"].pop(4)
    elif tamper == "batch_duplicate":
        changed["batches"][4] = copy.deepcopy(changed["batches"][3])
    elif tamper == "batch_reordered":
        changed["batches"][3], changed["batches"][4] = (
            changed["batches"][4],
            changed["batches"][3],
        )
    elif tamper == "batch_unhashable_index":
        changed["batches"][3]["leaf_indices"][0] = []
    elif tamper == "refinement_wrong_json_type":
        changed["refinement"]["refinement"] = []
    changed = _reseal(changed)
    assert campaign.selfhash_valid(changed)
    replay = campaign.verify_campaign_manifest(
        changed,
        parent,
        instance,
        parent_cube_index=PARENT_INDEX,
        strict_base=False,
    )
    assert replay["valid"] is False
    assert replay["binding_failures"]


def test_wrong_parent_expectation_and_invalid_indices_fail_closed(
    synthetic_material: tuple[optimized.OptimizedInstance, dict, dict],
) -> None:
    instance, parent, manifest = synthetic_material
    replay = campaign.verify_campaign_manifest(
        manifest,
        parent,
        instance,
        parent_cube_index=PARENT_INDEX + 1,
        strict_base=False,
    )
    assert replay["valid"] is False
    assert "selected parent does not match caller expectation" in replay[
        "binding_failures"
    ]
    with pytest.raises(campaign.WidenedParentCampaignError):
        campaign.build_campaign_manifest(
            parent,
            instance,
            parent_cube_index=True,
            strict_base=False,
        )
    with pytest.raises(campaign.WidenedParentCampaignError):
        campaign.verified_child_dimacs(
            manifest,
            parent,
            instance,
            parent_cube_index=PARENT_INDEX,
            leaf_index=64,
            strict_base=False,
        )
