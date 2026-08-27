from __future__ import annotations

import copy
import hashlib
from pathlib import Path

import numpy as np
import pytest

from evaluation import paper400_dic5_optimized_cnf_final_v13 as optimized
from investigations import paper400_dic5_cube16 as cube16
from investigations import paper400_dic5_hierarchical_cubes_v1 as hierarchy
from scripts import paper400_dic5_hierarchical_resume_static_v2 as static_v2


PARENT_CUBE_INDEX = 8
SPLIT_WIDTH = 2


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


@pytest.fixture()
def material() -> tuple[optimized.OptimizedInstance, dict, dict]:
    instance = _synthetic_instance()
    parent = cube16.build_coverage_manifest(
        instance,
        strict_base=False,
        split_variables=(1, 2, 3, 4),
    )
    refinement = hierarchy.build_refinement_manifest(
        parent,
        instance,
        parent_cube_index=PARENT_CUBE_INDEX,
        split_width=SPLIT_WIDTH,
        strict_base=False,
    )
    return instance, parent, refinement


@pytest.fixture()
def caps() -> dict[str, int]:
    return {
        "proof_max_bytes": 1 << 20,
        "checkpoint_image_max_bytes": 2 << 20,
        "checkpoint_images_per_generation_max": 2,
        "checkpoint_generation_max_count": 3,
        "checkpoint_generation_metadata_max_bytes": 4096,
    }


@pytest.fixture()
def tools(tmp_path: Path) -> tuple[dict[str, Path], dict[str, str]]:
    directory = tmp_path / "pinned-tools"
    directory.mkdir()
    paths: dict[str, Path] = {}
    hashes: dict[str, str] = {}
    for role in sorted(static_v2.TOOL_ROLES):
        path = directory / role
        payload = f"fixed tool fixture: {role}\n".encode("ascii")
        path.write_bytes(payload)
        if role in static_v2.EXECUTABLE_TOOL_ROLES:
            path.chmod(0o700)
        paths[role] = path
        hashes[role] = hashlib.sha256(payload).hexdigest()
    return paths, hashes


def _root_with_child(
    tmp_path: Path,
    material: tuple[optimized.OptimizedInstance, dict, dict],
    *,
    name: str,
    child_index: int,
) -> tuple[Path, Path]:
    instance, parent, refinement = material
    root = (tmp_path / name).resolve()
    static_dir = root / "static"
    static_dir.mkdir(parents=True)
    child_path = static_dir / f"child-{child_index:04d}.cnf"
    child_path.write_bytes(hierarchy.verified_child_dimacs(
        refinement,
        parent,
        instance,
        child_index=child_index,
        strict_base=False,
        expected_parent_cube_index=PARENT_CUBE_INDEX,
        expected_split_width=SPLIT_WIDTH,
    ))
    return root, child_path


def _build(
    *,
    root: Path,
    child_path: Path,
    material: tuple[optimized.OptimizedInstance, dict, dict],
    tools: tuple[dict[str, Path], dict[str, str]],
    caps: dict[str, int],
    child_index: int = 0,
) -> dict:
    instance, parent, refinement = material
    paths, hashes = tools
    return static_v2.build_resume_static_record(
        root=root,
        parent_manifest=parent,
        refinement_manifest=refinement,
        instance=instance,
        parent_cube_index=PARENT_CUBE_INDEX,
        child_index=child_index,
        split_width=SPLIT_WIDTH,
        child_cnf_path=child_path,
        tool_paths=paths,
        expected_tool_sha256=hashes,
        resource_caps=caps,
        strict_base=False,
    )


def _verify(
    record: dict,
    *,
    root: Path,
    child_path: Path,
    material: tuple[optimized.OptimizedInstance, dict, dict],
    tools: tuple[dict[str, Path], dict[str, str]],
    caps: dict[str, int],
    child_index: int = 0,
) -> dict:
    instance, parent, refinement = material
    paths, hashes = tools
    return static_v2.verify_resume_static_record(
        record,
        root=root,
        parent_manifest=parent,
        refinement_manifest=refinement,
        instance=instance,
        parent_cube_index=PARENT_CUBE_INDEX,
        child_index=child_index,
        split_width=SPLIT_WIDTH,
        child_cnf_path=child_path,
        tool_paths=paths,
        expected_tool_sha256=hashes,
        resource_caps=caps,
        strict_base=False,
    )


def test_valid_static_binds_resume_caps_and_mandatory_fresh_replay(
    tmp_path: Path,
    material: tuple[optimized.OptimizedInstance, dict, dict],
    tools: tuple[dict[str, Path], dict[str, str]],
    caps: dict[str, int],
) -> None:
    root, child_path = _root_with_child(
        tmp_path, material, name="root-a", child_index=0,
    )
    record = _build(
        root=root,
        child_path=child_path,
        material=material,
        tools=tools,
        caps=caps,
    )
    report = _verify(
        record,
        root=root,
        child_path=child_path,
        material=material,
        tools=tools,
        caps=caps,
    )

    assert report["valid"] is True
    assert report["resume"] is True
    assert record["resume_policy"]["resume"] is True
    assert record["resume_policy"][
        "dmtcp_transport_trusted_for_scientific_proof"
    ] is False
    assert record["fresh_replay_policy"][
        "complete_drat_from_exact_child_cnf_required"
    ] is True
    assert record["fresh_replay_policy"][
        "fresh_lrat_replay_from_exact_child_cnf_required"
    ] is True
    assert record["authority"] == static_v2.AUTHORITY_SYNTHETIC_TEST_ONLY
    assert record["production_eligible"] is False
    assert record["resource_policy"]["total_runtime_artifact_max_bytes"] == (
        caps["proof_max_bytes"]
        + caps["checkpoint_image_max_bytes"]
        * caps["checkpoint_images_per_generation_max"]
        * caps["checkpoint_generation_max_count"]
        + caps["checkpoint_generation_metadata_max_bytes"]
        * caps["checkpoint_generation_max_count"]
    )


def test_non_test_manifests_map_only_to_production_candidate_authority() -> None:
    assert static_v2._authority(
        {"test_only": False}, {"test_only": False},
    ) == static_v2.AUTHORITY_PRODUCTION_CANDIDATE
    assert static_v2.AUTHORITY_PRODUCTION_CANDIDATE == "PRODUCTION_CANDIDATE"


def test_cross_child_substitution_fails_fresh_replay(
    tmp_path: Path,
    material: tuple[optimized.OptimizedInstance, dict, dict],
    tools: tuple[dict[str, Path], dict[str, str]],
    caps: dict[str, int],
) -> None:
    root0, child0 = _root_with_child(
        tmp_path, material, name="child-zero-root", child_index=0,
    )
    record0 = _build(
        root=root0,
        child_path=child0,
        material=material,
        tools=tools,
        caps=caps,
        child_index=0,
    )
    instance, parent, refinement = material
    child1 = root0 / "static/child-0001.cnf"
    child1.write_bytes(hierarchy.verified_child_dimacs(
        refinement,
        parent,
        instance,
        child_index=1,
        strict_base=False,
        expected_parent_cube_index=PARENT_CUBE_INDEX,
        expected_split_width=SPLIT_WIDTH,
    ))
    report = _verify(
        record0,
        root=root0,
        child_path=child1,
        material=material,
        tools=tools,
        caps=caps,
        child_index=1,
    )
    assert report["valid"] is False
    assert "fresh canonical replay" in " ".join(report["binding_failures"])


def test_cross_root_copy_fails_even_when_cnf_bytes_match(
    tmp_path: Path,
    material: tuple[optimized.OptimizedInstance, dict, dict],
    tools: tuple[dict[str, Path], dict[str, str]],
    caps: dict[str, int],
) -> None:
    root_a, child_a = _root_with_child(
        tmp_path, material, name="root-a", child_index=0,
    )
    record_a = _build(
        root=root_a,
        child_path=child_a,
        material=material,
        tools=tools,
        caps=caps,
    )
    root_b, child_b = _root_with_child(
        tmp_path, material, name="root-b", child_index=0,
    )
    assert child_a.read_bytes() == child_b.read_bytes()
    report = _verify(
        record_a,
        root=root_b,
        child_path=child_b,
        material=material,
        tools=tools,
        caps=caps,
    )
    assert report["valid"] is False
    assert "root" in " ".join(report["binding_failures"])


def test_source_or_tool_mutation_after_seal_fails_closed(
    tmp_path: Path,
    material: tuple[optimized.OptimizedInstance, dict, dict],
    tools: tuple[dict[str, Path], dict[str, str]],
    caps: dict[str, int],
) -> None:
    root, child_path = _root_with_child(
        tmp_path, material, name="source-tamper", child_index=0,
    )
    record = _build(
        root=root,
        child_path=child_path,
        material=material,
        tools=tools,
        caps=caps,
    )
    paths, _ = tools
    paths["dmtcp_controller_source"].write_bytes(b"mutated controller\n")
    report = _verify(
        record,
        root=root,
        child_path=child_path,
        material=material,
        tools=tools,
        caps=caps,
    )
    assert report["valid"] is False
    assert "SHA-256 mismatch" in " ".join(report["binding_failures"])


def test_resealed_alternative_caps_fail_external_policy_binding(
    tmp_path: Path,
    material: tuple[optimized.OptimizedInstance, dict, dict],
    tools: tuple[dict[str, Path], dict[str, str]],
    caps: dict[str, int],
) -> None:
    root, child_path = _root_with_child(
        tmp_path, material, name="cap-substitution", child_index=0,
    )
    changed_caps = copy.deepcopy(caps)
    changed_caps["proof_max_bytes"] *= 2
    alternative = _build(
        root=root,
        child_path=child_path,
        material=material,
        tools=tools,
        caps=changed_caps,
    )
    assert static_v2.selfhash_valid(alternative)
    report = _verify(
        alternative,
        root=root,
        child_path=child_path,
        material=material,
        tools=tools,
        caps=caps,
    )
    assert report["valid"] is False
    assert "resource caps" in " ".join(report["binding_failures"])


def test_resealed_source_binding_tamper_still_fails_exact_replay(
    tmp_path: Path,
    material: tuple[optimized.OptimizedInstance, dict, dict],
    tools: tuple[dict[str, Path], dict[str, str]],
    caps: dict[str, int],
) -> None:
    root, child_path = _root_with_child(
        tmp_path, material, name="resealed-source", child_index=0,
    )
    record = _build(
        root=root,
        child_path=child_path,
        material=material,
        tools=tools,
        caps=caps,
    )
    changed = copy.deepcopy(record)
    changed.pop("record_sha256")
    changed["source_binding"]["sources"]["hierarchical_refiner_source"][
        "sha256"
    ] = "f" * 64
    changed = static_v2.seal(changed)
    assert static_v2.selfhash_valid(changed)
    report = _verify(
        changed,
        root=root,
        child_path=child_path,
        material=material,
        tools=tools,
        caps=caps,
    )
    assert report["valid"] is False
    assert "exact fresh canonical replay" in " ".join(
        report["binding_failures"]
    )


def test_cap_types_and_combined_budget_fail_closed(caps: dict[str, int]) -> None:
    bool_cap = copy.deepcopy(caps)
    bool_cap["checkpoint_generation_max_count"] = True
    with pytest.raises(static_v2.ResumeStaticError, match="strict integers"):
        static_v2.normalize_resource_caps(bool_cap)

    too_large = copy.deepcopy(caps)
    too_large["proof_max_bytes"] = static_v2.MAX_PROOF_BYTES
    too_large["checkpoint_image_max_bytes"] = static_v2.MAX_CHECKPOINT_IMAGE_BYTES
    too_large["checkpoint_images_per_generation_max"] = 64
    too_large["checkpoint_generation_max_count"] = 1 << 16
    with pytest.raises(static_v2.ResumeStaticError, match="combined"):
        static_v2.normalize_resource_caps(too_large)
