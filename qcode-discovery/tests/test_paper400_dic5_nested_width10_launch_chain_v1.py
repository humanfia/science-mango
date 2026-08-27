from __future__ import annotations

import contextlib
import inspect
import json
import os
from pathlib import Path
from types import SimpleNamespace

import pytest

from investigations import paper400_dic5_nested_width10_campaign_v1 as nested
from scripts import paper400_dic5_nested_width10_resume_static_v1 as static_v1
from scripts import run_paper400_dic5_nested_width10_child_resume_proof_v1 as runner
from scripts import run_paper400_dic5_nested_width10_four_lane_v1 as coordinator


def _verification(manifest_sha256: str) -> dict:
    return nested._canonical_valid_verification_record(manifest_sha256)


def _fake_campaign() -> dict:
    leaves = []
    for global_leaf_index in range(nested.LEAF_COUNT):
        width6_leaf_index, local_child_index = divmod(
            global_leaf_index, nested.LOCAL_CHILD_COUNT
        )
        leaves.append(nested.seal({
            "global_leaf_index": global_leaf_index,
            "width6_leaf_index": width6_leaf_index,
            "local_child_index": local_child_index,
            "parent_cube_index": nested.TARGET_PARENT_CUBE_INDEX,
            "child_dimacs_sha256": f"{global_leaf_index:064x}",
        }, "leaf_sha256"))
    return {
        "manifest_sha256": "1" * 64,
        "test_only": False,
        "selected_parent": {"parent_cube_index": 0},
        "leaves": leaves,
    }


def test_interleaved_256_batches_are_exact_once_and_batch_zero_is_canonical():
    campaign = _fake_campaign()
    batches = [
        coordinator._selected_batch(campaign, index)
        for index in range(coordinator.BATCH_COUNT)
    ]
    assert batches[0]["leaf_indices"] == [0, 64, 128, 192]
    assert batches[1]["leaf_indices"] == [1, 65, 129, 193]
    assert batches[16]["leaf_indices"] == [16, 80, 144, 208]
    assert batches[64]["leaf_indices"] == [256, 320, 384, 448]
    flattened = [index for batch in batches for index in batch["leaf_indices"]]
    assert len(flattened) == nested.LEAF_COUNT
    assert len(set(flattened)) == nested.LEAF_COUNT
    assert sorted(flattened) == list(range(nested.LEAF_COUNT))
    for batch_index, batch in enumerate(batches):
        group_start = 4 * (batch_index // 64)
        old_suffix = (batch_index % 64) // 16
        new_suffix = batch_index % 16
        assert batch["width4_prefix_group_start"] == group_start
        assert batch["width6_old_suffix_index"] == old_suffix
        assert batch["extension_suffix_index"] == new_suffix
        for lane_index, global_leaf_index in enumerate(batch["leaf_indices"]):
            width6_leaf_index, observed_suffix = divmod(global_leaf_index, 16)
            assert observed_suffix == new_suffix
            assert width6_leaf_index == (group_start + lane_index) * 4 + old_suffix


@pytest.mark.parametrize(
    ("parent_cube_index", "global_leaf_index"),
    [(1, 0), (0, -1), (0, 1024), (False, 0), (0, True)],
)
def test_static_request_is_exactly_parent000_width10_index_range(
    parent_cube_index: int, global_leaf_index: int,
):
    with pytest.raises(static_v1.ResumeStaticError):
        static_v1._require_width10_request(
            parent_cube_index=parent_cube_index,
            global_leaf_index=global_leaf_index,
        )
    assert static_v1.EXPECTED_SPLIT_WIDTH == 10
    assert static_v1.EXPECTED_LEAF_COUNT == 1024


def test_resigned_mutation_of_verification_record_is_rejected():
    good = _verification("2" * 64)
    mutated = dict(good)
    mutated.pop("record_sha256")
    mutated["launch_authorized_by_this_record"] = True
    mutated["record_sha256"] = nested.canonical_sha256(mutated)
    with pytest.raises(static_v1.ResumeStaticError):
        static_v1._require_campaign_verification_record(
            mutated, campaign_manifest_sha256="2" * 64,
        )


def test_no_cli_accepts_an_external_verification_record():
    runner_prepare = runner.build_parser().parse_args([
        "prepare", "--root", "/tmp/r", "--parent-manifest", "/tmp/p",
        "--width6-campaign", "/tmp/w6", "--width10-campaign", "/tmp/w10",
        "--parent-cube-index", "0", "--global-leaf-index", "0",
        "--proof-max-bytes", "1", "--checkpoint-image-max-bytes", "1",
        "--checkpoint-images-per-generation-max", "1",
        "--checkpoint-generation-max-count", "1",
        "--checkpoint-generation-metadata-max-bytes", "1",
    ])
    coordinator_prepare = coordinator.build_parser().parse_args([
        "prepare", "--root", "/tmp/b", "--parent-manifest", "/tmp/p",
        "--width6-campaign", "/tmp/w6", "--width10-campaign", "/tmp/w10",
        "--parent-cube-index", "0", "--batch-index", "0",
        "--cpus", "0", "1", "2", "3", "--proof-max-bytes", "1",
        "--checkpoint-image-max-bytes", "1",
        "--checkpoint-images-per-generation-max", "1",
        "--checkpoint-generation-max-count", "1",
        "--checkpoint-generation-metadata-max-bytes", "1",
    ])
    assert not hasattr(runner_prepare, "campaign_verification_record")
    assert not hasattr(coordinator_prepare, "campaign_verification_record")
    assert "campaign_verification_record" not in inspect.signature(
        coordinator.prepare_batch
    ).parameters


def test_direct_action_admission_full_replays_exactly_once(monkeypatch):
    campaign = _fake_campaign()
    verification = _verification(campaign["manifest_sha256"])
    static_record = {
        "test_only": False,
        "child": {"parent_cube_index": 0},
    }
    by_name = {
        runner.STATIC_COMMIT.name: static_record,
        runner.STATIC_PARENT.name: {"test_only": False},
        runner.STATIC_WIDTH6_CAMPAIGN.name: {"test_only": False},
        runner.STATIC_WIDTH10_CAMPAIGN.name: campaign,
    }
    monkeypatch.setattr(runner, "_read_json", lambda path: by_name[Path(path).name])
    monkeypatch.setattr(
        nested.cube16.optimized, "build_optimized_instance", lambda: object(),
    )
    calls = []

    def full_verify(*args, **kwargs):
        calls.append((args, kwargs))
        return verification

    monkeypatch.setattr(nested, "verify_campaign_manifest", full_verify)
    result = runner._action_static_kwargs(Path("/tmp/fake-root"), {})
    assert calls and len(calls) == 1
    assert result["campaign_verification_record"] is verification


def test_supplied_same_call_record_skips_child_full_replay(monkeypatch):
    campaign = _fake_campaign()
    verification = _verification(campaign["manifest_sha256"])
    monkeypatch.setattr(
        runner, "_read_json", lambda path: campaign
        if Path(path).name == runner.STATIC_WIDTH10_CAMPAIGN.name else {},
    )
    monkeypatch.setattr(
        nested, "verify_campaign_manifest",
        lambda *args, **kwargs: pytest.fail("child repeated full campaign replay"),
    )
    result = runner._action_static_kwargs(
        Path("/tmp/fake-root"),
        {"campaign_verification_record": verification},
    )
    assert result["campaign_verification_record"] == verification


def test_prepare_full_replays_once_and_fast_rebuilds_exactly_four(
    monkeypatch, tmp_path: Path,
):
    campaign = _fake_campaign()
    width6 = {"manifest_sha256": "3" * 64, "test_only": False}
    parent = {"manifest_sha256": "4" * 64, "test_only": False}
    verification = _verification(campaign["manifest_sha256"])
    paths = {
        "width10.json": (campaign, b"w10\n"),
        "width6.json": (width6, b"w6\n"),
        "parent.json": (parent, b"parent\n"),
    }
    monkeypatch.setattr(
        coordinator, "_read_canonical_json",
        lambda path: paths[Path(path).name],
    )
    monkeypatch.setattr(coordinator, "_validate_cpus", lambda cpus: list(cpus))
    fake_instance = object()
    monkeypatch.setattr(
        coordinator, "_current_instance", lambda strict, instance: fake_instance,
    )
    counts = {"full": 0, "fast": 0, "child": 0}

    def full_verify(*args, **kwargs):
        counts["full"] += 1
        return verification

    def fast_child(*args, **kwargs):
        counts["fast"] += 1
        assert kwargs["verification_record"] is verification
        return f"cnf-{kwargs['global_leaf_index']}".encode("ascii")

    monkeypatch.setattr(nested, "verify_campaign_manifest", full_verify)
    monkeypatch.setattr(
        nested, "verified_child_dimacs_from_verification", fast_child,
    )
    caps = {
        "proof_max_bytes": 1,
        "checkpoint_image_max_bytes": 1,
        "checkpoint_images_per_generation_max": 1,
        "checkpoint_generation_max_count": 1,
        "checkpoint_generation_metadata_max_bytes": 1,
    }
    coordinator_path = Path(coordinator.__file__).resolve()
    monkeypatch.setattr(
        coordinator.child_runner, "_default_tool_paths",
        lambda: {"four_lane_coordinator_source": coordinator_path},
    )
    monkeypatch.setattr(
        coordinator.child_runner, "_default_tool_hashes",
        lambda: {"four_lane_coordinator_source": "5" * 64},
    )
    monkeypatch.setattr(coordinator, "_file_sha256", lambda *args, **kwargs: "5" * 64)
    monkeypatch.setattr(coordinator, "_new_root", lambda root: Path(root))
    monkeypatch.setattr(coordinator, "_create_lock", lambda root: None)
    monkeypatch.setattr(
        coordinator, "_batch_lock", lambda root: contextlib.nullcontext({}),
    )
    monkeypatch.setattr(
        coordinator, "_mkdir", lambda parent_path, name: Path(parent_path) / name,
    )
    monkeypatch.setattr(coordinator, "_publish_bytes", lambda *args, **kwargs: None)
    monkeypatch.setattr(coordinator, "_publish_json", lambda *args, **kwargs: None)
    monkeypatch.setattr(
        coordinator, "_prepare_claim",
        lambda *args, **kwargs: {"record_sha256": "6" * 64},
    )

    def prepare_child(*args, **kwargs):
        counts["child"] += 1
        assert kwargs["campaign_verification_record"] is verification
        assert kwargs["verified_child_dimacs"].startswith(b"cnf-")
        return {"record_sha256": f"{counts['child']:064x}"}

    monkeypatch.setattr(
        coordinator.child_runner, "prepare_root_from_material", prepare_child,
    )
    monkeypatch.setattr(
        coordinator, "_batch_manifest", lambda *args, **kwargs: {
            "record_sha256": "7" * 64
        },
    )
    result = coordinator.prepare_batch(
        tmp_path / "batch",
        width10_campaign_manifest_path=Path("width10.json"),
        width6_campaign_manifest_path=Path("width6.json"),
        parent_manifest_path=Path("parent.json"),
        parent_cube_index=0,
        batch_index=0,
        cpus=[0, 1, 2, 3],
        resource_caps=caps,
        strict_base=True,
    )
    assert result["all_lanes_succeeded"] is True
    assert counts == {"full": 1, "fast": 4, "child": 4}


def test_lane_outcome_round_trip_uses_real_global_index_schema(monkeypatch):
    lane = {"lane_index": 1, "global_leaf_index": 64, "cpu": 11}
    outcome = coordinator._make_lane_outcome(
        lane=lane,
        action="start",
        sequence=0,
        claim_sha256="a" * 64,
        disposition="APPLIED",
        reason="START_APPLIED",
        goal_satisfied=True,
        before=None,
        after=None,
        child_result={"kind": "fake-start", "state": "RUNNING"},
    )
    assert outcome["global_leaf_index"] == 64
    assert "leaf_index" not in outcome
    monkeypatch.setattr(
        coordinator,
        "_read_canonical_json",
        lambda path: (outcome, coordinator.canonical_bytes(outcome) + b"\n"),
    )
    assert coordinator._read_lane_outcome(
        Path("lane-1.json"),
        lane=lane,
        action="start",
        sequence=0,
        claim_sha256="a" * 64,
    ) == outcome

    legacy = dict(outcome)
    legacy.pop("record_sha256")
    legacy["leaf_index"] = legacy.pop("global_leaf_index")
    legacy = coordinator.seal(legacy)
    monkeypatch.setattr(
        coordinator,
        "_read_canonical_json",
        lambda path: (legacy, coordinator.canonical_bytes(legacy) + b"\n"),
    )
    with pytest.raises(
        coordinator.FourLaneBatchError,
        match="lane action outcome schema or binding mismatch",
    ):
        coordinator._read_lane_outcome(
            Path("lane-1.json"),
            lane=lane,
            action="start",
            sequence=0,
            claim_sha256="a" * 64,
        )


def test_synthetic_start_persists_four_real_width10_global_indices(
    monkeypatch, tmp_path: Path,
):
    root = (tmp_path / "batch").resolve()
    root.mkdir(mode=0o700)
    actions = root / coordinator.ACTIONS
    actions.mkdir(mode=0o700)
    lanes_root = root / coordinator.LANES
    lanes_root.mkdir(mode=0o700)
    cpus = sorted(os.sched_getaffinity(0))[:4]
    assert len(cpus) == 4
    global_indices = [0, 64, 128, 192]
    lanes = []
    for lane_index, (cpu, global_leaf_index) in enumerate(
        zip(cpus, global_indices, strict=True)
    ):
        child_root = lanes_root / f"lane-{lane_index}"
        child_root.mkdir(mode=0o700)
        lanes.append({
            "lane_index": lane_index,
            "global_leaf_index": global_leaf_index,
            "cpu": cpu,
            "child_root": str(child_root),
        })
    manifest = {
        "record_sha256": "b" * 64,
        "batch": {"batch_index": 0},
        "authority": coordinator.AUTHORITY_COVER_TRANSPORT,
        "lanes": lanes,
    }
    monkeypatch.setattr(
        coordinator,
        "_batch_lock",
        lambda target: contextlib.nullcontext({}),
    )
    monkeypatch.setattr(
        coordinator,
        "_load_batch",
        lambda *args, **kwargs: {
            "manifest": manifest,
            "static_kwargs": {},
        },
    )
    observed_affinities = []

    def fake_start(child_root: Path, **kwargs):
        observed_affinities.append(set(os.sched_getaffinity(0)))
        return {
            "kind": "fake-start",
            "state": "RUNNING",
            "root": str(child_root),
        }

    def fake_status(child_root: Path, **kwargs):
        return {
            "kind": "fake-status",
            "chain": {"state": "RUNNING"},
            "terminal_claimed": False,
            "terminal_committed": False,
        }

    monkeypatch.setattr(coordinator.child_runner, "start_root", fake_start)
    monkeypatch.setattr(coordinator.child_runner, "status_root", fake_status)
    before = set(os.sched_getaffinity(0))
    result = coordinator.run_batch_action(root, "start", strict_base=False)
    assert result["all_lanes_succeeded"] is True
    assert observed_affinities == [{cpu} for cpu in cpus]
    assert set(os.sched_getaffinity(0)) == before
    outcomes = [
        json.loads(
            (actions / "000000" / f"lane-{lane_index}.json").read_bytes()
        )
        for lane_index in range(4)
    ]
    assert [item["global_leaf_index"] for item in outcomes] == global_indices
    assert all("leaf_index" not in item for item in outcomes)


def test_production_static_kwargs_never_inject_instance():
    replay = _verification("8" * 64)
    kwargs = coordinator._static_kwargs(None, True, {
        key: 1 for key in static_v1.CAP_INPUT_FIELDS
    }, replay)
    assert kwargs["instance"] is None
    assert kwargs["strict_base"] is True
    assert kwargs["campaign_verification_record"] == replay


def test_child_runner_pin_equals_frozen_coordinator_source_bytes():
    actual = coordinator._file_sha256(
        Path(coordinator.__file__).resolve(), cap=16 << 20,
    )
    assert actual == "ab55b4beebbe45234b19165dad7f3e46e85a00f769766a5c8f77e7fe840c07d9"
    assert runner.EXPECTED_FOUR_LANE_SHA256 == actual


def test_batch_255_is_the_exact_upper_interleaving_boundary():
    batch = coordinator._selected_batch(_fake_campaign(), 255)
    assert batch["width4_prefix_group_start"] == 12
    assert batch["width6_old_suffix_index"] == 3
    assert batch["extension_suffix_index"] == 15
    assert batch["leaf_indices"] == [831, 895, 959, 1023]


def test_runner_pin_is_nonzero_and_all_launch_source_roles_are_exact():
    actual_coordinator = coordinator._file_sha256(
        Path(coordinator.__file__).resolve(), cap=16 << 20,
    )
    assert runner.EXPECTED_FOUR_LANE_SHA256 != "0" * 64
    assert runner.EXPECTED_FOUR_LANE_SHA256 == actual_coordinator
    assert (
        runner._default_tool_paths()["four_lane_coordinator_source"].resolve()
        == Path(coordinator.__file__).resolve()
    )
    assert (
        runner._default_tool_hashes()["four_lane_coordinator_source"]
        == actual_coordinator
    )

    binding = coordinator._source_binding()
    by_role = {record["role"]: record for record in binding["sources"]}
    assert set(by_role) == {
        "nested_width10_campaign_source",
        "width6_campaign_source",
        "hierarchical_refiner_source",
        "resume_static_source",
        "nested_width10_proof_records_source",
        "nested_width10_child_runner_source",
        "four_lane_coordinator_source",
    }
    assert by_role["nested_width10_child_runner_source"]["sha256"] == (
        coordinator._file_sha256(Path(runner.__file__).resolve(), cap=16 << 20)
    )
    assert by_role["four_lane_coordinator_source"]["sha256"] == actual_coordinator


def test_static_target_payload_hash_is_exact_and_fails_closed():
    payload = b"p cnf 1 1\n1 0\n"
    leaf = {
        "child_dimacs_bytes": len(payload),
        "child_dimacs_sha256": static_v1.hashlib.sha256(payload).hexdigest(),
    }
    assert static_v1._verified_payload_for_leaf(payload, leaf) == payload

    resigned_wrong_leaf = dict(leaf)
    resigned_wrong_leaf["child_dimacs_sha256"] = "0" * 64
    with pytest.raises(
        static_v1.ResumeStaticError,
        match="does not match the selected leaf",
    ):
        static_v1._verified_payload_for_leaf(payload, resigned_wrong_leaf)


def test_direct_invalid_replay_is_rejected_before_start_or_controller(
    monkeypatch,
):
    campaign = _fake_campaign()
    invalid = _verification(campaign["manifest_sha256"])
    invalid.pop("record_sha256")
    invalid["launch_authorized_by_this_record"] = True
    invalid["record_sha256"] = nested.canonical_sha256(invalid)
    target = Path("/tmp/no-controller-admission")
    monkeypatch.setattr(runner, "_existing_root", lambda root: Path(root))
    monkeypatch.setattr(
        runner, "_root_lock", lambda *args, **kwargs: contextlib.nullcontext({}),
    )
    monkeypatch.setattr(runner, "_read_json", lambda path: campaign)
    monkeypatch.setattr(
        runner, "_start_root_locked",
        lambda *args, **kwargs: pytest.fail("start/controller path was reached"),
    )
    monkeypatch.setattr(
        runner.controller, "initialize",
        lambda *args, **kwargs: pytest.fail("controller was reached"),
    )

    with pytest.raises(static_v1.ResumeStaticError):
        runner.start_root(
            target, campaign_verification_record=invalid,
        )


def test_invalid_batch_full_replay_invokes_no_fast_path_or_child(
    monkeypatch,
):
    campaign = _fake_campaign()
    width6 = {"manifest_sha256": "3" * 64, "test_only": False}
    parent = {"manifest_sha256": "4" * 64, "test_only": False}
    paths = {
        "width10.json": (campaign, b"w10\n"),
        "width6.json": (width6, b"w6\n"),
        "parent.json": (parent, b"parent\n"),
    }
    monkeypatch.setattr(
        coordinator, "_read_canonical_json",
        lambda path: paths[Path(path).name],
    )
    monkeypatch.setattr(coordinator, "_validate_cpus", lambda cpus: list(cpus))
    monkeypatch.setattr(
        coordinator, "_current_instance", lambda strict, instance: object(),
    )
    counts = {"full": 0, "fast": 0, "child": 0}

    def invalid_full(*args, **kwargs):
        counts["full"] += 1
        return {"valid": False, "binding_failures": ["synthetic mismatch"]}

    def forbidden_fast(*args, **kwargs):
        counts["fast"] += 1
        pytest.fail("targeted fast path ran after invalid full replay")

    def forbidden_child(*args, **kwargs):
        counts["child"] += 1
        pytest.fail("child prepare ran after invalid full replay")

    monkeypatch.setattr(nested, "verify_campaign_manifest", invalid_full)
    monkeypatch.setattr(
        nested, "verified_child_dimacs_from_verification", forbidden_fast,
    )
    monkeypatch.setattr(
        coordinator.child_runner, "prepare_root_from_material", forbidden_child,
    )
    with pytest.raises(
        coordinator.FourLaneBatchError,
        match="fresh replay failed",
    ):
        coordinator.prepare_batch(
            Path("/tmp/rejected-width10-batch"),
            width10_campaign_manifest_path=Path("width10.json"),
            width6_campaign_manifest_path=Path("width6.json"),
            parent_manifest_path=Path("parent.json"),
            parent_cube_index=0,
            batch_index=0,
            cpus=[0, 1, 2, 3],
            resource_caps={
                key: 1 for key in static_v1.CAP_INPUT_FIELDS
            },
            strict_base=True,
        )
    assert counts == {"full": 1, "fast": 0, "child": 0}


def _synthetic_dmtcp_image(generation: Path, token: str) -> Path:
    image = generation / "images" / f"ckpt_cadical_{token}.dmtcp"
    image.write_bytes(
        runner.controller.DMTCP_IMAGE_MAGIC + b"synthetic-image"
    )
    return image


def _synthetic_restart_pair(
    directory: Path, image: Path, token: str,
) -> tuple[Path, Path]:
    target = directory / f"dmtcp_restart_script_{token}.sh"
    target.write_bytes(
        f'#!/bin/sh\ngiven_ckpt_files=" {image}"\n'.encode("ascii")
    )
    target.chmod(0o744)
    alias = directory / runner.RESTART_ALIAS_NAME
    alias.symlink_to(target.name)
    return alias, target


def _synthetic_checkpoint(
    runtime: Path, generation: Path, number: int, image: Path,
) -> dict:
    return runner.controller.write_manifest(
        generation / "checkpoint.commit.json", "checkpoint.commit", {
            "generation": number,
            "images": [
                runner.controller.stable_file_record(
                    image, relative_to=runtime,
                )
            ],
            "single_writer_stopped": True,
        },
    )


def test_v4_transport_accepts_natural_gen0_then_resumed_gen1_layout(
    tmp_path: Path,
):
    root = tmp_path / "root"
    root.mkdir(mode=0o700)
    (root / "runtime").mkdir(mode=0o700)
    runtime = root / runner.RUNTIME_ROOT
    runtime.mkdir(mode=0o700)
    (runtime / "generations").mkdir(mode=0o700)

    generation0 = runner.controller._create_generation(runtime, 0)
    image0 = _synthetic_dmtcp_image(
        generation0, "deadbeef-40000-cafebabe",
    )
    alias0, _target0 = _synthetic_restart_pair(
        generation0 / "images", image0, "deadbeef-40000-cafebabe",
    )
    _synthetic_checkpoint(runtime, generation0, 0, image0)

    generation1 = runner.controller._create_generation(runtime, 1)
    image1 = _synthetic_dmtcp_image(
        generation1, "deadbeef-40000-feedface",
    )
    _synthetic_checkpoint(runtime, generation1, 1, image1)
    root_alias, root_target = _synthetic_restart_pair(
        runtime, image1, "deadbeef-40000-feedface",
    )

    identity = runner._root_tree_identity(root.resolve())
    aliases = {
        record["relative_path"] for record in identity
        if record["entry_type"] == "symlink"
    }
    assert aliases == {
        alias0.relative_to(root).as_posix(),
        root_alias.relative_to(root).as_posix(),
    }
    assert not any(
        (generation1 / "images").glob("dmtcp_restart_script*")
    )
    generation1_bytes = runner._generation_metadata_bytes(
        generation1, {image1}, generation=1,
    )
    observed_target, target_bytes = runner._runtime_restart_pair(
        runtime, image1,
    )
    assert generation1_bytes >= 0
    assert observed_target == root_target
    assert target_bytes == root_target.stat().st_size

