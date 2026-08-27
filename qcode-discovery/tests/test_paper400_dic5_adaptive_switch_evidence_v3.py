from __future__ import annotations

import errno
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
from typing import Any

import pytest

from scripts import paper400_dic5_adaptive_switch_evidence_v2 as v2
from scripts import paper400_dic5_adaptive_switch_evidence_v3 as v3


H = "a" * 64


def _write_json(path: Path, value: dict[str, Any]) -> None:
    path.write_bytes(v3.canonical_bytes(value) + b"\n")
    path.chmod(0o600)


def _lock_file(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.touch(mode=0o600, exist_ok=False)
    path.chmod(0o600)


def _root(path: Path) -> dict[str, Any]:
    path.mkdir(mode=0o700)
    path.chmod(0o700)
    return v3.base._root_identity(path)


def _valid_switch_record(root: Path) -> dict[str, Any]:
    """Build the smallest record accepted by the real v2 validator."""

    lanes: list[dict[str, Any]] = []
    for lane in range(4):
        chain = v3.seal({
            "state": "CHECKPOINTED", "writable_holders": [],
        })
        hard = v3.seal({
            "status": "UNKNOWN", "hardness_only": True,
            "solver_terminal_claim": False,
        }, "evidence_sha256")
        lanes.append(v3.seal({
            "schema_version": v2.SCHEMA_VERSION,
            "kind": v2.LANE_KIND,
            "lane_index": lane,
            "cpu": lane,
            "global_leaf_index": 100 + lane,
            "global_leaf_id": f"leaf-{lane}",
            "leaf_sha256": f"{lane + 1:064x}",
            "child_cnf_sha256": f"{lane + 5:064x}",
            "child_dimacs_sha256": f"{lane + 9:064x}",
            "combined_unit_clauses_sha256": f"{lane + 13:064x}",
            "child_root": str(root / "lanes" / f"lane-{lane}"),
            "child_root_identity": {"lane": lane},
            "resume_static_sha256": f"{lane + 17:064x}",
            "session_sha256": f"{lane + 21:064x}",
            "checkpoint_stop_lane_outcome_sha256": f"{lane + 25:064x}",
            "transport_chain": chain,
            "transport_chain_sha256": chain["record_sha256"],
            "controller_inspection": {"state": "CHECKPOINTED"},
            "latest_checkpoint_sha256": f"{lane + 29:064x}",
            "checkpoint_proof_prefix": {"sha256": H, "bytes": 0},
            "checkpoint_proof_physical": {"file_sha256": H, "bytes": 0},
            "hard_evidence": hard,
            "hard_evidence_sha256": hard["evidence_sha256"],
            "solver_stopped": True,
            "terminal_claimed": False,
            "terminal_committed": False,
            "hardness_only": True,
            "solver_terminal_claim": False,
        }, "lane_record_sha256"))
    history = v3.seal({
        "latest_action": "checkpoint-stop", "complete": True,
    }, "action_history_sha256")
    source = v3.seal({
        "sitecustomize_imported_by_loader": False,
        "pyc_executed_by_loader": False,
    }, "source_binding_sha256")
    return v3.seal({
        "schema_version": v2.SCHEMA_VERSION,
        "kind": v2.SWITCH_KIND,
        "gate": v2.SWITCH_GATE,
        "authority": "EVIDENCE_ONLY_ATOMIC_LEASE_REQUIRED",
        "test_only": True,
        "production_eligible": False,
        "authenticated": False,
        "launch_authorized": False,
        "scientific_claim": False,
        "root": str(root),
        "root_identity": v3.base._root_identity(root),
        "batch_manifest_sha256": "d" * 64,
        "width10_campaign_sha256": "e" * 64,
        "width6_campaign_sha256": "f" * 64,
        "parent_manifest_sha256": "1" * 64,
        "observation_policy": {
            "timeout_seconds": 1.0,
            "elapsed_seconds_by_lane": [0.0] * 4,
        },
        "action_history": history,
        "lanes": lanes,
        "source_binding": source,
        "claim_scope": {
            "candidate_evidence_only": True,
            "serialized_record_is_launch_authority": False,
        },
    })


def test_v2_launch_lease_is_superseded_and_not_exported(tmp_path: Path) -> None:
    assert "acquire_atomic_switch_lease" not in v2.__all__
    context = v2.acquire_atomic_switch_lease(
        tmp_path,
        expected_batch_manifest_sha256=H,
        expected_switch_evidence_sha256=H,
        expected_hard_evidence_sha256s=[H] * 4,
        timeout_seconds=1.0,
        elapsed_seconds_by_lane=[0.0] * 4,
    )
    with pytest.raises(v2.AdaptiveSwitchEvidenceV2Error, match="SUPERSEDED_BY_V3"):
        context.__enter__()


def test_v2_exact_source_loader_binds_location_before_execution(
    tmp_path: Path,
) -> None:
    source = tmp_path / "location_probe.py"
    payload = (
        b"TOP_LEVEL_FILE = __file__\n"
        b"TOP_LEVEL_CACHED = __cached__\n"
    )
    source.write_bytes(payload)
    observed: dict[str, dict[str, Any]] = {}
    fullname = "scripts.location_probe"
    loader = v2._SourceBytesLoader(
        fullname, source, payload, observed, externally_bound=True,
    )
    spec = importlib.util.spec_from_loader(
        fullname, loader, origin=str(source),
    )
    assert spec is not None and spec.has_location is False
    module = importlib.util.module_from_spec(spec)

    loader.exec_module(module)

    assert module.TOP_LEVEL_FILE == str(source)
    assert module.TOP_LEVEL_CACHED is None
    assert module.__file__ == str(source)
    assert module.__cached__ is None
    assert observed[fullname]["sha256"] == hashlib.sha256(payload).hexdigest()


def test_v3_retirement_binds_post_rename_identity_and_blocks_old_name(
    tmp_path: Path,
) -> None:
    root = tmp_path / "root"
    _root(root)
    original = root / ".batch.lock"
    _lock_file(original)
    held = v3.base._HeldLock(original, "batch", fcntl.LOCK_EX)
    pre = dict(held.identity)
    retired = root / ".batch.lock.retired-v3-test"
    try:
        record = v3._retire_lock_v3(held, retired)
        assert not original.exists()
        assert record["identity"] == v3.base._stat_identity(retired.lstat())
        assert record["identity"] == v3.base._stat_identity(os.fstat(held.fd))
        assert record["pre_rename_identity"] == pre
        assert (
            v3._identity_without_ctime(record["identity"])
            == v3._identity_without_ctime(pre)
        )
        held.close()
        with pytest.raises(Exception):
            v3.base._HeldLock(original, "old-runner", fcntl.LOCK_EX)
    finally:
        held.close()


def test_stream_hash_does_not_use_whole_file_reader(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    proof = tmp_path / "proof.drat"
    payload = (b"proof-line\n" * 200_000)
    proof.write_bytes(payload)
    monkeypatch.setattr(
        v3.base, "_stable_bytes",
        lambda *args, **kwargs: (_ for _ in ()).throw(
            AssertionError("whole-file reader was called")
        ),
    )
    digest, size = v3._stream_hash_size(proof)
    assert digest == hashlib.sha256(payload).hexdigest()
    assert size == len(payload)


def _old_retirements(root: Path) -> list[dict[str, Any]]:
    paths: list[tuple[str, Path]] = [("batch", root / ".batch.lock")]
    for lane in range(4):
        lane_root = root / "lanes" / f"lane-{lane}"
        paths.append((f"lane-{lane}", lane_root / ".hierarchical-resume.lock"))
    for lane in range(4):
        lane_root = root / "lanes" / f"lane-{lane}"
        paths.append((f"controller-{lane}", lane_root / "runtime/dmtcp/.controller.lock"))
    records: list[dict[str, Any]] = []
    # Persisted retirement order is controllers, lanes, batch.
    order = [*paths[5:], *paths[1:5], paths[0]]
    for sequence, (role, original) in enumerate(order):
        _lock_file(original)
        pre = v3.base._stat_identity(original.lstat())
        retired = original.with_name(original.name + ".retired-v3-fixture")
        os.rename(original, retired)
        records.append({
            "sequence": sequence,
            "role": role,
            "original_path": str(original),
            "retired_path": str(retired),
            "pre_rename_identity": pre,
            "identity": v3.base._stat_identity(retired.lstat()),
        })
    return records


def _committed_fixture(tmp_path: Path) -> dict[str, Any]:
    batch = tmp_path / "batch"
    batch_identity = _root(batch)
    retirements = _old_retirements(batch)
    batch_sha = "d" * 64
    switch_record = v3.seal({
        "batch_manifest_sha256": batch_sha,
    })
    switch_sha = switch_record["record_sha256"]
    prepared = v3.seal({
        "schema_version": 3,
        "kind": v3.PREPARED_KIND,
        "batch_manifest_sha256": batch_sha,
        "switch_evidence_sha256": switch_sha,
        "retired_locks": retirements,
    })
    prepared_sha = prepared["record_sha256"]
    _write_json(batch / v3.PREPARED_COMMIT, prepared)
    for relative in (
        v3.TARGET_DIRECTORY,
        v3.STARTED_DIRECTORY,
        v3.QUIESCENCE_DIRECTORY,
    ):
        (batch / relative).mkdir(mode=0o700)
    bindings: list[dict[str, Any]] = []
    rollback_quiescence: list[dict[str, Any]] = []
    new_roots: list[Path] = []
    active_by_root: dict[str, dict[str, Any]] = {}
    for position, (lane, descendant) in enumerate(v3.TARGET_KEYS):
        new_root = tmp_path / f"new-{lane}-{descendant}"
        identity = _root(new_root)
        new_roots.append(new_root)
        _lock_file(new_root / ".adaptive-child.lock")
        _lock_file(new_root / "runtime/dmtcp/.controller.lock")
        proof = new_root / "runtime/dmtcp/proof.drat"
        proof.write_bytes(f"proof-{lane}-{descendant}\n".encode())
        pid = 900_000_000 + position
        ticks = 100 + position
        descendant_sha = f"{position + 1:064x}"
        permit_sha = f"{position + 31:064x}"
        session_sha = f"{position + 41:064x}"
        start_sha = f"{position + 51:064x}"
        target_record = v3.seal({
            "schema_version": 3,
            "kind": "paper400-adaptive-prepared-target-v3",
            "authenticated": False,
            "launch_authorized": False,
            "lane_index": lane,
            "global_leaf_index": lane,
            "descendant_index": descendant,
            "descendant_sha256": descendant_sha,
            "overlay_manifest_sha256": f"{position + 61:064x}",
            "hard_evidence_sha256": f"{lane + 71:064x}",
            "permit_binding_sha256": permit_sha,
            "new_root_identity": identity,
            "switch_evidence_sha256": switch_sha,
            "prepared_retirement_sha256": prepared_sha,
        })
        _write_json(
            batch / v3.TARGET_DIRECTORY
            / f"lane-{lane}-descendant-{descendant}.json",
            target_record,
        )
        started_record = v3.seal({
            "schema_version": 3,
            "kind": "paper400-adaptive-started-worker-v3",
            "authenticated": False,
            "launch_authorized": False,
            "lane_index": lane,
            "descendant_index": descendant,
            "prepared_target_sha256": target_record["record_sha256"],
            "permit_binding_sha256": permit_sha,
            "new_root_identity": identity,
            "new_pid": pid,
            "new_proc_start_ticks": ticks,
            "switch_evidence_sha256": switch_sha,
            "prepared_retirement_sha256": prepared_sha,
        })
        _write_json(
            batch / v3.STARTED_DIRECTORY
            / f"lane-{lane}-descendant-{descendant}.json",
            started_record,
        )
        digest, size = v3._stream_hash_size(proof)
        cohort_quiescence_sha: str | None = None
        if descendant == 0:
            cohort_quiescence = v3.seal({
                "schema_version": 3,
                "kind": v3.QUIESCENCE_KIND,
                "lane_index": lane,
                "descendant_index": descendant,
                "new_root_identity": identity,
                "new_pid": pid,
                "new_proc_start_ticks": ticks,
                "state": "CHECKPOINTED",
                "pid_identity_alive": False,
                "checkpoint_commit_sha256":
                    f"{position + 81:064x}",
                "proof_sha256": digest,
                "proof_bytes": size,
                "writable_holders": [],
            })
            cohort_quiescence_sha = (
                cohort_quiescence["record_sha256"]
            )
            _write_json(
                batch / v3.QUIESCENCE_DIRECTORY
                / f"lane-{lane}-descendant-{descendant}.json",
                cohort_quiescence,
            )
        rollback_quiescence.append(v3.seal({
            "schema_version": 3,
            "kind": v3.QUIESCENCE_KIND,
            "lane_index": lane,
            "descendant_index": descendant,
            "new_root_identity": identity,
            "new_pid": pid,
            "new_proc_start_ticks": ticks,
            "state": "INACTIVE_UNCHECKPOINTED",
            "pid_identity_alive": False,
            "checkpoint_commit_sha256": None,
            "proof_sha256": digest,
            "proof_bytes": size,
            "writable_holders": [],
        }))
        unsigned = {
            "lane_index": lane,
            "global_leaf_index": lane,
            "descendant_index": descendant,
            "descendant_sha256": descendant_sha,
            "new_root_identity": identity,
            "new_session_sha256": session_sha,
            "new_start_commit_sha256": start_sha,
            "new_pid": pid,
            "new_proc_start_ticks": ticks,
            "permit_binding_sha256": permit_sha,
            "prepared_target_sha256": target_record["record_sha256"],
            "started_worker_journal_sha256":
                started_record["record_sha256"],
        }
        fence = v3.canonical_sha256(unsigned)
        bindings.append({
            **unsigned,
            "fence_sha256": fence,
            "cohort_index": descendant,
            "handoff_state":
                "CHECKPOINTED" if descendant == 0 else "RUNNING",
            "cohort_quiescence_sha256": cohort_quiescence_sha,
        })
        active_by_root[str(new_root)] = {
            "pid": pid,
            "proc_start_ticks": ticks,
            "self_sha256": start_sha,
        }
    commit = v3.seal({
        "schema_version": 3,
        "kind": v3.HANDOFF_KIND,
        "gate": v3.GATE,
        "test_only": True,
        "production_eligible": False,
        "authenticated": False,
        "launch_authorized": False,
        "scientific_claim": False,
        "historical_atomic_handoff_observed": True,
        "batch_root": str(batch),
        "batch_root_identity": batch_identity,
        "batch_manifest_sha256": batch_sha,
        "switch_evidence_sha256": switch_sha,
        "switch_observation_policy":
            v3.base._observation_policy(1.0, [0.0] * 4),
        "prepared_retirement_sha256": prepared_sha,
        "retired_locks": retirements,
        "root_bindings": bindings,
        "fence_sha256s": [item["fence_sha256"] for item in bindings],
        "cohort_policy": {
            "target_keys": [
                [lane, descendant]
                for lane, descendant in v3.TARGET_KEYS
            ],
            "target_count": 8,
            "cohort_count": 2,
            "cohort_size": 4,
            "max_live_workers": 4,
            "checkpointed_at_commit": 4,
            "running_at_commit": 4,
        },
        "source_binding": v3._v3_source_binding(),
        "root_link_policy": {},
        "claim_scope": {},
    })
    commit_path = batch / v3.HANDOFF_COMMIT
    _write_json(commit_path, commit)
    return {
        "batch": batch,
        "commit": commit,
        "commit_path": commit_path,
        "switch_sha": switch_sha,
        "switch_record": switch_record,
        "batch_sha": batch_sha,
        "retirements": retirements,
        "bindings": bindings,
        "quiescence": rollback_quiescence,
        "new_roots": new_roots,
        "active_by_root": active_by_root,
    }


def _verify_fixture(fixture: dict[str, Any]) -> dict[str, Any]:
    return v3.verify_committed_handoff(
        fixture["commit_path"],
        expected_batch_commit_sha256=fixture["commit"]["record_sha256"],
        expected_switch_evidence_sha256=fixture["switch_sha"],
        expected_batch_manifest_sha256=fixture["batch_sha"],
    )


def _patch_committed_runtime(
    monkeypatch: pytest.MonkeyPatch, fixture: dict[str, Any],
) -> None:
    class FakeController:
        def _active_commit(
            self, generation_dir: Path, generation: int,
        ) -> dict[str, Any]:
            assert generation == 0
            new_root = generation_dir.parents[3]
            return dict(fixture["active_by_root"][str(new_root)])

    class FakeEnvironment:
        def __enter__(self) -> None:
            return None

        def __exit__(self, *args: Any) -> None:
            return None

    class FakeChild:
        RUNTIME_ROOT = Path("runtime/dmtcp")
        controller = FakeController()

        @staticmethod
        def _fixed_environment() -> FakeEnvironment:
            return FakeEnvironment()

    def inspect(child: Any, root: Path) -> dict[str, Any]:
        del child
        active = fixture["active_by_root"][str(root)]
        return {
            "hash_verification_requested": True,
            "state": "INACTIVE_UNCHECKPOINTED",
            "generations": [{
                "generation": 0,
                "pid_identity_alive": False,
                "checkpointed": False,
                "active_manifest_sha256": active["self_sha256"],
                "poison_claim": None,
            }],
        }

    monkeypatch.setattr(
        v3.base, "_discover_sources", lambda *args, **kwargs: {}
    )
    monkeypatch.setattr(
        v3, "_load_legacy_exact",
        lambda discovery: (None, FakeChild(), []),
    )
    monkeypatch.setattr(v3, "_direct_controller_inspect", inspect)
    monkeypatch.setattr(
        v3, "_writable_holders", lambda path, **kwargs: []
    )
    monkeypatch.setattr(
        v3, "validate_switch_record_structure", lambda record: {}
    )


def test_committed_rollback_retires_new_before_old_replay_and_marker_rejects_resume(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _committed_fixture(tmp_path)
    assert _verify_fixture(fixture)["valid"] is True
    _patch_committed_runtime(monkeypatch, fixture)

    def replay(root: Path, **kwargs: Any) -> dict[str, Any]:
        assert root == fixture["batch"]
        assert (
            kwargs["expected_batch_manifest_sha256"]
            == fixture["batch_sha"]
        )
        assert (
            kwargs["expected_switch_record"]
            == fixture["switch_record"]
        )
        # This callback runs only after the transition point.  New entry points
        # must already be absent while all old entry points are restored.
        for new_root in fixture["new_roots"]:
            assert not (new_root / ".adaptive-child.lock").exists()
            assert not (new_root / "runtime/dmtcp/.controller.lock").exists()
        for item in fixture["retirements"]:
            assert Path(item["original_path"]).is_file()
            assert not Path(item["retired_path"]).exists()
        return v3.seal({
            "schema_version": 3,
            "kind": "test-old-replay",
            "batch_manifest_sha256": fixture["batch_sha"],
        })

    monkeypatch.setattr(v3, "_fresh_restored_old_checkpoint", replay)
    result = v3.rollback_committed_handoff(
        fixture["commit_path"],
        expected_batch_commit_sha256=fixture["commit"]["record_sha256"],
        expected_switch_evidence_sha256=fixture["switch_sha"],
        expected_batch_manifest_sha256=fixture["batch_sha"],
        expected_switch_record=fixture["switch_record"],
        quiescence_records=fixture["quiescence"],
    )
    assert result["old_checkpoint_replayed"] is True
    assert result["new_workers_quiescent"] is True
    assert len(result["retired_new_locks"]) == 16
    assert len(result["restored_old_locks"]) == 9
    with pytest.raises(v3.AdaptiveSwitchEvidenceV3Error, match="rolled back"):
        _verify_fixture(fixture)


def test_committed_rollback_retires_old_again_if_replay_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _committed_fixture(tmp_path)
    _patch_committed_runtime(monkeypatch, fixture)

    def fail_replay(*args: Any, **kwargs: Any) -> dict[str, Any]:
        raise RuntimeError("injected replay failure")

    monkeypatch.setattr(v3, "_fresh_restored_old_checkpoint", fail_replay)
    with pytest.raises(RuntimeError, match="injected replay failure"):
        v3.rollback_committed_handoff(
            fixture["commit_path"],
            expected_batch_commit_sha256=fixture["commit"]["record_sha256"],
            expected_switch_evidence_sha256=fixture["switch_sha"],
            expected_batch_manifest_sha256=fixture["batch_sha"],
            expected_switch_record=fixture["switch_record"],
            quiescence_records=fixture["quiescence"],
        )
    for item in fixture["retirements"]:
        assert not Path(item["original_path"]).exists()
        assert Path(item["retired_path"]).is_file()
    for new_root in fixture["new_roots"]:
        assert not (new_root / ".adaptive-child.lock").exists()
        assert not (new_root / "runtime/dmtcp/.controller.lock").exists()
    assert not (fixture["batch"] / v3.ROLLBACK_COMMIT).exists()


def test_new_root_fence_is_nonblocking_and_exclusive(tmp_path: Path) -> None:
    identities: list[dict[str, Any]] = []
    for lane, descendant in v3.TARGET_KEYS:
        root = tmp_path / f"root-{lane}-{descendant}"
        identities.append(_root(root))
        _lock_file(root / ".adaptive-child.lock")
        _lock_file(root / "runtime/dmtcp/.controller.lock")
    locks = v3._acquire_new_root_fences(identities)
    assert len(locks) == 16
    fd = os.open(
        Path(identities[0]["path"]) / ".adaptive-child.lock",
        os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW,
    )
    try:
        with pytest.raises(BlockingIOError) as captured:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        assert captured.value.errno in {errno.EAGAIN, errno.EWOULDBLOCK}
    finally:
        os.close(fd)
        v3._close_locks(locks)


def test_cohort_transition_lock_plan_keeps_eight_outer_and_adds_four_controller(
    tmp_path: Path,
) -> None:
    identities: dict[tuple[int, int], dict[str, Any]] = {}
    for key in v3.TARGET_KEYS:
        root = tmp_path / f"cohort-{key[0]}-{key[1]}"
        identities[key] = _root(root)
        _lock_file(root / ".adaptive-child.lock")
        if key[1] == 0:
            _lock_file(root / "runtime/dmtcp/.controller.lock")
    all_identities = [identities[key] for key in v3.TARGET_KEYS]
    cohort0 = [
        identities[key] for key in v3.TARGET_KEYS if key[1] == 0
    ]
    outer = v3._acquire_new_root_fences(
        all_identities, controller_root_identities=[]
    )
    try:
        controllers = v3._acquire_new_root_fences(
            all_identities,
            controller_root_identities=cohort0,
            already_held=outer,
        )
        try:
            assert len(outer) == 8
            assert len(controllers) == 4
            assert all(
                "new-controller:" in item.role
                for item in controllers
            )
        finally:
            v3._close_locks(controllers)
    finally:
        v3._close_locks(outer)


def test_quiescence_pid_fields_are_strict_ints(tmp_path: Path) -> None:
    root = tmp_path / "root"
    identity = _root(root)
    valid = v3.seal({
        "schema_version": 3,
        "kind": v3.QUIESCENCE_KIND,
        "lane_index": 0,
        "descendant_index": 0,
        "new_root_identity": identity,
        "new_pid": 123,
        "new_proc_start_ticks": 456,
        "state": "CHECKPOINTED",
        "pid_identity_alive": False,
        "checkpoint_commit_sha256": H,
        "proof_sha256": H,
        "proof_bytes": 0,
        "writable_holders": [],
    })
    assert v3._validate_quiescence_record(valid)["new_pid"] == 123
    invalid = dict(valid)
    invalid["new_pid"] = True
    invalid.pop("record_sha256")
    invalid = v3.seal(invalid)
    with pytest.raises(v3.AdaptiveSwitchEvidenceV3Error):
        v3._validate_quiescence_record(invalid)


def test_precommit_rollback_retires_all_prepared_outer_locks(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    batch = tmp_path / "precommit-batch"
    _root(batch)
    lock_specs: list[tuple[str, Path, int]] = [
        ("batch", batch / ".batch.lock", fcntl.LOCK_EX)
    ]
    for lane in range(4):
        lane_root = batch / "lanes" / f"lane-{lane}"
        lock_specs.append((
            f"lane-{lane}", lane_root / ".hierarchical-resume.lock",
            fcntl.LOCK_EX,
        ))
    for lane in range(4):
        lane_root = batch / "lanes" / f"lane-{lane}"
        lock_specs.append((
            f"controller-{lane}",
            lane_root / "runtime/dmtcp/.controller.lock",
            fcntl.LOCK_SH,
        ))
    old_locks: list[Any] = []
    for role, path, operation in lock_specs:
        _lock_file(path)
        old_locks.append(v3.base._HeldLock(path, role, operation))
    ordered = [*old_locks[5:], *old_locks[1:5], old_locks[0]]
    retirements: list[dict[str, Any]] = []
    for sequence, held in enumerate(ordered):
        record = v3._retire_lock_v3(
            held,
            held.original_path.with_name(
                held.original_path.name + ".retired-v3-precommit-fixture"
            ),
        )
        retirements.append({"sequence": sequence, **record})
    switch_record = {
        "record_sha256": "e" * 64,
        "batch_manifest_sha256": "d" * 64,
    }
    lease = v3.AtomicSwitchLease(
        batch, old_locks, {}, object(), object(), object(), [], {}, [], {},
        switch_record, timeout_seconds=1.0,
        elapsed_seconds_by_lane=[0.0] * 4, candidate_only=False,
        v3_sources={},
    )
    lease._prepared = {"record_sha256": "f" * 64}
    lease._retired_records = retirements
    new_roots: list[Path] = []
    runner_locks: list[Any] = []
    for lane, descendant in v3.TARGET_KEYS:
        new_root = (
            tmp_path / f"prepared-only-{lane}-{descendant}"
        )
        identity = _root(new_root)
        new_roots.append(new_root)
        outer = new_root / ".adaptive-child.lock"
        _lock_file(outer)
        runner_locks.append(
            v3.base._HeldLock(
                outer, f"runner-{lane}-{descendant}",
                fcntl.LOCK_EX,
            )
        )
        lease._target_records[(lane, descendant)] = {
            "new_root_identity": identity,
        }
    monkeypatch.setattr(
        v3.AtomicSwitchLease, "_old_post_retirement_fence",
        lambda self: None,
    )
    lease.adopt_prepared_outer_locks(
        outer_lock_fds=[item.fd for item in runner_locks]
    )
    # Transfer closes the caller copies without LOCK_UN; v3's dup keeps the
    # same open-file-description flock continuously held.
    for item in runner_locks:
        os.close(item.fd)
        item.fd = -1
    monkeypatch.setattr(v3.base, "_snapshot_locked", lambda *args: {})
    monkeypatch.setattr(
        v3.base, "_build_record",
        lambda *args, **kwargs: dict(switch_record),
    )
    try:
        result = lease.rollback_after_new_quiescent(
            quiescence_records=[],
            not_started_target_keys=list(v3.TARGET_KEYS),
        )
        assert len(result["retired_new_locks"]) == 8
        for new_root in new_roots:
            assert not (new_root / ".adaptive-child.lock").exists()
            assert not (new_root / "runtime/dmtcp").exists()
        for retirement in retirements:
            assert Path(retirement["original_path"]).is_file()
            assert not Path(retirement["retired_path"]).exists()
    finally:
        lease._close()


@pytest.mark.parametrize(
    "fault",
    [*(f"retire-{index}" for index in range(9)),
     "plan-drift", "prepared-publish", "post-fence"],
)
def test_pre_yield_retirement_faults_restore_all_old_entrypoints(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, fault: str,
) -> None:
    batch = tmp_path / f"fault-{fault}"
    _root(batch)
    specs: list[tuple[str, Path, int]] = [
        ("batch", batch / ".batch.lock", fcntl.LOCK_EX),
    ]
    for lane in range(4):
        specs.append((
            f"lane-{lane}",
            batch / "lanes" / f"lane-{lane}"
            / ".hierarchical-resume.lock",
            fcntl.LOCK_EX,
        ))
    for lane in range(4):
        specs.append((
            f"controller-{lane}",
            batch / "lanes" / f"lane-{lane}"
            / "runtime/dmtcp/.controller.lock",
            fcntl.LOCK_SH,
        ))
    locks: list[Any] = []
    for role, path, operation in specs:
        _lock_file(path)
        locks.append(v3.base._HeldLock(path, role, operation))
    switch_record = v3.seal({
        "batch_manifest_sha256": "9" * 64,
    })
    lease = v3.AtomicSwitchLease(
        batch, locks, {}, object(), object(), object(), [], {}, [], {},
        switch_record, timeout_seconds=1.0,
        elapsed_seconds_by_lane=[0.0] * 4, candidate_only=False,
        v3_sources={},
    )
    replay_count = 0

    def replay(*args: Any, **kwargs: Any) -> dict[str, Any]:
        nonlocal replay_count
        replay_count += 1
        return dict(switch_record)

    monkeypatch.setattr(v3.base, "_snapshot_locked", lambda *args: {})
    monkeypatch.setattr(v3.base, "_build_record", replay)
    real_retire = v3._retire_lock_v3
    if fault.startswith("retire-"):
        fail_index = int(fault.removeprefix("retire-"))
        calls = 0

        def injected_retire(held: Any, target: Path) -> dict[str, Any]:
            nonlocal calls
            if calls == fail_index:
                raise RuntimeError("injected retirement fault")
            calls += 1
            return real_retire(held, target)

        monkeypatch.setattr(v3, "_retire_lock_v3", injected_retire)
    elif fault == "plan-drift":
        calls = 0

        def drift_retire(held: Any, target: Path) -> dict[str, Any]:
            nonlocal calls
            record = real_retire(held, target)
            calls += 1
            if calls == 1:
                record["role"] = "injected-drift"
            return record

        monkeypatch.setattr(v3, "_retire_lock_v3", drift_retire)
    elif fault == "prepared-publish":
        real_publish = v3._publish

        def fail_prepared(
            path: Path, record: dict[str, Any],
        ) -> None:
            if path == batch / v3.PREPARED_COMMIT:
                raise RuntimeError("injected PREPARED publish fault")
            real_publish(path, record)

        monkeypatch.setattr(v3, "_publish", fail_prepared)
    if fault == "post-fence":
        monkeypatch.setattr(
            v3.AtomicSwitchLease, "_old_post_retirement_fence",
            lambda self: (_ for _ in ()).throw(
                RuntimeError("injected post-retirement fence fault")
            ),
        )
    else:
        monkeypatch.setattr(
            v3.AtomicSwitchLease, "_old_post_retirement_fence",
            lambda self: None,
        )
    try:
        with pytest.raises(Exception):
            lease.prepare_retirement()
        assert replay_count == 1
        assert lease._prepared is None
        assert lease._retired_records == []
        assert lease.started_target_keys() == ()
        suffix = switch_record["record_sha256"][:16]
        for held in locks:
            assert held.current_path == held.original_path
            assert held.original_path.is_file()
            assert not held.original_path.with_name(
                held.original_path.name + f".retired-v3-{suffix}"
            ).exists()
            assert (
                v3.base._stat_identity(held.original_path.lstat())
                == v3.base._stat_identity(os.fstat(held.fd))
            )
        assert (batch / v3.PREPARED_COMMIT).exists() is (
            fault == "post-fence"
        )
    finally:
        lease._close()

def test_fresh_restored_checkpoint_replays_full_real_switch_record(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    batch = tmp_path / "real-switch-replay"
    _root(batch)
    expected = _valid_switch_record(batch)
    # This is the public, non-monkeypatched v2 structural validator.
    structural = v3.validate_switch_record_structure(expected)
    assert structural["valid"] is True
    snapshot = {
        "manifest": {"record_sha256": expected["batch_manifest_sha256"]},
        "checkpoint_result": {"record_sha256": "2" * 64},
        "lanes": [
            {
                "chain": {
                    "record_sha256": lane["transport_chain_sha256"],
                    "latest_proof_prefix":
                        dict(lane["checkpoint_proof_prefix"]),
                },
            }
            for lane in expected["lanes"]
        ],
    }
    monkeypatch.setattr(v3.base, "_discover_sources", lambda *args, **kwargs: {})
    monkeypatch.setattr(
        v3, "_load_legacy_exact",
        lambda *args, **kwargs: (object(), object(), []),
    )
    monkeypatch.setattr(
        v3, "_load_overlay_exact",
        lambda *args, **kwargs: (object(), {}, []),
    )
    monkeypatch.setattr(v3.base, "_snapshot_locked", lambda *args: snapshot)
    monkeypatch.setattr(
        v3.base, "_build_record",
        lambda *args, **kwargs: dict(expected),
    )
    result = v3._fresh_restored_old_checkpoint(
        batch,
        expected_batch_manifest_sha256=expected["batch_manifest_sha256"],
        expected_switch_evidence_sha256=expected["record_sha256"],
        expected_switch_record=expected,
        switch_observation_policy=expected["observation_policy"],
    )
    assert result["exact_switch_record_rebuilt"] is True
    assert (
        result["switch_evidence_sha256"] == expected["record_sha256"]
    )

@pytest.mark.parametrize("publish_then_throw", [False, True])
def test_note_started_journal_fault_preserves_process_local_started_truth(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    publish_then_throw: bool,
) -> None:
    batch = tmp_path / f"started-fault-{int(publish_then_throw)}"
    _root(batch)
    (batch / v3.STARTED_DIRECTORY).mkdir(mode=0o700)
    specs: list[tuple[str, Path, int]] = [
        ("batch", batch / ".batch.lock", fcntl.LOCK_EX),
    ]
    for lane in range(4):
        specs.append((
            f"lane-{lane}",
            batch / "lanes" / f"lane-{lane}"
            / ".hierarchical-resume.lock",
            fcntl.LOCK_EX,
        ))
    for lane in range(4):
        specs.append((
            f"controller-{lane}",
            batch / "lanes" / f"lane-{lane}"
            / "runtime/dmtcp/.controller.lock",
            fcntl.LOCK_SH,
        ))
    locks: list[Any] = []
    for role, path, operation in specs:
        _lock_file(path)
        locks.append(v3.base._HeldLock(path, role, operation))
    ordered = [*locks[5:], *locks[1:5], locks[0]]
    retirements: list[dict[str, Any]] = []
    for sequence, held in enumerate(ordered):
        retirement = v3._retire_lock_v3(
            held,
            held.original_path.with_name(
                held.original_path.name + ".retired-v3-note-fixture"
            ),
        )
        retirements.append({"sequence": sequence, **retirement})
    switch = v3.seal({"batch_manifest_sha256": "d" * 64})
    lease = v3.AtomicSwitchLease(
        batch, locks, {}, object(), object(), object(), [], {}, [], {},
        switch, timeout_seconds=1.0,
        elapsed_seconds_by_lane=[0.0] * 4, candidate_only=False,
        v3_sources={},
    )
    lease._retired_records = retirements
    lease._prepared = {"record_sha256": "e" * 64}
    for position, key in enumerate(v3.TARGET_KEYS):
        target_root = tmp_path / f"started-target-{position}"
        identity = _root(target_root)
        lease._target_records[key] = {
            "record_sha256": f"{position + 1:064x}",
            "new_root_identity": identity,
        }
    # note_started_worker only needs proof of continuous outer ownership here;
    # adoption itself has a separate real-FD test.
    lease._outer_locks = [object() for _ in v3.TARGET_KEYS]
    key = (0, 0)
    permit = v3.base.LaunchPermit(
        lease, lane_index=key[0], global_leaf_index=0,
        descendant_index=key[1], descendant_sha256=H,
        overlay_manifest_sha256=H, hard_evidence_sha256=H,
    )
    lease._permits[key] = permit
    ticks = 777
    monkeypatch.setattr(v3.base, "_proc_start_ticks", lambda pid: ticks)
    real_publish = v3._publish

    def injected_publish(path: Path, record: dict[str, Any]) -> None:
        if publish_then_throw:
            real_publish(path, record)
        raise RuntimeError("injected started-journal publish fault")

    monkeypatch.setattr(v3, "_publish", injected_publish)
    try:
        with pytest.raises(RuntimeError, match="started-journal"):
            lease.note_started_worker(
                permit=permit,
                new_root_identity=lease._target_records[key][
                    "new_root_identity"
                ],
                new_pid=os.getpid(), new_proc_start_ticks=ticks,
            )
        assert lease.started_target_keys() == (key,)
        started = lease._started_workers[key]
        journal_path = (
            batch / v3.STARTED_DIRECTORY
            / "lane-0-descendant-0.json"
        )
        assert journal_path.exists() is publish_then_throw
        if publish_then_throw:
            persisted = json.loads(journal_path.read_text(encoding="ascii"))
            assert (
                persisted["record_sha256"]
                == started.started_worker_journal_sha256
            )
    finally:
        lease._outer_locks = []
        lease._close()

def test_real_lease_cohort_transition_keeps_eight_outer_and_adds_four_controller(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    batch = tmp_path / "cohort-integration"
    _root(batch)
    for relative in (
        v3.TARGET_DIRECTORY,
        v3.STARTED_DIRECTORY,
        v3.QUIESCENCE_DIRECTORY,
    ):
        (batch / relative).mkdir(mode=0o700)
    specs: list[tuple[str, Path, int]] = [
        ("batch", batch / ".batch.lock", fcntl.LOCK_EX),
    ]
    for lane in range(4):
        specs.append((
            f"lane-{lane}",
            batch / "lanes" / f"lane-{lane}"
            / ".hierarchical-resume.lock",
            fcntl.LOCK_EX,
        ))
    for lane in range(4):
        specs.append((
            f"controller-{lane}",
            batch / "lanes" / f"lane-{lane}"
            / "runtime/dmtcp/.controller.lock",
            fcntl.LOCK_SH,
        ))
    old_locks: list[Any] = []
    for role, path, operation in specs:
        _lock_file(path)
        old_locks.append(v3.base._HeldLock(path, role, operation))
    ordered = [*old_locks[5:], *old_locks[1:5], old_locks[0]]
    retirements: list[dict[str, Any]] = []
    for sequence, held in enumerate(ordered):
        retirement = v3._retire_lock_v3(
            held,
            held.original_path.with_name(
                held.original_path.name + ".retired-v3-cohort-fixture"
            ),
        )
        retirements.append({"sequence": sequence, **retirement})
    switch = v3.seal({"batch_manifest_sha256": "d" * 64})
    lease = v3.AtomicSwitchLease(
        batch, old_locks, {}, object(), object(), object(), [], {}, [], {},
        switch, timeout_seconds=1.0,
        elapsed_seconds_by_lane=[0.0] * 4, candidate_only=False,
        v3_sources={},
    )
    lease._retired_records = retirements
    lease._prepared = {"record_sha256": "e" * 64}
    monkeypatch.setattr(
        v3.AtomicSwitchLease, "_old_post_retirement_fence",
        lambda self: None,
    )
    ticks_by_pid = {
        10_000 + lane: 20_000 + lane for lane in range(4)
    }
    monkeypatch.setattr(
        v3.base, "_proc_start_ticks", lambda pid: ticks_by_pid[pid],
    )
    monkeypatch.setattr(
        v3.AtomicSwitchLease, "_verify_quiescent_worker",
        lambda self, key, record, **kwargs:
            v3._validate_quiescence_record(record),
    )
    runner_locks: list[Any] = []
    identities: dict[tuple[int, int], dict[str, Any]] = {}
    try:
        for position, key in enumerate(v3.TARGET_KEYS):
            lane, descendant = key
            new_root = tmp_path / f"cohort-target-{lane}-{descendant}"
            identity = _root(new_root)
            identities[key] = identity
            _lock_file(new_root / ".adaptive-child.lock")
            runner_locks.append(v3.base._HeldLock(
                new_root / ".adaptive-child.lock",
                f"runner-{lane}-{descendant}", fcntl.LOCK_EX,
            ))
            permit = v3.base.LaunchPermit(
                lease, lane_index=lane, global_leaf_index=lane,
                descendant_index=descendant,
                descendant_sha256=f"{position + 1:064x}",
                overlay_manifest_sha256=f"{position + 21:064x}",
                hard_evidence_sha256=f"{lane + 41:064x}",
            )
            lease._permits[key] = permit
            prepared = lease.prepare_target(
                permit=permit, new_root_identity=identity,
            )
            assert (
                prepared["descendant_index"] == descendant
                and prepared["lane_index"] == lane
            )
        lease.adopt_prepared_outer_locks(
            outer_lock_fds=[item.fd for item in runner_locks],
        )
        for item in runner_locks:
            os.close(item.fd)
            item.fd = -1
        assert len(lease._outer_locks) == v3.TARGET_COUNT

        quiescence: list[dict[str, Any]] = []
        for lane in range(4):
            key = (lane, 0)
            permit = lease._permits[key]
            pid = 10_000 + lane
            ticks = ticks_by_pid[pid]
            started = lease.note_started_worker(
                permit=permit,
                new_root_identity=identities[key],
                new_pid=pid, new_proc_start_ticks=ticks,
            )
            fence = lease.post_start_fence(
                permit=permit, started_worker=started,
                new_session_sha256=f"{lane + 51:064x}",
                new_start_commit_sha256=f"{lane + 61:064x}",
            )
            assert fence.descendant_index == 0
            _lock_file(
                Path(identities[key]["path"])
                / "runtime/dmtcp/.controller.lock"
            )
            quiescence.append(v3.seal({
                "schema_version": v3.SCHEMA_VERSION,
                "kind": v3.QUIESCENCE_KIND,
                "lane_index": lane,
                "descendant_index": 0,
                "new_root_identity": identities[key],
                "new_pid": pid,
                "new_proc_start_ticks": ticks,
                "state": "CHECKPOINTED",
                "pid_identity_alive": False,
                "checkpoint_commit_sha256": f"{lane + 71:064x}",
                "proof_sha256": f"{lane + 81:064x}",
                "proof_bytes": 0,
                "writable_holders": [],
            }))
        transition = lease.note_cohort_checkpointed(
            quiescence_records=quiescence,
        )
        assert type(transition) is v3.CohortTransitionPermit
        assert len(lease._outer_locks) == 8
        assert len(lease._cohort_locks) == 4
        assert {
            Path(item.current_path)
            for item in lease._cohort_locks
        } == {
            Path(identities[(lane, 0)]["path"])
            / "runtime/dmtcp/.controller.lock"
            for lane in range(4)
        }
        assert len(list((batch / v3.TARGET_DIRECTORY).iterdir())) == 8
        assert len(list((batch / v3.STARTED_DIRECTORY).iterdir())) == 4
        assert len(list((batch / v3.QUIESCENCE_DIRECTORY).iterdir())) == 4
    finally:
        lease._close()
        for item in runner_locks:
            item.close()
