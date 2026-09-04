from __future__ import annotations

import copy
import contextlib
import importlib.util
import os
from pathlib import Path

import pytest

from investigations import paper400_dic5_recursive_split_v1 as recursive


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "paper400_dic5_recursive_checkpoint_recovery_v1.py"
)
SPEC = importlib.util.spec_from_file_location("recursive_checkpoint_recovery_v1_test", SOURCE)
assert SPEC is not None and SPEC.loader is not None
recovery = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(recovery)


def _status(root: Path, *, state: str = "CHECKPOINTED") -> dict:
    chain = {
        "state": state,
        "latest_checkpoint_sha256": "c" * 64 if state == "CHECKPOINTED" else None,
        "total_checkpoint_image_bytes": 123,
        "generations": [
            {
                "generation": 0,
                "active_kind": "start.commit",
                "active_manifest_sha256": "start",
                "pid": 123,
                "proc_start_ticks": 456,
                "pid_identity_alive": False,
                "checkpoint_manifest_sha256": "c" * 64 if state == "CHECKPOINTED" else None,
                "image_bytes": 123,
            }
        ],
    }
    result = {
        "root": str(root),
        "resume_static_sha256": "a" * 64,
        "session_sha256": "b" * 64,
        "terminal_claimed": False,
        "terminal_committed": False,
        "record_sha256": "d" * 64,
        "chain": chain,
    }
    return {"action": "status", "returncode": 0, "stdout_sha256": "e" * 64, "stderr_sha256": "f" * 64, "result": result}


def _loaded(tmp_path: Path) -> dict:
    control = tmp_path / "control"
    control.mkdir(mode=0o700)
    control.chmod(0o700)
    bundle = control / "bundle"
    bundle.mkdir(mode=0o700)
    bundle.chmod(0o700)
    (bundle / "workers").mkdir(mode=0o700)
    (bundle / "children").mkdir(mode=0o700)
    root = tmp_path / "parent"
    root.mkdir(mode=0o700)
    root.chmod(0o700)
    lock = root / ".hierarchical-resume.lock"
    lock.write_bytes(b"")
    lock.chmod(0o600)
    state = root / "state"
    state.mkdir(mode=0o700)
    session = {"record_sha256": "b" * 64, "controller_start_sha256": "start"}
    # The unit tests isolate chain validation, so this minimal JSON is read by
    # a patched supervisor reader rather than the production parser.
    (state / "11-session.json").write_text("{}\n", encoding="utf-8")
    return {
        "root": bundle,
        "control_root": control,
        "bundle": {"bundle_sha256": "z" * 64},
        "audit": {
            "parent_root": str(root),
            "parent_root_identity": recovery.supervisor._root_identity(root),
            "parent_static_sha256": "a" * 64,
            "parent_session_sha256": "b" * 64,
            "parent_generation": 0,
            "parent_pid": 123,
            "parent_proc_start_ticks": 456,
        },
        "queue": {"queue_sha256": "q" * 64},
        "reservation": {"cpus": [7], "reservation_sha256": "r" * 64},
        "session": session,
    }


def test_checkpoint_chain_requires_exact_checkpointed_status(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    loaded = _loaded(tmp_path)
    root = Path(loaded["audit"]["parent_root"])
    monkeypatch.setattr(recovery.supervisor, "_read_json", lambda _path: loaded["session"])
    assert recovery._checkpoint_chain_from_status(loaded, _status(root))["state"] == "CHECKPOINTED"
    with pytest.raises(recovery.RecursiveCheckpointRecoveryError, match="not CHECKPOINTED"):
        recovery._checkpoint_chain_from_status(loaded, _status(root, state="INACTIVE_UNCHECKPOINTED"))


def test_checked_parent_uses_chain_state_not_a_missing_top_level_field(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    loaded = _loaded(tmp_path)
    root = Path(loaded["audit"]["parent_root"])
    monkeypatch.setattr(recovery.supervisor, "_legacy_terminal_absent", lambda _root: None)
    monkeypatch.setattr(recovery.supervisor, "_legacy_cli", lambda *_args, **_kwargs: _status(root))
    monkeypatch.setattr(recovery.supervisor, "_read_json", lambda _path: loaded["session"])

    observation, chain = recovery._checked_checkpointed_parent(loaded)
    assert observation["result"].get("state") is None
    assert chain["state"] == "CHECKPOINTED"


def test_dispatch_uses_checked_chain_before_claiming_child(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    loaded = _loaded(tmp_path)
    root = Path(loaded["audit"]["parent_root"])
    loaded["parent"] = b"p cnf 1 0\n"
    loaded["manifest"] = {"manifest_sha256": "m" * 64}
    claim = {
        "item": {"item_id": "leaf:0", "path": "0", "cpu_ids": [7], "item_sha256": "a" * 64},
        "claim": {"token": "b" * 64, "worker_id": "test", "cpu_ids": [7]},
    }
    claims = iter([claim, None])
    published: list[Path] = []
    prepared: list[Path] = []
    started: list[tuple[Path, int]] = []

    monkeypatch.setattr(recovery.supervisor, "_load_bundle", lambda *_args, **_kwargs: loaded)
    monkeypatch.setattr(recovery, "_require_checkpoint_receipt", lambda _loaded: {"ok": True})
    monkeypatch.setattr(
        recovery,
        "_checked_checkpointed_parent",
        lambda _loaded: (_status(root), _status(root)["result"]["chain"]),
    )
    monkeypatch.setattr(recovery, "_require_dispatchable_queue_state", lambda _loaded: set())
    monkeypatch.setattr(recovery, "_require_reserved_cpu_leases", lambda _loaded: None)
    monkeypatch.setattr(recovery.supervisor, "_catalog_lock", lambda _root: contextlib.nullcontext())
    monkeypatch.setattr(recovery.supervisor, "_worker_records", lambda _loaded: [])
    monkeypatch.setattr(recovery.recursive, "claim_queue_item", lambda *_args, **_kwargs: next(claims))
    monkeypatch.setattr(
        recovery.supervisor,
        "_worker_value",
        lambda *_args, **_kwargs: {"worker": True, "worker_sha256": "c" * 64},
    )
    monkeypatch.setattr(
        recovery.supervisor,
        "_worker_path",
        lambda bundle, _item, _token: Path(bundle) / "workers" / "worker.json",
    )
    monkeypatch.setattr(recovery.supervisor, "_publish_json", lambda path, _value: published.append(path))
    monkeypatch.setattr(
        recovery.supervisor.child_runner,
        "prepare_root_from_material",
        lambda child_root, **_kwargs: prepared.append(child_root),
    )
    monkeypatch.setattr(
        recovery.supervisor.child_runner,
        "start_root",
        lambda child_root, *, cpu: started.append((child_root, cpu)) or {"state": "RUNNING"},
    )
    monkeypatch.setattr(recovery.supervisor, "_legacy_terminal_absent", lambda _root: None)
    queue_views = iter([
        {"queue_sha256": "d" * 64, "event_sequence": 0},
        {"queue_sha256": "e" * 64, "event_sequence": 1},
        {"queue_sha256": "e" * 64, "event_sequence": 1},
    ])
    monkeypatch.setattr(recovery.recursive, "load_split_queue", lambda *_args, **_kwargs: next(queue_views))
    monkeypatch.setattr(recovery, "_append_queue_transition", lambda *_args, **_kwargs: {"record_sha256": "f" * 64})

    result = recovery.dispatch_children(
        Path(loaded["root"]), control_root=Path(loaded["control_root"]), worker_prefix="test",
    )
    child_root = Path(loaded["root"]) / "children" / "0"
    assert prepared == [child_root]
    assert started == [(child_root, 7)]
    assert published == [Path(loaded["root"]) / "workers" / "worker.json"]
    assert result["children"][0]["item_id"] == "leaf:0"


def test_recovery_publishes_only_after_pristine_checkpointed_replay(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    loaded = _loaded(tmp_path)
    root = Path(loaded["audit"]["parent_root"])
    receipt_path = Path(loaded["root"]) / recovery.supervisor.PARENT_CHECKPOINT
    monkeypatch.setattr(recovery.supervisor, "_load_bundle", lambda *_args, **_kwargs: loaded)
    monkeypatch.setattr(recovery.supervisor, "_legacy_terminal_absent", lambda _root: None)
    monkeypatch.setattr(recovery, "_require_pending_pre_dispatch_state", lambda _loaded: None)
    monkeypatch.setattr(recovery, "_require_reserved_cpu_leases", lambda _loaded: None)
    monkeypatch.setattr(recovery.supervisor, "_legacy_cli", lambda *_args, **_kwargs: _status(root))
    original_read_json = recovery.supervisor._read_json
    monkeypatch.setattr(
        recovery.supervisor,
        "_read_json",
        lambda path: loaded["session"] if path.name == "11-session.json" else original_read_json(path),
    )
    monkeypatch.setattr(recovery, "_script_binding", lambda: {"test": True})
    monkeypatch.setattr(recovery.supervisor, "_catalog_lock", lambda _root: contextlib.nullcontext())

    receipt = recovery.recover_checkpoint_receipt(Path(loaded["root"]), control_root=Path(loaded["control_root"]))
    assert receipt_path.exists()
    assert receipt["kind"] == recovery.RECOVERY_KIND
    assert receipt["parent_state"] == "CHECKPOINTED"
    assert recursive.selfhash_valid(receipt, "record_sha256")
    assert recovery.recover_checkpoint_receipt(Path(loaded["root"]), control_root=Path(loaded["control_root"])) == receipt


def _fast_fixture(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple[dict, dict, Path, dict]:
    """Build a controller-free, immutable view for fast-terminal replay tests."""

    root = tmp_path / "fast-child"
    root.mkdir(mode=0o700)
    root.chmod(0o700)
    (root / "state").mkdir(mode=0o700)
    child = {
        "leaf_id": "leaf:00",
        "leaf_sha256": "a" * 64,
        "child_cnf_sha256": "b" * 64,
        "child_dimacs_sha256": "c" * 64,
        "child_num_variables": 4,
        "child_num_clauses": 5,
        "child_dimacs_bytes": 6,
    }
    child_loaded = {"static": {"static_sha256": "d" * 64, "child": child}, "policy": {}}
    proof = {
        "role": "raw-binary-drat",
        "relative_path": "runtime/dmtcp/proof.drat",
        "file_sha256": "e" * 64,
        "bytes": 1,
        "mode": 0o600,
        "device": 1,
        "inode": 2,
        "links": 1,
    }
    snapshot = recovery.supervisor.child_runner.seal(
        {
            "schema_version": 1,
            "kind": "paper400-dic5-recursive-stopped-proof-snapshot-v1",
            "transport_state": "INACTIVE_UNCHECKPOINTED",
            "controller_status_sha256": "f" * 64,
            "latest_generation": 0,
            "latest_pid": 123,
            "latest_proc_start_ticks": 456,
            "latest_pid_identity_alive": False,
            "proof": proof,
            "writable_holders": [],
        },
        "snapshot_sha256",
    )
    context = {
        "root": root,
        "claim": {"record_sha256": "a" * 64},
        "config": {"self_sha256": "b" * 64},
        "active": {"self_sha256": "c" * 64, "pid": 123, "proc_start_ticks": 456},
        "snapshot": snapshot,
        "stdout": {
            "role": "solver-stdout", "relative_path": "runtime/dmtcp/solver.stdout",
            "file_sha256": "d" * 64, "bytes": 16, "mode": 0o600,
            "device": 1, "inode": 3, "links": 1,
        },
        "stderr": {
            "role": "solver-stderr", "relative_path": "runtime/dmtcp/solver.stderr",
            "file_sha256": "e" * 64, "bytes": 0, "mode": 0o600,
            "device": 1, "inode": 4, "links": 1,
        },
    }
    item = {
        "item_id": "leaf:00", "item_sha256": "f" * 64, "leaf_id": child["leaf_id"],
        "leaf_sha256": child["leaf_sha256"], "path": "00", "state": "CLAIMED",
    }
    worker = {
        "worker_sha256": "a" * 64, "token": "b" * 64, "worker_id": "worker",
        "cpu_ids": [7], "leaf_id": child["leaf_id"], "leaf_sha256": child["leaf_sha256"],
        "child_root": str(root), "state": "CLAIMED",
    }
    orphan = {**worker, "worker_sha256": "c" * 64, "state": "ORPHAN_UNRESOLVED"}
    loaded = {
        "root": tmp_path / "bundle",
        "bundle": {"bundle_sha256": "d" * 64},
        "manifest": {"manifest_sha256": "e" * 64},
        "audit": {"audit_sha256": "f" * 64},
    }
    receipt = {"record_sha256": "a" * 64}
    monkeypatch.setattr(recovery.supervisor.child_runner, "_load_static", lambda _root: child_loaded)
    monkeypatch.setattr(recovery, "_fast_start_context", lambda _root, _loaded: context)
    monkeypatch.setattr(recovery, "_script_binding", lambda: {"test": True})
    monkeypatch.setattr(
        recovery,
        "_worker_context",
        lambda _loaded, *, item_id, require_live_claim: (item, root / "worker.json", worker, orphan, {"items": [item]}),
    )
    return loaded, receipt, root, context


def test_fast_recovery_replays_every_immutable_binding(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    loaded, receipt, root, context = _fast_fixture(tmp_path, monkeypatch)
    item, _path, worker, orphan, _queue = recovery._worker_context(
        loaded, item_id="leaf:00", require_live_claim=True,
    )
    record = recovery._fast_recovery_value(
        loaded, receipt, item=item, worker=worker, orphan=orphan, context=context,
    )
    recovery.supervisor._publish_json(root / recovery.FAST_RECOVERY, record)
    reread, _current, _worker_context = recovery._read_fast_recovery(
        loaded, receipt, root=root, require_live_claim=True,
    )
    assert reread == record

    changed = copy.deepcopy(context)
    changed["snapshot"]["latest_pid"] = 999
    monkeypatch.setattr(recovery, "_fast_start_context", lambda _root, _loaded: changed)
    with pytest.raises(recovery.RecursiveCheckpointRecoveryError, match="evidence changed"):
        recovery._read_fast_recovery(loaded, receipt, root=root, require_live_claim=True)


def test_fast_terminal_claim_reuses_standard_proof_chain_shape(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    loaded, receipt, root, context = _fast_fixture(tmp_path, monkeypatch)
    item, _path, worker, orphan, _queue = recovery._worker_context(
        loaded, item_id="leaf:00", require_live_claim=True,
    )
    fast_recovery = recovery._fast_recovery_value(
        loaded, receipt, item=item, worker=worker, orphan=orphan, context=context,
    )
    raw = context["snapshot"]["proof"]
    lrat = {**raw, "role": "converted-lrat", "relative_path": "artifacts/attempt/child.lrat", "inode": 9}
    check = {"record_sha256": "f" * 64}
    chain = recovery.supervisor.child_runner._proof_chain_value(
        raw=raw, lrat=lrat, drat_check=check, conversion=check, lrat_check=check,
        fresh_drat=check, fresh_lrat=check, snapshot=context["snapshot"],
    )
    claim = recovery._fast_terminal_claim_value(
        loaded, fast_recovery, root=root, proof_chain=chain,
    )
    recovery.supervisor._publish_json(root / recovery.FAST_TERMINAL_CLAIM, claim)
    assert recovery._read_fast_terminal_claim(loaded, fast_recovery, root=root) == claim
    certificate = recovery._fast_certificate_value(loaded, fast_recovery, claim, root=root)
    assert certificate["kind"] == recovery.FAST_CERTIFICATE_KIND
    assert certificate["leaf_id"] == "leaf:00"
    assert certificate["strict_proof_unsat"] is True


def test_fast_transcript_reader_requires_private_regular_file(tmp_path: Path) -> None:
    transcript = tmp_path / "solver.stdout"
    transcript.write_bytes(recovery.FAST_UNSAT_STDOUT)
    transcript.chmod(0o600)
    assert recovery._read_regular_bytes(transcript, cap=1024) == recovery.FAST_UNSAT_STDOUT
    transcript.chmod(0o644)
    with pytest.raises(recovery.RecursiveCheckpointRecoveryError, match="metadata is unsafe"):
        recovery._read_regular_bytes(transcript, cap=1024)
