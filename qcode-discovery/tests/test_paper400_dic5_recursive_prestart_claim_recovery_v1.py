from __future__ import annotations

import contextlib
import importlib.util
from pathlib import Path

import pytest


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "paper400_dic5_recursive_prestart_claim_recovery_v1.py"
)
SPEC = importlib.util.spec_from_file_location("recursive_prestart_claim_recovery_v1_test", SOURCE)
assert SPEC is not None and SPEC.loader is not None
prestart = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(prestart)


def _fixture(tmp_path: Path) -> tuple[dict, dict, dict, Path, dict]:
    control = tmp_path / "control"
    control.mkdir(mode=0o700)
    control.chmod(0o700)
    bundle = control / "bundle"
    bundle.mkdir(mode=0o700)
    bundle.chmod(0o700)
    workers = bundle / "workers"
    children = bundle / "children"
    workers.mkdir(mode=0o700)
    children.mkdir(mode=0o700)
    root = tmp_path / "parent"
    root.mkdir(mode=0o700)
    root.chmod(0o700)
    (root / ".hierarchical-resume.lock").write_bytes(b"")
    (root / ".hierarchical-resume.lock").chmod(0o600)

    item = {
        "item_id": "leaf:00",
        "item_sha256": "a" * 64,
        "leaf_id": "leaf:00",
        "leaf_sha256": "b" * 64,
        "path": "00",
        "state": "CLAIMED",
        "attempts": 0,
        "last_error": None,
        "certificate_sha256": None,
        "cpu_ids": [7],
        "claim": {
            "token": "c" * 64,
            "worker_id": "worker",
            "cpu_ids": [7],
            "lease_expires_at": 123.0,
        },
    }
    queue = {"queue_sha256": "d" * 64, "event_sequence": 1, "items": [item]}
    worker_path = workers / "worker.json"
    worker_path.write_text("{}\n", encoding="utf-8")
    worker = {
        "state": "CLAIMED",
        "error": None,
        "queue_sha256_at_claim": queue["queue_sha256"],
        "item_id": item["item_id"],
        "leaf_id": item["leaf_id"],
        "leaf_sha256": item["leaf_sha256"],
        "token": item["claim"]["token"],
        "worker_id": item["claim"]["worker_id"],
        "cpu_ids": [7],
        "claim_expires_at": 123.0,
        "child_root": str(children / "00"),
        "worker_sha256": "e" * 64,
    }
    loaded = {
        "root": bundle,
        "control_root": control,
        "bundle": {"bundle_sha256": "f" * 64},
        "audit": {"parent_root": str(root)},
        "parent": b"p cnf 1 0\n",
        "manifest": {"manifest_sha256": "g" * 64},
        "queue_progress_bootstrap_required": True,
    }
    return loaded, item, queue, worker_path, worker


def test_claim_context_requires_no_child_evidence(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    loaded, item, queue, worker_path, worker = _fixture(tmp_path)
    monkeypatch.setattr(prestart.recursive, "load_split_queue", lambda _path: queue)
    monkeypatch.setattr(prestart.recovery, "_validate_bootstrap_queue_shape", lambda _queue: item)
    monkeypatch.setattr(prestart.supervisor, "_worker_records", lambda _loaded: [(worker_path, worker)])

    recovered = prestart._claim_context(loaded)
    assert recovered[0]["item_id"] == "leaf:00"
    assert recovered[2]["worker_sha256"] == worker["worker_sha256"]

    child_root = Path(worker["child_root"])
    child_root.mkdir(mode=0o700)
    with pytest.raises(prestart.PrestartClaimRecoveryError, match="runtime evidence"):
        prestart._claim_context(loaded)


def test_recovery_writes_intent_before_start_and_never_changes_queue(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    loaded, item, queue, worker_path, worker = _fixture(tmp_path)
    receipt = {"record_sha256": "h" * 64}
    started: list[tuple[Path, int]] = []
    prepared: list[Path] = []

    monkeypatch.setattr(prestart.recovery, "_load_recovery_bundle", lambda *_args, **_kwargs: loaded)
    monkeypatch.setattr(prestart.recovery, "_require_checkpoint_receipt", lambda _loaded: receipt)
    monkeypatch.setattr(prestart.recovery, "_legacy_shared_lock", lambda _root: contextlib.nullcontext())
    monkeypatch.setattr(prestart.recovery, "_checked_checkpointed_parent", lambda _loaded: ({}, {}))
    monkeypatch.setattr(prestart.recovery, "_require_reserved_cpu_leases", lambda _loaded: None)
    monkeypatch.setattr(prestart.supervisor, "_catalog_lock", lambda _root: contextlib.nullcontext())
    monkeypatch.setattr(prestart, "_claim_context", lambda _loaded: (item, worker_path, worker, queue))
    monkeypatch.setattr(prestart, "_source_binding", lambda: {"test": True})
    monkeypatch.setattr(
        prestart.supervisor.child_runner,
        "prepare_root_from_material",
        lambda child_root, **_kwargs: prepared.append(child_root),
    )
    monkeypatch.setattr(
        prestart.supervisor.child_runner,
        "start_root",
        lambda child_root, *, cpu: started.append((child_root, cpu)) or {"record_sha256": "1" * 64},
    )

    result = prestart.recover_prestart_claim(
        Path(loaded["root"]), control_root=Path(loaded["control_root"]),
    )

    child_root = Path(worker["child_root"])
    assert prepared == [child_root]
    assert started == [(child_root, 7)]
    assert result["already_started"] is False
    sidecar = Path(loaded["root"]) / prestart.INTENT_DIR
    assert (sidecar / prestart.INTENT_PATH.name).exists()
    assert (sidecar / prestart.STARTED_PATH.name).exists()
    assert queue["event_sequence"] == 1
    assert item["state"] == "CLAIMED"


def test_start_failure_leaves_an_orphan_and_refuses_to_hide_it(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    loaded, item, queue, worker_path, worker = _fixture(tmp_path)
    receipt = {"record_sha256": "h" * 64}
    monkeypatch.setattr(prestart.recovery, "_load_recovery_bundle", lambda *_args, **_kwargs: loaded)
    monkeypatch.setattr(prestart.recovery, "_require_checkpoint_receipt", lambda _loaded: receipt)
    monkeypatch.setattr(prestart.recovery, "_legacy_shared_lock", lambda _root: contextlib.nullcontext())
    monkeypatch.setattr(prestart.recovery, "_checked_checkpointed_parent", lambda _loaded: ({}, {}))
    monkeypatch.setattr(prestart.recovery, "_require_reserved_cpu_leases", lambda _loaded: None)
    monkeypatch.setattr(prestart.supervisor, "_catalog_lock", lambda _root: contextlib.nullcontext())
    monkeypatch.setattr(prestart, "_claim_context", lambda _loaded: (item, worker_path, worker, queue))
    monkeypatch.setattr(prestart, "_source_binding", lambda: {"test": True})
    monkeypatch.setattr(prestart.supervisor.child_runner, "prepare_root_from_material", lambda *_args, **_kwargs: None)

    def fail_start(_root: Path, *, cpu: int) -> dict:
        raise RuntimeError(f"test failure on cpu {cpu}")

    monkeypatch.setattr(prestart.supervisor.child_runner, "start_root", fail_start)
    with pytest.raises(RuntimeError, match="test failure"):
        prestart.recover_prestart_claim(
            Path(loaded["root"]), control_root=Path(loaded["control_root"]),
        )
    assert worker_path.with_name(worker_path.stem + ".orphan.json").exists()
