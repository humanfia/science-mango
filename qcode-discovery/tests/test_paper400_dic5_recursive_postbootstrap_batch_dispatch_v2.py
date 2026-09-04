from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

from investigations import paper400_dic5_recursive_split_v1 as recursive
from scripts import paper400_dic5_recursive_postbootstrap_batch_dispatch_v1 as batch


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "paper400_dic5_recursive_postbootstrap_batch_dispatch_v2.py"
)
SPEC = importlib.util.spec_from_file_location("recursive_postbootstrap_batch_dispatch_v2_test", SOURCE)
assert SPEC is not None and SPEC.loader is not None
v2 = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(v2)


PARENT_DIMACS = b"""p cnf 4 4
1 -2 0
2 3 0
-3 4 0
-1 -4 0
"""


def _fixture(tmp_path: Path, *, fanout: int) -> tuple[dict, dict, Path]:
    control = tmp_path / "control"
    control.mkdir(mode=0o700)
    control.chmod(0o700)
    bundle_root = control / "bundle"
    bundle_root.mkdir(mode=0o700)
    bundle_root.chmod(0o700)
    (bundle_root / "workers").mkdir(mode=0o700)
    (bundle_root / "children").mkdir(mode=0o700)
    parent = tmp_path / "parent"
    parent.mkdir(mode=0o700)
    parent.chmod(0o700)
    (parent / ".hierarchical-resume.lock").write_bytes(b"")
    (parent / ".hierarchical-resume.lock").chmod(0o600)
    manifest, _ = recursive.build_split_manifest(
        PARENT_DIMACS,
        parent_id="parent-g000000",
        fanout=fanout,
        split_variables=[1, 2, 3][: {2: 1, 4: 2}[fanout]],
    )
    queue = recursive.create_split_queue(
        bundle_root / batch.supervisor.QUEUE,
        manifest,
        cpu_pool=list(range(32, 32 + fanout)),
        parent_manifest_sha256="a" * 64,
        now=100.0,
    )
    loaded = {
        "root": bundle_root,
        "control_root": control,
        "bundle": {"bundle_sha256": "b" * 64},
        "audit": {"parent_root": str(parent)},
        "parent": PARENT_DIMACS,
        "manifest": manifest,
    }
    return loaded, queue, bundle_root


def _plan(tmp_path: Path, monkeypatch: pytest.MonkeyPatch, *, fanout: int) -> tuple[dict, dict, Path]:
    loaded, _queue, root = _fixture(tmp_path, fanout=fanout)
    monkeypatch.setattr(batch.recovery, "_require_checkpoint_receipt", lambda _loaded: {"record_sha256": "c" * 64})
    plan = batch._plan_value(loaded, worker_prefix="batch-v2-test", now=200.0)
    recursive._atomic_write_queue(root / batch.supervisor.QUEUE, plan["steps"][-1]["after_queue"])
    return loaded, plan, root


class _Process:
    def __init__(self, returncode: int, stderr: bytes = b"") -> None:
        self.returncode = returncode
        self.stderr = stderr

    def communicate(self) -> tuple[None, bytes]:
        return None, self.stderr


def test_visibility_retry_seals_live_child_without_writing_false_orphan(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    loaded, plan, bundle_root = _plan(tmp_path, monkeypatch, fanout=4)
    prepared: list[Path] = []
    spawned: list[Path] = []
    retried: list[tuple[Path, int]] = []

    def prepare(root: Path, **_kwargs: object) -> None:
        prepared.append(root)
        root.mkdir(mode=0o700)

    def spawn(root: Path, *, cpu: int) -> _Process:
        assert len(list((bundle_root / batch.STARTS_DIR).glob("*.intent.json"))) == 4
        assert prepared == [Path(step["worker"]["child_root"]) for step in plan["steps"]]
        spawned.append(root)
        if len(spawned) == 1:
            return _Process(2, b"ERROR: unsealed child start commit is not live and bound\n")
        return _Process(0)

    def sealed(root: Path) -> dict:
        ordinal = next(index for index, step in enumerate(plan["steps"]) if Path(step["worker"]["child_root"]) == root)
        return {"record_sha256": f"{ordinal + 2:064x}"}

    def retry(root: Path, *, cpu: int) -> dict:
        retried.append((root, cpu))
        return {"record_sha256": "1" * 64}

    monkeypatch.setattr(batch.supervisor.child_runner, "prepare_root_from_material", prepare)
    monkeypatch.setattr(batch, "_spawn_child_start", spawn)
    monkeypatch.setattr(batch, "_sealed_session_after_external_start", sealed)
    monkeypatch.setattr(v2, "_retry_visible_live_session", retry)

    results = v2._start_all_v2(loaded, plan)
    first = plan["steps"][0]
    assert spawned == [Path(step["worker"]["child_root"]) for step in plan["steps"]]
    assert retried == [(Path(first["worker"]["child_root"]), first["worker"]["cpu_ids"][0])]
    assert results[0]["state"] == "LIVE_SESSION_SEALED_AFTER_VISIBILITY_RETRY"
    assert all(result["state"] in {"RUNNING", "LIVE_SESSION_SEALED_AFTER_VISIBILITY_RETRY"} for result in results)
    orphan = bundle_root / "workers" / first["worker_filename"].replace(".json", ".orphan.json")
    assert not orphan.exists()
    assert len(list((bundle_root / batch.STARTS_DIR).glob("*.started.json"))) == 4


def test_exact_quiescent_fast_terminal_keeps_fast_orphan_but_launches_sibling(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    loaded, plan, bundle_root = _plan(tmp_path, monkeypatch, fanout=2)
    spawned: list[Path] = []

    def prepare(root: Path, **_kwargs: object) -> None:
        root.mkdir(mode=0o700)

    def spawn(root: Path, *, cpu: int) -> _Process:
        spawned.append(root)
        if len(spawned) == 1:
            return _Process(2, b"ERROR: unsealed child start commit is not live and bound\n")
        return _Process(0)

    monkeypatch.setattr(batch.supervisor.child_runner, "prepare_root_from_material", prepare)
    monkeypatch.setattr(batch, "_spawn_child_start", spawn)
    monkeypatch.setattr(batch, "_sealed_session_after_external_start", lambda _root: {"record_sha256": "2" * 64})
    monkeypatch.setattr(v2, "_retry_visible_live_session", lambda _root, *, cpu: None)

    results = v2._start_all_v2(loaded, plan)
    first = plan["steps"][0]
    assert len(spawned) == 2
    assert results[0]["state"] == "FAST_TERMINAL_ORPHAN"
    assert results[1]["state"] == "RUNNING"
    orphan = batch.supervisor._read_json(
        bundle_root / "workers" / first["worker_filename"].replace(".json", ".orphan.json")
    )
    assert orphan["error"] == batch.recovery.FAST_START_ERROR
