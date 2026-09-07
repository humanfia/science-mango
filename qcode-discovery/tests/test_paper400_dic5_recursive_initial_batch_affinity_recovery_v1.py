from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "paper400_dic5_recursive_initial_batch_affinity_recovery_v1.py"
)
SPEC = importlib.util.spec_from_file_location("recursive_initial_batch_affinity_recovery_v1_test", SOURCE)
assert SPEC is not None and SPEC.loader is not None
affinity = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(affinity)


class _Process:
    def __init__(self, events: list[tuple[str, str]], root: Path) -> None:
        self.events = events
        self.root = root
        self.returncode = 0

    def communicate(self) -> tuple[bytes, bytes]:
        self.events.append(("communicate", self.root.name))
        return b"", b""


def _entry(ordinal: int, root: Path, *, cpu: int) -> dict:
    return {
        "ordinal": ordinal,
        "item_id": f"leaf:{ordinal}",
        "leaf_id": f"leaf:{ordinal}",
        "leaf_sha256": f"{ordinal + 1:064x}",
        "worker_sha256": f"{ordinal + 11:064x}",
        "orphan_sha256": f"{ordinal + 21:064x}",
        "child_root": str(root),
        "static_sha256": f"{ordinal + 31:064x}",
        "start_claim_sha256": f"{ordinal + 41:064x}",
        "expected_single_cpu": cpu,
        "admission": {
            "available_memory_bytes": 32,
            "available_disk_bytes": 32,
            "minimum_memory_bytes": 16,
            "minimum_disk_bytes": 16,
            "passed": True,
        },
    }


def test_launches_every_affinity_recovery_sibling_before_observing_results(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    bundle = tmp_path / "bundle"
    bundle.mkdir(mode=0o700)
    bundle.chmod(0o700)
    entries = [_entry(0, bundle / "child-0", cpu=7), _entry(1, bundle / "child-1", cpu=9)]
    plan = {"record_sha256": "a" * 64, "entries": entries}
    steps = [
        {"ordinal": entry["ordinal"], "item_id": entry["item_id"], "worker": {}}
        for entry in entries
    ]
    loaded = {"root": bundle, "plan": {"steps": steps}}
    events: list[tuple[str, str]] = []

    monkeypatch.setattr(affinity, "_source_binding", lambda: {"test": True})
    monkeypatch.setattr(affinity, "_require_affinity", lambda _entries: None)
    monkeypatch.setattr(
        affinity,
        "_child_context",
        lambda _loaded, *, step, require_live_claim, require_precontroller: {
            **next(entry for entry in entries if entry["item_id"] == step["item_id"]),
            "policy": {},
        },
    )
    monkeypatch.setattr(affinity, "_require_precontroller_layout", lambda _root: None)
    monkeypatch.setattr(affinity.supervisor.child_runner, "_resource_admission", lambda *_args: {})
    monkeypatch.setattr(
        affinity.batch,
        "_spawn_child_start",
        lambda root, *, cpu: (events.append(("spawn", Path(root).name)) or _Process(events, Path(root))),
    )
    monkeypatch.setattr(
        affinity.batch,
        "_sealed_session_after_external_start",
        lambda root: {
            "record_sha256": f"{100 + int(Path(root).name.rsplit("-", 1)[1]):064x}",
            "expected_single_cpu": 7 if Path(root).name.endswith("0") else 9,
        },
    )

    started = affinity._launch_all(loaded, plan)

    assert [kind for kind, _name in events[:2]] == ["spawn", "spawn"]
    assert [kind for kind, _name in events[2:]] == ["communicate", "communicate"]
    assert {value["expected_single_cpu"] for value in started} == {7, 9}
    assert not list((bundle / affinity.SIDECAR_DIR / "starts").glob("*.failure.json"))


def test_precontroller_layout_rejects_any_runtime_material(tmp_path: Path) -> None:
    root = tmp_path / "child"
    root.mkdir(mode=0o700)
    for name in ("static", "state", "artifacts", "runtime", "logs"):
        (root / name).mkdir(mode=0o700)
    (root / affinity.supervisor.child_runner.ROOT_LOCK).write_bytes(b"")
    (root / "state" / "00-recursive-static.json").write_text("{}\n", encoding="utf-8")
    (root / "state" / "05-start.claim.json").write_text("{}\n", encoding="utf-8")

    affinity._require_precontroller_layout(root)

    (root / affinity.supervisor.child_runner.RUNTIME_ROOT).mkdir()
    with pytest.raises(affinity.InitialBatchAffinityRecoveryError, match="controller-side evidence"):
        affinity._require_precontroller_layout(root)


def test_affinity_guard_rejects_a_dispatcher_mask_that_excludes_a_child(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(affinity.os, "sched_getaffinity", lambda _pid: {7})
    with pytest.raises(affinity.InitialBatchAffinityRecoveryError, match="affinity excludes"):
        affinity._require_affinity([
            {"expected_single_cpu": 7}, {"expected_single_cpu": 9},
        ])
