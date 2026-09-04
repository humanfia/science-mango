from __future__ import annotations

import importlib.util
from pathlib import Path

from investigations import paper400_dic5_recursive_split_v1 as recursive


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "paper400_dic5_recursive_initial_batch_dispatch_v1.py"
)
SPEC = importlib.util.spec_from_file_location("recursive_initial_batch_dispatch_v1_test", SOURCE)
assert SPEC is not None and SPEC.loader is not None
initial = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(initial)


class _Process:
    def __init__(self, events: list[tuple[str, str]], root: Path) -> None:
        self.events = events
        self.root = root
        self.returncode = 0

    def communicate(self) -> tuple[bytes, bytes]:
        self.events.append(("communicate", self.root.name))
        return b"", b""


def test_all_children_are_spawned_before_any_start_result_is_observed(tmp_path: Path, monkeypatch) -> None:
    bundle = tmp_path / "bundle"
    bundle.mkdir(mode=0o700)
    bundle.chmod(0o700)
    (bundle / "workers").mkdir(mode=0o700)
    (bundle / "children").mkdir(mode=0o700)
    steps: list[dict] = []
    items: list[dict] = []
    for ordinal, path in enumerate(("00", "01", "10", "11")):
        token = f"{ordinal + 1:064x}"
        item_id = f"leaf:{path}"
        worker = {
            "worker_sha256": f"{ordinal + 11:064x}",
            "token": token,
            "worker_id": f"worker-{ordinal}",
            "cpu_ids": [20 + ordinal],
            "child_root": str(bundle / "children" / path),
            "item_id": item_id,
        }
        steps.append({
            "ordinal": ordinal,
            "item_id": item_id,
            "path": path,
            "worker": worker,
            "after_queue": {"queue_sha256": f"{ordinal + 21:064x}", "items": []},
        })
        items.append({"item_id": item_id, "path": path, "state": "CLAIMED", "cpu_ids": [20 + ordinal]})
    loaded = {
        "root": bundle,
        "plan": {"steps": steps},
        "parent": b"parent",
        "manifest": {},
        "audit": {},
        "bundle": {"bundle_sha256": "f" * 64},
    }
    events: list[tuple[str, str]] = []
    monkeypatch.setattr(initial.recursive, "load_split_queue", lambda _path: {"items": items})
    monkeypatch.setattr(initial.batch, "_claim_at_step", lambda _step: {})
    monkeypatch.setattr(
        initial.batch,
        "_start_intent_value",
        lambda _plan, step: {"record_sha256": f"{step['ordinal'] + 31:064x}"},
    )
    monkeypatch.setattr(initial, "_existing_initial_orphan", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(
        initial.supervisor.child_runner,
        "prepare_root_from_material",
        lambda root, **_kwargs: events.append(("prepare", Path(root).name)),
    )
    monkeypatch.setattr(
        initial.batch,
        "_spawn_child_start",
        lambda root, *, cpu: (events.append(("spawn", Path(root).name)) or _Process(events, Path(root))),
    )
    monkeypatch.setattr(
        initial.batch,
        "_sealed_session_after_external_start",
        lambda root: {"record_sha256": f"{int(Path(root).name, 2) + 41:064x}"},
    )
    monkeypatch.setattr(
        initial.batch,
        "_start_receipt_value",
        lambda intent, session: {"record_sha256": session["record_sha256"], "intent": intent["record_sha256"]},
    )

    result = initial._start_all(loaded)

    assert [event for event, _name in events[:4]] == ["prepare"] * 4
    assert [event for event, _name in events[4:8]] == ["spawn"] * 4
    assert [event for event, _name in events[8:]] == ["communicate"] * 4
    assert {entry["item_id"] for entry in result} == {item["item_id"] for item in items}


def test_initial_claim_ledger_replays_all_claims_from_the_pristine_queue(tmp_path: Path, monkeypatch) -> None:
    bundle = tmp_path / "bundle"
    bundle.mkdir(mode=0o700)
    bundle.chmod(0o700)
    (bundle / "workers").mkdir(mode=0o700)
    parent = b"p cnf 3 3\n1 2 0\n-1 3 0\n-2 -3 0\n"
    manifest, _payloads = recursive.build_split_manifest(
        parent, parent_id="parent-g000000", fanout=2, split_variables=[1],
    )
    queue = recursive.create_split_queue(
        bundle / "queue.json", manifest, cpu_pool=[20, 21],
        parent_manifest_sha256="a" * 64,
    )
    loaded = {
        "root": bundle,
        "bundle": {"bundle_sha256": "b" * 64, "queue_sha256": queue["queue_sha256"]},
        "manifest": manifest,
        "queue": queue,
    }
    monkeypatch.setattr(initial.recovery, "_require_checkpoint_receipt", lambda _loaded: {"record_sha256": "c" * 64})

    committed = initial._ensure_claims_committed(loaded, worker_prefix="test-initial")
    replay = initial._ensure_claims_committed(loaded, worker_prefix="must-not-replace-plan")

    final_queue = recursive.load_split_queue(bundle / "queue.json")
    assert [item["state"] for item in final_queue["items"]] == ["CLAIMED", "CLAIMED"]
    assert final_queue["event_sequence"] == 2
    assert committed["plan"]["record_sha256"] == replay["plan"]["record_sha256"]
    assert committed["ledger"]["final_queue_sha256"] == final_queue["queue_sha256"]
    assert (bundle / initial.LEDGER).exists()
    assert (bundle / initial.COMMIT).exists()
