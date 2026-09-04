from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

from investigations import paper400_dic5_recursive_split_v1 as recursive


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "paper400_dic5_recursive_postbootstrap_batch_dispatch_v1.py"
)
SPEC = importlib.util.spec_from_file_location("recursive_postbootstrap_batch_dispatch_v1_test", SOURCE)
assert SPEC is not None and SPEC.loader is not None
batch = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(batch)


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
    bundle = control / "bundle"
    bundle.mkdir(mode=0o700)
    bundle.chmod(0o700)
    (bundle / "workers").mkdir(mode=0o700)
    (bundle / "children").mkdir(mode=0o700)

    split_variables = [1, 2, 3][: {2: 1, 4: 2, 8: 3}[fanout]]
    manifest, _payloads = recursive.build_split_manifest(
        PARENT_DIMACS,
        parent_id="parent-g000000",
        fanout=fanout,
        split_variables=split_variables,
    )
    queue = recursive.create_split_queue(
        bundle / batch.supervisor.QUEUE,
        manifest,
        cpu_pool=list(range(32, 32 + fanout)),
        parent_manifest_sha256="a" * 64,
        now=100.0,
    )
    parent = tmp_path / "parent"
    parent.mkdir(mode=0o700)
    parent.chmod(0o700)
    (parent / ".hierarchical-resume.lock").write_bytes(b"")
    (parent / ".hierarchical-resume.lock").chmod(0o600)
    loaded = {
        "root": bundle,
        "control_root": control,
        "bundle": {"bundle_sha256": "b" * 64},
        "audit": {"parent_root": str(parent)},
        "parent": PARENT_DIMACS,
        "manifest": manifest,
        "reservation": {"cpus": list(range(32, 32 + fanout))},
    }
    return loaded, queue, bundle


def _receipt() -> dict:
    return {"record_sha256": "c" * 64}


@pytest.mark.parametrize("fanout", [2, 4, 8])
def test_plan_claims_every_pending_leaf_before_any_start(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, fanout: int,
) -> None:
    loaded, original, _bundle = _fixture(tmp_path, fanout=fanout)
    monkeypatch.setattr(batch.recovery, "_require_checkpoint_receipt", lambda _loaded: _receipt())

    plan = batch._plan_value(loaded, worker_prefix="batch-test", now=200.0)
    assert batch._validate_plan(loaded, plan) == plan
    assert len(plan["steps"]) == fanout
    assert plan["initial_queue_sha256"] == original["queue_sha256"]
    assert plan["final_event_sequence"] == original["event_sequence"] + fanout

    claimed_ids: list[str] = []
    leased: set[int] = set()
    for ordinal, step in enumerate(plan["steps"]):
        assert step["ordinal"] == ordinal
        assert step["before_queue"]["event_sequence"] == ordinal
        assert step["after_queue"]["event_sequence"] == ordinal + 1
        item = next(item for item in step["after_queue"]["items"] if item["item_id"] == step["item_id"])
        assert item["state"] == "CLAIMED"
        assert step["worker"]["queue_sha256_at_claim"] == step["after_queue"]["queue_sha256"]
        claimed_ids.append(item["item_id"])
        assert not leased.intersection(item["cpu_ids"])
        leased.update(item["cpu_ids"])
    assert len(set(claimed_ids)) == fanout
    assert len(leased) == fanout


def test_commit_publishes_all_workers_then_queue_ledger(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    loaded, _original, bundle = _fixture(tmp_path, fanout=4)
    monkeypatch.setattr(batch.recovery, "_require_checkpoint_receipt", lambda _loaded: _receipt())
    plan = batch._plan_value(loaded, worker_prefix="batch-test", now=200.0)

    records = [{"record_sha256": "d" * 64, "current_queue_sha256": plan["initial_queue_sha256"]}]
    appended: list[dict] = []

    def append(_loaded: dict, **kwargs: object) -> dict:
        before = kwargs["before"]
        after = kwargs["after"]
        assert before["queue_sha256"] == records[-1].get("current_queue_sha256")
        record = {
            "record_sha256": f"{len(records):064x}",
            "current_queue_sha256": after["queue_sha256"],
        }
        records.append(record)
        appended.append(dict(kwargs))
        return record

    monkeypatch.setattr(batch.recovery, "_read_queue_ledger_records", lambda _loaded: records)
    monkeypatch.setattr(batch.recovery, "_append_queue_transition", append)
    monkeypatch.setattr(batch, "_require_postbootstrap_bundle", lambda *_args, **_kwargs: loaded)
    monkeypatch.setattr(batch.recovery, "_require_dispatchable_queue_state", lambda _loaded: set())

    replay = batch._ensure_claims_committed(
        bundle, control_root=Path(loaded["control_root"]), plan=plan, loaded=loaded,
    )
    assert replay is loaded
    assert len(appended) == 4
    assert [entry["item_id"] for entry in appended] == [step["item_id"] for step in plan["steps"]]
    queue = recursive.load_split_queue(bundle / batch.supervisor.QUEUE)
    assert queue["queue_sha256"] == plan["final_queue_sha256"]
    for step in plan["steps"]:
        assert (bundle / "workers" / step["worker_filename"]).exists()
    assert (bundle / batch.SIDECAR_DIR / batch.COMMIT.name).exists()


def test_fast_terminal_does_not_prevent_later_sibling_starts(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    loaded, _original, bundle = _fixture(tmp_path, fanout=4)
    monkeypatch.setattr(batch.recovery, "_require_checkpoint_receipt", lambda _loaded: _receipt())
    plan = batch._plan_value(loaded, worker_prefix="batch-test", now=200.0)
    recursive._atomic_write_queue(bundle / batch.supervisor.QUEUE, plan["steps"][-1]["after_queue"])

    prepared: list[Path] = []
    spawned: list[Path] = []

    class Process:
        def __init__(self, root: Path, *, returncode: int, stderr: bytes) -> None:
            self.root = root
            self.returncode = returncode
            self.stderr = stderr

        def communicate(self) -> tuple[None, bytes]:
            return None, self.stderr

    def prepare(root: Path, **_kwargs: object) -> None:
        prepared.append(root)
        root.mkdir(mode=0o700)

    def spawn(root: Path, *, cpu: int) -> Process:
        assert len(list((bundle / batch.STARTS_DIR).glob("*.intent.json"))) == 4
        assert prepared == [Path(step["worker"]["child_root"]) for step in plan["steps"]]
        spawned.append(root)
        if len(spawned) == 1:
            return Process(
                root,
                returncode=2,
                stderr=b"ERROR: unsealed child start commit is not live and bound\n",
            )
        return Process(root, returncode=0, stderr=b"")

    def sealed(root: Path) -> dict:
        ordinal = next(
            index for index, step in enumerate(plan["steps"])
            if Path(step["worker"]["child_root"]) == root
        )
        return {"record_sha256": f"{ordinal + 1:064x}"}

    monkeypatch.setattr(batch.supervisor.child_runner, "prepare_root_from_material", prepare)
    monkeypatch.setattr(batch, "_spawn_child_start", spawn)
    monkeypatch.setattr(batch, "_sealed_session_after_external_start", sealed)

    results = batch._start_all(loaded, plan)
    assert spawned == [Path(step["worker"]["child_root"]) for step in plan["steps"]]
    assert results[0] == {"item_id": plan["steps"][0]["item_id"], "state": "FAST_TERMINAL_ORPHAN"}
    assert [result["state"] for result in results[1:]] == ["RUNNING", "RUNNING", "RUNNING"]
    first = plan["steps"][0]
    orphan_path = bundle / "workers" / first["worker_filename"].replace(".json", ".orphan.json")
    orphan = batch.supervisor._read_json(orphan_path)
    assert orphan["error"] == batch.recovery.FAST_START_ERROR
    assert orphan["queue_sha256_at_claim"] == first["after_queue"]["queue_sha256"]
    assert orphan["queue_sha256_at_claim"] != plan["final_queue_sha256"]


def test_interrupted_final_queue_replays_all_missing_transitions(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    loaded, _original, bundle = _fixture(tmp_path, fanout=2)
    monkeypatch.setattr(batch.recovery, "_require_checkpoint_receipt", lambda _loaded: _receipt())
    plan = batch._plan_value(loaded, worker_prefix="batch-test", now=200.0)
    sidecar = bundle / batch.SIDECAR_DIR
    sidecar.mkdir(mode=0o700)
    sidecar.chmod(0o700)
    batch.supervisor._publish_json(sidecar / batch.PLAN.name, plan)
    recursive._atomic_write_queue(bundle / batch.supervisor.QUEUE, plan["steps"][-1]["after_queue"])

    records = [{"record_sha256": "d" * 64, "current_queue_sha256": plan["initial_queue_sha256"]}]
    appended: list[str] = []

    def append(_loaded: dict, **kwargs: object) -> dict:
        after = kwargs["after"]
        appended.append(kwargs["item_id"])
        record = {
            "record_sha256": f"{len(records):064x}",
            "current_queue_sha256": after["queue_sha256"],
        }
        records.append(record)
        return record

    monkeypatch.setattr(batch, "_bare_loaded_for_interrupted_commit", lambda _bundle: loaded)
    monkeypatch.setattr(batch.recovery, "_read_queue_ledger_records", lambda _loaded: records)
    monkeypatch.setattr(batch.recovery, "_append_queue_transition", append)

    batch._recover_interrupted_final_queue(bundle)
    assert appended == [step["item_id"] for step in plan["steps"]]
    for step in plan["steps"]:
        assert (bundle / "workers" / step["worker_filename"]).exists()


def test_external_fast_terminal_classification_is_exact() -> None:
    assert batch._external_start_error(
        2, b"ERROR: unsealed child start commit is not live and bound\n",
    ) == batch.recovery.FAST_START_ERROR
    assert batch._external_start_error(2, b"ERROR: another failure\n") != batch.recovery.FAST_START_ERROR
