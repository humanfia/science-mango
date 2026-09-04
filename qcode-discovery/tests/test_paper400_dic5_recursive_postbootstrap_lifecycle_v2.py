from __future__ import annotations

import contextlib
import importlib.util
from pathlib import Path

from investigations import paper400_dic5_recursive_split_v1 as recursive
from scripts import paper400_dic5_recursive_checkpoint_recovery_v1 as recovery
from scripts import paper400_dic5_recursive_postbootstrap_batch_dispatch_v1 as batch
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "paper400_dic5_recursive_postbootstrap_lifecycle_v2.py"
)
SPEC = importlib.util.spec_from_file_location("recursive_postbootstrap_lifecycle_v2_test", SOURCE)
assert SPEC is not None and SPEC.loader is not None
lifecycle = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(lifecycle)


def test_baseline_queue_view_returns_a_copy_and_restores_loader(tmp_path: Path) -> None:
    bundle = tmp_path / "bundle"
    bundle.mkdir(mode=0o700)
    bundle.chmod(0o700)
    parent = b"p cnf 2 1\n1 2 0\n"
    manifest, _payloads = recursive.build_split_manifest(
        parent, parent_id="parent-g000000", fanout=2, split_variables=[1],
    )
    recursive.create_split_queue(
        bundle / supervisor.QUEUE, manifest, cpu_pool=[20, 21],
        parent_manifest_sha256="a" * 64,
    )
    baseline = recursive.claim_queue_item(
        bundle / supervisor.QUEUE, worker_id="worker", now=10.0,
    )
    assert baseline is not None
    baseline_queue = recursive.load_split_queue(bundle / supervisor.QUEUE)
    original = recursive.load_split_queue

    with lifecycle._baseline_queue_view(bundle, baseline_queue):
        observed = recursive.load_split_queue(bundle / supervisor.QUEUE)
        assert observed == baseline_queue
        observed["items"][0]["state"] = "BROKEN"
        assert recursive.load_split_queue(bundle / supervisor.QUEUE) == baseline_queue

    assert recursive.load_split_queue is original
    assert recursive.load_split_queue(bundle / supervisor.QUEUE) == baseline_queue


def test_adapter_seals_an_authenticated_postbootstrap_baseline(monkeypatch, tmp_path: Path) -> None:
    bundle = tmp_path / "bundle"
    control = tmp_path / "control"
    bundle.mkdir(mode=0o700)
    control.mkdir(mode=0o700)
    bundle.chmod(0o700)
    control.chmod(0o700)
    parent = b"p cnf 2 1\n1 2 0\n"
    manifest, _payloads = recursive.build_split_manifest(
        parent, parent_id="parent-g000000", fanout=2, split_variables=[1],
    )
    queue = recursive.create_split_queue(
        bundle / supervisor.QUEUE, manifest, cpu_pool=[20, 21],
        parent_manifest_sha256="a" * 64,
    )
    plan = {
        "record_sha256": "c" * 64,
        "steps": [{"after_queue": queue}],
    }
    ledger = {
        "record_sha256": "d" * 64,
        "after_queue_sha256": queue["queue_sha256"],
        "after_event_sequence": queue["event_sequence"],
    }
    loaded = {
        "root": bundle,
        "bundle": {"bundle_sha256": "a" * 64},
        "queue": queue,
        "control_root": control,
    }
    sidecar = batch._safe_sidecar_dir(bundle, batch.SIDECAR_DIR)
    supervisor._publish_json(sidecar / batch.PLAN.name, {"placeholder": True})
    commit = supervisor.seal(
        {
            "schema_version": batch.SCHEMA_VERSION,
            "kind": batch.COMMIT_KIND,
            "gate": batch.GATE,
            "bundle_sha256": "a" * 64,
            "plan_sha256": plan["record_sha256"],
            "queue_sha256": queue["queue_sha256"],
            "queue_event_sequence": queue["event_sequence"],
            "queue_ledger_sha256": ledger["record_sha256"],
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": batch._source_binding(),
        },
        "record_sha256",
    )
    supervisor._publish_json(sidecar / batch.COMMIT.name, commit)

    monkeypatch.setattr(recovery, "_load_recovery_bundle", lambda *_args, **_kwargs: dict(loaded))
    monkeypatch.setattr(batch, "_validate_plan", lambda *_args, **_kwargs: plan)
    monkeypatch.setattr(recovery, "_read_queue_ledger_records", lambda *_args, **_kwargs: [ledger])
    monkeypatch.setattr(recovery, "_require_checkpoint_receipt", lambda *_args, **_kwargs: {"record_sha256": "b" * 64})

    adapted = lifecycle._load_postbootstrap_batch(bundle, control_root=control)

    baseline_path = bundle / lifecycle.BASELINE
    assert baseline_path.exists()
    baseline = supervisor._read_json(baseline_path)
    assert recursive.selfhash_valid(baseline, "record_sha256")
    assert baseline["baseline_queue"] == queue
    assert adapted["initial_final_queue"] == queue
    assert adapted["initial_commit"] == commit


def test_runtime_applies_and_restores_postbootstrap_hooks(monkeypatch, tmp_path: Path) -> None:
    captured: dict[str, object] = {}
    old_gate = lifecycle.base.GATE
    old_loader = lifecycle.base._load_initial_batch
    old_aggregate = lifecycle.base._aggregate_if_complete
    old_verify = supervisor.child_runner.verify_final_root

    def fake_tick(_bundle: Path, *, control_root: Path) -> dict[str, object]:
        captured["gate"] = lifecycle.base.GATE
        captured["lock"] = lifecycle.base.LOCK
        captured["loader"] = lifecycle.base._load_initial_batch
        captured["aggregate"] = lifecycle.base._aggregate_if_complete
        captured["binding"] = lifecycle.base._source_binding()
        captured["verify"] = supervisor.child_runner.verify_final_root
        captured["control_root"] = control_root
        return {"ok": True}

    monkeypatch.setattr(lifecycle.base, "tick_bundle", fake_tick)
    monkeypatch.setattr(lifecycle.batch, "_batch_lock", lambda _bundle: contextlib.nullcontext())

    assert lifecycle.tick_bundle(tmp_path, control_root=tmp_path) == {"ok": True}
    assert captured["gate"] == lifecycle.GATE
    assert captured["lock"] == lifecycle.LOCK
    assert captured["loader"] is lifecycle._load_postbootstrap_batch
    assert captured["aggregate"] is lifecycle._aggregate_postbootstrap_if_complete
    assert captured["binding"] == lifecycle._source_binding()
    assert captured["verify"] is lifecycle.normal_v2.verify_normal_final_root_v2
    assert captured["control_root"] == tmp_path
    assert lifecycle.base.GATE == old_gate
    assert lifecycle.base._load_initial_batch is old_loader
    assert lifecycle.base._aggregate_if_complete is old_aggregate
    assert supervisor.child_runner.verify_final_root is old_verify
