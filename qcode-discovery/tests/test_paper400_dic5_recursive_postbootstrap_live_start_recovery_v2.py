from __future__ import annotations

import contextlib
import importlib.util
from pathlib import Path

import pytest


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "paper400_dic5_recursive_postbootstrap_live_start_recovery_v2.py"
)
SPEC = importlib.util.spec_from_file_location("recursive_postbootstrap_live_start_recovery_v2_test", SOURCE)
assert SPEC is not None and SPEC.loader is not None
live = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(live)


def _step(tmp_path: Path) -> tuple[dict, dict, dict, Path, dict, dict]:
    bundle = tmp_path / "bundle"
    bundle.mkdir(mode=0o700)
    bundle.chmod(0o700)
    (bundle / "workers").mkdir(mode=0o700)
    (bundle / "children").mkdir(mode=0o700)
    (bundle / live.batch.STARTS_DIR).mkdir(mode=0o700, parents=True)
    child = bundle / "children" / "10"
    child.mkdir(mode=0o700)
    worker = {
        "worker_sha256": "a" * 64,
        "token": "b" * 64,
        "cpu_ids": [17],
        "child_root": str(child),
        "item_id": "leaf:10",
    }
    step = {"ordinal": 0, "item_id": "leaf:10", "path": "10", "worker": worker}
    plan = {"record_sha256": "c" * 64}
    loaded = {"root": bundle, "bundle": {"bundle_sha256": "d" * 64}}
    intent = {"record_sha256": "e" * 64}
    orphan = {"worker_sha256": "f" * 64}
    return loaded, plan, step, bundle, intent, orphan


def _patch_step_context(
    monkeypatch: pytest.MonkeyPatch, *, loaded: dict, step: dict, intent: dict, orphan: dict,
) -> None:
    monkeypatch.setattr(live.batch, "_start_intent_value", lambda _plan, _step: intent)
    monkeypatch.setattr(
        live.recovery,
        "_worker_context",
        lambda _loaded, **_kwargs: (
            {"path": step["path"]}, Path(loaded["root"]) / "workers" / "worker.json",
            step["worker"], orphan, {},
        ),
    )
    monkeypatch.setattr(live, "_source_binding", lambda: {"test": True})
    monkeypatch.setattr(
        live, "_receipt_value",
        lambda *_args, **_kwargs: {"record_sha256": "1" * 64},
    )


def test_live_compatibility_session_is_recorded_without_restarting_child(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    loaded, plan, step, bundle, intent, orphan = _step(tmp_path)
    _patch_step_context(monkeypatch, loaded=loaded, step=step, intent=intent, orphan=orphan)
    intent_path, started_path = live._step_paths(bundle, step)
    live.supervisor._publish_json(intent_path, intent)
    session = {"record_sha256": "2" * 64}
    monkeypatch.setattr(
        live.compat, "seal_live_session",
        lambda _root, *, cpu: {"state": "LIVE_SESSION_SEALED", "session": session, "receipt": {}},
    )
    monkeypatch.setattr(
        live.batch,
        "_start_receipt_value",
        lambda _intent, sealed: {"record_sha256": sealed["record_sha256"], "intent": _intent["record_sha256"]},
    )

    result = live._recover_step(
        loaded, plan=plan, step=step,
        checkpoint_receipt={"record_sha256": "3" * 64},
        checkpoint_chain={"latest_checkpoint_sha256": "4" * 64},
    )

    assert result["state"] == "LIVE_SESSION_SEALED"
    assert live.supervisor._read_json(started_path)["record_sha256"] == session["record_sha256"]
    assert live.supervisor._read_json(live._receipt_path(bundle, step))["record_sha256"] == "1" * 64


def test_exact_stopped_sibling_is_deferred_without_writing_a_terminal_claim(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    loaded, plan, step, bundle, intent, orphan = _step(tmp_path)
    _patch_step_context(monkeypatch, loaded=loaded, step=step, intent=intent, orphan=orphan)
    intent_path, started_path = live._step_paths(bundle, step)
    live.supervisor._publish_json(intent_path, intent)

    def stopped(_root: Path, *, cpu: int) -> dict:
        raise live.compat.LiveSessionCompatError("not live")

    monkeypatch.setattr(live.compat, "seal_live_session", stopped)
    monkeypatch.setattr(live, "_exact_stopped_fast_context", lambda _root: True)

    result = live._recover_step(
        loaded, plan=plan, step=step,
        checkpoint_receipt={"record_sha256": "3" * 64},
        checkpoint_chain={"latest_checkpoint_sha256": "4" * 64},
    )

    assert result["state"] == "FAST_TERMINAL_STILL_UNRESOLVED"
    assert not started_path.exists()
    assert not live._receipt_path(bundle, step).exists()


def test_recovery_continues_after_one_deferred_sibling(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    bundle = tmp_path / "bundle"
    bundle.mkdir(mode=0o700)
    bundle.chmod(0o700)
    plan_path = bundle / live.batch.PLAN
    plan_path.parent.mkdir(mode=0o700)
    plan_path.write_text("{}")
    parent = tmp_path / "parent"
    parent.mkdir()
    control = tmp_path / "control"
    control.mkdir(mode=0o700)
    loaded = {
        "root": bundle,
        "bundle": {"bundle_sha256": "a" * 64},
        "audit": {"parent_root": str(parent)},
        "control_root": control,
        "queue_progress_bootstrap_required": False,
    }
    steps = [
        {"item_id": "leaf:01"},
        {"item_id": "leaf:10"},
        {"item_id": "leaf:11"},
    ]
    plan = {"record_sha256": "b" * 64, "steps": steps}
    seen: list[str] = []
    monkeypatch.setattr(live, "_recovery_lock", lambda _bundle: contextlib.nullcontext())
    monkeypatch.setattr(live.recovery, "_load_recovery_bundle", lambda _bundle, **_kwargs: loaded)
    monkeypatch.setattr(live.recovery, "_require_checkpoint_receipt", lambda _loaded: {"record_sha256": "c" * 64})
    monkeypatch.setattr(live.supervisor, "_read_json", lambda _path: plan)
    monkeypatch.setattr(live.batch, "_validate_plan", lambda _loaded, _plan: plan)
    monkeypatch.setattr(live.recovery, "_legacy_shared_lock", lambda _root: contextlib.nullcontext())
    monkeypatch.setattr(live.recovery, "_checked_checkpointed_parent", lambda _loaded: ({}, {"latest_checkpoint_sha256": "d" * 64}))
    monkeypatch.setattr(live.supervisor, "_catalog_lock", lambda _root: contextlib.nullcontext())
    monkeypatch.setattr(live.recovery, "_require_reserved_cpu_leases", lambda _loaded: None)
    monkeypatch.setattr(live.recovery, "_require_dispatchable_queue_state", lambda _loaded: set())
    monkeypatch.setattr(live, "_source_binding", lambda: {"test": True})

    def recover(_loaded: dict, **kwargs: object) -> dict:
        step = kwargs["step"]
        assert isinstance(step, dict)
        seen.append(step["item_id"])
        if step["item_id"] == "leaf:01":
            return {"item_id": "leaf:01", "state": "RECOVERY_DEFERRED", "hardness_only": True, "solver_terminal_claim": False}
        return {"item_id": step["item_id"], "state": "LIVE_SESSION_SEALED", "hardness_only": True, "solver_terminal_claim": False}

    monkeypatch.setattr(live, "_recover_step", recover)
    result = live.recover_live_starts(bundle)

    assert seen == ["leaf:01", "leaf:10", "leaf:11"]
    assert [entry["state"] for entry in result["children"]] == [
        "RECOVERY_DEFERRED", "LIVE_SESSION_SEALED", "LIVE_SESSION_SEALED",
    ]
