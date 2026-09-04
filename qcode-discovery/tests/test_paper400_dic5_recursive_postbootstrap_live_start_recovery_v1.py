from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "paper400_dic5_recursive_postbootstrap_live_start_recovery_v1.py"
)
SPEC = importlib.util.spec_from_file_location("recursive_postbootstrap_live_start_recovery_v1_test", SOURCE)
assert SPEC is not None and SPEC.loader is not None
live = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(live)


def _fixture(tmp_path: Path) -> tuple[dict, dict, dict, Path, dict, dict, dict]:
    control = tmp_path / "control"
    control.mkdir(mode=0o700)
    control.chmod(0o700)
    bundle = control / "bundle"
    bundle.mkdir(mode=0o700)
    bundle.chmod(0o700)
    (bundle / "workers").mkdir(mode=0o700)
    (bundle / "children").mkdir(mode=0o700)
    starts = bundle / live.batch.STARTS_DIR
    starts.mkdir(mode=0o700, parents=True)
    starts.chmod(0o700)
    child = bundle / "children" / "01"
    child.mkdir(mode=0o700)

    worker = {
        "worker_sha256": "a" * 64,
        "token": "b" * 64,
        "cpu_ids": [12],
        "child_root": str(child),
        "item_id": "leaf:01",
    }
    step = {"ordinal": 0, "item_id": "leaf:01", "path": "01", "worker": worker}
    plan = {"record_sha256": "c" * 64}
    loaded = {
        "root": bundle,
        "bundle": {"bundle_sha256": "d" * 64},
        "audit": {"parent_root": str(tmp_path / "parent")},
    }
    intent = {"record_sha256": "e" * 64}
    orphan = {"worker_sha256": "f" * 64}
    session = {"record_sha256": "1" * 64}
    return loaded, plan, step, bundle, intent, orphan, session


def _patch_context(
    monkeypatch: pytest.MonkeyPatch,
    *, loaded: dict, step: dict, intent: dict, orphan: dict, session: dict,
) -> None:
    monkeypatch.setattr(live, "_source_binding", lambda: {"test": True})
    monkeypatch.setattr(live.batch, "_start_intent_value", lambda _plan, _step: intent)
    monkeypatch.setattr(
        live.batch,
        "_start_receipt_value",
        lambda _intent, recovered: {"record_sha256": recovered["record_sha256"], "intent": _intent["record_sha256"]},
    )
    monkeypatch.setattr(
        live.recovery,
        "_worker_context",
        lambda _loaded, **_kwargs: (
            {"path": step["path"]}, Path(loaded["root"]) / "workers" / "worker.json",
            step["worker"], orphan, {},
        ),
    )
    monkeypatch.setattr(
        live.supervisor.child_runner,
        "start_root",
        lambda _root, *, cpu: session,
    )


def test_live_start_recovery_seals_session_and_retains_original_orphan(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    loaded, plan, step, bundle, intent, orphan, session = _fixture(tmp_path)
    _patch_context(
        monkeypatch, loaded=loaded, step=step, intent=intent, orphan=orphan, session=session,
    )
    intent_path, started_path = live._step_paths(bundle, step)
    live.supervisor._publish_json(intent_path, intent)

    result = live._recover_step(
        loaded,
        plan=plan,
        step=step,
        checkpoint_receipt={"record_sha256": "2" * 64},
        checkpoint_chain={"latest_checkpoint_sha256": "3" * 64},
    )

    assert result["state"] == "LIVE_SESSION_SEALED"
    assert result["session_sha256"] == session["record_sha256"]
    assert live.supervisor._read_json(started_path)["record_sha256"] == session["record_sha256"]
    receipt = live.supervisor._read_json(live._receipt_path(bundle, step))
    assert receipt["orphan_worker_sha256"] == orphan["worker_sha256"]
    assert receipt["session_sha256"] == session["record_sha256"]


def test_true_fast_terminal_remains_unresolved_without_new_receipts(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    loaded, plan, step, bundle, intent, orphan, session = _fixture(tmp_path)
    _patch_context(
        monkeypatch, loaded=loaded, step=step, intent=intent, orphan=orphan, session=session,
    )
    intent_path, started_path = live._step_paths(bundle, step)
    live.supervisor._publish_json(intent_path, intent)

    def fast(_root: Path, *, cpu: int) -> dict:
        raise live.supervisor.child_runner.RecursiveChildRunnerError(
            "unsealed child start commit is not live and bound"
        )

    monkeypatch.setattr(live.supervisor.child_runner, "start_root", fast)
    result = live._recover_step(
        loaded,
        plan=plan,
        step=step,
        checkpoint_receipt={"record_sha256": "2" * 64},
        checkpoint_chain={"latest_checkpoint_sha256": "3" * 64},
    )
    assert result["state"] == "FAST_TERMINAL_STILL_UNRESOLVED"
    assert not started_path.exists()
    assert not live._receipt_path(bundle, step).exists()
