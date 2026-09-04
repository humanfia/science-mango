from __future__ import annotations

import contextlib
import importlib.util
from pathlib import Path
from types import SimpleNamespace

import pytest


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "paper400_dic5_recursive_incomplete_child_restart_v1.py"
)
SPEC = importlib.util.spec_from_file_location("recursive_incomplete_restart_v1_test", SOURCE)
assert SPEC is not None and SPEC.loader is not None
restart = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(restart)


def _entry(index: int, bundle: Path) -> dict:
    path = str(index)
    return {
        "ordinal": index,
        "item_id": f"leaf:{path}",
        "path": path,
        "worker_sha256": f"{index + 1:064x}",
        "claim_token": f"{index + 11:064x}",
        "worker_id": f"worker-{index}",
        "cpu_ids": [20 + index],
        "original_child_root": str(bundle / "children" / path),
        "original_session_sha256": f"{index + 21:064x}",
        "forensic_sha256": f"{index + 31:064x}",
        "retry_child_root": str(bundle / "children" / f"retry-{path}-attempt-000001"),
    }


def test_retry_dispatch_publishes_all_intents_and_spawns_all_siblings_first(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    bundle = tmp_path / "bundle"
    bundle.mkdir(mode=0o700)
    bundle.chmod(0o700)
    (bundle / "children").mkdir(mode=0o700)
    entries = [_entry(0, bundle), _entry(1, bundle)]
    plan = {"restart_plan_sha256": "a" * 64, "entries": entries}
    loaded = {"root": bundle}
    events: list[tuple[str, str]] = []

    class Process:
        def __init__(self, entry: dict) -> None:
            self.entry = entry
            self.returncode = 0

        def communicate(self) -> tuple[bytes, bytes]:
            events.append(("communicate", self.entry["path"]))
            return b"", b""

    runner = SimpleNamespace(
        _safe_root=lambda root: Path(root),
        _root_lock=lambda _root, exclusive=False: contextlib.nullcontext(),
        _load_session=lambda root, _loaded: {"record_sha256": "b" * 63 + Path(root).name[-1]},
    )
    monkeypatch.setattr(restart.supervisor, "child_runner", runner)
    monkeypatch.setattr(restart, "_validate_retry_static", lambda _loaded, _entry: {})
    monkeypatch.setattr(restart, "_source_binding", lambda: {"test": True})
    monkeypatch.setattr(
        restart,
        "_prepare_or_validate_retry_root",
        lambda _loaded, entry: events.append(("prepare", entry["path"])) or True,
    )

    def spawn(root: Path, *, cpu: int) -> Process:
        intents = list((bundle / restart.STARTS_DIR).glob("*.intent.json"))
        assert len(intents) == 2
        entry = next(candidate for candidate in entries if candidate["retry_child_root"] == str(root))
        events.append(("spawn", entry["path"]))
        return Process(entry)

    monkeypatch.setattr(restart.batch, "_spawn_child_start", spawn)

    result = restart._dispatch_all(loaded, plan)

    assert [kind for kind, _path in events[:2]] == ["prepare", "prepare"]
    assert [kind for kind, _path in events[2:4]] == ["spawn", "spawn"]
    assert [kind for kind, _path in events[4:]] == ["communicate", "communicate"]
    assert [value["state"] for value in result] == ["RUNNING", "RUNNING"]


def test_partial_forensic_requires_a_stable_no_conflict_rejection(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    root = tmp_path / "children" / "0"
    root.parent.mkdir(mode=0o700)
    root.mkdir(mode=0o700)
    root.chmod(0o700)
    snapshot = {
        "transport_state": "INACTIVE_UNCHECKPOINTED",
        "proof": {"bytes": 17},
        "snapshot_sha256": "a" * 64,
    }
    runner = SimpleNamespace(
        _safe_root=lambda value: Path(value),
        _root_lock=lambda _root: contextlib.nullcontext(),
        _load_static=lambda _root: {"static": {"static_sha256": "b" * 64}, "policy": {"proof_max_bytes": 99}},
        _load_session=lambda _root, _loaded: {"record_sha256": "c" * 64},
        _stopped_snapshot=lambda *_args: snapshot,
        _checker=lambda *_args, **_kwargs: ({"verified": False, "record_sha256": "d" * 64}, b"c ERROR: no conflict\ns NOT VERIFIED\n", b"", {}),
        _require_snapshot_unchanged=lambda left, right: left == right or (_ for _ in ()).throw(AssertionError()),
        _root_identity=lambda _root: {"path": str(root)},
        RUNTIME_ROOT=Path("runtime/dmtcp"),
        TERMINAL_CLAIM=Path("state/20-terminal.json"),
        CERTIFICATE=Path("state/30-certificate.json"),
        VALIDATION=Path("state/40-validation.json"),
        FINAL_COMMIT=Path("state/50-final.json"),
    )
    monkeypatch.setattr(restart.supervisor, "child_runner", runner)
    monkeypatch.setattr(restart, "_terminal_artifacts_absent", lambda _root: True)
    item = {"item_id": "leaf:0", "path": "0"}
    monkeypatch.setattr(restart, "_validate_original_child_binding", lambda *_args: item)
    monkeypatch.setattr(restart, "_source_binding", lambda: {"test": True})
    loaded = {
        "bundle": {"bundle_sha256": "e" * 64},
        "plan": {"record_sha256": "f" * 64},
        "initial_commit": {"record_sha256": "0" * 64},
    }
    step = {
        "worker": {"child_root": str(root), "cpu_ids": [7], "worker_sha256": "1" * 64, "token": "2" * 64, "worker_id": "w"},
        "after_queue": {"items": [item]},
        "item_id": "leaf:0",
    }

    value = restart._partial_forensic_value(loaded, step)

    assert value["partial_diagnosis"] == restart.PARTIAL_DIAGNOSIS
    assert value["drat_check"]["verified"] is False

    monkeypatch.setattr(
        runner,
        "_checker",
        lambda *_args, **_kwargs: ({"verified": False, "record_sha256": "d" * 64}, b"s NOT VERIFIED\n", b"", {}),
    )
    with pytest.raises(restart.IncompleteChildRestartError, match="no-conflict"):
        restart._partial_forensic_value(loaded, step)


def test_retry_root_is_deterministic_and_distinct_from_original(tmp_path: Path) -> None:
    bundle = tmp_path / "bundle"
    bundle.mkdir()
    (bundle / "children").mkdir()

    assert restart._retry_root(bundle, "00") == bundle / "children" / "retry-00-attempt-000001"
    with pytest.raises(restart.IncompleteChildRestartError, match="unsafe"):
        restart._retry_root(bundle, "../0")
