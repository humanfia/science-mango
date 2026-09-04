from __future__ import annotations

import contextlib
import importlib.util
from pathlib import Path
from types import SimpleNamespace

import pytest


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "paper400_dic5_recursive_incomplete_child_restart_v2.py"
)
SPEC = importlib.util.spec_from_file_location("recursive_incomplete_restart_v2_test", SOURCE)
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
        "cpu_ids": [40 + index],
        "original_child_root": str(bundle / "children" / path),
        "original_session_sha256": f"{index + 21:064x}",
        "forensic_sha256": f"{index + 31:064x}",
        "retry_child_root": str(bundle / "children" / f"retry-{path}-attempt-000002"),
    }


def test_v2_dispatch_seals_live_visibility_races_after_all_siblings_spawn(
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
        returncode = 2

        def __init__(self, entry: dict) -> None:
            self.entry = entry

        def communicate(self) -> tuple[bytes, bytes]:
            events.append(("communicate", self.entry["path"]))
            return b"", b"ERROR: unsealed child start commit is not live and bound\n"

    runner = SimpleNamespace(
        _safe_root=lambda root: Path(root),
        _root_lock=lambda _root, exclusive=False: contextlib.nullcontext(),
        _load_session=lambda _root, _loaded: {"record_sha256": "f" * 64},
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
        assert len(list((bundle / restart.STARTS_DIR).glob("*.intent.json"))) == 2
        entry = next(item for item in entries if item["retry_child_root"] == str(root))
        events.append(("spawn", entry["path"]))
        return Process(entry)

    monkeypatch.setattr(restart.batch, "_spawn_child_start", spawn)
    monkeypatch.setattr(
        restart.compat,
        "seal_live_session",
        lambda root, *, cpu: {"state": "LIVE_SESSION_SEALED", "session": {"record_sha256": "e" * 64}},
    )

    result = restart._dispatch_all(loaded, plan)

    assert [kind for kind, _path in events[:2]] == ["prepare", "prepare"]
    assert [kind for kind, _path in events[2:4]] == ["spawn", "spawn"]
    assert [kind for kind, _path in events[4:]] == ["communicate", "communicate"]
    assert [item["state"] for item in result] == [
        "LIVE_SESSION_SEALED_SCHEMA_COMPAT",
        "LIVE_SESSION_SEALED_SCHEMA_COMPAT",
    ]


def test_v2_rejects_a_non_visibility_start_failure(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    entry = _entry(0, tmp_path)
    monkeypatch.setattr(restart.supervisor, "child_runner", SimpleNamespace(_safe_root=lambda root: Path(root)))

    with pytest.raises(restart.IncompleteChildRestartV2Error, match="different failure"):
        restart._sealed_session_after_start({}, entry, error="different failure")
