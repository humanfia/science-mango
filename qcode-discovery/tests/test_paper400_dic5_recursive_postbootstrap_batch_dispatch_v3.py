from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "paper400_dic5_recursive_postbootstrap_batch_dispatch_v3.py"
)
SPEC = importlib.util.spec_from_file_location("recursive_postbootstrap_batch_dispatch_v3_test", SOURCE)
assert SPEC is not None and SPEC.loader is not None
v3 = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(v3)


def test_v3_uses_compat_session_sealer_before_fast_terminal_fallback(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    child = Path("/tmp/child")
    session = {"record_sha256": "a" * 64}
    monkeypatch.setattr(v3.compat, "seal_live_session", lambda root, *, cpu: {
        "state": "LIVE_SESSION_SEALED", "session": session,
    })

    assert v3._retry_visible_live_session(child, cpu=7) == session


def test_v3_allows_only_exact_stopped_fast_fallback(monkeypatch: pytest.MonkeyPatch) -> None:
    child = Path("/tmp/child")

    def fail(_root: Path, *, cpu: int) -> dict:
        raise v3.compat.LiveSessionCompatError("not live")

    monkeypatch.setattr(v3.compat, "seal_live_session", fail)
    monkeypatch.setattr(v3, "_exact_stopped_fast_context", lambda _root: True)
    assert v3._retry_visible_live_session(child, cpu=7) is None

    monkeypatch.setattr(v3, "_exact_stopped_fast_context", lambda _root: False)
    with pytest.raises(v3.BatchDispatchV3Error, match="neither exact live nor exact stopped"):
        v3._retry_visible_live_session(child, cpu=7)


def test_v3_scopes_the_v2_retry_override_to_one_dispatch(monkeypatch: pytest.MonkeyPatch) -> None:
    previous = v3.v2._retry_visible_live_session
    observed: list[object] = []

    def fake_start_all(_loaded: dict, _plan: dict) -> list[dict]:
        observed.append(v3.v2._retry_visible_live_session)
        return [{"item_id": "leaf:00", "state": "RUNNING"}]

    monkeypatch.setattr(v3.v2, "_start_all_v2", fake_start_all)

    result = v3._start_all_v3({}, {})

    assert result == [{"item_id": "leaf:00", "state": "RUNNING"}]
    assert observed == [v3._retry_visible_live_session]
    assert v3.v2._retry_visible_live_session is previous
