from __future__ import annotations

import importlib.util
from pathlib import Path


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "paper400_dic5_recursive_incomplete_child_restart_lifecycle_v2.py"
)
SPEC = importlib.util.spec_from_file_location("recursive_incomplete_restart_lifecycle_v2_test", SOURCE)
assert SPEC is not None and SPEC.loader is not None
lifecycle = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(lifecycle)


def test_v2_adapter_scopes_and_restores_the_v1_engine() -> None:
    old_gate = lifecycle.implementation.GATE
    old_restart = lifecycle.implementation.restart
    captured: dict[str, object] = {}

    with lifecycle._v2_runtime():
        captured["gate"] = lifecycle.implementation.GATE
        captured["restart"] = lifecycle.implementation.restart
        captured["transitions"] = lifecycle.implementation.TRANSITIONS
        captured["binding"] = lifecycle.implementation._source_binding()

    assert captured["gate"] == lifecycle.GATE
    assert captured["restart"] is lifecycle.restart
    assert captured["transitions"] == lifecycle.TRANSITIONS
    assert captured["binding"] == lifecycle._source_binding()
    assert lifecycle.implementation.GATE == old_gate
    assert lifecycle.implementation.restart is old_restart
