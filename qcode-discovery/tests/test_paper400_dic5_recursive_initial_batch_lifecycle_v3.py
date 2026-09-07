from __future__ import annotations

import importlib.util
from pathlib import Path

from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "paper400_dic5_recursive_initial_batch_lifecycle_v3.py"
)
SPEC = importlib.util.spec_from_file_location("recursive_initial_batch_lifecycle_v3_test", SOURCE)
assert SPEC is not None and SPEC.loader is not None
lifecycle = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(lifecycle)


def test_v3_bypasses_only_a_completed_affinity_recovery_and_restores_hooks(monkeypatch) -> None:
    captured: dict[str, object] = {}
    original_fast = lifecycle.base._is_fast_orphan
    original_verify = supervisor.child_runner.verify_final_root

    def fake_tick(_bundle: Path, *, control_root: Path) -> dict[str, object]:
        captured["gate"] = lifecycle.base.GATE
        captured["fast"] = lifecycle.base._is_fast_orphan({"bundle": True}, item_id="leaf:0")
        captured["verify"] = supervisor.child_runner.verify_final_root
        captured["control"] = control_root
        return {"ok": True}

    monkeypatch.setattr(lifecycle.base, "tick_bundle", fake_tick)
    monkeypatch.setattr(
        lifecycle.affinity, "completed_recovery_for_item", lambda _loaded, *, item_id: item_id == "leaf:0",
    )

    assert lifecycle.tick_bundle(Path("/tmp/bundle"), control_root=Path("/tmp/control")) == {"ok": True}
    assert captured["gate"] == lifecycle.GATE
    assert captured["fast"] is False
    assert captured["verify"] is lifecycle.v2.verify_normal_final_root_v2
    assert captured["control"] == Path("/tmp/control")
    assert lifecycle.base._is_fast_orphan is original_fast
    assert supervisor.child_runner.verify_final_root is original_verify
