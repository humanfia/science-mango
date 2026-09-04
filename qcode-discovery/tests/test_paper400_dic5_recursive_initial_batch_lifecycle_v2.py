from __future__ import annotations

import contextlib
import importlib.util
from pathlib import Path
from types import SimpleNamespace

from investigations import paper400_dic5_recursive_split_v1 as recursive
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "paper400_dic5_recursive_initial_batch_lifecycle_v2.py"
)
SPEC = importlib.util.spec_from_file_location("recursive_initial_batch_lifecycle_v2_test", SOURCE)
assert SPEC is not None and SPEC.loader is not None
lifecycle = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(lifecycle)


def test_normal_final_validation_uses_a_distinct_prior_validation_digest(monkeypatch, tmp_path: Path) -> None:
    root = tmp_path / "child"
    root.mkdir()
    static = {"static": {"static_sha256": "a" * 64}}
    session = {"record_sha256": "b" * 64}
    claim = {"terminal_claim_sha256": "c" * 64}
    certificate = {"certificate_sha256": "d" * 64}
    stored_validation = {"validation_sha256": "e" * 64}
    fresh_drat = {"record_sha256": "f" * 64, "verified": True}
    fresh_lrat = {"record_sha256": "0" * 64, "verified": True}

    runner = SimpleNamespace(
        _safe_root=lambda value: Path(value),
        _root_lock=lambda _root, exclusive=False: contextlib.nullcontext(),
        _load_static=lambda _root: static,
        _load_session=lambda _root, _loaded: session,
        _validated_certificate=lambda _root, _loaded, _session: (
            claim, certificate, stored_validation,
        ),
        _revalidate_terminal_claim=lambda *_args, **_kwargs: {
            "fresh_drat": fresh_drat,
            "fresh_lrat": fresh_lrat,
        },
    )
    monkeypatch.setattr(supervisor, "child_runner", runner)
    monkeypatch.setattr(lifecycle, "_source_binding", lambda: {"method": "test"})

    result = lifecycle.verify_normal_final_root_v2(root)

    assert recursive.selfhash_valid(result, "validation_sha256")
    assert result["stored_validation_sha256"] == "e" * 64
    assert result["validation_sha256"] != result["stored_validation_sha256"]
    assert result["fresh_drat"] == fresh_drat
    assert result["fresh_lrat"] == fresh_lrat


def test_v2_runtime_applies_and_restores_all_versioned_hooks(monkeypatch) -> None:
    captured: dict[str, object] = {}
    old_gate = lifecycle.base.GATE
    old_lock = lifecycle.base.LOCK
    old_verify = supervisor.child_runner.verify_final_root

    def fake_tick(_bundle: Path, *, control_root: Path) -> dict[str, object]:
        captured["gate"] = lifecycle.base.GATE
        captured["lock"] = lifecycle.base.LOCK
        captured["transitions"] = lifecycle.base.TRANSITIONS
        captured["binding"] = lifecycle.base._source_binding()
        captured["verify"] = supervisor.child_runner.verify_final_root
        captured["control_root"] = control_root
        return {"ok": True}

    monkeypatch.setattr(lifecycle.base, "tick_bundle", fake_tick)

    assert lifecycle.tick_bundle(Path("/tmp/bundle"), control_root=Path("/tmp/control")) == {"ok": True}
    assert captured["gate"] == lifecycle.GATE
    assert captured["lock"] == lifecycle.LOCK
    assert captured["transitions"] == lifecycle.TRANSITIONS
    assert captured["binding"] == lifecycle._source_binding()
    assert captured["verify"] is lifecycle.verify_normal_final_root_v2
    assert captured["control_root"] == Path("/tmp/control")
    assert lifecycle.base.GATE == old_gate
    assert lifecycle.base.LOCK == old_lock
    assert supervisor.child_runner.verify_final_root is old_verify
