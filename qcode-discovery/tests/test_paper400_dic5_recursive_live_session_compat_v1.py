from __future__ import annotations

import contextlib
import importlib.util
from pathlib import Path

import pytest


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "paper400_dic5_recursive_live_session_compat_v1.py"
)
SPEC = importlib.util.spec_from_file_location("recursive_live_session_compat_v1_test", SOURCE)
assert SPEC is not None and SPEC.loader is not None
compat = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(compat)


def _patch_live_root(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> tuple[Path, dict[str, dict]]:
    root = tmp_path / "child"
    (root / "state").mkdir(parents=True)
    runtime = root / "runtime" / "dmtcp"
    runtime.mkdir(parents=True)
    published: dict[str, dict] = {}
    static = {
        "static": {"static_sha256": "a" * 64, "child": {"leaf_id": "leaf:00"}},
        "policy": {"proof_max_bytes": 1 << 30},
    }
    claim = {
        "expected_single_cpu": 17,
        "resource_admission": {"passed": True},
        "record_sha256": "b" * 64,
    }
    config = {"self_sha256": "c" * 64}
    active = {
        "kind": "start.commit",
        "generation": 0,
        "self_sha256": "d" * 64,
        "config_manifest_sha256": config["self_sha256"],
        "pid": 4321,
        "proc_start_ticks": 9876,
    }
    status = {
        "root": str(runtime),
        "config_manifest_sha256": config["self_sha256"],
        "state": "RUNNING",
        "generations": [{
            "generation": 0,
            "active_kind": "start.commit",
            "active_manifest_sha256": active["self_sha256"],
            "pid_identity_alive": True,
            "checkpointed": False,
            "poison_claim": None,
            "stale_tail_injected": False,
        }],
    }
    monkeypatch.setattr(compat.child_runner, "_safe_root", lambda value: Path(value))
    monkeypatch.setattr(compat.child_runner, "_root_lock", lambda _root: contextlib.nullcontext())
    monkeypatch.setattr(compat.child_runner, "_load_static", lambda _root: static)
    monkeypatch.setattr(compat.child_runner, "_read_start_claim", lambda _root, _loaded: claim)
    monkeypatch.setattr(compat.child_runner, "_load_expected_controller_config", lambda _root: config)
    monkeypatch.setattr(compat.child_runner, "_clean_controller_environment", lambda: contextlib.nullcontext())
    monkeypatch.setattr(compat.child_runner.controller, "inspect", lambda _runtime, **_kwargs: status)
    monkeypatch.setattr(compat.child_runner.controller, "_generation_dir", lambda _runtime, _generation: runtime)
    monkeypatch.setattr(compat.child_runner.controller, "_active_commit", lambda _directory, _generation: active)
    monkeypatch.setattr(
        compat.recursive,
        "observe_proc_cpu_seconds",
        lambda _pid: {"proc_start_ticks": active["proc_start_ticks"], "state": "R"},
    )
    monkeypatch.setattr(
        compat.child_runner, "_verify_live_affinity",
        lambda pid, cpu: {"pid": pid, "cpu": cpu, "observed_affinity": [cpu], "verified": True},
    )
    monkeypatch.setattr(
        compat.child_runner, "_verify_live_limits",
        lambda pid, _cap: {"pid": pid, "verified": True},
    )
    monkeypatch.setattr(
        compat.child_runner,
        "_session_value",
        lambda _root, _loaded, *, cpu, config, started, affinity, limits, admission: {
            "record_sha256": "e" * 64,
            "expected_single_cpu": cpu,
            "controller_config_sha256": config["self_sha256"],
            "controller_start_sha256": started["self_sha256"],
            "affinity": affinity,
            "limits": limits,
            "admission": admission,
        },
    )
    monkeypatch.setattr(compat, "_source_binding", lambda: {"test": True})
    monkeypatch.setattr(
        compat.child_runner,
        "_publish_json",
        lambda path, value: published.__setitem__(str(path), dict(value)),
    )
    return root, {"static": static, "claim": claim, "config": config, "active": active, "status": status, "published": published}


def test_seals_live_schema_compat_session_only_after_exact_attestations(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    root, values = _patch_live_root(monkeypatch, tmp_path)

    result = compat.seal_live_session(root, cpu=17)

    assert result["state"] == "LIVE_SESSION_SEALED"
    assert result["session"]["controller_start_sha256"] == values["active"]["self_sha256"]
    assert str(root / compat.child_runner.SESSION_COMMIT) in values["published"]
    receipt = values["published"][str(root / compat.COMPAT_RECEIPT)]
    assert receipt["controller_start_config_field"] == "config_manifest_sha256"
    assert receipt["controller_start_config_sha256"] == values["config"]["self_sha256"]


def test_rejects_a_live_start_with_wrong_new_schema_binding(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    root, values = _patch_live_root(monkeypatch, tmp_path)
    values["active"]["config_manifest_sha256"] = "f" * 64

    with pytest.raises(compat.LiveSessionCompatError, match="live start/config binding"):
        compat.seal_live_session(root, cpu=17)

    assert values["published"] == {}


def test_existing_valid_session_is_not_republished(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    root, values = _patch_live_root(monkeypatch, tmp_path)
    session_path = root / compat.child_runner.SESSION_COMMIT
    session_path.parent.mkdir(exist_ok=True)
    session_path.write_text("{}")
    session = {"record_sha256": "9" * 64, "expected_single_cpu": 17}
    monkeypatch.setattr(compat.child_runner, "_load_session", lambda _root, _loaded: session)
    monkeypatch.setattr(
        compat.child_runner.controller,
        "inspect",
        lambda *_args, **_kwargs: pytest.fail("existing session must avoid controller inspection"),
    )

    result = compat.seal_live_session(root, cpu=17)

    assert result == {"state": "ALREADY_SESSION_SEALED", "session": session, "receipt": None}
    assert values["published"] == {}
