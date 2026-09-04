from __future__ import annotations

import types
from pathlib import Path

import pytest

from scripts import paper400_dic5_recursive_r5_legacy_adapter_v1 as adapter
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


def _r5_static_root(tmp_path: Path) -> Path:
    root = tmp_path / "r5-root"
    state = root / "state"
    state.mkdir(parents=True, mode=0o700)
    root.chmod(0o700)
    state.chmod(0o700)
    record = {
        "toolchain_binding": {
            "tools": {
                "dmtcp_controller_source": {
                    "path": str(adapter.R5_CONTROLLER),
                    "sha256": adapter.R5_CONTROLLER_SHA256,
                },
                "four_lane_coordinator_source": {
                    "path": str(adapter.R5_COORDINATOR),
                    "sha256": adapter.R5_COORDINATOR_SHA256,
                },
            }
        }
    }
    (state / "00-resume-static.json").write_bytes(supervisor.canonical_bytes(record) + b"\n")
    return root


def test_r5_context_selects_r5_runner_and_restores_globals() -> None:
    before_runner = supervisor.LEGACY_RUNNER
    before_binding = supervisor._legacy_source_binding
    with adapter.r5_legacy_context():
        assert supervisor.LEGACY_RUNNER == adapter.R5_RUNNER
        binding = supervisor._legacy_source_binding()
        assert binding["sources"]["legacy_runner"]["path"] == str(adapter.R5_RUNNER)
        assert binding["sources"]["r5_legacy_adapter"]["path"] == str(Path(adapter.__file__).resolve())
    assert supervisor.LEGACY_RUNNER == before_runner
    assert supervisor._legacy_source_binding is before_binding


def test_r5_context_routes_legacy_cli_to_exact_r5_runner(monkeypatch: pytest.MonkeyPatch) -> None:
    calls: list[list[str]] = []

    def fake_run(args: list[str], **_kwargs: object) -> types.SimpleNamespace:
        calls.append(args)
        return types.SimpleNamespace(returncode=0, stdout=b"{}", stderr=b"")

    monkeypatch.setattr(supervisor.subprocess, "run", fake_run)
    with adapter.r5_legacy_context():
        supervisor._legacy_cli("status", Path("/tmp/legacy-root"))
    assert calls[0][1] == str(adapter.R5_RUNNER)


def test_r5_static_path_validation_is_exact(tmp_path: Path) -> None:
    root = _r5_static_root(tmp_path)
    adapter.validate_r5_static_root(root)
    static = root / "state/00-resume-static.json"
    text = static.read_text(encoding="utf-8")
    static.write_text(text.replace("science-mango-r5", "science-mango-r4"), encoding="utf-8")
    with pytest.raises(adapter.R5LegacyAdapterError, match="exact r5"):
        adapter.validate_r5_static_root(root)


def test_r5_checkpoint_recovery_wrapper_installs_context(monkeypatch: pytest.MonkeyPatch) -> None:
    from scripts import paper400_dic5_recursive_checkpoint_recovery_r5_v1 as wrapper

    observed: list[Path] = []

    def fake_main(_argv: list[str] | None) -> int:
        observed.append(supervisor.LEGACY_RUNNER)
        return 0

    monkeypatch.setattr(wrapper.recovery, "main", fake_main)
    assert wrapper.main(["recover-receipt", "--bundle", "/tmp/bundle"]) == 0
    assert observed == [adapter.R5_RUNNER]
