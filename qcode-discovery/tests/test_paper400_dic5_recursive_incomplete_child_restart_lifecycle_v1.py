from __future__ import annotations

import contextlib
import importlib.util
from pathlib import Path
from types import SimpleNamespace

import pytest

from investigations import paper400_dic5_recursive_split_v1 as recursive


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "paper400_dic5_recursive_incomplete_child_restart_lifecycle_v1.py"
)
SPEC = importlib.util.spec_from_file_location("recursive_incomplete_restart_lifecycle_v1_test", SOURCE)
assert SPEC is not None and SPEC.loader is not None
lifecycle = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(lifecycle)


def test_retry_final_validation_keeps_the_prior_validation_digest_distinct(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path,
) -> None:
    root = tmp_path / "retry"
    root.mkdir()
    child_loaded = {"static": {"static_sha256": "a" * 64}}
    session = {"record_sha256": "b" * 64}
    claim = {"terminal_claim_sha256": "c" * 64}
    certificate = {"certificate_sha256": "d" * 64}
    stored_validation = {"validation_sha256": "e" * 64}
    fresh_drat = {"record_sha256": "f" * 64, "verified": True}
    fresh_lrat = {"record_sha256": "0" * 64, "verified": True}
    runner = SimpleNamespace(
        _safe_root=lambda value: Path(value),
        _root_lock=lambda _root, exclusive=False: contextlib.nullcontext(),
        _load_static=lambda _root: child_loaded,
        _load_session=lambda _root, _loaded: session,
        _validated_certificate=lambda _root, _loaded, _session: (claim, certificate, stored_validation),
        _revalidate_terminal_claim=lambda *_args, **_kwargs: {"fresh_drat": fresh_drat, "fresh_lrat": fresh_lrat},
    )
    monkeypatch.setattr(lifecycle.supervisor, "child_runner", runner)
    monkeypatch.setattr(lifecycle, "_source_binding", lambda: {"test": True})

    result = lifecycle._verify_retry_final(root)

    assert recursive.selfhash_valid(result, "validation_sha256")
    assert result["stored_validation_sha256"] == "e" * 64
    assert result["validation_sha256"] != result["stored_validation_sha256"]
    assert result["fresh_drat"] == fresh_drat


def test_retry_revalidation_rejects_a_changed_handoff_binding(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path,
) -> None:
    item = {
        "item_id": "leaf:0",
        "item_sha256": "a" * 64,
        "claim": {"worker_id": "worker", "token": "b" * 64},
    }
    worker = {"worker_id": "worker", "token": "b" * 64, "worker_sha256": "c" * 64}
    certificate = recursive.seal(
        {
            "leaf_id": "leaf:0",
            "leaf_sha256": "d" * 64,
            "child_cnf_sha256": "e" * 64,
            "child_dimacs_sha256": "f" * 64,
            "child_num_variables": 1,
            "child_num_clauses": 1,
            "child_dimacs_bytes": 1,
            "valid": True,
            "strict_proof_unsat": True,
            "fresh_proof_replay": True,
            "source_toolchain_fresh": True,
        },
        "certificate_sha256",
    )
    validation = {
        "valid": True,
        "strict_proof_unsat": True,
        "fresh_proof_replay": True,
        "source_toolchain_fresh": True,
        "failures": [],
    }
    entry = {"item_id": "leaf:0", "retry_child_root": str(tmp_path / "retry")}
    forensic = {"forensic_sha256": "1" * 64}
    started = {"record_sha256": "2" * 64, "retry_session_sha256": "3" * 64}
    loaded = {"restart_handoff": {"plan": {"restart_plan_sha256": "4" * 64}}}
    prepared = {
        "item_id": "leaf:0",
        "proof_mode": "NORMAL",
        "before_queue": {"items": [item]},
        "binding": {
            "proof_mode": "NORMAL",
            "worker_id": "worker",
            "token": "b" * 64,
            "worker_sha256": "c" * 64,
            "queue_item_sha256_before": "a" * 64,
            "restart_plan_sha256": "4" * 64,
            "forensic_sha256": "wrong",
            "retry_child_root": str(tmp_path / "retry"),
            "retry_started_sha256": "2" * 64,
            "retry_session_sha256": "3" * 64,
            "certificate": certificate,
            "validation": validation,
        },
    }
    monkeypatch.setattr(lifecycle.base, "_worker_for_item", lambda *_args, **_kwargs: (item, worker, tmp_path / "old"))
    monkeypatch.setattr(
        lifecycle,
        "_retry_certificate",
        lambda *_args: (entry, forensic, started, certificate, validation),
    )
    monkeypatch.setattr(lifecycle.recursive, "_queue_certificate_complete", lambda *_args: True)

    with pytest.raises(lifecycle.IncompleteChildRestartLifecycleError, match="handoff binding"):
        lifecycle._revalidate_restart_certification(loaded, prepared)


def test_runtime_scopes_and_restores_the_initial_transaction_namespace(monkeypatch: pytest.MonkeyPatch) -> None:
    old_gate = lifecycle.base.GATE
    old_lock = lifecycle.base.LOCK
    captured: dict[str, object] = {}

    def observe() -> None:
        captured["gate"] = lifecycle.base.GATE
        captured["lock"] = lifecycle.base.LOCK
        captured["transitions"] = lifecycle.base.TRANSITIONS
        captured["binding"] = lifecycle.base._source_binding()

    with lifecycle._runtime():
        observe()

    assert captured["gate"] == lifecycle.GATE
    assert captured["lock"] == lifecycle.LOCK
    assert captured["transitions"] == lifecycle.TRANSITIONS
    assert captured["binding"] == lifecycle._source_binding()
    assert lifecycle.base.GATE == old_gate
    assert lifecycle.base.LOCK == old_lock
