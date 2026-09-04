from __future__ import annotations

import hashlib
import importlib.util
import os
import resource
from pathlib import Path

import pytest

from investigations import paper400_dic5_recursive_split_v1 as recursive


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "run_paper400_dic5_recursive_child_resume_proof_v1.py"
)
SPEC = importlib.util.spec_from_file_location("recursive_child_runner_v1_test", SOURCE)
assert SPEC is not None and SPEC.loader is not None
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)


PARENT_DIMACS = b"""p cnf 4 4
1 -2 0
2 3 0
-3 4 0
-1 -4 0
"""


def _audit_and_manifest() -> tuple[dict, dict]:
    ledger = recursive.new_timing_ledger("legacy-parent", timeout_seconds=10)
    ledger = recursive.update_timing_ledger(
        ledger,
        {
            "state": "RUNNING",
            "generation": 0,
            "pid": 123,
            "proc_start_ticks": 456,
            "cpu_seconds": 11.0,
            "baseline": True,
            "observed_monotonic": 1.0,
        },
    )
    evidence = recursive.build_timeout_evidence(ledger, observed_state="RUNNING")
    trigger = recursive.seal(
        {
            "kind": "paper400-dic5-recursive-split-trigger-v1",
            "reason": "EFFECTIVE_SOLVER_CPU_TIMEOUT",
            "observed_state": "RUNNING",
            "timeout_seconds": evidence["timeout_seconds"],
            "effective_solver_seconds": evidence["effective_solver_seconds"],
            "timed_out": True,
            "hardness_only": True,
            "solver_terminal_claim": False,
            "ledger_sha256": ledger["ledger_sha256"],
            "evidence": evidence,
            "evidence_sha256": evidence["evidence_sha256"],
        },
        "trigger_sha256",
    )
    manifest, _ = recursive.build_split_manifest(
        PARENT_DIMACS,
        parent_id="legacy-parent",
        fanout=4,
        split_variables=[1, 2],
        trigger=trigger,
    )
    audit = recursive.seal(
        {
            "schema_version": 1,
            "kind": runner.PARENT_AUDIT_KIND,
            "parent_root": "/tmp/legacy-parent",
            "parent_root_identity": {"device": 1, "inode": 2, "mode": 448, "uid": os.geteuid()},
            "parent_static_sha256": "a" * 64,
            "parent_session_sha256": "b" * 64,
            "parent_dimacs_sha256": hashlib.sha256(PARENT_DIMACS).hexdigest(),
            "parent_dimacs_bytes": len(PARENT_DIMACS),
            "parent_generation": 0,
            "parent_pid": 123,
            "parent_proc_start_ticks": 456,
            "observed_state": "RUNNING",
            "timing_ledger": ledger,
            "timing_evidence": evidence,
            "timing_trigger": trigger,
            "split_allowed": True,
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": {"test": True},
        },
        "audit_sha256",
    )
    return audit, manifest


def test_import_pins_controller_and_proof_helper_sources() -> None:
    sources = runner._source_binding()["sources"]
    assert sources["dmtcp_controller"]["sha256"] == runner.EXPECTED_CONTROLLER_SHA256
    assert sources["proof_helper"]["sha256"] == runner.EXPECTED_PROOF_HELPER_SHA256
    assert runner._toolchain_binding()["tools"]["cadical_solver"]["sha256"] == (
        runner.EXPECTED_SOLVER_SHA256
    )


def test_prepare_replays_exact_timeout_cover_and_static_child_material(tmp_path: Path) -> None:
    audit, manifest = _audit_and_manifest()
    root = tmp_path / "recursive-child"
    static = runner.prepare_root_from_material(
        root,
        parent_dimacs=PARENT_DIMACS,
        split_manifest=manifest,
        leaf_path="01",
        parent_audit=audit,
        proof_max_bytes=1 << 30,
        checkpoint_image_max_bytes=1 << 29,
        checkpoint_generation_max=4,
    )
    loaded = runner._load_static(root)
    assert loaded["static"]["static_sha256"] == static["static_sha256"]
    assert loaded["leaf"]["path"] == "01"
    assert runner.status_root(root)["state"] == "PREPARED"
    assert (root / "static" / "cube.cnf").read_bytes() == recursive.render_leaf_payload(
        manifest, PARENT_DIMACS, "01"
    )


def test_static_child_tampering_is_rejected_before_any_transport_action(tmp_path: Path) -> None:
    audit, manifest = _audit_and_manifest()
    root = tmp_path / "recursive-child"
    runner.prepare_root_from_material(
        root, parent_dimacs=PARENT_DIMACS, split_manifest=manifest,
        leaf_path="00", parent_audit=audit,
        proof_max_bytes=1 << 30, checkpoint_image_max_bytes=1 << 29,
        checkpoint_generation_max=4,
    )
    child = root / "static" / "cube.cnf"
    child.chmod(0o600)
    child.write_bytes(child.read_bytes() + b"c tampered\n")
    with pytest.raises(runner.RecursiveChildRunnerError, match="static child DIMACS"):
        runner._load_static(root)


def _admission(policy: dict) -> dict:
    minimum_disk = policy["disk_admission_headroom_bytes"] + policy["proof_max_bytes"]
    return {
        "available_memory_bytes": policy["memory_admission_min_available_bytes"],
        "available_disk_bytes": minimum_disk,
        "minimum_memory_bytes": policy["memory_admission_min_available_bytes"],
        "minimum_disk_bytes": minimum_disk,
        "passed": True,
    }


def _session(root: Path, loaded: dict, *, cpu: int = 6) -> dict:
    return runner._session_value(
        root,
        loaded,
        cpu=cpu,
        config={"self_sha256": "c" * 64},
        started={"self_sha256": "d" * 64},
        affinity={"pid": 123, "cpu": cpu, "observed_affinity": [cpu], "verified": True},
        limits={
            "pid": 123,
            "proof_fsize_soft_bytes": loaded["policy"]["proof_max_bytes"],
            "proof_fsize_hard_bytes": resource.RLIM_INFINITY,
            "core_soft_bytes": 0,
            "core_hard_bytes": resource.RLIM_INFINITY,
            "cpu_soft_seconds": resource.RLIM_INFINITY,
            "cpu_hard_seconds": resource.RLIM_INFINITY,
            "verified": True,
        },
        admission=_admission(loaded["policy"]),
    )


def test_start_claim_is_cpu_bound_and_reports_recovery_required(tmp_path: Path) -> None:
    audit, manifest = _audit_and_manifest()
    root = tmp_path / "recursive-child"
    runner.prepare_root_from_material(
        root, parent_dimacs=PARENT_DIMACS, split_manifest=manifest,
        leaf_path="00", parent_audit=audit,
        proof_max_bytes=1 << 30, checkpoint_image_max_bytes=1 << 29,
        checkpoint_generation_max=4,
    )
    loaded = runner._load_static(root)
    claim = runner._start_claim_value(
        root, loaded, cpu=6, admission=_admission(loaded["policy"]),
    )
    runner._publish_json(root / runner.START_CLAIM, claim)

    status = runner.status_root(root)
    assert status["state"] == "START_RECOVERY_REQUIRED"
    assert status["expected_single_cpu"] == 6
    with pytest.raises(runner.RecursiveChildRunnerError, match="start CPU changed"):
        runner.start_root(root, cpu=26)


def test_terminal_claim_revalidation_binds_copied_artifacts_before_recovery(tmp_path: Path) -> None:
    audit, manifest = _audit_and_manifest()
    root = tmp_path / "recursive-child"
    runner.prepare_root_from_material(
        root, parent_dimacs=PARENT_DIMACS, split_manifest=manifest,
        leaf_path="00", parent_audit=audit,
        proof_max_bytes=1 << 30, checkpoint_image_max_bytes=1 << 29,
        checkpoint_generation_max=4,
    )
    loaded = runner._load_static(root)
    session = _session(root, loaded)
    runner._publish_json(root / runner.SESSION_COMMIT, session)

    attempt = root / "artifacts" / "attempt-test"
    attempt.mkdir(mode=0o700)
    raw_path = attempt / "child.drat"
    lrat_path = attempt / "child.lrat"
    raw_path.write_bytes(b"proof-a\n")
    lrat_path.write_bytes(b"proof-b\n")
    raw_path.chmod(0o600)
    lrat_path.chmod(0o600)
    raw = runner.v2._physical_record(
        raw_path, root, "raw-binary-drat", cap=loaded["policy"]["proof_max_bytes"],
    )
    lrat = runner.v2._physical_record(
        lrat_path, root, "converted-lrat", cap=runner.MAX_PROOF_BYTES,
    )
    snapshot = runner.seal(
        {
            "schema_version": runner.SCHEMA_VERSION,
            "kind": "paper400-dic5-recursive-stopped-proof-snapshot-v1",
            "transport_state": "CHECKPOINTED",
            "controller_status_sha256": "e" * 64,
            "latest_generation": 0,
            "latest_pid": 123,
            "latest_proc_start_ticks": 456,
            "latest_pid_identity_alive": False,
            "proof": raw,
            "writable_holders": [],
        },
        "snapshot_sha256",
    )
    check = {"record_sha256": "f" * 64}
    chain = runner._proof_chain_value(
        raw=raw, lrat=lrat, drat_check=check, conversion=check, lrat_check=check,
        fresh_drat=check, fresh_lrat=check, snapshot=snapshot,
    )
    claim = runner._terminal_claim_value(
        root, loaded, session, snapshot=snapshot, chain=chain,
    )

    replay = runner._revalidate_terminal_claim(
        root, loaded, session, claim,
        require_stopped_snapshot=False, fresh_replay=False,
    )
    assert replay["raw"] == raw
    lrat_path.write_bytes(b"tampered\n")
    with pytest.raises(runner.RecursiveChildRunnerError, match="artifact binding changed"):
        runner._revalidate_terminal_claim(
            root, loaded, session, claim,
            require_stopped_snapshot=False, fresh_replay=False,
        )


def test_controller_status_rehydrates_pid_identity_from_authenticated_commit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    summary = {
        "generation": 0,
        "active_manifest_sha256": "a" * 64,
        "pid_identity_alive": False,
    }
    monkeypatch.setattr(runner.controller, "_clean_dmtcp_environment", lambda: {})
    monkeypatch.setattr(
        runner.controller,
        "inspect",
        lambda *_args, **_kwargs: {
            "state": "CHECKPOINTED",
            "config_manifest_sha256": "b" * 64,
            "generations": [summary],
        },
    )
    monkeypatch.setattr(runner.controller, "_generation_dir", lambda *_args: Path("/tmp/generation"))
    monkeypatch.setattr(
        runner.controller,
        "_active_commit",
        lambda *_args: {
            "self_sha256": "a" * 64,
            "pid": 123,
            "proc_start_ticks": 456,
        },
    )
    status = runner._controller_status(
        Path("/tmp/recursive-child"),
        {"policy": {"checkpoint_generation_max": 4}},
        {"controller_config_sha256": "b" * 64, "expected_single_cpu": 6},
        verify_hashes=False,
    )
    latest = status["generations"][-1]
    assert latest["pid"] == 123
    assert latest["proc_start_ticks"] == 456


def test_parser_has_exact_actions_and_no_abbreviation() -> None:
    parser = runner.build_parser()
    assert parser.allow_abbrev is False
    assert parser.parse_args(["start", "--root", "/tmp/x", "--cpu", "6"]).action == "start"
    assert parser.parse_args(["harvest", "--root", "/tmp/x"]).action == "harvest"
    with pytest.raises(SystemExit):
        parser.parse_args(["sta", "--root", "/tmp/x", "--cpu", "6"])
