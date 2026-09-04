from __future__ import annotations

import hashlib
import importlib.util
import os
from pathlib import Path

import pytest

from investigations import paper400_dic5_recursive_split_v1 as recursive
from scripts import run_paper400_dic5_recursive_child_resume_proof_v1 as child_runner


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "paper400_dic5_recursive_split_supervisor_v1.py"
)
SPEC = importlib.util.spec_from_file_location("recursive_split_supervisor_v1_test", SOURCE)
assert SPEC is not None and SPEC.loader is not None
supervisor = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(supervisor)


PARENT_DIMACS = b"""p cnf 4 4
1 -2 0
2 3 0
-3 4 0
-1 -4 0
"""


def _audit_manifest(parent_root: Path) -> tuple[dict, dict]:
    ledger = recursive.new_timing_ledger("parent", timeout_seconds=10)
    ledger = recursive.update_timing_ledger(
        ledger,
        {
            "state": "RUNNING", "generation": 0, "pid": 123,
            "proc_start_ticks": 456, "cpu_seconds": 11.0,
            "baseline": True, "observed_monotonic": 1.0,
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
        PARENT_DIMACS, parent_id="parent-g000000", fanout=2,
        split_variables=[1], trigger=trigger,
    )
    audit = recursive.seal(
        {
            "schema_version": 1,
            "kind": child_runner.PARENT_AUDIT_KIND,
            "parent_root": str(parent_root),
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


def test_catalog_reservation_is_serialized_and_releasable(tmp_path: Path) -> None:
    control = tmp_path / "control"
    control.mkdir(mode=0o700)
    control.chmod(0o700)
    bundle = control / "bundle-a"
    reservation = supervisor._reserve_cpus(
        control, bundle=bundle, cpus=[6, 26], observations=[],
    )
    with pytest.raises(supervisor.RecursiveSplitSupervisorError, match="already reserved"):
        supervisor._reserve_cpus(control, bundle=control / "bundle-b", cpus=[26], observations=[])
    supervisor._release_cpus(control, reservation)
    catalog = supervisor._load_catalog(control)
    assert all(item["state"] == "RELEASED" for item in catalog["leases"])


def test_create_bundle_binds_queue_audit_manifest_and_scheduler_reservation(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    control = tmp_path / "control"
    control.mkdir(mode=0o700)
    control.chmod(0o700)
    parent = tmp_path / "legacy-parent"
    parent.mkdir(mode=0o700)
    parent.chmod(0o700)
    (parent / "static").mkdir(mode=0o700)
    cnf = parent / "static" / "cube.cnf"
    cnf.write_bytes(PARENT_DIMACS)
    cnf.chmod(0o600)
    audit, manifest = _audit_manifest(parent)
    monkeypatch.setattr(supervisor, "audit_parent", lambda root, fanout: (audit, manifest))
    monkeypatch.setattr(supervisor, "_validate_cpu_pool", lambda cpus: ([6, 26], []))
    bundle = control / "bundle-a"
    created = supervisor.create_bundle(
        bundle, parent_root=parent, cpus=[6, 26], control_root=control,
    )
    loaded = supervisor._load_bundle(bundle, control_root=control)
    assert created["bundle_sha256"] == loaded["bundle"]["bundle_sha256"]
    assert loaded["queue"]["fanout"] == 2
    assert loaded["reservation"]["kernel_hardware_exclusive"] is False


def test_tick_recovers_a_durable_unsealed_start_only_after_parent_recheck(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    bundle = tmp_path / "bundle"
    bundle.mkdir(mode=0o700)
    child_root = bundle / "children" / "0"
    record = {
        "item_id": "leaf:0", "token": "token", "worker_id": "worker",
        "cpu_ids": [6], "child_root": str(child_root),
    }
    queue = {
        "items": [{
            "item_id": "leaf:0", "state": "CLAIMED",
            "claim": {"token": "token", "worker_id": "worker", "lease_expires_at": 10**12},
        }],
    }
    loaded = {
        "root": bundle,
        "bundle": {"bundle_sha256": "a" * 64},
        "audit": {"parent_root": "/tmp/parent"},
        "control_root": tmp_path / "control",
        "reservation": {"reservation_sha256": "b" * 64},
    }
    statuses = iter([
        {"state": "START_RECOVERY_REQUIRED"},
        {"state": "RUNNING"},
    ])
    starts: list[tuple[Path, int]] = []
    eligibility: list[dict] = []
    monkeypatch.setattr(supervisor, "_load_bundle", lambda *_args, **_kwargs: loaded)
    monkeypatch.setattr(supervisor, "_worker_records", lambda _loaded: [(bundle / "worker.json", record)])
    monkeypatch.setattr(supervisor.recursive, "load_split_queue", lambda _path: queue)
    monkeypatch.setattr(
        supervisor.recursive, "split_queue_status",
        lambda _path: {"status": recursive.QUEUE_STATUS_OPEN},
    )
    monkeypatch.setattr(supervisor.child_runner, "status_root", lambda *_args, **_kwargs: next(statuses))
    monkeypatch.setattr(
        supervisor.child_runner,
        "start_root",
        lambda root, *, cpu: starts.append((root, cpu)) or {"started": True},
    )
    monkeypatch.setattr(
        supervisor,
        "_legacy_parent_still_split_eligible",
        lambda audit: eligibility.append(dict(audit)),
    )

    result = supervisor.tick_bundle(bundle, control_root=tmp_path / "control")
    assert starts == [(child_root, 6)]
    assert eligibility == [{"parent_root": "/tmp/parent"}]
    assert result["actions"][-1] == {
        "item_id": "leaf:0", "action": "OBSERVED", "state": "RUNNING",
    }
    assert result["actions"][0]["action"] == "START_RECOVERED"


def test_parser_has_explicit_commands_and_no_abbreviation() -> None:
    parser = supervisor.build_parser()
    assert parser.allow_abbrev is False
    assert parser.parse_args(["audit-parent", "--parent-root", "/tmp/x"]).action == "audit-parent"
    assert parser.parse_args(["tick", "--bundle", "/tmp/x"]).action == "tick"
    with pytest.raises(SystemExit):
        parser.parse_args(["aud", "--parent-root", "/tmp/x"])
