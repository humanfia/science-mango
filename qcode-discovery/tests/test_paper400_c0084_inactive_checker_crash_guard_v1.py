from __future__ import annotations

import fcntl
import hashlib
import json
import os
from pathlib import Path
from typing import Any

import pytest

from scripts import paper400_c0084_inactive_checker_crash_guard_v1 as guard
from scripts import paper400_c0084_inactive_checker_crash_recursive_split_v1 as split
from scripts import paper400_drat_segv_quarantine_guard_v1 as quarantine
from scripts import render_paper400_c0084_inactive_checker_crash_guard_v1 as renderer


def _canonical(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
        allow_nan=False,
    ).encode("ascii")


def _seal(value: dict[str, Any], field: str) -> dict[str, Any]:
    result = dict(value)
    result[field] = hashlib.sha256(_canonical(result)).hexdigest()
    return result


def _write(path: Path, data: bytes, mode: int = 0o600) -> None:
    path.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
    path.write_bytes(data)
    path.chmod(mode)


def _write_record(path: Path, value: dict[str, Any]) -> None:
    _write(path, _canonical(value) + b"\n")


def _full(path: Path) -> dict[str, int]:
    return quarantine.identity_record(path.stat(follow_symlinks=False), full=True)


def _root_identity(path: Path) -> dict[str, int]:
    return quarantine.identity_record(path.stat(follow_symlinks=False), full=False)


def _record_spec(path: Path, relative: str, field: str) -> dict[str, Any]:
    value = json.loads(path.read_bytes())
    return {
        "relative_path": relative,
        "identity": _full(path),
        "file_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "self_hash_field": field,
        "self_hash": value[field],
    }


def _supplement(
    *, proof_sha: str, cube_sha: str, checker_sha: str,
) -> dict[str, Any]:
    return {
        "unit": "paper400-r4-auto-h-b0020-l1-1788745926729814348.service",
        "cursor": "s=fixture;i=58",
        "realtime_usec": 1_788_746_598_810_462,
        "boot_id": "a" * 32,
        "invocation_id": "b" * 32,
        "preflight_record_sha256": "1" * 64,
        "checker_result_sha256": "2" * 64,
        "process_record_sha256": "3" * 64,
        "proof_sha256": proof_sha,
        "cube_sha256": cube_sha,
        "checker_sha256": checker_sha,
        "exit_code": -11,
        "signal": 11,
        "child_pid": 999_999_981,
        "supervisor_pid": 999_999_982,
        "elapsed_ns": 407_554_882_440,
        "drat_verified": False,
        "terminal_claim_created": False,
        "verification_retry_allowed": True,
    }


def _fixture(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    *,
    base_attempts: int = 57,
    supplements: int = 2,
    stage_pid: int = 999_999_991,
    solver_pid: int = 999_999_992,
    bad_session_link: bool = False,
) -> dict[str, Any]:
    root = tmp_path / "paper400-batch-0020/lanes/lane-1"
    root.mkdir(parents=True, mode=0o700)
    root.chmod(0o700)
    monkeypatch.setattr(guard, "EXPECTED_ROOT", root)

    lock = root / ".hierarchical-resume.lock"
    proof = root / "runtime/dmtcp/proof.drat"
    cube = root / "static/cube.cnf"
    checker = tmp_path / "toolchain/drat-trim"
    _write(lock, b"")
    _write(proof, b"proof-fixture-" + b"x" * 243)
    _write(cube, b"p cnf 4 3\n1 -2 0\n2 3 0\n-3 4 0\n")
    _write(checker, b"checker-fixture\n", 0o755)
    checker_sha = hashlib.sha256(checker.read_bytes()).hexdigest()
    cube_sha = hashlib.sha256(cube.read_bytes()).hexdigest()
    proof_sha = hashlib.sha256(proof.read_bytes()).hexdigest()
    monkeypatch.setattr(quarantine, "BAD_CHECKER_SHA256", checker_sha)

    static = _seal({
        "state": "RESUMABLE_STATIC_SEALED",
        "root": str(root),
        "child": {
            "child_id": guard.EXPECTED_CHILD_ID,
            "global_leaf_id": guard.EXPECTED_CHILD_ID,
            "global_leaf_index": guard.EXPECTED_CHILD_INDEX,
            "child_index": guard.EXPECTED_CHILD_INDEX,
            "child_dimacs_sha256": cube_sha,
            "child_dimacs_bytes": len(cube.read_bytes()),
        },
        "cnf_artifact": {
            "relative_path": "static/cube.cnf",
            "sha256": cube_sha,
            "bytes": len(cube.read_bytes()),
        },
    }, "record_sha256")
    start_claim = _seal({
        "action": "start", "terminal": False, "root": str(root),
        "pid": stage_pid,
    }, "record_sha256")
    controller_start = _seal({
        "kind": "start.commit", "generation": 0, "pid": solver_pid,
        "proc_start_ticks": 3_247_604, "single_process_peer_count": 1,
        "claim_sha256": "4" * 64,
    }, "self_sha256")
    session = _seal({
        "state": "RUNNING", "root": str(root),
        "resume_static_sha256": static["record_sha256"],
        "start_claim_sha256": (
            "5" * 64 if bad_session_link else start_claim["record_sha256"]
        ),
        "controller_start_sha256": controller_start["self_sha256"],
        "child_dimacs_sha256": cube_sha,
        "expected_single_cpu": guard.EXPECTED_CPU,
        "started_peer_rlimits": {"pid": solver_pid, "verified": True},
    }, "record_sha256")
    paths = {
        "static": root / guard.REQUIRED_RECORD_PATHS["static"],
        "start_claim": root / guard.REQUIRED_RECORD_PATHS["start_claim"],
        "session": root / guard.REQUIRED_RECORD_PATHS["session"],
        "controller_start": root / guard.REQUIRED_RECORD_PATHS["controller_start"],
    }
    values = {
        "static": static, "start_claim": start_claim, "session": session,
        "controller_start": controller_start,
    }
    for role, path in paths.items():
        _write_record(path, values[role])
    (root / "state").chmod(0o700)
    (root / "runtime").chmod(0o700)
    (root / "runtime/dmtcp").chmod(0o700)
    (root / "runtime/dmtcp/generations").chmod(0o700)
    (root / "runtime/dmtcp/generations/000000").chmod(0o700)
    (root / "static").chmod(0o700)

    qentry = {
        "id": guard.EXPECTED_ENTRY_ID,
        "global_child_id": "c0084",
        "global_child_index": guard.EXPECTED_CHILD_INDEX,
        "quarantine_enabled": True,
        "root": str(root),
        "root_identity": _root_identity(root),
        "lock": {
            "relative_path": ".hierarchical-resume.lock",
            "identity": _full(lock),
            "sha256": hashlib.sha256(b"").hexdigest(),
        },
        "proof": {
            "relative_path": "runtime/dmtcp/proof.drat",
            "identity": _full(proof),
            "sha256": proof_sha,
            "content_hash_replay": "journal-bound-stat-only",
        },
        "cube": {
            "relative_path": "static/cube.cnf",
            "identity": _full(cube),
            "sha256": cube_sha,
        },
        "checker": {
            "path": str(checker), "identity": _full(checker),
            "sha256": checker_sha,
        },
        "incident": {
            "deterministic_attempts": base_attempts,
            "signal": 11,
            "all_same_proof_cube_checker": True,
        },
        "alternative_certification": "none",
        "required_absent_relative_paths": sorted(quarantine.REQUIRED_ABSENT),
    }
    qmanifest = quarantine.seal_manifest({
        "schema_version": 1,
        "kind": quarantine.SCHEMA,
        "bad_checker_sha256": checker_sha,
        "entries": [qentry],
    })
    qpath = tmp_path / "quarantine.json"
    _write(qpath, quarantine.manifest_payload(qmanifest))
    qfile_sha = hashlib.sha256(qpath.read_bytes()).hexdigest()
    monkeypatch.setattr(guard, "EXPECTED_QUARANTINE_MANIFEST", qpath)
    monkeypatch.setattr(
        guard, "EXPECTED_QUARANTINE_FILE_SHA256", qfile_sha,
    )
    monkeypatch.setattr(
        guard, "EXPECTED_QUARANTINE_RECORD_SHA256",
        qmanifest["record_sha256"],
    )

    supplemental = [
        _supplement(
            proof_sha=proof_sha, cube_sha=cube_sha, checker_sha=checker_sha,
        )
        for _ in range(supplements)
    ]
    for index, item in enumerate(supplemental):
        item["unit"] = (
            f"paper400-r4-auto-h-b0020-l1-{1788745926729814348 + index}.service"
        )
        item["cursor"] = f"s=fixture;i={58 + index}"
        item["process_record_sha256"] = f"{index + 3:064x}"
        item["child_pid"] += index
        item["supervisor_pid"] += index
        item["elapsed_ns"] += index
    journal_fields = set(guard.EXPECTED_SUPPLEMENTAL_JOURNAL_ATTEMPTS[0])
    monkeypatch.setattr(
        guard, "EXPECTED_SUPPLEMENTAL_JOURNAL_ATTEMPTS",
        tuple(
            {field: item[field] for field in journal_fields}
            for item in supplemental
        ),
    )
    admission = guard.seal({
        "schema_version": 1,
        "kind": guard.ADMISSION_KIND,
        "gate": guard.GATE,
        "root": str(root),
        "global_child_id": "c0084",
        "global_child_index": guard.EXPECTED_CHILD_INDEX,
        "quarantine_binding": {
            "manifest_path": str(qpath),
            "manifest_file_sha256": qfile_sha,
            "manifest_record_sha256": qmanifest["record_sha256"],
            "entry_id": guard.EXPECTED_ENTRY_ID,
            "base_attempts": base_attempts,
        },
        "records": {
            role: _record_spec(
                paths[role], guard.REQUIRED_RECORD_PATHS[role],
                "self_sha256" if role == "controller_start" else "record_sha256",
            )
            for role in paths
        },
        "stale_processes": [
            {
                "role": "stage_claim", "pid": stage_pid,
                "expected_absent": True, "proc_start_ticks": None,
            },
            {
                "role": "solver", "pid": solver_pid,
                "expected_absent": True,
                "proc_start_ticks": controller_start["proc_start_ticks"],
            },
        ],
        "incident": {
            "base_attempts": base_attempts,
            "supplemental_attempts": supplemental,
            "total_attempts": base_attempts + supplements,
            "same_proof_cube_checker": True,
            "required_signal": 11,
            "proof_sha256": proof_sha,
            "cube_sha256": cube_sha,
            "checker_sha256": checker_sha,
            "proof_content_hash_replay": "journal-bound-stat-only",
        },
        "claim_scope": {
            "hardness_only": True,
            "solver_terminal_claim": False,
            "unsat_claim": False,
            "old_proof_certified": False,
            "recursive_children_require_fresh_proof": True,
            "terminal_publication_authorized": False,
            "root_guard_blocks_only_exclusive_legacy_actions": True,
            "saturator_stop_required": False,
        },
        "source_binding": guard.source_binding(),
    })
    admission_path = tmp_path / "admission.json"
    _write(admission_path, guard.payload(admission))
    return {
        "root": root, "lock": lock, "proof": proof,
        "admission": admission_path,
        "admission_sha": hashlib.sha256(admission_path.read_bytes()).hexdigest(),
        "value": admission,
    }


def _exclusive_available(path: Path) -> bool:
    descriptor = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            return False
        fcntl.flock(descriptor, fcntl.LOCK_UN)
        return True
    finally:
        os.close(descriptor)


def test_guard_holds_shared_lock_and_preserves_all_inputs(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path, monkeypatch)
    watched = [fixture["admission"], fixture["lock"], fixture["proof"]]
    before = {
        path: (path.stat().st_size, path.stat().st_mtime_ns, path.stat().st_ctime_ns)
        for path in watched
    }
    held = guard.acquire(fixture["admission"], fixture["admission_sha"])
    try:
        assert not _exclusive_available(fixture["lock"])
        guard.replay(held)
    finally:
        guard.close(held)
    assert _exclusive_available(fixture["lock"])
    assert before == {
        path: (path.stat().st_size, path.stat().st_mtime_ns, path.stat().st_ctime_ns)
        for path in watched
    }


def test_active_legacy_checker_is_never_interrupted(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path, monkeypatch)
    competitor = os.open(
        fixture["lock"], os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW,
    )
    try:
        fcntl.flock(competitor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        with pytest.raises(guard.C0084RecoveryBusyError, match="not interrupted"):
            guard.acquire(fixture["admission"], fixture["admission_sha"])
    finally:
        fcntl.flock(competitor, fcntl.LOCK_UN)
        os.close(competitor)
    held = guard.acquire(fixture["admission"], fixture["admission_sha"])
    guard.close(held)


def test_59_sigsegv_attempts_are_hardness_only_not_unsat(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path, monkeypatch)
    assert fixture["value"]["incident"]["total_attempts"] == 59
    assert fixture["value"]["claim_scope"] == {
        "hardness_only": True,
        "solver_terminal_claim": False,
        "unsat_claim": False,
        "old_proof_certified": False,
        "recursive_children_require_fresh_proof": True,
        "terminal_publication_authorized": False,
        "root_guard_blocks_only_exclusive_legacy_actions": True,
        "saturator_stop_required": False,
    }
    held = guard.acquire(fixture["admission"], fixture["admission_sha"])
    guard.close(held)


def test_58_attempts_fail_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(
        tmp_path, monkeypatch, base_attempts=57, supplements=1,
    )
    with pytest.raises(guard.C0084RecoveryGuardError, match="59 exact failures"):
        guard.acquire(fixture["admission"], fixture["admission_sha"])


def test_stale_solver_pid_must_really_be_absent(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path, monkeypatch, solver_pid=os.getpid())
    with pytest.raises(guard.C0084RecoveryGuardError, match="stale PID is present"):
        guard.acquire(fixture["admission"], fixture["admission_sha"])


def test_00_10_11_start_commit_cross_binding_is_mandatory(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path, monkeypatch, bad_session_link=True)
    with pytest.raises(guard.C0084RecoveryGuardError, match="chain is inconsistent"):
        guard.acquire(fixture["admission"], fixture["admission_sha"])


def test_terminal_progress_rejects_guard_before_readiness(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path, monkeypatch)
    _write(fixture["root"] / "COMMIT.json", b"{}\n")
    with pytest.raises(
        quarantine.QuarantineGuardError, match="artifact exists",
    ):
        guard.acquire(fixture["admission"], fixture["admission_sha"])
    assert _exclusive_available(fixture["lock"])


def test_large_proof_content_is_not_rehashed_by_guard(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path, monkeypatch)
    proof_size = fixture["proof"].stat().st_size
    original = quarantine._digest_descriptor
    hashed_sizes: list[int] = []

    def observe(descriptor: int, expected_size: int) -> str:
        hashed_sizes.append(expected_size)
        return original(descriptor, expected_size)

    monkeypatch.setattr(quarantine, "_digest_descriptor", observe)
    held = guard.acquire(fixture["admission"], fixture["admission_sha"])
    guard.close(held)
    assert proof_size not in hashed_sizes


def test_periodic_replay_detects_bound_record_replacement(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path, monkeypatch)
    held = guard.acquire(fixture["admission"], fixture["admission_sha"])
    session = fixture["root"] / guard.REQUIRED_RECORD_PATHS["session"]
    old = session.with_suffix(".old")
    try:
        session.rename(old)
        _write(session, old.read_bytes())
        with pytest.raises(
            quarantine.QuarantineGuardError,
            match="root-relative bound pathname changed",
        ):
            guard.replay(held)
    finally:
        guard.close(held)


def test_source_binding_tamper_is_rejected(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path, monkeypatch)
    value = dict(fixture["value"])
    value.pop("record_sha256")
    value["source_binding"] = json.loads(json.dumps(value["source_binding"]))
    value["source_binding"]["c0084_guard"]["sha256"] = "0" * 64
    changed = guard.seal(value)
    _write(fixture["admission"], guard.payload(changed))
    digest = hashlib.sha256(fixture["admission"].read_bytes()).hexdigest()
    with pytest.raises(
        guard.C0084RecoveryGuardError, match="schema/source binding",
    ):
        guard.acquire(fixture["admission"], digest)


def test_fixed_journal_identity_tamper_is_rejected(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path, monkeypatch)
    value = json.loads(json.dumps(fixture["value"]))
    value.pop("record_sha256")
    value["incident"]["supplemental_attempts"][1]["cursor"] += "-forged"
    changed = guard.seal(value)
    _write(fixture["admission"], guard.payload(changed))
    digest = hashlib.sha256(fixture["admission"].read_bytes()).hexdigest()
    with pytest.raises(
        guard.C0084RecoveryGuardError, match="fixed journal identity",
    ):
        guard.acquire(fixture["admission"], digest)


def test_renderer_emits_source_bound_retry_unit_without_control_actions(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    _fixture(tmp_path, monkeypatch)
    admission = renderer.admission_payload()
    value = json.loads(admission)
    unit = renderer.unit_payload(admission).decode("utf-8")
    assert value["incident"]["total_attempts"] == 59
    assert value["incident"]["proof_content_hash_replay"] == (
        "journal-bound-stat-only"
    )
    assert value["claim_scope"]["hardness_only"] is True
    assert value["claim_scope"]["solver_terminal_claim"] is False
    assert "Type=notify\n" in unit
    assert "Restart=on-failure\n" in unit
    assert "RestartSec=5s\n" in unit
    assert "RefuseManualStart=no\n" in unit
    assert "RefuseManualStop=yes\n" in unit
    assert "KillMode=process\n" in unit
    assert f"--admission-sha256 {hashlib.sha256(admission).hexdigest()}" in unit
    assert "ExecStop=" not in unit
    assert "/usr/bin/systemctl" not in unit
    assert " saturator" not in unit.lower()


def test_renderer_check_is_byte_exact(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    _fixture(tmp_path, monkeypatch)
    output = tmp_path / "rendered"
    output.mkdir()
    monkeypatch.setattr(renderer, "ADMISSION_PATH", output / "admission.json")
    monkeypatch.setattr(renderer, "UNIT_PATH", output / "guard.service")
    assert renderer.render(check=False) is True
    assert renderer.render(check=True) is True
    renderer.UNIT_PATH.write_bytes(renderer.UNIT_PATH.read_bytes() + b"\n")
    assert renderer.render(check=True) is False


def test_recursive_audit_builds_exact_fanout4_from_static_cube(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path, monkeypatch)
    result = split.audit_recovery(
        fixture["admission"], fixture["admission_sha"],
    )
    manifest = result["split_manifest"]
    audit = result["parent_audit"]
    assert result["writes_performed"] is False
    assert result["services_started_or_stopped"] is False
    assert manifest["split_policy"]["fanout"] == 4
    assert [leaf["path"] for leaf in manifest["leaves"]] == [
        "00", "01", "10", "11",
    ]
    assert manifest["coverage"]["mutually_exclusive"] is True
    assert manifest["coverage"]["exhaustive"] is True
    assert manifest["trigger"]["kind"] == split.TRIGGER_KIND
    assert manifest["trigger"]["total_attempts"] == 59
    assert manifest["trigger"]["solver_terminal_claim"] is False
    assert manifest["trigger"]["unsat_claim"] is False
    assert manifest["trigger"]["old_proof_certified"] is False
    assert audit["observed_state"] == "INACTIVE"
    assert audit["timing_evidence"]["admission_threshold_met"] is True


def test_custom_crash_manifest_fails_closed_outside_adapter_runtime(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path, monkeypatch)
    result = split.audit_recovery(
        fixture["admission"], fixture["admission_sha"],
    )
    parent = (fixture["root"] / "static/cube.cnf").read_bytes()
    with pytest.raises(
        split.recursive.RecursiveSplitError,
        match="split trigger",
    ):
        split.recursive.verify_cover(result["split_manifest"], parent)


def test_adapter_runtime_restores_every_frozen_symbol(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path, monkeypatch)
    watched = [
        (split.recursive, "_normalize_trigger"),
        (split.supervisor.child_runner, "_validate_parent_audit"),
        (split.supervisor, "_legacy_source_binding"),
        (split.supervisor, "_legacy_parent_still_split_eligible"),
        (split.supervisor, "GATE"),
        (split.checkpoint_recovery, "_require_checkpoint_receipt"),
        (split.checkpoint_recovery, "_checked_checkpointed_parent"),
        (split.initial_dispatch, "_source_binding"),
        (split.initial_dispatch.batch, "_spawn_child_start"),
    ]
    before = {(id(module), name): getattr(module, name) for module, name in watched}
    with split._adapter_runtime(fixture["admission"], fixture["admission_sha"]):
        assert split.recursive._normalize_trigger is split._normalize_crash_trigger
        assert split.supervisor.child_runner._validate_parent_audit is split._validate_parent_audit
        assert split.initial_dispatch.batch._spawn_child_start is split._spawn_adapter_child_start
    after = {(id(module), name): getattr(module, name) for module, name in watched}
    assert after == before


def test_bundle_creation_uses_standard_queue_and_scheduler_leases_without_dispatch(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path, monkeypatch)
    cpus = [1, 2, 3, 4]
    observations = [
        {
            "cpu": cpu,
            "pinned_running_processes": [],
            "broad_affinity_running_process_count": 0,
            "kernel_hardware_exclusive": False,
            "lease_scope": "recursive-sidecar-dispatch-only",
        }
        for cpu in cpus
    ]
    monkeypatch.setattr(
        split.supervisor, "_validate_cpu_pool",
        lambda values: (list(values), observations),
    )
    control = tmp_path / "recursive-control"
    bundle = control / "r4-c0084-g0-f4-checker-crash-v1"
    result = split.create_bundle(
        bundle,
        admission_path=fixture["admission"],
        admission_file_sha256=fixture["admission_sha"],
        cpus=cpus,
        control_root=control,
    )
    assert result["fanout"] == 4
    assert result["children_dispatched"] is False
    assert result["old_proof_certified"] is False
    manifest = split.supervisor._read_json(bundle / split.supervisor.SPLIT_MANIFEST)
    queue = split.recursive.load_split_queue(bundle / split.supervisor.QUEUE)
    reservation = split.supervisor._read_json(bundle / split.supervisor.CPU_RESERVATION)
    retirement = split.supervisor._read_json(bundle / split.supervisor.PARENT_CHECKPOINT)
    assert manifest["manifest_sha256"] == result["split_manifest_sha256"]
    assert queue["cpu_pool"] == cpus
    assert [item["state"] for item in queue["items"]] == ["PENDING"] * 4
    assert reservation["cpus"] == cpus
    assert reservation["scheduler_lease_only"] is True
    assert retirement["parent_state"] == "INACTIVE_CHECKER_CRASH_GUARDED"
    assert retirement["checkpoint_created"] is False
    assert retirement["old_proof_certified"] is False
    assert not any((bundle / split.supervisor.CHILDREN_DIR).iterdir())


def test_external_child_start_is_forced_through_source_bound_adapter(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path, monkeypatch)
    captured: dict[str, Any] = {}

    class Dummy:
        pass

    def fake_popen(argv, **kwargs):
        captured["argv"] = argv
        captured["kwargs"] = kwargs
        return Dummy()

    monkeypatch.setattr(split.subprocess, "Popen", fake_popen)
    child = tmp_path / "child-00"
    with split._adapter_runtime(fixture["admission"], fixture["admission_sha"]):
        result = split._spawn_adapter_child_start(child, cpu=7)
    assert isinstance(result, Dummy)
    assert captured["argv"][1] == str(Path(split.__file__).resolve())
    assert captured["argv"][2] == "child-start"
    assert captured["argv"][-4:] == ["--root", str(child), "--cpu", "7"]
    assert captured["kwargs"]["close_fds"] is True
