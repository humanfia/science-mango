from __future__ import annotations

import copy
import fcntl
import hashlib
import json
import os
import time
from dataclasses import replace
from pathlib import Path

import pytest

from investigations import paper400_dic5_recursive_split_v1 as recursive
from scripts import paper400_grat_pilot_cpu_reservation_v1 as grat_reservation
from scripts import paper400_native_lrat_lease_owner_v1 as lease_owner
from scripts import paper400_native_lrat_future_v1 as native
from scripts import paper400_native_lrat_launcher_v1 as launcher


@pytest.fixture(autouse=True)
def _deny_production_paths_and_unowned_signals(
    monkeypatch: pytest.MonkeyPatch,
) -> set[int]:
    original_validate_config = launcher._validate_config

    def guarded_validate_config(
        config: launcher.ExecutionConfig, *, test_mode: bool,
    ) -> launcher.ExecutionConfig:
        paths = [config.output_root, *config.lease_catalogs]
        assert all(
            Path(path) != launcher.RUNS and launcher.RUNS not in Path(path).parents
            for path in paths
        ), "native-LRAT tests may not touch the production run tree"
        return original_validate_config(config, test_mode=test_mode)

    monkeypatch.setattr(launcher, "_validate_config", guarded_validate_config)
    owned_pids: set[int] = set()
    original_fork = os.fork

    def guarded_fork() -> int:
        pid = original_fork()
        if pid > 0:
            owned_pids.add(pid)
        return pid

    monkeypatch.setattr(launcher.os, "fork", guarded_fork)
    original_kill = os.kill
    original_killpg = os.killpg

    def guarded_kill(pid: int, sig: int) -> None:
        assert pid == os.getpid() or pid in owned_pids
        original_kill(pid, sig)

    def guarded_killpg(pgid: int, sig: int) -> None:
        assert pgid in owned_pids
        original_killpg(pgid, sig)

    monkeypatch.setattr(launcher.os, "kill", guarded_kill)
    monkeypatch.setattr(launcher.os, "killpg", guarded_killpg)
    return owned_pids


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _write_json(path: Path, value: object, *, mode: int = 0o600) -> None:
    path.write_bytes(native.canonical_bytes(value) + b"\n")
    path.chmod(mode)


def _reservation(root: Path, cpus: list[int]) -> dict[str, object]:
    created_at = time.time()
    value = native.seal({
        "schema_version": 1,
        "kind": launcher.RESERVATION_KIND,
        "bundle": str(root),
        "cpus": sorted(cpus),
        "observations": [{
            "cpu": cpu,
            "pinned_running_processes": [],
            "broad_affinity_running_process_count": 0,
            "kernel_hardware_exclusive": False,
            "lease_scope": launcher.RESERVATION_LEASE_SCOPE,
        } for cpu in sorted(cpus)],
        "kernel_hardware_exclusive": False,
        "scheduler_lease_only": True,
        "created_at": created_at,
    }, "reservation_sha256")
    _write_json(root / "cpu-reservation.json", value, mode=0o400)
    state = lease_owner._state(
        value, state="ACTIVE", epoch=1,
        acquired_at=created_at, renewed_at=created_at,
        expires_at=created_at + 3600.0,
    )
    _write_json(root / lease_owner.STATE_FILE, state, mode=0o600)
    return value


def _resource_tree(base: Path) -> tuple[Path, Path]:
    proc = base / "fake-proc"
    (proc / "pressure").mkdir(parents=True)
    (proc / "self").mkdir()
    (proc / "meminfo").write_text(
        "MemAvailable: 1048576 kB\n", encoding="ascii",
    )
    (proc / "vmstat").write_text("oom_kill 0\n", encoding="ascii")
    psi = (
        "some avg10=0.00 avg60=0.00 avg300=0.00 total=0\n"
        "full avg10=0.00 avg60=0.00 avg300=0.00 total=0\n"
    )
    (proc / "pressure/memory").write_text(psi, encoding="ascii")
    (proc / "self/cgroup").write_text(
        "0::/native-test\n", encoding="ascii",
    )
    mount = base / "fake-cgroup"
    cgroup = mount / "native-test"
    cgroup.mkdir(parents=True)
    (cgroup / "memory.current").write_text("0\n", encoding="ascii")
    (cgroup / "memory.max").write_text("1073741824\n", encoding="ascii")
    (cgroup / "memory.events").write_text(
        "oom 0\noom_kill 0\n", encoding="ascii",
    )
    (cgroup / "memory.pressure").write_text(psi, encoding="ascii")
    return proc, mount


def _resource_kwargs(base: Path) -> dict[str, object]:
    proc, mount = _resource_tree(base)
    return {
        "proc_root": proc,
        "cgroup_mount": mount,
        "min_host_available_bytes": 1,
        "min_cgroup_available_bytes": 1,
        "max_host_psi_some_avg10": 100.0,
        "max_host_psi_full_avg10": 100.0,
        "max_cgroup_psi_some_avg10": 100.0,
        "max_cgroup_psi_full_avg10": 100.0,
    }


def _catalogs(
    base: Path, root: Path, reservation_sha256: str, cpus: list[int],
) -> tuple[Path, ...]:
    base.mkdir(mode=0o700, parents=True, exist_ok=True)
    result: list[Path] = []
    for index in range(3):
        directory = base / f"catalog-{index}"
        directory.mkdir(mode=0o700)
        lock = directory / "cpu-leases.lock"
        lock.write_bytes(b"")
        lock.chmod(0o600)
        path = directory / "cpu-leases.json"
        value = native.seal({
            "schema_version": 1,
            "kind": launcher.CATALOG_KIND,
            "leases": [
                {
                    "cpu": cpu,
                    "bundle": str(root),
                    "reservation_sha256": reservation_sha256,
                    "state": "RESERVED",
                    "created_at": 1_700_000_000.0,
                    "released_at": None,
                }
                for cpu in cpus
            ],
            "updated_at": 1_700_000_000.0,
        }, "catalog_sha256")
        _write_json(path, value)
        result.append(path)
    return tuple(sorted(result, key=str))


def _pins(tmp_path: Path, *, checker_second_fails: bool = False) -> native.ToolchainPins:
    tools = tmp_path / "tools"
    tools.mkdir(mode=0o700, parents=True)
    solver = tools / "cadical"
    solver.write_text(
        "#!/usr/bin/python3\n"
        "import os,sys\n"
        "assert sys.argv[1:3] == ['--lrat','--no-binary']\n"
        "assert sys.argv[3] == '/proc/self/fd/201'\n"
        "assert sys.argv[4] == '/proc/self/fd/202'\n"
        "open(sys.argv[4],'wb',buffering=0).write(b'3 0 0\\n')\n"
        "raise SystemExit(20)\n",
        encoding="ascii",
    )
    solver.chmod(0o700)
    checker = tools / "lrat-check"
    if checker_second_fails:
        checker.write_text(
            "#!/usr/bin/python3\n"
            "import pathlib,sys\n"
            "counter=pathlib.Path(__file__).with_suffix('.count')\n"
            "n=int(counter.read_text() if counter.exists() else '0')+1\n"
            "counter.write_text(str(n))\n"
            "assert sys.argv[1:] == ['/proc/self/fd/211','/proc/self/fd/212']\n"
            "assert open(sys.argv[2],'rb').read()\n"
            "print('c VERIFIED' if n == 1 else 'c INVALID')\n"
            "raise SystemExit(0 if n == 1 else 1)\n",
            encoding="ascii",
        )
    else:
        checker.write_text(
            "#!/usr/bin/python3\n"
            "import sys\n"
            "assert sys.argv[1:] == ['/proc/self/fd/211','/proc/self/fd/212']\n"
            "assert open(sys.argv[2],'rb').read()\n"
            "print('c VERIFIED')\n",
            encoding="ascii",
        )
    checker.chmod(0o700)
    audit_value = {
        "schema_version": 1,
        "kind": "cadical-rel-1.9.5-standalone-audit-v1",
        "status": "PASS",
        "build": {"generated_files": {"build/cadical": {
            "bytes": solver.stat().st_size, "sha256": _sha(solver),
        }}},
        "scope": {"n400_solver_invoked": False},
        "cli_audit": {
            "default_proof_format": "binary DRAT",
            "exit_codes": {"sat": 10, "unsat": 20, "unknown": 0},
            "version": {"returncode": 0, "stdout": "1.9.5"},
        },
        "upstream": {"commit_git_sha1": "1" * 40},
    }
    audit = tools / "standalone-audit-manifest.json"
    _write_json(audit, audit_value)
    marker_hash = hashlib.sha256(b"c VERIFIED\n").hexdigest()
    policy_value = native.seal({
        "schema_version": 1,
        "kind": "paper400-trusted-checker-policy-v1",
        "checkers": {
            "lrat-check-v05.22.2023-gcc11.4.0-x86_64": {
                "argv_roles": ["binary", "dimacs", "proof"],
                "binary_sha256": _sha(checker),
                "checker_role": "lrat-check",
                "max_proof_bytes": 1 << 20,
                "proof_format": "lrat",
                "semantic_stdout_sha256": marker_hash,
                "source_commit": "2" * 40,
                "timeout_s": 30,
            }
        },
    }, "policy_sha256")
    policy = tools / "trusted-checker-policy.json"
    _write_json(policy, policy_value)
    return native.ToolchainPins(
        solver_path=solver,
        solver_sha256=_sha(solver),
        solver_version="1.9.5",
        solver_upstream_commit="1" * 40,
        audit_path=audit,
        audit_sha256=_sha(audit),
        lrat_checker_path=checker,
        lrat_checker_sha256=_sha(checker),
        lrat_checker_source_commit="2" * 40,
        trusted_policy_path=policy,
        trusted_policy_file_sha256=_sha(policy),
        trusted_policy_internal_sha256=policy_value["policy_sha256"],
        lrat_checker_semantic_stdout_sha256=marker_hash,
        lrat_checker_timeout_seconds=30,
        lrat_checker_max_proof_bytes=1 << 20,
    )


def _world(
    tmp_path: Path, *, participants: int = 2,
    checker_second_fails: bool = False,
) -> dict[str, object]:
    tmp_path.mkdir(mode=0o700, parents=True, exist_ok=True)
    allowed = sorted(os.sched_getaffinity(0))
    if len(allowed) < participants:
        pytest.skip("test needs enough allowed CPUs")
    cpus = allowed[:participants]
    root = tmp_path / "pilot"
    root.mkdir(mode=0o700)
    leaves_root = root / "leaves"
    leaves_root.mkdir(mode=0o700)
    reservation = _reservation(root, cpus)
    catalogs = _catalogs(
        tmp_path, root, str(reservation["reservation_sha256"]), cpus,
    )
    inputs = tmp_path / "inputs"
    inputs.mkdir(mode=0o700)
    leaves = []
    for index, cpu in enumerate(cpus):
        leaf_id = f"leaf-{index:02d}"
        leaf_root = leaves_root / leaf_id
        leaf_root.mkdir(mode=0o700)
        cnf = inputs / f"{leaf_id}.cnf"
        cnf.write_bytes(b"c tiny UNSAT\np cnf 1 2\n1 0\n-1 0\n")
        cnf.chmod(0o600)
        leaves.append({
            "leaf_id": leaf_id,
            "cnf_path": str(cnf),
            "proof_output_path": str(leaf_root / "proof.lrat"),
            "cpu_lease": launcher.derive_plan_cpu_lease(
                cpu=cpu, bundle=root,
                reservation_sha256=str(reservation["reservation_sha256"]),
                catalogs=catalogs,
            ),
        })
    pins = _pins(tmp_path, checker_second_fails=checker_second_fails)
    spec = {
        "schema_version": 1,
        "kind": native.SPEC_KIND,
        "campaign_id": "native-lrat-pilot-test",
        "launch_id": "launch-001",
        "generation": 0,
        "fresh_leaf_generation": True,
        "resume": False,
        "checkpoint_source": None,
        "existing_proof_path": None,
        "existing_proof_format": None,
        "all_start_barrier": {
            "barrier_id": "all-start-001",
            "timeout_seconds": 10,
            "require_every_leaf": True,
        },
        "leaves": leaves,
    }
    plan = native.build_plan(spec, pins=pins)
    config = launcher.ExecutionConfig(
        output_root=root,
        lease_catalogs=catalogs,
        reservation_sha256=str(reservation["reservation_sha256"]),
        solver_timeout_seconds=10,
        checker_timeout_seconds=10,
        proof_cap_bytes=1 << 20,
        stdout_cap_bytes=1 << 20,
        stderr_cap_bytes=1 << 20,
        lease_recheck_seconds=0.05,
        disk_reserve_bytes=1,
        sealed_elf_runtime=False,
        **_resource_kwargs(tmp_path / "resource-world"),
    )
    return {
        "root": root, "leaves_root": leaves_root, "reservation": reservation,
        "catalogs": catalogs, "cpus": cpus, "pins": pins,
        "spec": spec, "plan": plan, "config": config,
    }


def _test_audit(world: dict[str, object]) -> dict[str, object]:
    return launcher.audit_pilot(
        world["plan"], world["config"],  # type: ignore[arg-type]
        pins=world["pins"],  # type: ignore[arg-type]
        _test_nonce=launcher._TEST_ONLY_NONCE,
    )


def test_three_catalog_contract_and_read_only_audit(tmp_path: Path) -> None:
    world = _world(tmp_path)
    before = [path.read_bytes() for path in world["catalogs"]]  # type: ignore[union-attr]
    audit = _test_audit(world)
    reservation_path = Path(world["root"]) / "cpu-reservation.json"  # type: ignore[arg-type]
    assert reservation_path.stat().st_mode & 0o777 == 0o400
    assert all(
        item["lease_scope"] == launcher.RESERVATION_LEASE_SCOPE
        for item in world["reservation"]["observations"]  # type: ignore[index]
    )
    assert audit["go"] is True
    assert audit["production_eligible"] is False
    assert audit["lease_authority"]["each_cpu_has_one_identical_owner_in_every_catalog"] is True
    assert audit["queue_mutation"] is False
    assert audit["terminal_publication"] is False
    assert [path.read_bytes() for path in world["catalogs"]] == before  # type: ignore[union-attr]
    assert set(item.name for item in Path(world["root"]).iterdir()) == {  # type: ignore[arg-type]
        "cpu-reservation.json", lease_owner.STATE_FILE, "leaves",
    }


def test_grat_schema_fixture_is_not_native_lrat_reservation_authority(
    tmp_path: Path,
) -> None:
    world = _world(tmp_path, participants=1)
    grat_value = grat_reservation._reservation(
        world["root"], world["cpus"], 1_700_000_001.0,  # type: ignore[arg-type]
    )
    (Path(world["root"]) / "cpu-reservation.json").chmod(0o600)  # type: ignore[arg-type]
    _write_json(
        Path(world["root"]) / "cpu-reservation.json",  # type: ignore[arg-type]
        grat_value, mode=0o400,
    )
    config = replace(
        world["config"],  # type: ignore[arg-type]
        reservation_sha256=grat_value["reservation_sha256"],
    )
    with pytest.raises(launcher.NativeLratLaunchError, match="malformed or cross-bound"):
        launcher._validate_reservation(config, world["cpus"])  # type: ignore[arg-type]


@pytest.mark.parametrize("conflict_kind", ["pinned", "broad"])
def test_native_reservation_rejects_every_nonempty_conflict_observation(
    tmp_path: Path, conflict_kind: str,
) -> None:
    world = _world(tmp_path, participants=1)
    reservation = copy.deepcopy(world["reservation"])
    reservation.pop("reservation_sha256")
    observation = reservation["observations"][0]
    if conflict_kind == "pinned":
        observation["pinned_running_processes"] = [{
            "command": "foreign-worker", "pid": 12345, "state": "R",
        }]
    else:
        observation["broad_affinity_running_process_count"] = 1
    reservation = native.seal(reservation, "reservation_sha256")
    reservation_path = Path(world["root"]) / "cpu-reservation.json"
    reservation_path.chmod(0o600)
    _write_json(reservation_path, reservation, mode=0o400)
    config = replace(
        world["config"],
        reservation_sha256=reservation["reservation_sha256"],
    )
    with pytest.raises(
        launcher.NativeLratLaunchError,
        match="nonempty conflict observation",
    ):
        launcher._validate_reservation(config, world["cpus"])


def test_missing_or_mismatched_catalog_owner_fails_closed(tmp_path: Path) -> None:
    world = _world(tmp_path)
    path = world["catalogs"][1]  # type: ignore[index]
    value = json.loads(path.read_text(encoding="ascii"))
    unsigned = dict(value)
    unsigned.pop("catalog_sha256")
    unsigned["leases"] = unsigned["leases"][1:]
    _write_json(path, native.seal(unsigned, "catalog_sha256"))
    with pytest.raises(launcher.NativeLratLaunchError, match="exactly one active owner"):
        _test_audit(world)

    world2 = _world(tmp_path / "other")
    path2 = world2["catalogs"][0]  # type: ignore[index]
    value2 = json.loads(path2.read_text(encoding="ascii"))
    unsigned2 = dict(value2)
    unsigned2.pop("catalog_sha256")
    unsigned2["leases"][0]["bundle"] = str(tmp_path / "wrong-owner")
    _write_json(path2, native.seal(unsigned2, "catalog_sha256"))
    with pytest.raises(launcher.NativeLratLaunchError, match="mismatched scheduler owner"):
        _test_audit(world2)


def test_launcher_resource_gate_blocks_before_any_fork(
    tmp_path: Path,
    _deny_production_paths_and_unowned_signals: set[int],
) -> None:
    world = _world(tmp_path, participants=1)
    config = world["config"]
    (config.proc_root / "meminfo").write_text(
        "MemAvailable: 0 kB\n", encoding="ascii",
    )
    with pytest.raises(launcher.NativeLratLaunchError, match="resource admission is NO-GO"):
        launcher.run_pilot(
            world["plan"], config, pins=world["pins"],
            _test_nonce=launcher._TEST_ONLY_NONCE,
        )
    assert not _deny_production_paths_and_unowned_signals


def test_launcher_rejects_expired_native_lease_state(tmp_path: Path) -> None:
    world = _world(tmp_path, participants=1)
    now = time.time()
    expired = lease_owner._state(
        world["reservation"], state="ACTIVE", epoch=2,
        acquired_at=now - 120.0, renewed_at=now - 60.0,
        expires_at=now - 1.0,
    )
    _write_json(
        Path(world["root"]) / lease_owner.STATE_FILE,
        expired, mode=0o600,
    )
    with pytest.raises(launcher.NativeLratLaunchError, match="inactive, expired"):
        _test_audit(world)
    assert not (Path(world["root"]) / "00-launch-intent.json").exists()


def test_plan_lease_tamper_and_extra_root_material_are_rejected(tmp_path: Path) -> None:
    world = _world(tmp_path)
    attacked = copy.deepcopy(world["plan"])
    attacked["participants"][0]["cpu_lease"]["lease_token_sha256"] = "f" * 64
    attacked["plan_sha256"] = native._digest({
        key: value for key, value in attacked.items() if key != "plan_sha256"
    })
    with pytest.raises(native.NativeLratPlanError, match="does not match"):
        launcher.audit_pilot(
            attacked, world["config"], pins=world["pins"],  # type: ignore[arg-type]
            _test_nonce=launcher._TEST_ONLY_NONCE,
        )

    marker = Path(world["root"]) / "checkpoint.dmtcp"  # type: ignore[arg-type]
    marker.write_bytes(b"forbidden")
    with pytest.raises(launcher.NativeLratLaunchError, match="contain only"):
        _test_audit(world)


def test_all_start_native_lrat_and_two_distinct_checks(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    world = _world(tmp_path)
    original_file_record = launcher._file_record
    proof_writer_observations: list[list[int]] = []

    def assert_no_writer(path: Path, role: str, *, cap: int) -> dict[str, object]:
        if role == "native-ascii-lrat-proof":
            identity = path.stat()
            writable: list[int] = []
            for name in os.listdir("/proc/self/fd"):
                if not name.isdecimal():
                    continue
                fd = int(name)
                try:
                    info = os.fstat(fd)
                    mode = fcntl.fcntl(fd, fcntl.F_GETFL) & os.O_ACCMODE
                except OSError:
                    continue
                if (info.st_dev, info.st_ino) == (identity.st_dev, identity.st_ino):
                    if mode in {os.O_WRONLY, os.O_RDWR}:
                        writable.append(fd)
            proof_writer_observations.append(writable)
            assert writable == []
        return original_file_record(path, role, cap=cap)

    monkeypatch.setattr(launcher, "_file_record", assert_no_writer)
    result = launcher.run_pilot(
        world["plan"], world["config"],  # type: ignore[arg-type]
        pins=world["pins"],  # type: ignore[arg-type]
        _test_nonce=launcher._TEST_ONLY_NONCE,
    )
    assert result["status"] == "PILOT_VERIFIED"
    assert result["all_native_lrat_proofs_checked_twice"] is True
    assert result["terminal_publication"] is False
    assert len(proof_writer_observations) == 2
    barrier = json.loads(
        (Path(world["root"]) / "20-all-start-barrier.json").read_text(encoding="ascii")  # type: ignore[arg-type]
    )
    assert barrier["all_start_receipts_complete"] is True
    assert len(barrier["membership"]) == 2
    assert len(set(
        (item["pid"], item["proc_start_ticks"])
        for item in barrier["pid_start_identities"]
    )) == 2
    for leaf in Path(world["leaves_root"]).iterdir():  # type: ignore[arg-type]
        assert (leaf / "proof.lrat").read_bytes() == b"3 0 0\n"
        handoff = json.loads(
            (leaf / "40-certification-handoff.json").read_text(encoding="ascii")
        )
        assert handoff["initial_lrat_check"]["verified"] is True
        assert handoff["fresh_lrat_replay"]["verified"] is True
        first = handoff["initial_lrat_check"]["process"]
        second = handoff["fresh_lrat_replay"]["process"]
        assert (first["pid"], first["proc_start_ticks"]) != (
            second["pid"], second["proc_start_ticks"]
        )
        assert handoff["is_recursive_certificate"] is False
        assert handoff["has_certificate_sha256"] is False
        assert "certificate_sha256" not in handoff
        assert handoff["adapter_candidate"]["solver_terminal_claim"] is False
        assert handoff["ready_for_external_authoritative_certifier"] is False


def test_fixed_fd_target_collisions_are_relocated_before_exec(tmp_path: Path) -> None:
    world = _world(tmp_path, participants=1)
    fillers: list[int] = []
    try:
        while not fillers or fillers[-1] < launcher.SOLVER_CNF_FD - 2:
            fillers.append(os.open("/dev/null", os.O_RDONLY | os.O_CLOEXEC))
        if fillers[-1] != launcher.SOLVER_CNF_FD - 2:
            pytest.skip("fixed protocol FD neighbourhood is already occupied")
        # run_pilot's persistent CNF/proof opens now land on 200/201.  Thus
        # the proof source numerically collides with the CNF target; an
        # unsafe sequential dup2 implementation would pass the CNF twice.
        result = launcher.run_pilot(
            world["plan"], world["config"],  # type: ignore[arg-type]
            pins=world["pins"],  # type: ignore[arg-type]
            _test_nonce=launcher._TEST_ONLY_NONCE,
        )
        assert result["status"] == "PILOT_VERIFIED"
        leaf = next(Path(world["leaves_root"]).iterdir())  # type: ignore[arg-type]
        assert (leaf / "proof.lrat").read_bytes() == b"3 0 0\n"
    finally:
        for fd in fillers:
            os.close(fd)


def test_postfork_construction_failure_reaps_unregistered_child(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    _deny_production_paths_and_unowned_signals: set[int],
) -> None:
    world = _world(tmp_path, participants=1)

    def fail_child_construction(*args: object, **kwargs: object) -> object:
        raise RuntimeError("simulated post-fork child construction failure")

    monkeypatch.setattr(launcher, "_Child", fail_child_construction)
    with pytest.raises(RuntimeError, match="post-fork child construction failure"):
        launcher.run_pilot(
            world["plan"], world["config"],  # type: ignore[arg-type]
            pins=world["pins"],  # type: ignore[arg-type]
            _test_nonce=launcher._TEST_ONLY_NONCE,
        )
    assert _deny_production_paths_and_unowned_signals
    for pid in _deny_production_paths_and_unowned_signals:
        with pytest.raises(ChildProcessError):
            os.waitpid(pid, os.WNOHANG)
    failure = json.loads(
        (Path(world["root"]) / "99-failure.json").read_text(encoding="ascii")  # type: ignore[arg-type]
    )
    assert failure["owned_process_termination_error"] is None
    assert failure["terminal_publication"] is False


def test_postfork_registry_failure_reaps_unregistered_child(
    tmp_path: Path,
    _deny_production_paths_and_unowned_signals: set[int],
) -> None:
    class RefusingRegistry(list[launcher._Child]):
        def append(self, child: launcher._Child) -> None:
            raise RuntimeError("injected registry failure")

    cnf = tmp_path / "tiny.cnf"
    proof = tmp_path / "proof.lrat"
    cnf.write_bytes(b"p cnf 1 2\n1 0\n-1 0\n")
    proof.write_bytes(b"")
    cnf_fd = os.open(cnf, os.O_RDONLY | os.O_CLOEXEC)
    proof_fd = os.open(proof, os.O_WRONLY | os.O_CLOEXEC)
    try:
        with pytest.raises(RuntimeError, match="injected registry failure"):
            launcher._fork_gated_child(
                leaf_id="synthetic/00", role="solver",
                cpu=min(os.sched_getaffinity(0)),
                cnf_fd=cnf_fd, proof_fd=proof_fd,
                logical_argv=["/bin/true"], runtime=None,
                proof_cap=1 << 20, owner_registry=RefusingRegistry(),
            )
    finally:
        os.close(cnf_fd)
        os.close(proof_fd)
    assert _deny_production_paths_and_unowned_signals
    for pid in _deny_production_paths_and_unowned_signals:
        with pytest.raises(ChildProcessError):
            os.waitpid(pid, os.WNOHANG)


def test_second_checker_failure_never_publishes_handoff(tmp_path: Path) -> None:
    world = _world(tmp_path, participants=1, checker_second_fails=True)
    with pytest.raises(launcher.NativeLratLaunchError, match="fresh-lrat-replay"):
        launcher.run_pilot(
            world["plan"], world["config"],  # type: ignore[arg-type]
            pins=world["pins"],  # type: ignore[arg-type]
            _test_nonce=launcher._TEST_ONLY_NONCE,
        )
    leaf = next(Path(world["leaves_root"]).iterdir())  # type: ignore[arg-type]
    assert (leaf / "proof.lrat").exists()
    assert not (leaf / "40-certification-handoff.json").exists()
    failure = json.loads(
        (Path(world["root"]) / "99-failure.json").read_text(encoding="ascii")  # type: ignore[arg-type]
    )
    assert failure["automatic_retry"] is False
    assert failure["terminal_publication"] is False
    assert failure["proof_outputs_may_be_abandoned"] is True
    artifact = failure["proof_artifacts"][leaf.name]
    assert artifact["exists"] is True
    assert artifact["regular"] is True
    assert artifact["bytes"] > 0


def test_final_replay_failure_records_existing_proof_as_abandoned(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    world = _world(tmp_path, participants=1)
    original = launcher._catalog_snapshot

    def fail_after_handoff(config: object, participants: object) -> dict[str, object]:
        leaf = next(Path(world["leaves_root"]).iterdir())  # type: ignore[arg-type]
        if (leaf / "40-certification-handoff.json").exists():
            raise launcher.NativeLratLaunchError("simulated final replay failure")
        return original(config, participants)  # type: ignore[arg-type]

    monkeypatch.setattr(launcher, "_catalog_snapshot", fail_after_handoff)
    with pytest.raises(launcher.NativeLratLaunchError, match="final replay failure"):
        launcher.run_pilot(
            world["plan"], world["config"],  # type: ignore[arg-type]
            pins=world["pins"],  # type: ignore[arg-type]
            _test_nonce=launcher._TEST_ONLY_NONCE,
        )
    failure = json.loads(
        (Path(world["root"]) / "99-failure.json").read_text(encoding="ascii")  # type: ignore[arg-type]
    )
    leaf = next(Path(world["leaves_root"]).iterdir())  # type: ignore[arg-type]
    assert (leaf / "40-certification-handoff.json").exists()
    assert failure["proof_outputs_may_be_abandoned"] is True
    assert failure["proof_artifacts"][leaf.name]["bytes"] > 0
    assert not (Path(world["root"]) / "50-pilot-result.json").exists()  # type: ignore[arg-type]


@pytest.mark.parametrize("race_point", ["before-receipt", "before-release"])
def test_replaced_o_excl_proof_inode_fails_before_solver_release(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, race_point: str,
) -> None:
    world = _world(tmp_path, participants=1)
    leaf = next(Path(world["leaves_root"]).iterdir())  # type: ignore[arg-type]
    proof = leaf / "proof.lrat"

    def replace_proof() -> None:
        proof.unlink()
        proof.write_bytes(b"")
        proof.chmod(0o600)

    if race_point == "before-receipt":
        original_ready = launcher._wait_gated_ready

        def raced_ready(children: object, timeout_seconds: int) -> None:
            original_ready(children, timeout_seconds)  # type: ignore[arg-type]
            replace_proof()

        monkeypatch.setattr(launcher, "_wait_gated_ready", raced_ready)
    else:
        original_barrier = native.build_barrier_receipt

        def raced_barrier(*args: object, **kwargs: object) -> dict[str, object]:
            result = original_barrier(*args, **kwargs)  # type: ignore[arg-type]
            replace_proof()
            return result

        monkeypatch.setattr(native, "build_barrier_receipt", raced_barrier)

    with pytest.raises(launcher.NativeLratLaunchError, match="bound file identity changed"):
        launcher.run_pilot(
            world["plan"], world["config"],  # type: ignore[arg-type]
            pins=world["pins"],  # type: ignore[arg-type]
            _test_nonce=launcher._TEST_ONLY_NONCE,
        )
    assert proof.stat().st_size == 0
    assert not (Path(world["root"]) / "30-solver-group-result.json").exists()  # type: ignore[arg-type]
    assert not (leaf / "solver.stdout").exists()


def test_cleanup_never_signals_a_reaped_numeric_process_group(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    child = launcher._Child(
        leaf_id="reaped", role="solver", cpu=0, pid=424_242,
        ready_fd=-1, gate_fd=-1, stdout_fd=-1, stderr_fd=-1,
        logical_argv=[], transport_argv=[], proc_start_ticks=123,
        exit_code=20, reaped=True,
    )
    signals: list[tuple[str, int, int]] = []
    monkeypatch.setattr(
        launcher.os, "killpg",
        lambda pid, sig: signals.append(("group", pid, sig)),
    )
    monkeypatch.setattr(
        launcher.os, "kill",
        lambda pid, sig: signals.append(("process", pid, sig)),
    )
    launcher._terminate_owned([child])
    assert signals == []


def test_lease_replay_failure_at_barrier_releases_no_solver(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    world = _world(tmp_path)
    original = launcher._catalog_snapshot
    calls = 0

    def fail_second_snapshot(config: object, participants: object) -> dict[str, object]:
        nonlocal calls
        calls += 1
        if calls == 2:
            raise launcher.NativeLratLaunchError("simulated lease loss at barrier")
        return original(config, participants)  # type: ignore[arg-type]

    monkeypatch.setattr(launcher, "_catalog_snapshot", fail_second_snapshot)
    with pytest.raises(launcher.NativeLratLaunchError, match="lease loss at barrier"):
        launcher.run_pilot(
            world["plan"], world["config"],  # type: ignore[arg-type]
            pins=world["pins"],  # type: ignore[arg-type]
            _test_nonce=launcher._TEST_ONLY_NONCE,
        )
    assert (Path(world["root"]) / "20-all-start-barrier.json").exists()  # type: ignore[arg-type]
    assert not (Path(world["root"]) / "30-solver-group-result.json").exists()  # type: ignore[arg-type]
    for leaf in Path(world["leaves_root"]).iterdir():  # type: ignore[arg-type]
        assert (leaf / "proof.lrat").stat().st_size == 0
        assert not (leaf / "solver.stdout").exists()
        assert not (leaf / "40-certification-handoff.json").exists()


def test_recursive_binding_is_read_only_and_still_not_a_certificate(tmp_path: Path) -> None:
    allowed_cpu = min(os.sched_getaffinity(0))
    parent = b"p cnf 2 2\n1 0\n-1 0\n"
    manifest, payloads = recursive.build_binary_cover(
        parent, fanout=2, split_variables=[2], parent_id="toy",
    )
    queue_path = tmp_path / "recursive-queue.json"
    time_value = 1_900_000_000.0
    queue = recursive.create_split_queue(
        queue_path, manifest, cpu_pool=[allowed_cpu], default_cpu_slots=1,
        lease_seconds=3600, now=time_value,
    )
    claim = recursive.claim_queue_item(
        queue_path, worker_id="native-lrat-test", now=time_value,
        lease_seconds=3600,
    )
    assert claim is not None
    item = claim["item"]

    root = tmp_path / "pilot"
    root.mkdir(mode=0o700)
    leaves_root = root / "leaves"
    leaves_root.mkdir(mode=0o700)
    leaf_root = leaves_root / item["leaf_id"]
    leaf_root.mkdir(mode=0o700)
    reservation = _reservation(root, [allowed_cpu])
    catalogs = _catalogs(
        tmp_path / "catalog-world", root,
        str(reservation["reservation_sha256"]), [allowed_cpu],
    )
    cnf = tmp_path / "child.cnf"
    cnf.write_bytes(payloads[item["path"]])
    cnf.chmod(0o600)
    pins = _pins(tmp_path / "pin-world")
    spec = {
        "schema_version": 1, "kind": native.SPEC_KIND,
        "campaign_id": "recursive-native-lrat-test", "launch_id": "launch-001",
        "generation": 0, "fresh_leaf_generation": True, "resume": False,
        "checkpoint_source": None, "existing_proof_path": None,
        "existing_proof_format": None,
        "all_start_barrier": {
            "barrier_id": "recursive-barrier", "timeout_seconds": 10,
            "require_every_leaf": True,
        },
        "leaves": [{
            "leaf_id": item["leaf_id"], "cnf_path": str(cnf),
            "proof_output_path": str(leaf_root / "proof.lrat"),
            "cpu_lease": launcher.derive_plan_cpu_lease(
                cpu=allowed_cpu, bundle=root,
                reservation_sha256=str(reservation["reservation_sha256"]),
                catalogs=catalogs,
            ),
        }],
    }
    plan = native.build_plan(spec, pins=pins)
    binding = launcher.build_recursive_binding(
        plan, queue_path=queue_path, item_id=item["item_id"], pins=pins,
    )
    before = queue_path.read_bytes()
    replay = launcher._replay_recursive_binding(plan, binding)
    assert replay["claim_live"] is True
    assert queue_path.read_bytes() == before
    assert binding["leaf_sha256"] == item["leaf_sha256"]
    assert "certificate_sha256" not in binding
    config = launcher.ExecutionConfig(
        output_root=root, lease_catalogs=catalogs,
        reservation_sha256=str(reservation["reservation_sha256"]),
        solver_timeout_seconds=10, checker_timeout_seconds=10,
        proof_cap_bytes=1 << 20, stdout_cap_bytes=1 << 20,
        stderr_cap_bytes=1 << 20, lease_recheck_seconds=0.05,
        disk_reserve_bytes=1, sealed_elf_runtime=False,
        **_resource_kwargs(tmp_path / "resource-world"),
    )
    result = launcher.run_pilot(
        plan, config, pins=pins, recursive_bindings=[binding],
        _test_nonce=launcher._TEST_ONLY_NONCE,
    )
    assert result["status"] == "PILOT_VERIFIED"
    handoff = json.loads(
        (leaf_root / "40-certification-handoff.json").read_text(encoding="ascii")
    )
    assert handoff["ready_for_external_authoritative_certifier"] is True
    assert handoff["recursive_binding_final_replay"]["claim_live"] is True
    assert handoff["adapter_candidate"]["leaf_sha256"] == item["leaf_sha256"]
    assert handoff["adapter_candidate"]["solver_terminal_claim"] is False
    assert recursive._queue_certificate_complete(
        handoff["adapter_candidate"], item, None,
    ) is False
    assert queue_path.read_bytes() == before


def test_cli_mode_refuses_nonversioned_test_root(tmp_path: Path) -> None:
    world = _world(tmp_path)
    with pytest.raises(launcher.NativeLratLaunchError, match="versioned pilot root"):
        launcher.audit_pilot(
            world["plan"], world["config"], pins=world["pins"],  # type: ignore[arg-type]
        )


def test_read_only_derive_lease_cli(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    world = _world(tmp_path, participants=1)
    cpu = world["cpus"][0]  # type: ignore[index]
    argv = [
        "derive-lease", "--output-root", str(world["root"]),
        "--reservation-sha256", str(world["reservation"]["reservation_sha256"]),  # type: ignore[index]
        "--cpu", str(cpu),
    ]
    for catalog in world["catalogs"]:  # type: ignore[union-attr]
        argv.extend(["--lease-catalog", str(catalog)])
    assert launcher.main(argv) == 0
    value = json.loads(capsys.readouterr().out)
    expected = launcher.derive_plan_cpu_lease(
        cpu=cpu, bundle=world["root"],  # type: ignore[arg-type]
        reservation_sha256=str(world["reservation"]["reservation_sha256"]),  # type: ignore[index]
        catalogs=world["catalogs"],  # type: ignore[arg-type]
    )
    assert expected == value


def test_real_pinned_cadical_ascii_lrat_integration(tmp_path: Path) -> None:
    if not native.SOLVER_PATH.exists() or not native.LRAT_CHECKER_PATH.exists():
        pytest.skip("pinned Paper400 tools are unavailable")
    allowed_cpu = min(os.sched_getaffinity(0))
    root = tmp_path / "real-pilot"
    root.mkdir(mode=0o700)
    leaves = root / "leaves"
    leaves.mkdir(mode=0o700)
    leaf = leaves / "tiny-00"
    leaf.mkdir(mode=0o700)
    reservation = _reservation(root, [allowed_cpu])
    catalogs = _catalogs(
        tmp_path / "real-catalogs", root,
        str(reservation["reservation_sha256"]), [allowed_cpu],
    )
    cnf = tmp_path / "tiny.cnf"
    cnf.write_bytes(b"p cnf 1 2\n1 0\n-1 0\n")
    cnf.chmod(0o600)
    spec = {
        "schema_version": 1, "kind": native.SPEC_KIND,
        "campaign_id": "real-native-lrat-smoke", "launch_id": "launch-001",
        "generation": 0, "fresh_leaf_generation": True, "resume": False,
        "checkpoint_source": None, "existing_proof_path": None,
        "existing_proof_format": None,
        "all_start_barrier": {
            "barrier_id": "real-barrier", "timeout_seconds": 10,
            "require_every_leaf": True,
        },
        "leaves": [{
            "leaf_id": "tiny-00", "cnf_path": str(cnf),
            "proof_output_path": str(leaf / "proof.lrat"),
            "cpu_lease": launcher.derive_plan_cpu_lease(
                cpu=allowed_cpu, bundle=root,
                reservation_sha256=str(reservation["reservation_sha256"]),
                catalogs=catalogs,
            ),
        }],
    }
    plan = native.build_plan(spec)
    config = launcher.ExecutionConfig(
        output_root=root, lease_catalogs=catalogs,
        reservation_sha256=str(reservation["reservation_sha256"]),
        solver_timeout_seconds=30, checker_timeout_seconds=30,
        proof_cap_bytes=1 << 20, stdout_cap_bytes=1 << 20,
        stderr_cap_bytes=1 << 20, lease_recheck_seconds=0.05,
        disk_reserve_bytes=1, sealed_elf_runtime=True,
        **_resource_kwargs(tmp_path / "resource-world"),
    )
    result = launcher.run_pilot(
        plan, config, _test_nonce=launcher._TEST_ONLY_NONCE,
    )
    assert result["status"] == "PILOT_VERIFIED"
    assert (leaf / "proof.lrat").stat().st_size > 0
    handoff = json.loads(
        (leaf / "40-certification-handoff.json").read_text(encoding="ascii")
    )
    assert handoff["initial_lrat_check"]["verified"] is True
    assert handoff["fresh_lrat_replay"]["verified"] is True
    runtime = json.loads(
        (root / "05-runtime-binding.json").read_text(encoding="ascii")
    )
    assert runtime["dso_payloads_are_sealed_memfds"] is True
    assert runtime["directory_membership_exact"] is True
    assert runtime["recursive_dt_needed_closure_complete"] is True
    assert runtime["startup_base_namespace_dt_needed_path_fallback_excluded"] is True
    assert runtime["same_uid_symlink_directory_is_a_declared_trust_boundary"] is False
    assert runtime["runtime_contains_symlinks"] is False
    assert runtime["runtime_dlopen_path_fallback_excluded"] is False
    assert runtime["every_dependency_bearing_elf_has_df_1_nodeflib"] is True
    assert runtime["directory"]["unlinked_before_fork"] is True
    for item in [runtime["solver"], runtime["checker"], *runtime["objects"]]:
        assert item["nodeflib_derivation"] is True
        assert item["nodeflib_patch_witness"]["byte_differences"]
        assert item["dynamic"]["nodeflib"] is True
    assert not any(
        item.name.startswith(".native-lrat-elf-v1-") for item in root.iterdir()
    )


@pytest.mark.parametrize("missing_dso_index", range(4))
def test_dead_runtime_has_no_symlink_race_and_missing_preload_never_falls_back(
    tmp_path: Path, missing_dso_index: int,
) -> None:
    if not native.SOLVER_PATH.exists() or not native.LRAT_CHECKER_PATH.exists():
        pytest.skip("pinned Paper400 tools are unavailable")
    world = _world(tmp_path, participants=1)
    config = replace(world["config"], sealed_elf_runtime=True)
    runtime = launcher._stage_runtime(config, native.DEFAULT_PINS)
    bad_fd = cnf_fd = proof_fd = -1
    children: list[launcher._Child] = []
    try:
        assert not (Path(world["root"]) / runtime.directory_name).exists()
        held_directory = os.dup(runtime.directory_fd)
        try:
            with pytest.raises(OSError):
                descriptor = os.open(
                    "injected.so", os.O_WRONLY | os.O_CREAT | os.O_EXCL,
                    0o600, dir_fd=held_directory,
                )
                os.close(descriptor)
        finally:
            os.close(held_directory)

        bad_fd = os.memfd_create("invalid-native-lrat-dso", os.MFD_CLOEXEC)
        os.write(bad_fd, b"not an ELF object")
        dso_fds = list(runtime.dso_fds)
        dso_fds[missing_dso_index] = bad_fd
        bad_runtime = replace(runtime, dso_fds=tuple(dso_fds))
        cnf = tmp_path / "fallback.cnf"
        proof = tmp_path / "fallback.lrat"
        cnf.write_bytes(b"p cnf 1 2\n1 0\n-1 0\n")
        proof.write_bytes(b"")
        cnf_fd = os.open(cnf, os.O_RDONLY | os.O_CLOEXEC)
        proof_fd = os.open(proof, os.O_WRONLY | os.O_CLOEXEC)
        child = launcher._fork_gated_child(
            leaf_id="fallback-test", role="solver",
            cpu=world["cpus"][0], cnf_fd=cnf_fd, proof_fd=proof_fd,
            logical_argv=[
                str(native.SOLVER_PATH), "--lrat", "--no-binary",
                f"/proc/self/fd/{launcher.SOLVER_CNF_FD}",
                f"/proc/self/fd/{launcher.SOLVER_PROOF_FD}",
            ],
            runtime=bad_runtime, proof_cap=1 << 20,
            owner_registry=children,
        )
        launcher._wait_gated_ready(children, 10)
        launcher._release_gates(children)
        processes, _snapshots = launcher._monitor_children(
            children, timeout_seconds=10,
            stdout_cap=1 << 20, stderr_cap=1 << 20,
            lease_recheck_seconds=1.0,
            replay_authority=lambda: {"authority_sha256": "0" * 64},
        )
        assert processes[0]["exit_code"] != 20
        assert child.stderr
    finally:
        if children and not children[0].reaped:
            launcher._terminate_owned(children)
        for descriptor in (proof_fd, cnf_fd, bad_fd):
            if descriptor >= 0:
                os.close(descriptor)
        launcher._destroy_runtime(runtime)
