from __future__ import annotations

import ast
import dataclasses
import errno
import fcntl
import hashlib
import importlib.util
import json
import os
import pwd
import stat
import sys
from pathlib import Path
from types import SimpleNamespace

import pytest


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts/paper400_grat_pilot_cpu_reservation_v1.py"
)
SPEC = importlib.util.spec_from_file_location(
    "paper400_grat_pilot_cpu_reservation_v1_test", SOURCE,
)
assert SPEC is not None and SPEC.loader is not None
reservation = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = reservation
SPEC.loader.exec_module(reservation)

WRAPPER_SOURCE = (
    Path(__file__).resolve().parents[1] / "scripts/paper400_grat_parallel_pilot_v1.py"
)
WRAPPER_SPEC = importlib.util.spec_from_file_location(
    "paper400_grat_parallel_pilot_v1_reservation_compat_test", WRAPPER_SOURCE,
)
assert WRAPPER_SPEC is not None and WRAPPER_SPEC.loader is not None
wrapper = importlib.util.module_from_spec(WRAPPER_SPEC)
sys.modules[WRAPPER_SPEC.name] = wrapper
WRAPPER_SPEC.loader.exec_module(wrapper)
REAL_SCAN_PROCESSES = reservation._scan_processes


@pytest.fixture(autouse=True)
def forbid_production_test_io(monkeypatch: pytest.MonkeyPatch) -> None:
    """No unit/integration selector may touch the live Paper400 namespace."""

    production_root = reservation.RUN_ROOT
    discover = reservation._discover_catalogs
    open_lock = reservation._open_catalog_lock
    publish_catalog = reservation._atomic_catalog_write
    scan_processes = reservation._scan_processes

    def outside_production(path: Path) -> bool:
        text = str(path)
        return not (
            text == str(production_root)
            or text.startswith(str(production_root) + os.sep)
        )

    def guarded_discover(run_root: Path) -> tuple[Path, ...]:
        assert outside_production(run_root)
        return discover(run_root)

    def guarded_lock(catalog: Path) -> int:
        assert outside_production(catalog)
        return open_lock(catalog)

    def guarded_publish(
        path: Path, value: dict, *, expected_catalog_sha256: str,
    ) -> None:
        assert outside_production(path)
        publish_catalog(
            path, value, expected_catalog_sha256=expected_catalog_sha256,
        )

    def guarded_scan(config: reservation.ReservationConfig) -> reservation.ProcessScan:
        assert config.proc_root != Path("/proc")
        assert outside_production(config.run_root)
        return scan_processes(config)

    monkeypatch.setattr(reservation, "_discover_catalogs", guarded_discover)
    monkeypatch.setattr(reservation, "_open_catalog_lock", guarded_lock)
    monkeypatch.setattr(reservation, "_atomic_catalog_write", guarded_publish)
    monkeypatch.setattr(reservation, "_scan_processes", guarded_scan)


def _write_json(
    path: Path, value: dict, *, mode: int = 0o600, newline: bool = True,
) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(reservation._canonical(value) + (b"\n" if newline else b""))
    path.chmod(mode)


def _row(
    run_root: Path,
    cpu: int,
    *,
    state: str = "RESERVED",
    bundle: Path | None = None,
    digest: str = "a" * 64,
    created_at: float = 1.0,
    released_at: float | None = None,
) -> dict:
    if bundle is None:
        bundle = run_root / "legacy-bundle"
    if state == "RELEASED" and released_at is None:
        released_at = 2.0
    return {
        "cpu": cpu,
        "bundle": str(bundle),
        "reservation_sha256": digest,
        "state": state,
        "created_at": created_at,
        "released_at": released_at,
    }


def _catalog_value(rows: list[dict] | None = None, updated_at: float = 1.0) -> dict:
    return reservation._seal({
        "schema_version": 1,
        "kind": reservation.CATALOG_KIND,
        "leases": list(rows or []),
        "updated_at": updated_at,
    }, "catalog_sha256")


@pytest.fixture
def world(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> dict:
    run_root = tmp_path / "paper400-runs"
    run_root.mkdir(mode=0o700)
    catalogs = []
    for name in (".catalog-a", ".catalog-b", ".catalog-c"):
        control = run_root / name
        control.mkdir(mode=0o700)
        catalog = control / "cpu-leases.json"
        _write_json(catalog, _catalog_value())
        lock = control / "cpu-leases.lock"
        lock.write_bytes(b"")
        lock.chmod(0o600)
        catalogs.append(catalog)
    output = run_root / "paper400-grat-pilot-v1-unit"
    config = reservation.ReservationConfig(
        run_root=run_root,
        catalogs=tuple(catalogs),
        output_root=output,
        threads=4,
        proc_root=tmp_path / "fake-proc",
    )
    monkeypatch.setattr(reservation.os, "sched_getaffinity", lambda _pid: set(range(16)))
    monkeypatch.setattr(
        reservation,
        "_scan_processes",
        lambda _config: reservation.ProcessScan((), ()),
    )
    return {
        "run_root": run_root,
        "catalogs": tuple(catalogs),
        "output": output,
        "config": config,
    }


def _load(path: Path) -> dict:
    return json.loads(path.read_bytes())


def _replace_catalog(path: Path, value: dict) -> None:
    _write_json(path, value)


def _proc_stat(pid: int, comm: str, start_ticks: int, state: str = "S") -> bytes:
    fields = [state, *("0" for _ in range(18)), str(start_ticks)]
    return f"{pid} ({comm}) {' '.join(fields)}\n".encode("ascii")


def _fake_proc_process(
    proc_root: Path,
    *,
    pid: int,
    comm: str,
    argv: tuple[str, ...],
    cgroup: str,
    cwd: Path,
    start_ticks: int = 100,
) -> Path:
    entry = proc_root / str(pid)
    entry.mkdir(parents=True)
    (entry / "stat").write_bytes(_proc_stat(pid, comm, start_ticks))
    (entry / "cmdline").write_bytes(
        b"" if not argv else b"\0".join(os.fsencode(item) for item in argv) + b"\0"
    )
    (entry / "cgroup").write_bytes(cgroup.encode("utf-8"))
    (entry / "cwd").symlink_to(cwd, target_is_directory=True)
    return entry


def _scan_config(tmp_path: Path, proc_root: Path) -> reservation.ReservationConfig:
    run_root = tmp_path / "paper400-runs"
    return reservation.ReservationConfig(
        run_root=run_root,
        catalogs=(),
        output_root=run_root / "paper400-grat-pilot-v1-scan-test",
        threads=4,
        proc_root=proc_root,
    )


def _sd_pam_cgroup() -> str:
    uid = os.geteuid()
    return (
        f"0::/user.slice/user-{uid}.slice/"
        f"user@{uid}.service/init.scope\n"
    )


def _current_username() -> str:
    return pwd.getpwuid(os.geteuid()).pw_name


def _sshd_notty_argv(*tail: str) -> tuple[str, ...]:
    return (f"sshd: {_current_username()}@notty", *tail)


def _sshd_session_cgroup(
    session: str = "78830", *, uid: int | None = None,
) -> str:
    effective_uid = os.geteuid() if uid is None else uid
    return (
        f"0::/user.slice/user-{effective_uid}.slice/"
        f"session-{session}.scope\n"
    )


def _deny_cwd_readlink(
    monkeypatch: pytest.MonkeyPatch, denied: Path,
) -> None:
    real_readlink = os.readlink

    def guarded(path: os.PathLike[str] | str) -> str:
        if Path(path) == denied:
            raise PermissionError(13, "permission denied", str(path))
        return real_readlink(path)

    monkeypatch.setattr(reservation.os, "readlink", guarded)


def _replace_immutable_manifest(path: Path, value: dict) -> None:
    path.chmod(0o600)
    _write_json(path, value, mode=0o400, newline=False)


def _reseal_manifest(value: dict) -> dict:
    body = dict(value)
    body.pop("manifest_sha256", None)
    return reservation._seal(body, "manifest_sha256")


def _wrapper_source_record() -> dict:
    return _file_record(WRAPPER_SOURCE, "pilot wrapper source")


def _file_record(path: Path, role: str, *, digest: str | None = None) -> dict:
    info = path.stat()
    return {
        "role": role, "requested_path": str(path), "realpath": str(path.resolve()),
        "device": info.st_dev, "inode": info.st_ino, "bytes": info.st_size,
        "sha256": digest or hashlib.sha256(path.read_bytes()).hexdigest(),
        "mode": stat.S_IMODE(info.st_mode), "uid": info.st_uid, "gid": info.st_gid,
        "links": info.st_nlink, "mtime_ns": info.st_mtime_ns, "ctime_ns": info.st_ctime_ns,
    }


def _finalize_pilot(
    world: dict, *, status: str = "GRATCHK_ACCEPTED_PILOT_ONLY",
) -> tuple[dict, dict, dict]:
    cpu_reservation = _load(world["output"] / "cpu-reservation.json")
    admission = {
        "run_root": str(world["run_root"]),
        "bundle": str(world["output"]),
        "reservation_sha256": cpu_reservation["reservation_sha256"],
        "cpus": cpu_reservation["cpus"],
        "scheduler_lease_only": True,
        "catalog_mutation_by_pilot": False,
    }
    wrapper_record = _wrapper_source_record()
    inputs = {
        "cnf": {**wrapper_record, "role": "input CNF"},
        "drat": {**wrapper_record, "role": "input DRAT proof"},
    }
    lock_record = {
        **wrapper_record, "role": "toolchain lock",
        "sha256": reservation.TRUSTED_TOOLCHAIN_MANIFEST_SHA256,
    }
    tools = {
        name: {
            "name": name,
            "binary": {
                **wrapper_record, "role": f"{name} binary",
                "sha256": reservation.TRUSTED_PILOT_TOOL_SHA256S[name],
            },
            "runtime_kind": "dynamic",
            "runtime_libraries": [],
        }
        for name in ("gratgen", "gratchk")
    }
    threads = len(cpu_reservation["cpus"])
    pipeline = [
        {"stage": "gratgen", "argv": ["gratgen", "cnf", "proof", "-b", "-j", str(threads)]},
        {"stage": "gratchk", "argv": ["gratchk", "unsat", "cnf", "gratl", "gratp"]},
    ]
    plan = reservation._seal({
        "schema_version": 1,
        "kind": reservation.PILOT_PLAN_KIND,
        "gate": reservation.PILOT_GATE,
        "created_utc": "2026-09-08T00:00:00Z",
        "label": "unit",
        "mode": "NON_PRODUCTION_PILOT",
        "authoritative": False,
        "terminal_publication": False,
        "aggregate_publication": False,
        "cleanup_authority": False,
        "output_root": str(world["output"]),
        "wrapper_source": wrapper_record,
        "wrapper_source_fd_pinned_for_context_lifetime": True,
        "wrapper_source_initial_full_hash_verified": True,
        "inputs": inputs,
        "proof_quiescence": {},
        "proof_format": "binary",
        "threads": threads,
        "cpus": cpu_reservation["cpus"],
        "cpu_scheduler_authority": {
            "admission": admission,
            "catalog_locks_released_before_expensive_work": True,
            "run_requires_short_locked_revalidation_at_each_boundary": True,
        },
        "resources": {"passed": True},
        "stage_timeout_seconds": 60,
        "toolchain": {"lock": lock_record, "tools": tools},
        "toolchain_trust": {
            "observed_lock_sha256": reservation.TRUSTED_TOOLCHAIN_MANIFEST_SHA256,
            "compiled_binary_sha256": reservation.TRUSTED_PILOT_TOOL_SHA256S,
            "compiled_runtime_policy": True,
            "run_enabled": True,
        },
        "pipeline": pipeline,
    }, "manifest_sha256")
    result_body = {
        "schema_version": 1,
        "kind": reservation.PILOT_RESULT_KIND,
        "gate": reservation.PILOT_GATE,
        "completed_utc": "2026-09-08T00:01:00Z",
        "status": status,
        "authoritative": False,
        "terminal_publication": False,
        "aggregate_publication": False,
        "cleanup_authority": False,
        "eligible_for_terminal_publication": False,
        "plan_sha256": plan["manifest_sha256"],
        "wrapper_source": plan["wrapper_source"],
    }
    if status == "FAILED_CLOSED":
        result_body["wrapper_source_final_full_reverify"] = {
            "checked_utc": "2026-09-08T00:01:00Z",
            "full_hash": True,
            "passed": False,
            "error": {"type": "OSError", "message": "source changed"},
        }
        result_body["failure"] = {"type": "unit", "message": "unit"}
    else:
        staging = world["output"] / "staging"
        staging.mkdir(mode=0o700, exist_ok=True)
        files = {
            "gratgen.stdout": b"",
            "gratgen.stderr": (
                f"c Checking with {threads} parallel threads\ns VERIFIED\n".encode()
            ),
            "gratchk.stdout": b"c Done\ns VERIFIED UNSAT\n",
            "gratchk.stderr": b"",
            "pilot.gratl": b"lemmas",
            "pilot.gratp": b"proof",
        }
        for name, payload in files.items():
            path = staging / name
            path.write_bytes(payload)
            path.chmod(0o400)
        def runtime(stage: str) -> dict:
            return {
                "kind": "paper400-grat-private-runtime-v1", "tool": stage,
                "runtime_kind": "dynamic",
                "binary_memfd": {
                    "name": f"{stage}-binary", "bytes": 1,
                    "sha256": reservation.TRUSTED_PILOT_TOOL_SHA256S[stage],
                    "mode": 0o500, "seals": 15,
                },
                "runtime_objects": [],
                "loader_options": ["--inhibit-cache", "--library-path", "--argv0"],
                "system_loader_cache_bypassed": True,
            }

        def stage(stage_name: str) -> dict:
            argv = ["loader", "--argv0", stage_name]
            if stage_name == "gratgen":
                argv += ["binary", "cnf", "proof", "-b", "-j", str(threads)]
            else:
                argv += ["binary", "unsat", "cnf", "gratl", "gratp"]
            return {
                "stage": stage_name, "exit_code": 0, "elapsed_wall_seconds": 1.0,
                "required_success_line": (
                    "s VERIFIED" if stage_name == "gratgen" else "s VERIFIED UNSAT"
                ),
                "status_stream": "stderr" if stage_name == "gratgen" else "stdout",
                "observed_parallel_threads": threads if stage_name == "gratgen" else None,
                "stdout": _file_record(staging / f"{stage_name}.stdout", f"{stage_name} stdout"),
                "stderr": _file_record(staging / f"{stage_name}.stderr", f"{stage_name} stderr"),
                "runtime": runtime(stage_name),
                "process_identity": {
                    "pid": 100, "proc_start_ticks": 200, "argv": argv,
                    "observed_affinity": cpu_reservation["cpus"],
                    "observed_before_wait": True,
                },
                "process_policy": {"exact_affinity": cpu_reservation["cpus"]},
            }
        result_body.update({
            "wrapper_source_final_full_reverify": {
                "checked_utc": "2026-09-08T00:01:00Z",
                "full_hash": True,
                "passed": True,
            },
            "artifacts_staged_only": True,
            "inputs": inputs,
            "scheduler_boundary_snapshots": [],
            "catalog_locks_held_across_stage": False,
            "toolchain": plan["toolchain"],
            "cgroup_after_stages": [],
            "stages": [stage("gratgen"), stage("gratchk")],
            "staged_artifacts": {
                "gratl": _file_record(staging / "pilot.gratl", "staged GRAT lemmas"),
                "gratp": _file_record(staging / "pilot.gratp", "staged GRAT proof"),
            },
        })
    result = reservation._seal(result_body, "manifest_sha256")
    _write_json(world["output"] / "PLAN.json", plan, mode=0o400, newline=False)
    _write_json(world["output"] / "RESULT.json", result, mode=0o400, newline=False)
    return cpu_reservation, plan, result


def test_seal_is_tamper_evident() -> None:
    value = reservation._seal({"x": 1})
    assert reservation._selfhash_valid(value, "record_sha256")
    value["x"] = True
    assert not reservation._selfhash_valid(value, "record_sha256")


def test_scan_allows_stable_sd_pam_with_inaccessible_cwd(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    proc_root = tmp_path / "proc"
    entry = _fake_proc_process(
        proc_root,
        pid=23535,
        comm="(sd-pam)",
        argv=("(sd-pam)",),
        cgroup=_sd_pam_cgroup(),
        cwd=tmp_path,
    )
    _deny_cwd_readlink(monkeypatch, entry / "cwd")
    monkeypatch.setattr(reservation.os, "sched_getaffinity", lambda _pid: set(range(224)))

    scan = REAL_SCAN_PROCESSES(_scan_config(tmp_path, proc_root))

    assert scan == reservation.ProcessScan((), ())


def test_scan_allows_exact_stable_scrubbed_sshd_notty_session(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    proc_root = tmp_path / "proc"
    argv = _sshd_notty_argv("", "", "", "")
    entry = _fake_proc_process(
        proc_root,
        pid=1054589,
        comm="sshd",
        argv=argv,
        cgroup=_sshd_session_cgroup(),
        cwd=tmp_path,
    )
    expected_cmdline = os.fsencode(argv[0]) + (b"\0" * 5)
    assert (entry / "cmdline").read_bytes() == expected_cmdline
    assert reservation._decode_argv(expected_cmdline) == argv
    cwd_reads = 0

    def deny_twice(path: os.PathLike[str] | str) -> str:
        nonlocal cwd_reads
        assert Path(path) == entry / "cwd"
        cwd_reads += 1
        raise PermissionError(errno.EACCES, "permission denied", str(path))

    affinity_reads = 0

    def stable_affinity(pid: int) -> set[int]:
        nonlocal affinity_reads
        assert pid == 1054589
        affinity_reads += 1
        return set(range(224))

    monkeypatch.setattr(reservation.os, "readlink", deny_twice)
    monkeypatch.setattr(reservation.os, "sched_getaffinity", stable_affinity)

    scan = REAL_SCAN_PROCESSES(_scan_config(tmp_path, proc_root))

    assert cwd_reads == 2
    assert affinity_reads == 2
    assert scan == reservation.ProcessScan((), ())


@pytest.mark.parametrize(
    "case",
    (
        "wrong_comm",
        "wrong_username",
        "interactive_tty",
        "no_scrubbed_tail",
        "nonempty_tail",
        "wrong_uid_cgroup",
        "nonnumeric_session",
        "nested_cgroup",
        "wrong_cgroup_kind",
        "missing_cgroup_newline",
    ),
)
def test_scan_rejects_near_miss_scrubbed_sshd_notty_session(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    case: str,
) -> None:
    proc_root = tmp_path / "proc"
    comm = "sshd"
    argv = _sshd_notty_argv("", "", "", "")
    cgroup = _sshd_session_cgroup()
    if case == "wrong_comm":
        comm = "sshd-session"
    elif case == "wrong_username":
        argv = ("sshd: not-the-current-user@notty", "", "", "", "")
    elif case == "interactive_tty":
        argv = (f"sshd: {_current_username()}@pts/0", "", "", "", "")
    elif case == "no_scrubbed_tail":
        argv = _sshd_notty_argv()
    elif case == "nonempty_tail":
        argv = _sshd_notty_argv("", str(tmp_path / "paper400-runs"), "", "")
    elif case == "wrong_uid_cgroup":
        cgroup = _sshd_session_cgroup(uid=os.geteuid() + 1)
    elif case == "nonnumeric_session":
        cgroup = _sshd_session_cgroup("78830x")
    elif case == "nested_cgroup":
        cgroup = _sshd_session_cgroup().removesuffix("\n") + "/child.scope\n"
    elif case == "wrong_cgroup_kind":
        cgroup = _sd_pam_cgroup()
    elif case == "missing_cgroup_newline":
        cgroup = _sshd_session_cgroup().removesuffix("\n")
    else:  # pragma: no cover - protects the test table itself.
        raise AssertionError(case)
    entry = _fake_proc_process(
        proc_root,
        pid=1054590,
        comm=comm,
        argv=argv,
        cgroup=cgroup,
        cwd=tmp_path,
    )
    _deny_cwd_readlink(monkeypatch, entry / "cwd")
    monkeypatch.setattr(reservation.os, "sched_getaffinity", lambda _pid: {0})

    with pytest.raises(reservation.ReservationError, match="candidate same-UID"):
        REAL_SCAN_PROCESSES(_scan_config(tmp_path, proc_root))


def test_scan_rejects_sshd_session_when_current_username_is_unavailable(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    proc_root = tmp_path / "proc"
    argv = _sshd_notty_argv("", "", "", "")
    entry = _fake_proc_process(
        proc_root,
        pid=1054591,
        comm="sshd",
        argv=argv,
        cgroup=_sshd_session_cgroup(),
        cwd=tmp_path,
    )
    _deny_cwd_readlink(monkeypatch, entry / "cwd")

    def missing_user(_uid: int) -> None:
        raise KeyError("no passwd entry")

    monkeypatch.setattr(reservation.pwd, "getpwuid", missing_user)

    with pytest.raises(reservation.ReservationError, match="candidate same-UID"):
        REAL_SCAN_PROCESSES(_scan_config(tmp_path, proc_root))


@pytest.mark.parametrize("denial_errno", (errno.EPERM, None))
def test_scan_rejects_sshd_session_cwd_permission_other_than_eacces(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    denial_errno: int | None,
) -> None:
    proc_root = tmp_path / "proc"
    entry = _fake_proc_process(
        proc_root,
        pid=1054592,
        comm="sshd",
        argv=_sshd_notty_argv("", "", "", ""),
        cgroup=_sshd_session_cgroup(),
        cwd=tmp_path,
    )

    def deny(path: os.PathLike[str] | str) -> str:
        assert Path(path) == entry / "cwd"
        if denial_errno is None:
            raise PermissionError("permission denied without errno")
        raise PermissionError(denial_errno, "operation not permitted", str(path))

    monkeypatch.setattr(reservation.os, "readlink", deny)

    with pytest.raises(reservation.ReservationError, match="candidate same-UID"):
        REAL_SCAN_PROCESSES(_scan_config(tmp_path, proc_root))


@pytest.mark.parametrize("second_errno", (errno.EPERM, None))
def test_scan_rejects_changed_sshd_session_denial_errno_on_recheck(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    second_errno: int | None,
) -> None:
    proc_root = tmp_path / "proc"
    entry = _fake_proc_process(
        proc_root,
        pid=1054593,
        comm="sshd",
        argv=_sshd_notty_argv("", "", "", ""),
        cgroup=_sshd_session_cgroup(),
        cwd=tmp_path,
    )
    cwd_reads = 0

    def changed_denial(path: os.PathLike[str] | str) -> str:
        nonlocal cwd_reads
        assert Path(path) == entry / "cwd"
        cwd_reads += 1
        if cwd_reads == 1:
            raise PermissionError(errno.EACCES, "permission denied", str(path))
        if second_errno is None:
            raise PermissionError("permission denied without errno")
        raise PermissionError(second_errno, "operation not permitted", str(path))

    monkeypatch.setattr(reservation.os, "readlink", changed_denial)
    monkeypatch.setattr(reservation.os, "sched_getaffinity", lambda _pid: set(range(4)))

    with pytest.raises(reservation.ReservationError, match="recheck benign cwd denial"):
        REAL_SCAN_PROCESSES(_scan_config(tmp_path, proc_root))


@pytest.mark.parametrize(
    ("record_name", "second_payload"),
    [
        ("stat", _proc_stat(1054594, "sshd", 101)),
        (
            "cmdline",
            os.fsencode(f"sshd: {_current_username()}@notty")
            + b"\0\0extra\0\0\0",
        ),
        ("cgroup", _sshd_session_cgroup("78831").encode("utf-8")),
    ],
)
def test_scan_blocks_sshd_session_proc_identity_or_classification_race(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    record_name: str,
    second_payload: bytes,
) -> None:
    proc_root = tmp_path / "proc"
    pid = 1054594
    entry = _fake_proc_process(
        proc_root,
        pid=pid,
        comm="sshd",
        argv=_sshd_notty_argv("", "", "", ""),
        cgroup=_sshd_session_cgroup(),
        cwd=tmp_path,
    )
    _deny_cwd_readlink(monkeypatch, entry / "cwd")
    monkeypatch.setattr(reservation.os, "sched_getaffinity", lambda _pid: set(range(4)))
    real_read_proc = reservation._read_proc
    reads = 0

    def race(path: Path, cap: int = reservation.MAX_PROC_TEXT_BYTES) -> bytes:
        nonlocal reads
        if path == entry / record_name:
            reads += 1
            if reads == 2:
                return second_payload
        return real_read_proc(path, cap)

    monkeypatch.setattr(reservation, "_read_proc", race)

    scan = REAL_SCAN_PROCESSES(_scan_config(tmp_path, proc_root))

    assert scan.processes == ()
    assert scan.races == (
        {"pid": pid, "reason": "identity_or_affinity_changed"},
    )


def test_scan_blocks_sshd_session_affinity_race(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    proc_root = tmp_path / "proc"
    pid = 1054595
    entry = _fake_proc_process(
        proc_root,
        pid=pid,
        comm="sshd",
        argv=_sshd_notty_argv("", "", "", ""),
        cgroup=_sshd_session_cgroup(),
        cwd=tmp_path,
    )
    _deny_cwd_readlink(monkeypatch, entry / "cwd")
    affinity_reads = 0

    def changing_affinity(requested_pid: int) -> set[int]:
        nonlocal affinity_reads
        assert requested_pid == pid
        affinity_reads += 1
        return {0, 1} if affinity_reads == 1 else {0}

    monkeypatch.setattr(reservation.os, "sched_getaffinity", changing_affinity)

    scan = REAL_SCAN_PROCESSES(_scan_config(tmp_path, proc_root))

    assert scan.processes == ()
    assert scan.races == (
        {"pid": pid, "reason": "identity_or_affinity_changed"},
    )


def test_scan_blocks_sshd_session_cwd_permission_state_change(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    proc_root = tmp_path / "proc"
    pid = 1054596
    entry = _fake_proc_process(
        proc_root,
        pid=pid,
        comm="sshd",
        argv=_sshd_notty_argv("", "", "", ""),
        cgroup=_sshd_session_cgroup(),
        cwd=tmp_path,
    )
    real_readlink = os.readlink
    cwd_reads = 0

    def deny_once(path: os.PathLike[str] | str) -> str:
        nonlocal cwd_reads
        assert Path(path) == entry / "cwd"
        cwd_reads += 1
        if cwd_reads == 1:
            raise PermissionError(errno.EACCES, "permission denied", str(path))
        return real_readlink(path)

    monkeypatch.setattr(reservation.os, "readlink", deny_once)
    monkeypatch.setattr(reservation.os, "sched_getaffinity", lambda _pid: set(range(4)))

    scan = REAL_SCAN_PROCESSES(_scan_config(tmp_path, proc_root))

    assert cwd_reads == 2
    assert scan.processes == ()
    assert scan.races == ({"pid": pid, "reason": "cwd_access_changed"},)


@pytest.mark.parametrize("denial_errno", (errno.EPERM, None))
def test_scan_rejects_sd_pam_cwd_permission_other_than_eacces(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    denial_errno: int | None,
) -> None:
    proc_root = tmp_path / "proc"
    entry = _fake_proc_process(
        proc_root,
        pid=23537,
        comm="(sd-pam)",
        argv=("(sd-pam)",),
        cgroup=_sd_pam_cgroup(),
        cwd=tmp_path,
    )

    def deny(path: os.PathLike[str] | str) -> str:
        assert Path(path) == entry / "cwd"
        if denial_errno is None:
            raise PermissionError("permission denied without errno")
        raise PermissionError(denial_errno, "permission denied", str(path))

    monkeypatch.setattr(reservation.os, "readlink", deny)

    with pytest.raises(reservation.ReservationError, match="candidate same-UID"):
        REAL_SCAN_PROCESSES(_scan_config(tmp_path, proc_root))


@pytest.mark.parametrize("second_errno", (errno.EPERM, None))
def test_scan_rejects_changed_sd_pam_denial_errno_on_recheck(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    second_errno: int | None,
) -> None:
    proc_root = tmp_path / "proc"
    entry = _fake_proc_process(
        proc_root,
        pid=23538,
        comm="(sd-pam)",
        argv=("(sd-pam)",),
        cgroup=_sd_pam_cgroup(),
        cwd=tmp_path,
    )
    cwd_reads = 0

    def changed_denial(path: os.PathLike[str] | str) -> str:
        nonlocal cwd_reads
        assert Path(path) == entry / "cwd"
        cwd_reads += 1
        if cwd_reads == 1:
            raise PermissionError(errno.EACCES, "permission denied", str(path))
        if second_errno is None:
            raise PermissionError("permission denied without errno")
        raise PermissionError(second_errno, "operation not permitted", str(path))

    monkeypatch.setattr(reservation.os, "readlink", changed_denial)
    monkeypatch.setattr(reservation.os, "sched_getaffinity", lambda _pid: set(range(4)))

    with pytest.raises(reservation.ReservationError, match="recheck benign cwd denial"):
        REAL_SCAN_PROCESSES(_scan_config(tmp_path, proc_root))


def test_scan_rejects_unknown_noncompute_with_inaccessible_cwd(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    proc_root = tmp_path / "proc"
    entry = _fake_proc_process(
        proc_root,
        pid=23536,
        comm="sleep",
        argv=("/usr/bin/sleep", "60"),
        cgroup=_sd_pam_cgroup(),
        cwd=tmp_path,
    )
    _deny_cwd_readlink(monkeypatch, entry / "cwd")
    monkeypatch.setattr(reservation.os, "sched_getaffinity", lambda _pid: {0})

    with pytest.raises(reservation.ReservationError, match="candidate same-UID"):
        REAL_SCAN_PROCESSES(_scan_config(tmp_path, proc_root))


@pytest.mark.parametrize(
    ("comm", "argv"),
    [
        ("cadical", ("/opt/solver/bin/cadical", "cube.cnf")),
        ("python3", ("/lib64/ld-linux.so.2", "--argv0", "lrat-check")),
        ("python3", ("/lib64/ld-linux.so.2", "--argv0=gratchk")),
    ],
)
def test_scan_blocks_compute_or_argv0_checker_with_inaccessible_cwd(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    comm: str,
    argv: tuple[str, ...],
) -> None:
    proc_root = tmp_path / "proc"
    entry = _fake_proc_process(
        proc_root,
        pid=24001,
        comm=comm,
        argv=argv,
        cgroup="0::/user.slice/user-1001.slice/user@1001.service/app.scope\n",
        cwd=tmp_path,
    )
    _deny_cwd_readlink(monkeypatch, entry / "cwd")
    monkeypatch.setattr(reservation.os, "sched_getaffinity", lambda _pid: {0})

    with pytest.raises(reservation.ReservationError, match="candidate same-UID"):
        REAL_SCAN_PROCESSES(_scan_config(tmp_path, proc_root))


@pytest.mark.parametrize(
    ("comm", "argv", "vanishing_record"),
    [
        ("cadical", ("/opt/solver/bin/cadical",), "cmdline"),
        ("drat-trim", ("/opt/solver/bin/drat-trim",), "cmdline"),
        ("lrat-check", ("/opt/solver/bin/lrat-check",), "cmdline"),
        ("final-drat-repl", ("/opt/solver/bin/final-drat-replay",), "cmdline"),
        ("final-lrat-repl", ("/opt/solver/bin/final-lrat-replay",), "cmdline"),
        ("python3", ("/lib64/ld-linux.so.2", "--argv0=gratchk"), "cgroup"),
    ],
)
def test_scan_retains_candidate_that_disappears_during_classification(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    comm: str,
    argv: tuple[str, ...],
    vanishing_record: str,
) -> None:
    proc_root = tmp_path / "proc"
    pid = 24007
    entry = _fake_proc_process(
        proc_root,
        pid=pid,
        comm=comm,
        argv=argv,
        cgroup="0::/user.slice/candidate.scope\n",
        cwd=tmp_path,
    )
    real_read_proc = reservation._read_proc

    def vanish(path: Path, cap: int = reservation.MAX_PROC_TEXT_BYTES) -> bytes:
        if path == entry / vanishing_record:
            raise FileNotFoundError(2, "vanished", str(path))
        return real_read_proc(path, cap)

    monkeypatch.setattr(reservation, "_read_proc", vanish)

    scan = REAL_SCAN_PROCESSES(_scan_config(tmp_path, proc_root))

    assert scan.processes == ()
    assert scan.races == ({"pid": pid, "reason": "disappeared_during_scan"},)


def test_scan_blocks_paper400_cgroup_with_inaccessible_cwd(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    proc_root = tmp_path / "proc"
    entry = _fake_proc_process(
        proc_root,
        pid=24002,
        comm="(sd-pam)",
        argv=("(sd-pam)",),
        cgroup="0::/paper400/pilot.scope\n",
        cwd=tmp_path,
    )
    _deny_cwd_readlink(monkeypatch, entry / "cwd")
    monkeypatch.setattr(reservation.os, "sched_getaffinity", lambda _pid: {0})

    with pytest.raises(reservation.ReservationError, match="candidate same-UID"):
        REAL_SCAN_PROCESSES(_scan_config(tmp_path, proc_root))


def test_scan_blocks_identity_race_before_benign_cwd_skip(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    proc_root = tmp_path / "proc"
    pid = 24003
    entry = _fake_proc_process(
        proc_root,
        pid=pid,
        comm="(sd-pam)",
        argv=("(sd-pam)",),
        cgroup=_sd_pam_cgroup(),
        cwd=tmp_path,
    )
    _deny_cwd_readlink(monkeypatch, entry / "cwd")
    monkeypatch.setattr(reservation.os, "sched_getaffinity", lambda _pid: set(range(4)))
    real_read_proc = reservation._read_proc
    stat_reads = 0

    def identity_race(path: Path, cap: int = reservation.MAX_PROC_TEXT_BYTES) -> bytes:
        nonlocal stat_reads
        if path == entry / "stat":
            stat_reads += 1
            if stat_reads == 2:
                return _proc_stat(pid, "(sd-pam)", 101)
        return real_read_proc(path, cap)

    monkeypatch.setattr(reservation, "_read_proc", identity_race)

    scan = REAL_SCAN_PROCESSES(_scan_config(tmp_path, proc_root))

    assert scan.processes == ()
    assert scan.races == ({"pid": pid, "reason": "identity_or_affinity_changed"},)


def test_scan_blocks_identity_race_before_second_classification(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    proc_root = tmp_path / "proc"
    pid = 24008
    entry = _fake_proc_process(
        proc_root,
        pid=pid,
        comm="sleep",
        argv=("/usr/bin/sleep", "60"),
        cgroup="0::/user.slice/background.scope\n",
        cwd=tmp_path,
    )
    monkeypatch.setattr(reservation.os, "sched_getaffinity", lambda _pid: set(range(4)))
    real_read_proc = reservation._read_proc
    stat_reads = 0

    def identity_race(path: Path, cap: int = reservation.MAX_PROC_TEXT_BYTES) -> bytes:
        nonlocal stat_reads
        if path == entry / "stat":
            stat_reads += 1
            if stat_reads == 2:
                return _proc_stat(pid, "python3", 101)
        return real_read_proc(path, cap)

    monkeypatch.setattr(reservation, "_read_proc", identity_race)

    scan = REAL_SCAN_PROCESSES(_scan_config(tmp_path, proc_root))

    assert scan.processes == ()
    assert scan.races == ({"pid": pid, "reason": "identity_or_affinity_changed"},)


@pytest.mark.parametrize(
    ("record_name", "second_payload"),
    [
        ("cmdline", b"/lib64/ld-linux.so.2\0--argv0=gratchk\0"),
        ("cgroup", b"0::/paper400/raced.scope\n"),
    ],
)
def test_scan_blocks_classification_race_before_benign_cwd_skip(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    record_name: str,
    second_payload: bytes,
) -> None:
    proc_root = tmp_path / "proc"
    pid = 24006
    entry = _fake_proc_process(
        proc_root,
        pid=pid,
        comm="(sd-pam)",
        argv=("(sd-pam)",),
        cgroup=_sd_pam_cgroup(),
        cwd=tmp_path,
    )
    _deny_cwd_readlink(monkeypatch, entry / "cwd")
    monkeypatch.setattr(reservation.os, "sched_getaffinity", lambda _pid: set(range(4)))
    real_read_proc = reservation._read_proc
    reads = 0

    def classification_race(
        path: Path, cap: int = reservation.MAX_PROC_TEXT_BYTES,
    ) -> bytes:
        nonlocal reads
        if path == entry / record_name:
            reads += 1
            if reads == 2:
                return second_payload
        return real_read_proc(path, cap)

    monkeypatch.setattr(reservation, "_read_proc", classification_race)

    scan = REAL_SCAN_PROCESSES(_scan_config(tmp_path, proc_root))

    assert scan.processes == ()
    assert scan.races == ({"pid": pid, "reason": "identity_or_affinity_changed"},)


def test_scan_blocks_sd_pam_cwd_permission_state_change(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    proc_root = tmp_path / "proc"
    pid = 24004
    entry = _fake_proc_process(
        proc_root,
        pid=pid,
        comm="(sd-pam)",
        argv=("(sd-pam)",),
        cgroup=_sd_pam_cgroup(),
        cwd=tmp_path,
    )
    real_readlink = os.readlink
    cwd_reads = 0

    def deny_once(path: os.PathLike[str] | str) -> str:
        nonlocal cwd_reads
        if Path(path) == entry / "cwd":
            cwd_reads += 1
            if cwd_reads == 1:
                raise PermissionError(13, "permission denied", str(path))
        return real_readlink(path)

    monkeypatch.setattr(reservation.os, "readlink", deny_once)
    monkeypatch.setattr(reservation.os, "sched_getaffinity", lambda _pid: set(range(4)))

    scan = REAL_SCAN_PROCESSES(_scan_config(tmp_path, proc_root))

    assert cwd_reads == 2
    assert scan.processes == ()
    assert scan.races == ({"pid": pid, "reason": "cwd_access_changed"},)


def test_scan_blocks_readable_cwd_identity_change(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    proc_root = tmp_path / "proc"
    pid = 24005
    first_cwd = tmp_path / "outside-a"
    second_cwd = tmp_path / "outside-b"
    first_cwd.mkdir()
    second_cwd.mkdir()
    entry = _fake_proc_process(
        proc_root,
        pid=pid,
        comm="sleep",
        argv=("/usr/bin/sleep", "60"),
        cgroup="0::/user.slice/ordinary.service\n",
        cwd=first_cwd,
    )
    cwd_reads = 0

    def changing_cwd(path: os.PathLike[str] | str) -> str:
        nonlocal cwd_reads
        assert Path(path) == entry / "cwd"
        cwd_reads += 1
        return str(first_cwd if cwd_reads == 1 else second_cwd)

    monkeypatch.setattr(reservation.os, "readlink", changing_cwd)
    monkeypatch.setattr(reservation.os, "sched_getaffinity", lambda _pid: set(range(4)))

    scan = REAL_SCAN_PROCESSES(_scan_config(tmp_path, proc_root))

    assert scan.processes == ()
    assert scan.races == ({"pid": pid, "reason": "cwd_identity_changed"},)


def test_audit_excludes_every_historical_row_and_broad_compute(
    world: dict, monkeypatch: pytest.MonkeyPatch,
) -> None:
    first, second, third = world["catalogs"]
    _replace_catalog(first, _catalog_value([
        _row(world["run_root"], 0, state="RELEASED"),
    ]))
    _replace_catalog(second, _catalog_value([_row(world["run_root"], 1)]))
    broad = {
        "pid": 99,
        "start_ticks": 7,
        "state": "R",
        "compute_kind": "cadical",
        "paper400_bound": True,
        "affinity": [2, 8],
        "affinity_class": "broad",
        "cmdline_sha256": "b" * 64,
        "cgroup_sha256": "c" * 64,
        "cwd": "",
        "argv": [],
        "cgroup": "paper400",
    }
    monkeypatch.setattr(
        reservation, "_scan_processes",
        lambda _config: reservation.ProcessScan((broad,), ()),
    )
    record = reservation.audit(world["config"])
    assert record["go"] is True
    assert record["selected_cpus"] == [3, 4, 5, 6]
    assert 0 not in record["eligible_cpus"]
    assert 1 not in record["eligible_cpus"]
    assert 2 not in record["eligible_cpus"]
    assert 8 not in record["eligible_cpus"]
    assert _load(third)["leases"] == []


@pytest.mark.parametrize("threads", [4, 8])
def test_reserve_publishes_wrapper_compatible_identity_in_all_three_catalogs(
    world: dict, threads: int,
) -> None:
    config = dataclasses.replace(world["config"], threads=threads)
    record = reservation.reserve(config)
    binding = _load(world["output"] / "cpu-reservation.json")
    assert stat.S_IMODE(world["output"].stat().st_mode) == 0o700
    assert stat.S_IMODE((world["output"] / "cpu-reservation.json").stat().st_mode) == 0o400
    assert sorted(path.name for path in world["output"].iterdir()) == ["cpu-reservation.json"]
    assert set(binding) == reservation.RESERVATION_FIELDS
    assert reservation._selfhash_valid(binding, "reservation_sha256")
    assert binding["cpus"] == list(range(threads))
    assert record["reservation_sha256"] == binding["reservation_sha256"]
    for path in world["catalogs"]:
        rows = _load(path)["leases"]
        assert [row["cpu"] for row in rows] == list(range(threads))
        assert {row["bundle"] for row in rows} == {str(world["output"])}
        assert {row["reservation_sha256"] for row in rows} == {
            binding["reservation_sha256"],
        }
        assert {row["state"] for row in rows} == {"RESERVED"}


def test_frozen_grat_wrapper_accepts_helper_reservation(world: dict) -> None:
    reservation.reserve(world["config"])
    value = _load(world["output"] / "cpu-reservation.json")
    config = SimpleNamespace(
        output_root=world["output"],
        cpus=tuple(value["cpus"]),
        reservation_sha256=value["reservation_sha256"],
    )
    pin, observed = wrapper._read_reservation(config)
    try:
        assert observed == value
    finally:
        pin.close()


def test_reserve_replays_a_crash_between_catalogs(
    world: dict, monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = reservation._atomic_catalog_write
    calls = 0

    def crash_second(
        path: Path, value: dict, *, expected_catalog_sha256: str,
    ) -> None:
        nonlocal calls
        calls += 1
        if calls == 2:
            raise OSError("simulated power loss")
        original(path, value, expected_catalog_sha256=expected_catalog_sha256)

    monkeypatch.setattr(reservation, "_atomic_catalog_write", crash_second)
    with pytest.raises(OSError, match="power loss"):
        reservation.reserve(world["config"])
    binding = _load(world["output"] / "cpu-reservation.json")
    assert len(_load(world["catalogs"][0])["leases"]) == 4
    assert len(_load(world["catalogs"][1])["leases"]) == 0

    monkeypatch.setattr(reservation, "_atomic_catalog_write", original)
    result = reservation.reserve(world["config"])
    assert result["recovery_replay"] is True
    for path in world["catalogs"]:
        rows = _load(path)["leases"]
        assert len(rows) == 4
        assert {row["reservation_sha256"] for row in rows} == {
            binding["reservation_sha256"],
        }


def test_reserve_recovery_rejects_foreign_row_without_mutation(world: dict) -> None:
    reservation.reserve(world["config"])
    target = world["catalogs"][1]
    value = _load(target)
    value["leases"][0]["bundle"] = str(world["run_root"] / "foreign")
    value["leases"][0]["reservation_sha256"] = "f" * 64
    value.pop("catalog_sha256")
    _replace_catalog(target, reservation._seal(value, "catalog_sha256"))
    before = [path.read_bytes() for path in world["catalogs"]]
    with pytest.raises(reservation.ReservationError, match="foreign"):
        reservation.reserve(world["config"])
    assert [path.read_bytes() for path in world["catalogs"]] == before


def test_reserve_never_overwrites_foreign_root(world: dict) -> None:
    world["output"].mkdir(mode=0o700)
    (world["output"] / "foreign.txt").write_text("keep", encoding="ascii")
    before = [path.read_bytes() for path in world["catalogs"]]
    with pytest.raises(reservation.ReservationError, match="pristine"):
        reservation.reserve(world["config"])
    assert (world["output"] / "foreign.txt").read_text("ascii") == "keep"
    assert [path.read_bytes() for path in world["catalogs"]] == before


def test_reserve_enforces_modes_even_under_restrictive_umask(world: dict) -> None:
    prior = os.umask(0o777)
    try:
        reservation.reserve(world["config"])
    finally:
        os.umask(prior)
    assert stat.S_IMODE(world["output"].stat().st_mode) == 0o700
    assert stat.S_IMODE(
        (world["output"] / "cpu-reservation.json").stat().st_mode
    ) == 0o400
    for path in world["catalogs"]:
        assert stat.S_IMODE(path.stat().st_mode) == 0o600


def test_busy_catalog_lock_prevents_every_mutation(world: dict) -> None:
    lock = world["catalogs"][1].with_name("cpu-leases.lock")
    descriptor = os.open(lock, os.O_RDWR)
    fcntl.flock(descriptor, fcntl.LOCK_EX)
    before = [path.read_bytes() for path in world["catalogs"]]
    try:
        with pytest.raises(reservation.ReservationError, match="busy"):
            reservation.reserve(world["config"])
    finally:
        os.close(descriptor)
    assert not world["output"].exists()
    assert [path.read_bytes() for path in world["catalogs"]] == before


def test_atomic_catalog_publication_detects_a_lost_update(world: dict) -> None:
    path = world["catalogs"][0]
    original = _load(path)
    replacement = dict(original)
    replacement.pop("catalog_sha256")
    replacement["updated_at"] = 2.0
    replacement = reservation._seal(replacement, "catalog_sha256")

    intervening = dict(original)
    intervening.pop("catalog_sha256")
    intervening["updated_at"] = 3.0
    intervening = reservation._seal(intervening, "catalog_sha256")
    _replace_catalog(path, intervening)
    with pytest.raises(reservation.ReservationError, match="changed"):
        reservation._atomic_catalog_write(
            path,
            replacement,
            expected_catalog_sha256=original["catalog_sha256"],
        )
    assert _load(path) == intervening


@pytest.mark.parametrize("status", ["GRATCHK_ACCEPTED_PILOT_ONLY", "FAILED_CLOSED"])
def test_release_requires_final_result_then_marks_only_exact_rows_released(
    world: dict, status: str,
) -> None:
    reservation.reserve(world["config"])
    binding, plan, result = _finalize_pilot(world, status=status)
    unrelated = world["output"] / "staging-artifact"
    unrelated.write_bytes(b"must remain")
    release = reservation.release(world["config"])
    assert release["result_status"] == status
    assert release["removed_data"] is False
    assert unrelated.read_bytes() == b"must remain"
    assert (world["output"] / "PLAN.json").is_file()
    assert (world["output"] / "RESULT.json").is_file()
    assert (world["output"] / "CPU-LEASE-RELEASE.json").is_file()
    times = set()
    for path in world["catalogs"]:
        rows = _load(path)["leases"]
        assert {row["state"] for row in rows} == {"RELEASED"}
        assert {row["reservation_sha256"] for row in rows} == {
            binding["reservation_sha256"],
        }
        times.update(row["released_at"] for row in rows)
    assert len(times) == 1
    assert release["plan_sha256"] == plan["manifest_sha256"]
    assert release["result_sha256"] == result["manifest_sha256"]


def test_release_without_result_is_read_only(world: dict) -> None:
    reservation.reserve(world["config"])
    _finalize_pilot(world)
    (world["output"] / "RESULT.json").unlink()
    before = [path.read_bytes() for path in world["catalogs"]]
    with pytest.raises(reservation.ReservationError, match="RESULT"):
        reservation.release(world["config"])
    assert [path.read_bytes() for path in world["catalogs"]] == before


def test_release_rejects_live_pilot_child(world: dict, monkeypatch: pytest.MonkeyPatch) -> None:
    reservation.reserve(world["config"])
    _finalize_pilot(world)
    child = {
        "pid": os.getpid() + 1000,
        "start_ticks": 8,
        "state": "R",
        "cwd": str(world["output"] / "staging"),
        "argv": ["gratchk"],
        "cgroup": "",
        "compute_kind": "grat",
        "paper400_bound": True,
        "affinity": [0, 1, 2, 3],
        "affinity_class": "broad",
    }
    monkeypatch.setattr(
        reservation, "_scan_processes",
        lambda _config: reservation.ProcessScan((child,), ()),
    )
    before = [path.read_bytes() for path in world["catalogs"]]
    with pytest.raises(reservation.ReservationError, match="child"):
        reservation.release(world["config"])
    assert [path.read_bytes() for path in world["catalogs"]] == before


def test_release_replays_crash_between_catalogs(
    world: dict, monkeypatch: pytest.MonkeyPatch,
) -> None:
    reservation.reserve(world["config"])
    _finalize_pilot(world)
    original = reservation._atomic_catalog_write
    calls = 0

    def crash_second(
        path: Path, value: dict, *, expected_catalog_sha256: str,
    ) -> None:
        nonlocal calls
        calls += 1
        if calls == 2:
            raise OSError("simulated release crash")
        original(path, value, expected_catalog_sha256=expected_catalog_sha256)

    monkeypatch.setattr(reservation, "_atomic_catalog_write", crash_second)
    with pytest.raises(OSError, match="release crash"):
        reservation.release(world["config"])
    first_time = _load(world["catalogs"][0])["leases"][0]["released_at"]
    assert first_time is not None
    assert _load(world["catalogs"][1])["leases"][0]["state"] == "RESERVED"

    monkeypatch.setattr(reservation, "_atomic_catalog_write", original)
    result = reservation.release(world["config"])
    assert result["released_at"] == first_time
    for path in world["catalogs"]:
        rows = _load(path)["leases"]
        assert {row["state"] for row in rows} == {"RELEASED"}
        assert {row["released_at"] for row in rows} == {first_time}


def test_release_rejects_cross_bound_result(world: dict) -> None:
    reservation.reserve(world["config"])
    _binding, _plan, result = _finalize_pilot(world)
    result["plan_sha256"] = "0" * 64
    result.pop("manifest_sha256")
    _write_json(
        world["output"] / "RESULT.bad", reservation._seal(result, "manifest_sha256"),
        mode=0o400, newline=False,
    )
    (world["output"] / "RESULT.json").chmod(0o600)
    (world["output"] / "RESULT.json").write_bytes(
        (world["output"] / "RESULT.bad").read_bytes()
    )
    (world["output"] / "RESULT.json").chmod(0o400)
    before = [path.read_bytes() for path in world["catalogs"]]
    with pytest.raises(reservation.ReservationError, match="RESULT"):
        reservation.release(world["config"])
    assert [path.read_bytes() for path in world["catalogs"]] == before


@pytest.mark.parametrize(
    ("field", "malformed"),
    [
        ("requested_path", "relative-wrapper.py"),
        ("bytes", True),
        ("bytes", 0),
        ("sha256", "D" * 64),
        ("inode", False),
        ("links", 2),
    ],
)
def test_release_rejects_malformed_plan_wrapper_source_identity(
    world: dict, field: str, malformed: object,
) -> None:
    reservation.reserve(world["config"])
    _binding, plan, _result = _finalize_pilot(world)
    plan["wrapper_source"] = dict(plan["wrapper_source"])
    plan["wrapper_source"][field] = malformed
    _replace_immutable_manifest(
        world["output"] / "PLAN.json", _reseal_manifest(plan),
    )
    before = [path.read_bytes() for path in world["catalogs"]]
    with pytest.raises(reservation.ReservationError, match="PLAN"):
        reservation.release(world["config"])
    assert [path.read_bytes() for path in world["catalogs"]] == before


@pytest.mark.parametrize(
    "field",
    [
        "wrapper_source_fd_pinned_for_context_lifetime",
        "wrapper_source_initial_full_hash_verified",
    ],
)
def test_release_requires_both_plan_source_guarantees(
    world: dict, field: str,
) -> None:
    reservation.reserve(world["config"])
    _binding, plan, _result = _finalize_pilot(world)
    plan[field] = False
    _replace_immutable_manifest(
        world["output"] / "PLAN.json", _reseal_manifest(plan),
    )
    before = [path.read_bytes() for path in world["catalogs"]]
    with pytest.raises(reservation.ReservationError, match="PLAN"):
        reservation.release(world["config"])
    assert [path.read_bytes() for path in world["catalogs"]] == before


def test_release_rejects_result_bound_to_another_wrapper_source(world: dict) -> None:
    reservation.reserve(world["config"])
    _binding, _plan, result = _finalize_pilot(world)
    result["wrapper_source"] = dict(result["wrapper_source"])
    result["wrapper_source"]["sha256"] = "e" * 64
    _replace_immutable_manifest(
        world["output"] / "RESULT.json", _reseal_manifest(result),
    )
    before = [path.read_bytes() for path in world["catalogs"]]
    with pytest.raises(reservation.ReservationError, match="RESULT"):
        reservation.release(world["config"])
    assert [path.read_bytes() for path in world["catalogs"]] == before


def test_release_rejects_failed_source_reverify_for_accepted_result(world: dict) -> None:
    reservation.reserve(world["config"])
    _binding, _plan, result = _finalize_pilot(world)
    result["wrapper_source_final_full_reverify"] = {
        "checked_utc": "2026-09-08T00:01:00Z",
        "full_hash": True,
        "passed": False,
        "error": {"type": "OSError", "message": "source changed"},
    }
    _replace_immutable_manifest(
        world["output"] / "RESULT.json", _reseal_manifest(result),
    )
    before = [path.read_bytes() for path in world["catalogs"]]
    with pytest.raises(reservation.ReservationError, match="RESULT"):
        reservation.release(world["config"])
    assert [path.read_bytes() for path in world["catalogs"]] == before


def test_release_rejects_malformed_failed_source_reverify_error(world: dict) -> None:
    reservation.reserve(world["config"])
    _binding, _plan, result = _finalize_pilot(world, status="FAILED_CLOSED")
    result["wrapper_source_final_full_reverify"]["error"] = {
        "type": "OSError",
    }
    _replace_immutable_manifest(
        world["output"] / "RESULT.json", _reseal_manifest(result),
    )
    before = [path.read_bytes() for path in world["catalogs"]]
    with pytest.raises(reservation.ReservationError, match="RESULT"):
        reservation.release(world["config"])
    assert [path.read_bytes() for path in world["catalogs"]] == before


def test_release_rejects_resealed_empty_stage_evidence(world: dict) -> None:
    reservation.reserve(world["config"])
    _binding, _plan, result = _finalize_pilot(world)
    result["stages"] = []
    _replace_immutable_manifest(
        world["output"] / "RESULT.json", _reseal_manifest(result),
    )
    before = [path.read_bytes() for path in world["catalogs"]]
    with pytest.raises(reservation.ReservationError, match="evidence"):
        reservation.release(world["config"])
    assert [path.read_bytes() for path in world["catalogs"]] == before


def test_release_rejects_changed_staged_artifact(world: dict) -> None:
    reservation.reserve(world["config"])
    _finalize_pilot(world)
    artifact = world["output"] / "staging/pilot.gratp"
    artifact.chmod(0o600)
    artifact.write_bytes(b"tampered")
    artifact.chmod(0o400)
    before = [path.read_bytes() for path in world["catalogs"]]
    with pytest.raises(reservation.ReservationError, match="evidence"):
        reservation.release(world["config"])
    assert [path.read_bytes() for path in world["catalogs"]] == before


def test_recover_abort_closes_sigkill_residue_without_result(world: dict) -> None:
    reservation.reserve(world["config"])
    _binding, plan, _result = _finalize_pilot(world)
    (world["output"] / "RESULT.json").unlink()
    release = reservation.recover_abort(world["config"])
    abort = _load(world["output"] / "RECOVERY-ABORT.json")
    assert abort["status"] == "RECOVERED_ABORTED"
    assert abort["plan_sha256"] == plan["manifest_sha256"]
    assert reservation._selfhash_valid(abort, "record_sha256")
    assert release["result_status"] == "RECOVERED_ABORTED"
    for path in world["catalogs"]:
        assert {row["state"] for row in _load(path)["leases"]} == {"RELEASED"}


def test_recovery_abort_rejects_live_child(world: dict, monkeypatch: pytest.MonkeyPatch) -> None:
    reservation.reserve(world["config"])
    _finalize_pilot(world)
    (world["output"] / "RESULT.json").unlink()
    child = {
        "pid": 123, "start_ticks": 9, "state": "R",
        "cwd": str(world["output"] / "staging"), "argv": ["gratgen"],
        "cgroup": "", "compute_kind": "grat", "paper400_bound": True,
        "affinity": [0, 1, 2, 3], "affinity_class": "broad",
    }
    monkeypatch.setattr(
        reservation, "_scan_processes",
        lambda _config: reservation.ProcessScan((child,), ()),
    )
    with pytest.raises(reservation.ReservationError, match="child"):
        reservation.recover_abort(world["config"])
    assert not (world["output"] / "RECOVERY-ABORT.json").exists()


def test_compiled_wrapper_source_anchor_matches_frozen_source() -> None:
    assert hashlib.sha256(WRAPPER_SOURCE.read_bytes()).hexdigest() == (
        reservation.TRUSTED_PILOT_WRAPPER_SHA256
    )


def test_source_has_no_process_control_or_subprocess_authority() -> None:
    tree = ast.parse(SOURCE.read_text(encoding="utf-8"))
    imports = {
        alias.name
        for node in ast.walk(tree)
        if isinstance(node, (ast.Import, ast.ImportFrom))
        for alias in node.names
    }
    called_attributes = {
        node.func.attr
        for node in ast.walk(tree)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
    }
    assert "subprocess" not in imports
    assert not ({"kill", "killpg", "system", "unlinkat"} & called_attributes)


def test_production_constants_are_exactly_three_known_catalogs() -> None:
    assert reservation.RUN_ROOT == Path("/home/jing/paper400-runs")
    assert reservation.CATALOGS == (
        reservation.RUN_ROOT / ".paper400-recursive-split-v1/cpu-leases.json",
        reservation.RUN_ROOT
        / ".paper400-recursive-certified-slot-handoffs-v1/borrow-control/cpu-leases.json",
        reservation.RUN_ROOT
        / ".paper400-recursive-nested-certified-slot-handoffs-v2/cpu-leases.json",
    )
