from __future__ import annotations

import dataclasses
import fcntl
import hashlib
import importlib.util
import json
import os
import resource
import sys
from pathlib import Path

import pytest


SOURCE = Path(__file__).resolve().parents[1] / "scripts/paper400_grat_parallel_pilot_v1.py"
QCODE_ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("paper400_grat_parallel_pilot_v1_test", SOURCE)
assert SPEC is not None and SPEC.loader is not None
pilot = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = pilot
SPEC.loader.exec_module(pilot)
REAL_TRUSTED_TOOL_POLICY = pilot.TRUSTED_TOOL_POLICY
REAL_TRUSTED_BUILD_MANIFEST_PATH = pilot.TRUSTED_BUILD_MANIFEST_PATH
REAL_TRUSTED_BUILD_MANIFEST_BYTES = pilot.TRUSTED_BUILD_MANIFEST_BYTES
REAL_TRUSTED_BUILD_MANIFEST_SHA256 = pilot.TRUSTED_BUILD_MANIFEST_SHA256
REAL_WRAPPER_SOURCE_PATH = pilot.WRAPPER_SOURCE_PATH
REAL_PROBE_RUNTIME = pilot._probe_runtime
REAL_SCHED_GETAFFINITY = os.sched_getaffinity


def _write(path: Path, payload: bytes, mode: int = 0o600) -> Path:
    path.write_bytes(payload)
    path.chmod(mode)
    return path


def _directory(path: Path) -> Path:
    path.mkdir()
    path.chmod(0o700)
    return path


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


@pytest.fixture(autouse=True)
def forbid_production_catalog_discovery(monkeypatch: pytest.MonkeyPatch) -> None:
    def forbidden() -> tuple[Path, ...]:
        raise AssertionError("unit/integration tests must not discover production catalogs")

    monkeypatch.setattr(pilot, "_discover_lease_catalogs", forbidden)


@pytest.fixture
def world(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> dict:
    inputs = _directory(tmp_path / "inputs")
    run_root = _directory(tmp_path / "paper400-runs")
    pilot_parent = _directory(run_root / ".grat-pilots")
    output = _directory(pilot_parent / "paper400-grat-pilot-v1-unit")
    controls = [
        _directory(run_root / name)
        for name in (".recursive-a", ".recursive-b", ".recursive-c")
    ]
    tools = _directory(tmp_path / "tools")

    cnf = _write(inputs / "cube.cnf", b"p cnf 1 2\n1 0\n-1 0\n")
    proof = _write(inputs / "proof.drat", b"a\x00d\x00")
    wrapper_source = _write(inputs / "pilot-wrapper.py", b"# isolated wrapper fixture\n")
    gratgen = _write(tools / "gratgen", b"#!/bin/sh\nexit 99\n", 0o500)
    gratchk = _write(tools / "gratchk", b"#!/bin/sh\nexit 99\n", 0o500)
    tool_policy = {
        name: {
            "path": str(path), "realpath": str(path), "bytes": path.stat().st_size,
            "sha256": _sha(path), "runtime_kind": "static", "runtime_libraries": [],
        }
        for name, path in (("gratgen", gratgen), ("gratchk", gratchk))
    }
    manifest_value = {
        "kind": "paper400-grat-toolchain-build-v1",
        "version": 1,
        "production_eligible": False,
        "inputs": {
            name: {"sha256": digest}
            for name, digest in pilot.OFFICIAL_SOURCE_ARCHIVE_SHA256.items()
        },
        "artifacts": {
            name: {"sha256": tool_policy[name]["sha256"]}
            for name in ("gratgen", "gratchk")
        },
    }
    manifest = tools / "BUILD-MANIFEST.json"
    _write(manifest, json.dumps(manifest_value).encode("ascii"))

    cpus = (0, 1, 2, 3)
    reservation = pilot._sealed({
        "schema_version": 1,
        "kind": pilot.CPU_RESERVATION_KIND,
        "bundle": str(output),
        "cpus": list(cpus),
        "observations": [],
        "kernel_hardware_exclusive": False,
        "scheduler_lease_only": True,
        "created_at": 1.0,
    }, "reservation_sha256")
    _write(output / "cpu-reservation.json", pilot._canonical_bytes(reservation))
    rows = [{
        "cpu": cpu,
        "bundle": str(output),
        "reservation_sha256": reservation["reservation_sha256"],
        "state": "RESERVED",
        "created_at": 1.0,
        "released_at": None,
    } for cpu in cpus]
    catalog_value = pilot._sealed({
        "schema_version": 1,
        "kind": pilot.CPU_CATALOG_KIND,
        "leases": rows,
        "updated_at": 1.0,
    }, "catalog_sha256")
    catalogs = tuple(
        _write(control / "cpu-leases.json", pilot._canonical_bytes(catalog_value))
        for control in controls
    )
    catalog_locks = tuple(
        _write(control / "cpu-leases.lock", b"") for control in controls
    )

    monkeypatch.setattr(pilot, "PRODUCTION_RUN_ROOT", run_root)
    monkeypatch.setattr(pilot, "TRUSTED_LEASE_CATALOGS", catalogs)
    monkeypatch.setattr(pilot, "WRAPPER_SOURCE_PATH", wrapper_source)
    monkeypatch.setattr(pilot, "TRUSTED_TOOL_POLICY", tool_policy)
    monkeypatch.setattr(pilot, "TRUSTED_BUILD_MANIFEST_PATH", manifest)
    monkeypatch.setattr(pilot, "TRUSTED_BUILD_MANIFEST_BYTES", manifest.stat().st_size)
    monkeypatch.setattr(pilot, "TRUSTED_BUILD_MANIFEST_SHA256", _sha(manifest))
    monkeypatch.setattr(pilot, "_probe_runtime", lambda _path: ("static", []))
    # Critical isolation selector: no test is allowed to discover production catalogs.
    monkeypatch.setattr(pilot, "_discover_lease_catalogs", lambda: catalogs)
    monkeypatch.setattr(pilot.os, "sched_getaffinity", lambda _pid: set(range(16)))
    monkeypatch.setattr(
        pilot.resource, "getrlimit",
        lambda _kind: (resource.RLIM_INFINITY, resource.RLIM_INFINITY),
    )
    monkeypatch.setattr(pilot, "_memory_available_bytes", lambda: 1 << 50)
    monkeypatch.setattr(pilot, "_disk_available_bytes", lambda _path: 1 << 50)
    cgroup = {
        "path": str(tmp_path / "mock-cgroup"),
        "memory_current": 1 << 30,
        "memory_max": 1 << 50,
        "memory_events": {"oom": 0, "oom_kill": 0, "oom_group_kill": 0},
        "memory_pressure": {"full": {"avg10": 0.0, "avg60": 0.0, "total": 0}},
        "psi_full_avg10": 0.0,
        "psi_full_avg60": 0.0,
    }
    monkeypatch.setattr(pilot, "_cgroup_resource_snapshot", lambda: dict(cgroup))
    monkeypatch.setattr(pilot, "_proof_quiescence", lambda _proof: {
        "no_writable_fd_or_mapping": True,
        "stable_physical_identity": True,
        "transport_stopped_evidence_only": True,
    })

    config = pilot.PilotConfig(
        cnf=cnf,
        proof=proof,
        expected_cnf_sha256=_sha(cnf),
        expected_proof_sha256=_sha(proof),
        expected_cnf_bytes=cnf.stat().st_size,
        expected_proof_bytes=proof.stat().st_size,
        proof_format="binary",
        output_root=output,
        toolchain_lock=manifest,
        threads=4,
        cpus=cpus,
        lease_catalogs=catalogs,
        reservation_sha256=reservation["reservation_sha256"],
        memory_limit_bytes=64 << 30,
        memory_reserve_bytes=1 << 30,
        output_limit_bytes=1 << 30,
        disk_reserve_bytes=1 << 30,
        log_limit_bytes=1 << 20,
        stage_timeout_seconds=60,
    )
    return {
        "config": config,
        "output": output,
        "catalog": catalogs[0],
        "catalogs": catalogs,
        "catalog_lock": catalog_locks[0],
        "catalog_locks": catalog_locks,
        "catalog_value": catalog_value,
        "manifest": manifest,
        "proof": proof,
        "wrapper_source": wrapper_source,
        "gratgen": gratgen,
        "cgroup": cgroup,
    }


def _rewrite_world_cpu_reservation(
    world: dict, cpus: tuple[int, ...],
) -> str:
    current = json.loads((world["output"] / "cpu-reservation.json").read_bytes())
    unsigned = dict(current)
    unsigned.pop("reservation_sha256")
    unsigned["cpus"] = list(cpus)
    updated = pilot._sealed(unsigned, "reservation_sha256")
    _write(world["output"] / "cpu-reservation.json", pilot._canonical_bytes(updated))
    for catalog_path in world["catalogs"]:
        catalog = json.loads(catalog_path.read_bytes())
        unsigned_catalog = dict(catalog)
        unsigned_catalog.pop("catalog_sha256")
        unsigned_catalog["leases"] = [{
            "cpu": cpu,
            "bundle": str(world["output"]),
            "reservation_sha256": updated["reservation_sha256"],
            "state": "RESERVED",
            "created_at": 1.0,
            "released_at": None,
        } for cpu in cpus]
        _write(catalog_path, pilot._canonical_bytes(
            pilot._sealed(unsigned_catalog, "catalog_sha256")
        ))
    return updated["reservation_sha256"]


def test_compiled_policy_binds_reviewed_pilot_binaries() -> None:
    assert pilot.TRUSTED_TOOL_POLICY["gratgen"]["sha256"] == (
        "9c945d7d4b983f3c6c2f40d73b8dd425f7c722edd48f45244f7c6c138ee6fbdb"
    )
    assert pilot.TRUSTED_TOOL_POLICY["gratchk"]["sha256"] == (
        "fc4cf9f93d8b834cf14aa4dee566c39d85e128c86e6cbdeac3c184b0c5d078c1"
    )
    expected_catalogs = tuple(sorted((
        Path("/home/jing/paper400-runs/.paper400-recursive-split-v1/cpu-leases.json"),
        Path(
            "/home/jing/paper400-runs/"
            ".paper400-recursive-certified-slot-handoffs-v1/borrow-control/"
            "cpu-leases.json"
        ),
        Path(
            "/home/jing/paper400-runs/"
            ".paper400-recursive-nested-certified-slot-handoffs-v2/"
            "cpu-leases.json"
        ),
    ), key=str))
    assert pilot.TRUSTED_LEASE_CATALOGS == expected_catalogs


@pytest.mark.parametrize(
    ("threads", "cpus", "memory"),
    [(4, (0, 1, 2, 3), 64 << 30), (8, tuple(range(8)), 128 << 30)],
)
def test_plan_is_read_only_and_binds_inputs_scheduler_and_pipeline(
    world: dict, threads: int, cpus: tuple[int, ...], memory: int,
) -> None:
    config = dataclasses.replace(world["config"], threads=threads, cpus=cpus, memory_limit_bytes=memory)
    if threads == 8:
        reservation = json.loads((world["output"] / "cpu-reservation.json").read_bytes())
        unsigned = dict(reservation)
        unsigned.pop("reservation_sha256")
        unsigned["cpus"] = list(cpus)
        reservation = pilot._sealed(unsigned, "reservation_sha256")
        _write(world["output"] / "cpu-reservation.json", pilot._canonical_bytes(reservation))
        for catalog_path in world["catalogs"]:
            catalog = json.loads(catalog_path.read_bytes())
            unsigned_catalog = dict(catalog)
            unsigned_catalog.pop("catalog_sha256")
            unsigned_catalog["leases"] = [{
                "cpu": cpu, "bundle": str(world["output"]),
                "reservation_sha256": reservation["reservation_sha256"],
                "state": "RESERVED", "created_at": 1.0, "released_at": None,
            } for cpu in cpus]
            _write(catalog_path, pilot._canonical_bytes(
                pilot._sealed(unsigned_catalog, "catalog_sha256")
            ))
        config = dataclasses.replace(config, reservation_sha256=reservation["reservation_sha256"])
    before = sorted(path.name for path in world["output"].iterdir())
    plan = pilot.plan_pilot(config)
    assert sorted(path.name for path in world["output"].iterdir()) == before
    assert plan["mode"] == "NON_PRODUCTION_PILOT"
    assert plan["authoritative"] is False
    assert plan["inputs"]["cnf"]["device"] > 0
    assert plan["inputs"]["drat"]["inode"] > 0
    assert plan["inputs"]["drat"]["sha256"] == config.expected_proof_sha256
    source_binding = plan["wrapper_source"]
    assert set(source_binding) == {
        "role", "requested_path", "realpath", "device", "inode", "bytes",
        "sha256", "mode", "uid", "gid", "links", "mtime_ns", "ctime_ns",
    }
    assert source_binding["role"] == "pilot wrapper source"
    assert source_binding["requested_path"] == str(world["wrapper_source"])
    assert source_binding["realpath"] == str(world["wrapper_source"])
    assert source_binding["bytes"] == world["wrapper_source"].stat().st_size
    assert source_binding["sha256"] == _sha(world["wrapper_source"])
    assert source_binding["device"] == world["wrapper_source"].stat().st_dev
    assert source_binding["inode"] == world["wrapper_source"].stat().st_ino
    assert source_binding["mode"] == 0o600
    assert plan["wrapper_source_fd_pinned_for_context_lifetime"] is True
    assert plan["wrapper_source_initial_full_hash_verified"] is True
    assert plan["cpu_scheduler_authority"]["catalog_locks_released_before_expensive_work"] is True
    assert plan["pipeline"][0]["argv"][-3:] == ["-b", "-j", str(threads)]


def test_invalid_threads_and_expected_input_fail_closed(world: dict) -> None:
    with pytest.raises(pilot.GratPilotError, match="threads must be exactly"):
        pilot.plan_pilot(dataclasses.replace(world["config"], threads=2, cpus=(0, 1)))
    with pytest.raises(pilot.GratPilotError, match="proof does not match"):
        pilot.plan_pilot(dataclasses.replace(world["config"], expected_proof_sha256="0" * 64))
    with pytest.raises(pilot.GratPilotError, match="strictly increasing"):
        pilot.plan_pilot(dataclasses.replace(world["config"], cpus=(1, 0, 2, 3)))
    with pytest.raises(pilot.GratPilotError, match="three compiled absolute paths"):
        pilot.plan_pilot(dataclasses.replace(
            world["config"], lease_catalogs=tuple(reversed(world["catalogs"])),
        ))


def test_empty_wrapper_source_fails_before_plan(world: dict) -> None:
    world["wrapper_source"].write_bytes(b"")
    with pytest.raises(pilot.GratPilotError, match="wrapper source must be non-empty"):
        pilot.plan_pilot(world["config"])


@pytest.mark.parametrize("inventory_delta", ("missing", "extra"))
def test_dynamic_catalog_inventory_must_equal_compiled_three(
    world: dict,
    monkeypatch: pytest.MonkeyPatch,
    inventory_delta: str,
) -> None:
    if inventory_delta == "missing":
        discovered = world["catalogs"][:-1]
    else:
        discovered = (*world["catalogs"], world["catalogs"][-1].with_name("extra.json"))
    monkeypatch.setattr(pilot, "_discover_lease_catalogs", lambda: discovered)
    with pytest.raises(pilot.GratPilotError, match="bounded production discovery"):
        pilot.plan_pilot(world["config"])


def test_build_manifest_and_binary_are_anchored(world: dict) -> None:
    world["manifest"].write_bytes(world["manifest"].read_bytes() + b" ")
    with pytest.raises(pilot.GratPilotError, match="build manifest does not match"):
        pilot.plan_pilot(world["config"])


def test_scheduler_lock_contention_fails_before_writes(world: dict) -> None:
    fd = os.open(world["catalog_lock"], os.O_RDWR)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        with pytest.raises(pilot.GratPilotError, match="scheduler lock is busy"):
            pilot.run_pilot(world["config"])
    finally:
        fcntl.flock(fd, fcntl.LOCK_UN)
        os.close(fd)
    assert sorted(path.name for path in world["output"].iterdir()) == ["cpu-reservation.json"]


def test_scheduler_owner_must_be_exact(world: dict) -> None:
    value = dict(world["catalog_value"])
    value.pop("catalog_sha256")
    value["leases"] = value["leases"][1:]
    _write(world["catalog"], pilot._canonical_bytes(pilot._sealed(value, "catalog_sha256")))
    with pytest.raises(pilot.GratPilotError, match="lacks exactly one"):
        pilot.plan_pilot(world["config"])


def test_scheduler_rejects_duplicate_cpu_in_one_catalog(world: dict) -> None:
    value = dict(world["catalog_value"])
    value.pop("catalog_sha256")
    value["leases"] = [*value["leases"], dict(value["leases"][0])]
    _write(world["catalog"], pilot._canonical_bytes(pilot._sealed(value, "catalog_sha256")))
    with pytest.raises(pilot.GratPilotError, match="duplicates an active CPU"):
        pilot.plan_pilot(world["config"])


def test_scheduler_rejects_one_catalog_with_different_owner(world: dict) -> None:
    value = dict(world["catalog_value"])
    value.pop("catalog_sha256")
    value["leases"] = [dict(row) for row in value["leases"]]
    value["leases"][0]["bundle"] = "/tmp/not-this-pilot"
    _write(world["catalog"], pilot._canonical_bytes(pilot._sealed(value, "catalog_sha256")))
    with pytest.raises(pilot.GratPilotError, match="mismatched scheduler owner"):
        pilot.plan_pilot(world["config"])


def _successful_stage(calls: list[dict]):
    def stage(**kwargs):
        calls.append(kwargs)
        if kwargs["stage"] == "gratgen":
            args = list(kwargs["arguments"])
            # A valid tiny GRAT split may contain an empty .gratl file.
            _write(Path(args[args.index("-l") + 1]), b"")
            _write(Path(args[args.index("-o") + 1]), b"proof")
            marker = "s VERIFIED"
        else:
            marker = "s VERIFIED UNSAT"
        return {
            "stage": kwargs["stage"], "exit_code": 0,
            "required_success_line": marker, "elapsed_wall_seconds": 0.01,
            "stdout": {}, "stderr": {}, "runtime": {}, "process_policy": {},
        }
    return stage


def test_run_is_ordered_atomic_and_never_authoritative(
    world: dict, monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls: list[dict] = []
    successful_stage = _successful_stage(calls)

    def stage_with_lock_probe(**kwargs):
        descriptors: list[int] = []
        try:
            for lock_path in world["catalog_locks"]:
                descriptor = os.open(lock_path, os.O_RDWR | os.O_CLOEXEC)
                descriptors.append(descriptor)
                fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
            return successful_stage(**kwargs)
        finally:
            for descriptor in reversed(descriptors):
                fcntl.flock(descriptor, fcntl.LOCK_UN)
                os.close(descriptor)

    monkeypatch.setattr(pilot, "_run_stage", stage_with_lock_probe)
    result = pilot.run_pilot(world["config"])
    assert [item["stage"] for item in calls] == ["gratgen", "gratchk"]
    assert list(calls[0]["arguments"])[-3:] == ["-b", "-j", "4"]
    assert result["status"] == "GRATCHK_ACCEPTED_PILOT_ONLY"
    assert result["authoritative"] is False
    assert result["eligible_for_terminal_publication"] is False
    assert result["catalog_locks_held_across_stage"] is False
    assert result["wrapper_source"] == json.loads(
        (world["output"] / "PLAN.json").read_bytes()
    )["wrapper_source"]
    assert result["wrapper_source_final_full_reverify"]["passed"] is True
    assert len(result["scheduler_boundary_snapshots"]) == 3
    assert (world["output"] / "PLAN.json").is_file()
    assert (world["output"] / "RESULT.json").is_file()
    for forbidden in pilot.FORBIDDEN_ANCESTOR_MARKERS:
        assert not (world["output"] / forbidden).exists()


def test_input_mutation_after_gratgen_records_failed_closed(
    world: dict, monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls: list[dict] = []
    success = _successful_stage(calls)
    def mutate(**kwargs):
        result = success(**kwargs)
        if kwargs["stage"] == "gratgen":
            world["proof"].write_bytes(b"b\x00d\x00")
        return result
    monkeypatch.setattr(pilot, "_run_stage", mutate)
    with pytest.raises(pilot.GratPilotError, match="identity changed|hash changed"):
        pilot.run_pilot(world["config"])
    failure = json.loads((world["output"] / "RESULT.json").read_bytes())
    assert failure["status"] == "FAILED_CLOSED"
    assert failure["terminal_publication"] is False
    assert failure["wrapper_source"]["sha256"] == _sha(world["wrapper_source"])
    assert failure["wrapper_source_final_full_reverify"]["passed"] is True


@pytest.mark.parametrize("mutation", ("content", "path_replacement"))
def test_wrapper_source_mutation_after_gratgen_records_failed_closed(
    world: dict, monkeypatch: pytest.MonkeyPatch, mutation: str,
) -> None:
    initial_sha256 = _sha(world["wrapper_source"])
    success = _successful_stage([])

    def mutate(**kwargs):
        result = success(**kwargs)
        if kwargs["stage"] == "gratgen":
            if mutation == "content":
                world["wrapper_source"].write_bytes(b"# mutated wrapper fixture\n")
            else:
                world["wrapper_source"].rename(
                    world["wrapper_source"].with_name("original-wrapper.py")
                )
                _write(
                    world["wrapper_source"], b"# replacement wrapper fixture\n",
                )
        return result

    monkeypatch.setattr(pilot, "_run_stage", mutate)
    with pytest.raises(pilot.GratPilotError, match="pilot wrapper source"):
        pilot.run_pilot(world["config"])
    failure = json.loads((world["output"] / "RESULT.json").read_bytes())
    assert failure["status"] == "FAILED_CLOSED"
    assert failure["wrapper_source"]["sha256"] == initial_sha256
    assert failure["wrapper_source_final_full_reverify"]["passed"] is False


def test_gratgen_uses_observed_stderr_protocol() -> None:
    assert pilot._validate_status_payload(
        "gratgen", b"",
        b"c parsing\nc Checking with 4 parallel threads\ns VERIFIED\n",
        expected_threads=4,
    ) == ("s VERIFIED", 4)
    for stdout, stderr in (
        (b"s VERIFIED\n", b""),
        (b"", b"s VERIFIED\ns VERIFIED\n"),
        (b"", b"s VERIFIED\x00\n"),
        (b"", b"s WRONG\n"),
        (b"", b"s VERIFIED\ns WRONG\n"),
        (b"", b"\xffs VERIFIED\n"),
    ):
        with pytest.raises(pilot.GratPilotError):
            pilot._validate_status_payload(
                "gratgen", stdout, stderr, expected_threads=4,
            )
    with pytest.raises(pilot.GratPilotError, match="differs"):
        pilot._validate_status_payload(
            "gratgen", b"",
            b"c Checking with 8 parallel threads\ns VERIFIED\n",
            expected_threads=4,
        )


def test_gratchk_uses_exact_stdout_protocol() -> None:
    assert pilot._validate_status_payload(
        "gratchk", b"c Reading cnf\nc Done\ns VERIFIED UNSAT\n", b"",
    ) == ("s VERIFIED UNSAT", None)
    for stdout, stderr in (
        (b"s VERIFIED UNSAT\n", b"warning\n"),
        (b"s VERIFIED UNSAT\ns VERIFIED UNSAT\n", b""),
        (b"ordinary log\ns VERIFIED UNSAT\n", b""),
        (b"s VERIFIED UNSAT\nc trailing\n", b""),
        (b"s VERIFIED UNSAT\x00\n", b""),
        (b"s WRONG\n", b""),
        (b"\xffs VERIFIED UNSAT\n", b""),
    ):
        with pytest.raises(pilot.GratPilotError):
            pilot._validate_status_payload("gratchk", stdout, stderr)


def test_empty_gratl_is_valid_but_empty_gratp_is_not(tmp_path: Path) -> None:
    empty_gratl = _write(tmp_path / "tiny.gratl", b"")
    empty_gratp = _write(tmp_path / "tiny.gratp", b"")
    with pilot._pin_generated(
        empty_gratl, role="tiny GRAT lemmas", cap=1024, allow_empty=True,
    ) as pin:
        assert pin.info.st_size == 0
    with pytest.raises(pilot.GratPilotError, match="empty or non-regular"):
        pilot._pin_generated(empty_gratp, role="tiny GRAT proof", cap=1024)


def test_dynamic_runtime_uses_sealed_loader_and_inhibits_cache(tmp_path: Path) -> None:
    executable = _write(tmp_path / "tool", b"tool", 0o500)
    loader = _write(tmp_path / "ld-linux-test.so", b"loader", 0o500)
    library = _write(tmp_path / "libtest.so", b"library", 0o400)
    staging = _directory(tmp_path / "staging")
    with pilot.PinnedFile.open(
        executable, role="tool", max_bytes=100, require_executable=True,
    ) as binary, pilot.PinnedFile.open(
        loader, role="loader", max_bytes=100, require_executable=True,
    ) as loader_pin, pilot.PinnedFile.open(
        library, role="library", max_bytes=100, require_executable=False,
    ) as library_pin:
        binding = pilot.ToolBinding("test", binary, "dynamic", [
            pilot.RuntimeObject("ld-linux-test.so", True, loader_pin),
            pilot.RuntimeObject("libtest.so", False, library_pin),
        ])
        with pilot._stage_tool_runtime(binding, staging) as runtime:
            argv = runtime.command(("arg",))
            assert argv[1:4] == ["--inhibit-cache", "--library-path", argv[3]]
            assert "--argv0" in argv
            for fd in runtime.pass_fds:
                if fd != runtime.library_directory_fd:
                    assert fcntl.fcntl(fd, pilot.F_GET_SEALS) == pilot.REQUIRED_MEMFD_SEALS


def test_dynamic_runtime_constructor_failure_rolls_back_links_directory_and_fds(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    executable = _write(tmp_path / "tool", b"tool", 0o500)
    loader = _write(tmp_path / "ld-linux-test.so", b"loader", 0o500)
    first_library = _write(tmp_path / "libfirst.so", b"first", 0o400)
    second_library = _write(tmp_path / "libsecond.so", b"second", 0o400)
    staging = _directory(tmp_path / "staging")
    with pilot.PinnedFile.open(
        executable, role="tool", max_bytes=100, require_executable=True,
    ) as binary, pilot.PinnedFile.open(
        loader, role="loader", max_bytes=100, require_executable=True,
    ) as loader_pin, pilot.PinnedFile.open(
        first_library, role="first library", max_bytes=100, require_executable=False,
    ) as first_pin, pilot.PinnedFile.open(
        second_library, role="second library", max_bytes=100, require_executable=False,
    ) as second_pin:
        binding = pilot.ToolBinding("fault", binary, "dynamic", [
            pilot.RuntimeObject("ld-linux-test.so", True, loader_pin),
            pilot.RuntimeObject("libfirst.so", False, first_pin),
            pilot.RuntimeObject("libsecond.so", False, second_pin),
        ])
        real_symlink = os.symlink
        calls = 0

        def fail_second_symlink(src, dst, *, dir_fd=None):
            nonlocal calls
            calls += 1
            if calls == 2:
                raise OSError("injected second symlink failure")
            return real_symlink(src, dst, dir_fd=dir_fd)

        monkeypatch.setattr(pilot.os, "symlink", fail_second_symlink)
        fd_count = len(os.listdir("/proc/self/fd"))
        with pytest.raises(OSError, match="injected second symlink failure"):
            pilot._stage_tool_runtime(binding, staging)
        assert len(os.listdir("/proc/self/fd")) == fd_count
        assert not (staging / "runtime-fault").exists()


def test_resource_gate_and_atomic_manifest(world: dict, monkeypatch: pytest.MonkeyPatch) -> None:
    config = world["config"]
    monkeypatch.setattr(
        pilot, "_memory_available_bytes",
        lambda: config.memory_limit_bytes + config.memory_reserve_bytes - 1,
    )
    with pytest.raises(pilot.GratPilotError, match="host memory admission"):
        pilot.plan_pilot(config)
    target = world["output"] / "atomic-test.json"
    pilot._atomic_write_json(target, {"first": True})
    with pytest.raises(pilot.GratPilotError, match="refusing to overwrite"):
        pilot._atomic_write_json(target, {"second": True})
    assert json.loads(target.read_bytes()) == {"first": True}


@pytest.mark.parametrize("threads", (4, 8))
def test_reviewed_toolchain_accepts_tracked_tiny_binary_drat(
    tmp_path: Path, threads: int,
) -> None:
    """Millisecond-scale real-tool integration; no production discovery or locks."""

    cnf_path = (
        QCODE_ROOT / "results/cube-and-conquer-smoke-v1-20260824T171713Z"
        / "leaves/leaf-0000/leaf.cnf"
    )
    proof_path = cnf_path.with_name("proof.drat")
    assert cnf_path.stat().st_size == 48
    assert _sha(cnf_path) == "351fa6ab6919a5a9f5d7e5c87002d5d1616552ad9cffeddebf4e54cea9c8178a"
    assert proof_path.stat().st_size == 8
    assert _sha(proof_path) == "166cd621308aa74427a60f29bb76087621beac31f0981bd2bce1b440db4d1af8"
    available = tuple(sorted(os.sched_getaffinity(0)))
    if len(available) < threads:
        pytest.skip(f"integration needs {threads} CPUs in the test affinity")
    cpus = available[:threads]
    staging = _directory(tmp_path / "staging")
    gratl_path = staging / "pilot.gratl"
    gratp_path = staging / "pilot.gratp"
    config = pilot.PilotConfig(
        cnf=cnf_path,
        proof=proof_path,
        expected_cnf_sha256=_sha(cnf_path),
        expected_proof_sha256=_sha(proof_path),
        expected_cnf_bytes=cnf_path.stat().st_size,
        expected_proof_bytes=proof_path.stat().st_size,
        proof_format="binary",
        output_root=staging,
        toolchain_lock=pilot.TRUSTED_BUILD_MANIFEST_PATH,
        threads=threads,
        cpus=cpus,
        lease_catalogs=(),
        reservation_sha256="0" * 64,
        memory_limit_bytes=(64 if threads == 4 else 128) << 30,
        memory_reserve_bytes=1 << 30,
        output_limit_bytes=1 << 20,
        disk_reserve_bytes=1 << 20,
        log_limit_bytes=4 << 20,
        stage_timeout_seconds=60,
    )
    with pilot.PinnedFile.open(
        cnf_path, role="tracked tiny CNF", max_bytes=1024, require_executable=False,
    ) as cnf, pilot.PinnedFile.open(
        proof_path,
        role="tracked tiny binary DRAT",
        max_bytes=1024,
        require_executable=False,
    ) as proof, pilot._open_toolchain(
        pilot.TRUSTED_BUILD_MANIFEST_PATH,
    ) as toolchain:
        with pilot._stage_tool_runtime(toolchain.tools["gratgen"], staging) as runtime:
            gratgen = pilot._run_stage(
                stage="gratgen",
                runtime=runtime,
                arguments=(
                    f"/proc/self/fd/{cnf.fd}",
                    f"/proc/self/fd/{proof.fd}",
                    "-l",
                    str(gratl_path),
                    "-o",
                    str(gratp_path),
                    "--no-progress-bar",
                    "-b",
                    "-j",
                    str(threads),
                ),
                pass_fds=(cnf.fd, proof.fd),
                cwd=staging,
                stdout_path=staging / "gratgen.stdout",
                stderr_path=staging / "gratgen.stderr",
                watched_paths=(gratl_path, gratp_path),
                config=config,
            )
        assert gratgen["required_success_line"] == "s VERIFIED"
        with pilot._pin_generated(
            gratl_path, role="tiny GRAT lemmas", cap=1 << 20, allow_empty=True,
        ) as gratl, pilot._pin_generated(
            gratp_path, role="tiny GRAT proof", cap=1 << 20,
        ) as gratp:
            assert gratl.info.st_size == 0
            assert gratp.info.st_size > 0
            with pilot._stage_tool_runtime(toolchain.tools["gratchk"], staging) as runtime:
                gratchk = pilot._run_stage(
                    stage="gratchk",
                    runtime=runtime,
                    arguments=(
                        "unsat",
                        f"/proc/self/fd/{cnf.fd}",
                        f"/proc/self/fd/{gratl.fd}",
                        f"/proc/self/fd/{gratp.fd}",
                    ),
                    pass_fds=(cnf.fd, gratl.fd, gratp.fd),
                    cwd=staging,
                    stdout_path=staging / "gratchk.stdout",
                    stderr_path=staging / "gratchk.stderr",
                    watched_paths=(gratl_path, gratp_path),
                    config=config,
                )
        assert gratchk["required_success_line"] == "s VERIFIED UNSAT"


@pytest.mark.parametrize("threads", (4, 8))
def test_full_pilot_with_three_fake_catalogs_and_reviewed_real_tools(
    world: dict,
    monkeypatch: pytest.MonkeyPatch,
    threads: int,
) -> None:
    """Exercise run_pilot end to end without any production catalog access."""

    monkeypatch.setattr(pilot, "TRUSTED_TOOL_POLICY", REAL_TRUSTED_TOOL_POLICY)
    monkeypatch.setattr(
        pilot, "TRUSTED_BUILD_MANIFEST_PATH", REAL_TRUSTED_BUILD_MANIFEST_PATH,
    )
    monkeypatch.setattr(
        pilot, "TRUSTED_BUILD_MANIFEST_BYTES", REAL_TRUSTED_BUILD_MANIFEST_BYTES,
    )
    monkeypatch.setattr(
        pilot, "TRUSTED_BUILD_MANIFEST_SHA256", REAL_TRUSTED_BUILD_MANIFEST_SHA256,
    )
    monkeypatch.setattr(pilot, "WRAPPER_SOURCE_PATH", REAL_WRAPPER_SOURCE_PATH)
    monkeypatch.setattr(pilot, "_probe_runtime", REAL_PROBE_RUNTIME)
    monkeypatch.setattr(pilot.os, "sched_getaffinity", REAL_SCHED_GETAFFINITY)
    available = tuple(sorted(REAL_SCHED_GETAFFINITY(0)))
    if len(available) < threads:
        pytest.skip(f"end-to-end integration needs {threads} CPUs")
    cpus = available[:threads]
    reservation_sha256 = _rewrite_world_cpu_reservation(world, cpus)
    sample_root = (
        QCODE_ROOT / "results/cube-and-conquer-smoke-v1-20260824T171713Z"
        / "leaves/leaf-0000"
    )
    cnf = sample_root / "leaf.cnf"
    proof = sample_root / "proof.drat"
    config = dataclasses.replace(
        world["config"],
        cnf=cnf,
        proof=proof,
        expected_cnf_sha256=_sha(cnf),
        expected_proof_sha256=_sha(proof),
        expected_cnf_bytes=cnf.stat().st_size,
        expected_proof_bytes=proof.stat().st_size,
        toolchain_lock=REAL_TRUSTED_BUILD_MANIFEST_PATH,
        threads=threads,
        cpus=cpus,
        reservation_sha256=reservation_sha256,
        memory_limit_bytes=(64 if threads == 4 else 128) << 30,
    )
    catalogs_before = {path: path.read_bytes() for path in world["catalogs"]}
    result = pilot.run_pilot(config)
    plan = json.loads((world["output"] / "PLAN.json").read_bytes())
    assert result["status"] == "GRATCHK_ACCEPTED_PILOT_ONLY"
    assert [stage["required_success_line"] for stage in result["stages"]] == [
        "s VERIFIED", "s VERIFIED UNSAT",
    ]
    assert result["stages"][0]["observed_parallel_threads"] == threads
    assert result["stages"][1]["observed_parallel_threads"] is None
    for stage in result["stages"]:
        identity = stage["process_identity"]
        assert identity["pid"] > 0
        assert identity["proc_start_ticks"] > 0
        assert identity["observed_affinity"] == list(cpus)
        assert identity["observed_before_wait"] is True
        assert identity["argv"]
    assert result["stages"][0]["process_identity"]["argv"][-2:] == [
        "-j", str(threads),
    ]
    assert plan["cpus"] == list(cpus)
    assert result["wrapper_source"] == plan["wrapper_source"]
    assert result["wrapper_source_final_full_reverify"]["passed"] is True
    assert result["wrapper_source"]["sha256"] == _sha(REAL_WRAPPER_SOURCE_PATH)
    assert not list((world["output"] / "staging").glob("runtime-*"))
    assert {path: path.read_bytes() for path in world["catalogs"]} == catalogs_before
