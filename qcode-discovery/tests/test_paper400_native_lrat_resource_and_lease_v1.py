from __future__ import annotations

import json
import os
import time
from pathlib import Path

import pytest

from scripts import paper400_native_lrat_lease_owner_v1 as owner
from scripts import paper400_native_lrat_resource_gate_v1 as gate


def _write_json(path: Path, value: object, mode: int = 0o600) -> None:
    path.write_bytes(owner._canonical(value) + b"\n")
    path.chmod(mode)


def _resource_tree(base: Path) -> tuple[Path, Path]:
    proc = base / "proc"
    (proc / "pressure").mkdir(parents=True)
    (proc / "self").mkdir()
    (proc / "meminfo").write_text("MemAvailable: 1048576 kB\n", encoding="ascii")
    (proc / "vmstat").write_text("oom_kill 0\n", encoding="ascii")
    psi = (
        "some avg10=0.00 avg60=0.00 avg300=0.00 total=0\n"
        "full avg10=0.00 avg60=0.00 avg300=0.00 total=0\n"
    )
    (proc / "pressure/memory").write_text(psi, encoding="ascii")
    (proc / "self/cgroup").write_text("0::/pilot\n", encoding="ascii")
    mount = base / "cgroup"
    current = mount / "pilot"
    current.mkdir(parents=True)
    (current / "memory.current").write_text("0\n", encoding="ascii")
    (current / "memory.max").write_text("1073741824\n", encoding="ascii")
    (current / "memory.events").write_text("oom 0\noom_kill 0\n", encoding="ascii")
    (current / "memory.pressure").write_text(psi, encoding="ascii")
    return proc, mount


def _gate_config(base: Path) -> gate.ResourceGateConfig:
    proc, mount = _resource_tree(base)
    return gate.ResourceGateConfig(
        proc_root=proc, cgroup_mount=mount,
        min_host_available_bytes=1, min_cgroup_available_bytes=1,
        max_host_psi_some_avg10=10.0, max_host_psi_full_avg10=10.0,
        max_cgroup_psi_some_avg10=10.0, max_cgroup_psi_full_avg10=10.0,
    )


def _catalogs(run_root: Path) -> tuple[Path, ...]:
    result: list[Path] = []
    for index in range(3):
        directory = run_root / f"catalog-{index}"
        directory.mkdir()
        (directory / "cpu-leases.lock").write_bytes(b"")
        (directory / "cpu-leases.lock").chmod(0o600)
        catalog = directory / "cpu-leases.json"
        _write_json(catalog, owner._seal({
            "schema_version": 1, "kind": owner.CATALOG_KIND,
            "leases": [], "updated_at": 1_700_000_000.0,
        }, "catalog_sha256"))
        result.append(catalog)
    return tuple(sorted(result, key=str))


def _lease_config(tmp_path: Path) -> owner.LeaseConfig:
    run_root = tmp_path / "runs"
    run_root.mkdir()
    resources = _gate_config(tmp_path / "resources")
    return owner.LeaseConfig(
        run_root=run_root,
        output_root=run_root / "paper400-native-lrat-pilot-v1-test",
        catalogs=_catalogs(run_root), cpus=(2, 3), ttl_seconds=60.0,
        resource=resources,
    )


def _add_process(proc: Path, pid: int, cpu: int, command: str = "cadical") -> None:
    directory = proc / str(pid)
    directory.mkdir()
    fields = ["0"] * 18 + ["12345"]
    (directory / "stat").write_text(
        f"{pid} ({command}) R " + " ".join(fields) + "\n", encoding="ascii",
    )
    (directory / "status").write_text(
        f"Name:\t{command}\nCpus_allowed_list:\t{cpu}\n", encoding="ascii",
    )
    (directory / "cmdline").write_text(f"/usr/bin/{command}\0", encoding="ascii")


def test_resource_gate_healthy_and_owned_identity_exemption(tmp_path: Path) -> None:
    config = _gate_config(tmp_path)
    first = gate.snapshot(config, [2])
    assert first["go"] is True
    _add_process(config.proc_root, 4242, 2)
    with pytest.raises(gate.ResourceGateError, match="live CPU conflict"):
        gate.snapshot(config, [2])
    exempt = gate.snapshot(config, [2], owned_processes={4242: 12345})
    assert exempt["go"] is True


@pytest.mark.parametrize("failure", ["host-memory", "cgroup-memory", "psi", "oom"])
def test_resource_gate_fails_closed_on_pressure_and_oom(
    tmp_path: Path, failure: str,
) -> None:
    config = _gate_config(tmp_path)
    baseline = gate.snapshot(config, [2])
    if failure == "host-memory":
        (config.proc_root / "meminfo").write_text("MemAvailable: 0 kB\n", encoding="ascii")
    elif failure == "cgroup-memory":
        current = config.cgroup_mount / "pilot"
        (current / "memory.current").write_text("1073741824\n", encoding="ascii")
    elif failure == "psi":
        (config.proc_root / "pressure/memory").write_text(
            "some avg10=99.00 avg60=0.00 avg300=0.00 total=0\n"
            "full avg10=0.00 avg60=0.00 avg300=0.00 total=0\n",
            encoding="ascii",
        )
    else:
        (config.proc_root / "vmstat").write_text("oom_kill 1\n", encoding="ascii")
    with pytest.raises(gate.ResourceGateError, match="resource admission is NO-GO"):
        gate.snapshot(config, [2], baseline=baseline)


def test_partial_acquire_replays_then_renew_is_monotonic(tmp_path: Path) -> None:
    config = _lease_config(tmp_path)
    with pytest.raises(RuntimeError, match="partial native lease acquire"):
        owner.acquire(
            config, _test_nonce=owner._TEST_ONLY_NONCE,
            _fail_after_catalog=1,
        )
    assert config.output_root.exists()
    result = owner.acquire(config, _test_nonce=owner._TEST_ONLY_NONCE)
    assert result["recovery_replay"] is True
    state_before = owner._load_state(config, owner._load_reservation(config))
    renewed = owner.renew(config, _test_nonce=owner._TEST_ONLY_NONCE)
    state_after = owner._load_state(config, owner._load_reservation(config))
    assert renewed["epoch"] == state_before["epoch"] + 1 == state_after["epoch"]
    assert state_after["expires_at"] > state_before["expires_at"]


def test_partial_release_replays_without_process_or_cleanup_authority(tmp_path: Path) -> None:
    config = _lease_config(tmp_path)
    owner.acquire(config, _test_nonce=owner._TEST_ONLY_NONCE)
    with pytest.raises(RuntimeError, match="partial native lease release"):
        owner.release(
            config, _test_nonce=owner._TEST_ONLY_NONCE,
            _fail_after_catalog=1,
        )
    result = owner.release(config, _test_nonce=owner._TEST_ONLY_NONCE)
    assert result["all_three_catalogs_released"] is True
    assert result["process_control_authority"] is False
    assert result["cleanup_authority"] is False
    replay = owner.release(config, _test_nonce=owner._TEST_ONLY_NONCE)
    assert replay == result
    for path in config.catalogs:
        rows = owner._load_catalog(path)["leases"]
        assert {row["state"] for row in rows} == {"RELEASED"}


def test_native_lease_namespace_is_distinct_from_grat() -> None:
    assert "native-lrat" in owner.GATE
    assert "grat" not in owner.GATE
    assert owner.RESERVATION_KIND.startswith(owner.GATE)
    assert owner.LEASE_SCOPE.startswith(owner.GATE)
