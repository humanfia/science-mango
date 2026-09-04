from __future__ import annotations

from pathlib import Path

import pytest

from scripts import paper400_dic5_recursive_cpu_lease_compaction_v1 as compaction
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


def _entry(cpu: int, *, state: str, reservation: str, released_at: float | None) -> dict:
    return {
        "cpu": cpu,
        "bundle": f"/tmp/bundle-{reservation[:4]}",
        "reservation_sha256": reservation,
        "state": state,
        "created_at": 1.0,
        "released_at": released_at,
    }


def _write_catalog(control: Path, leases: list[dict]) -> dict:
    value = supervisor.seal(
        {
            "schema_version": supervisor.SCHEMA_VERSION,
            "kind": supervisor.CPU_CATALOG_KIND,
            "leases": leases,
            "updated_at": 2.0,
        },
        "catalog_sha256",
    )
    (control / supervisor.CATALOG).write_bytes(supervisor.canonical_bytes(value) + b"\n")
    return value


def test_compaction_archives_released_history_before_republishing_live_catalog(tmp_path: Path) -> None:
    control = tmp_path / "control"
    control.mkdir(mode=0o700)
    control.chmod(0o700)
    original = _write_catalog(
        control,
        [
            _entry(7, state="RELEASED", reservation="a" * 64, released_at=3.0),
            _entry(7, state="RESERVED", reservation="b" * 64, released_at=None),
            _entry(8, state="RESERVED", reservation="c" * 64, released_at=None),
        ],
    )

    result = compaction.compact_released_cpu_leases(control_root=control)
    assert result["compacted"] is True
    live = supervisor._load_catalog(control)
    assert [entry["cpu"] for entry in live["leases"]] == [7, 8]
    assert all(entry["state"] == "RESERVED" for entry in live["leases"])
    archive = Path(result["archive_path"])
    stored = supervisor._read_json(archive)
    assert stored["original_catalog_sha256"] == original["catalog_sha256"]
    assert len(stored["removed_released_leases"]) == 1
    assert compaction.compact_released_cpu_leases(control_root=control)["compacted"] is False


def test_compaction_refuses_two_active_leases_for_one_cpu(tmp_path: Path) -> None:
    control = tmp_path / "control"
    control.mkdir(mode=0o700)
    control.chmod(0o700)
    _write_catalog(
        control,
        [
            _entry(7, state="RESERVED", reservation="a" * 64, released_at=None),
            _entry(7, state="RESERVED", reservation="b" * 64, released_at=None),
        ],
    )
    with pytest.raises(compaction.CpuLeaseCompactionError, match="duplicate active"):
        compaction.compact_released_cpu_leases(control_root=control)
