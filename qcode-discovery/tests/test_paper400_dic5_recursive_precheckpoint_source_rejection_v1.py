from __future__ import annotations

from pathlib import Path

import pytest

from investigations import paper400_dic5_recursive_split_v1 as recursive
from scripts import paper400_dic5_recursive_precheckpoint_source_rejection_v1 as rejection
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


def _loaded(tmp_path: Path) -> tuple[dict, Path]:
    control = tmp_path / "control"
    bundle = control / "bundle"
    workers = bundle / "workers"
    children = bundle / "children"
    for path in (control, bundle, workers, children):
        path.mkdir(mode=0o700)
        path.chmod(0o700)
    reservation = supervisor._reserve_cpus(
        control, bundle=bundle, cpus=[7, 8], observations=[],
    )
    queue = {
        "queue_sha256": "q" * 64,
        "status": recursive.QUEUE_STATUS_OPEN,
        "event_sequence": 0,
        "items": [
            {"state": "PENDING", "claim": None, "attempts": 0, "cpu_ids": []},
        ],
    }
    loaded = {
        "root": bundle,
        "control_root": control,
        "bundle": {"bundle_sha256": "b" * 64, "queue_sha256": "q" * 64},
        "audit": {
            "parent_root": str(tmp_path / "parent"),
            "parent_static_sha256": "a" * 64,
            "parent_session_sha256": "s" * 64,
            "parent_pid": 123,
            "parent_proc_start_ticks": 456,
        },
        "reservation": reservation,
        "queue": queue,
    }
    return loaded, bundle


def test_rejection_seals_before_releasing_and_is_idempotent(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    loaded, bundle = _loaded(tmp_path)
    parent = {
        "controller_status_sha256": "c" * 64,
        "pid": 123,
        "proc_start_ticks": 456,
        "cpu_seconds": 43201.0,
        "state": "R",
    }
    monkeypatch.setattr(rejection.supervisor, "_load_bundle", lambda *_args, **_kwargs: loaded)
    monkeypatch.setattr(rejection, "_require_pristine_queue", lambda _loaded: None)
    monkeypatch.setattr(rejection, "_require_recorded_r4_for_r5_parent", lambda _loaded: None)
    monkeypatch.setattr(rejection, "_require_reserved_catalog_leases", lambda _loaded: None)
    monkeypatch.setattr(rejection, "_verify_original_live_r5_parent", lambda _loaded: parent)

    first = rejection.reject_precheckpoint_source_mismatch(bundle, control_root=loaded["control_root"])
    receipt = bundle / rejection.REJECTION
    assert receipt.exists()
    assert recursive.selfhash_valid(first, "record_sha256")
    catalog = supervisor._load_catalog(loaded["control_root"])
    assert all(entry["state"] == "RELEASED" for entry in catalog["leases"])

    second = rejection.reject_precheckpoint_source_mismatch(bundle, control_root=loaded["control_root"])
    assert second == first


def test_pristine_queue_rejects_any_child_evidence(tmp_path: Path) -> None:
    loaded, bundle = _loaded(tmp_path)
    child = bundle / "children" / "0"
    child.mkdir(mode=0o700)
    child.chmod(0o700)
    with pytest.raises(rejection.PrecheckpointSourceRejectionError, match="child evidence"):
        rejection._require_pristine_queue(loaded)
