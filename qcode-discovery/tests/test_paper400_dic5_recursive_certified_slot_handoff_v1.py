from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

from investigations import paper400_dic5_recursive_split_v1 as recursive


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "paper400_dic5_recursive_certified_slot_handoff_v1.py"
)
SPEC = importlib.util.spec_from_file_location("certified_slot_handoff_v1_test", SOURCE)
assert SPEC is not None and SPEC.loader is not None
handoff = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(handoff)


def _provider(tmp_path: Path, *, states: list[str] | None = None) -> tuple[Path, dict]:
    bundle = tmp_path / "primary" / "provider"
    bundle.mkdir(parents=True)
    pool = [1, 2, 3, 4]
    states = states or ["CLAIMED", "CERTIFIED", "CERTIFIED", "CERTIFIED"]
    items = []
    for index, (path, state) in enumerate(zip(["00", "01", "10", "11"], states)):
        child = bundle / "children" / path
        (child / "state").mkdir(parents=True)
        if state == "CERTIFIED":
            (child / "state" / "30-terminal.claim.json").write_text("{}")
            (child / "COMMIT.json").write_text("{}")
            (child / "certificate.json").write_text("{}")
            (child / "validation.json").write_text("{}")
        item = {
            "item_id": f"parent:{path}", "path": path, "state": state,
            "cpu_slots": 1, "cpu_ids": [pool[index]] if state == "CLAIMED" else [],
        }
        items.append(item)
    queue = {"items": items, "queue_sha256": "a" * 64}
    loaded = {
        "root": bundle,
        "bundle": {"bundle_sha256": "b" * 64},
        "reservation": {"cpus": pool, "reservation_sha256": "c" * 64},
        "queue": queue,
    }
    return bundle, loaded


def _patch_provider(monkeypatch: pytest.MonkeyPatch, primary: Path, bundle: Path, loaded: dict) -> None:
    monkeypatch.setattr(
        handoff.supervisor,
        "_load_catalog",
        lambda _control: {"leases": [{"cpu": cpu, "bundle": str(bundle), "state": "RESERVED"} for cpu in [1, 2, 3, 4]]},
    )
    monkeypatch.setattr(handoff.initial, "_load_immutable_components", lambda _bundle, *, control_root: loaded)
    monkeypatch.setattr(handoff, "_fixed_user_processes", lambda _cpus: [])


def test_reserve_serializes_only_certified_complement(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    primary = tmp_path / "primary"
    consumer = tmp_path / "consumer"
    root = tmp_path / "handoffs"
    bundle, loaded = _provider(tmp_path)
    _patch_provider(monkeypatch, primary, bundle, loaded)

    result = handoff.reserve_handoff(
        primary_control_root=primary, handoff_root=root, consumer_control_root=consumer,
        consumer_bundle_name="consumer-a", cpus=[2, 3],
    )
    assert result["action"] == "RESERVED"
    assert [entry["cpu"] for entry in result["entries"]] == [2, 3]
    catalog = handoff._load_catalog(root, primary_control_root=primary)
    assert [entry["cpu"] for entry in catalog["entries"] if entry["state"] == "RESERVED"] == [2, 3]


def test_reserve_rejects_claimed_or_noncertified_slot(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    primary = tmp_path / "primary"
    consumer = tmp_path / "consumer"
    root = tmp_path / "handoffs"
    bundle, loaded = _provider(tmp_path)
    _patch_provider(monkeypatch, primary, bundle, loaded)
    with pytest.raises(handoff.CertifiedSlotHandoffError, match="claimed"):
        handoff.reserve_handoff(
            primary_control_root=primary, handoff_root=root, consumer_control_root=consumer,
            consumer_bundle_name="consumer-a", cpus=[1, 2],
        )

    _bundle, bad = _provider(tmp_path / "bad", states=["CLAIMED", "CERTIFIED", "PENDING", "CERTIFIED"])
    monkeypatch.setattr(handoff.initial, "_load_immutable_components", lambda _bundle, *, control_root: bad)
    with pytest.raises(handoff.CertifiedSlotHandoffError, match="pending or failed"):
        handoff.reserve_handoff(
            primary_control_root=primary, handoff_root=root, consumer_control_root=consumer,
            consumer_bundle_name="consumer-b", cpus=[2, 3],
        )


def test_reserve_refuses_duplicate_active_cpu(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    primary = tmp_path / "primary"
    consumer = tmp_path / "consumer"
    root = tmp_path / "handoffs"
    bundle, loaded = _provider(tmp_path)
    _patch_provider(monkeypatch, primary, bundle, loaded)
    handoff.reserve_handoff(
        primary_control_root=primary, handoff_root=root, consumer_control_root=consumer,
        consumer_bundle_name="consumer-a", cpus=[2, 3],
    )
    with pytest.raises(handoff.CertifiedSlotHandoffError, match="already has an active handoff"):
        handoff.reserve_handoff(
            primary_control_root=primary, handoff_root=root, consumer_control_root=consumer,
            consumer_bundle_name="consumer-b", cpus=[2, 4],
        )


def test_release_requires_certified_consumer_aggregate(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    primary = tmp_path / "primary"
    consumer = tmp_path / "consumer"
    root = tmp_path / "handoffs"
    bundle, provider = _provider(tmp_path)
    _patch_provider(monkeypatch, primary, bundle, provider)
    handoff.reserve_handoff(
        primary_control_root=primary, handoff_root=root, consumer_control_root=consumer,
        consumer_bundle_name="consumer-a", cpus=[2, 3],
    )
    consumer_bundle = consumer / "consumer-a"
    consumer_bundle.mkdir(parents=True)
    aggregate = recursive.seal({"kind": "aggregate"}, "record_sha256")
    (consumer_bundle / handoff.PARENT_AGGREGATE).write_bytes(recursive.canonical_bytes(aggregate))
    consumer_loaded = {
        "root": consumer_bundle,
        "bundle": {"bundle_sha256": "d" * 64},
        "reservation": {"cpus": [2, 3], "reservation_sha256": "e" * 64},
        "queue": {"items": [{"state": "CERTIFIED"}, {"state": "CERTIFIED"}], "queue_sha256": "f" * 64},
    }
    monkeypatch.setattr(
        handoff.initial,
        "_load_immutable_components",
        lambda path, *, control_root: consumer_loaded if Path(path) == consumer_bundle else provider,
    )
    result = handoff.release_handoff(
        primary_control_root=primary, handoff_root=root, consumer_control_root=consumer,
        consumer_bundle_name="consumer-a",
    )
    assert len(result["entries"]) == 2
    assert all(entry["state"] == "RELEASED" for entry in result["entries"])
