from __future__ import annotations

import importlib.util
from pathlib import Path

from investigations import paper400_dic5_recursive_split_v1 as recursive
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "paper400_dic5_recursive_initial_batch_lifecycle_v1.py"
)
SPEC = importlib.util.spec_from_file_location("recursive_initial_batch_lifecycle_v1_test", SOURCE)
assert SPEC is not None and SPEC.loader is not None
lifecycle = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(lifecycle)


def _claimed_queue(tmp_path: Path) -> tuple[Path, dict, dict, dict]:
    bundle = tmp_path / "bundle"
    bundle.mkdir(mode=0o700)
    bundle.chmod(0o700)
    parent = b"p cnf 3 3\n1 2 0\n-1 3 0\n-2 -3 0\n"
    manifest, _payloads = recursive.build_split_manifest(
        parent, parent_id="parent-g000000", fanout=2, split_variables=[1],
    )
    queue = recursive.create_split_queue(
        bundle / "queue.json", manifest, cpu_pool=[20, 21],
        parent_manifest_sha256="a" * 64,
    )
    claimed = recursive.claim_queue_item(
        bundle / "queue.json", worker_id="worker-a", now=100.0,
        lease_seconds=3600.0,
    )
    assert claimed is not None
    current = recursive.load_split_queue(bundle / "queue.json")
    return bundle, manifest, current, claimed


def _certificate_for(item: dict) -> tuple[dict, dict]:
    certificate = recursive.seal(
        {
            "leaf_id": item["leaf_id"],
            "leaf_sha256": item["leaf_sha256"],
            "child_cnf_sha256": item["child_cnf_sha256"],
            "child_dimacs_sha256": item["child_dimacs_sha256"],
            "child_num_variables": item["child_num_variables"],
            "child_num_clauses": item["child_num_clauses"],
            "child_dimacs_bytes": item["child_dimacs_bytes"],
            "valid": True,
            "strict_proof_unsat": True,
            "fresh_proof_replay": True,
            "source_toolchain_fresh": True,
        },
        "certificate_sha256",
    )
    validation = {
        "valid": True,
        "strict_proof_unsat": True,
        "fresh_proof_replay": True,
        "source_toolchain_fresh": True,
        "failures": [],
    }
    return certificate, validation


def test_certification_transition_replays_the_public_queue_mutation(tmp_path: Path) -> None:
    bundle, _manifest, before, claimed = _claimed_queue(tmp_path)
    item = claimed["item"]
    certificate, validation = _certificate_for(item)

    expected = lifecycle._expected_certified_queue(
        before, item_id=item["item_id"], worker_id=item["claim"]["worker_id"],
        token=item["claim"]["token"], certificate=certificate, validation=validation,
        timestamp=123.5,
    )
    actual = recursive.certify_queue_item(
        bundle / "queue.json", item_id=item["item_id"], worker_id=item["claim"]["worker_id"],
        token=item["claim"]["token"], certificate=certificate, validation=validation,
        now=123.5,
    )

    assert actual == expected
    assert next(value for value in actual["items"] if value["item_id"] == item["item_id"])["state"] == "CERTIFIED"


def test_renewal_transition_replays_the_public_queue_mutation(tmp_path: Path) -> None:
    bundle, _manifest, before, claimed = _claimed_queue(tmp_path)
    item = claimed["item"]

    expected = lifecycle._expected_renewed_queue(
        before, item_id=item["item_id"], worker_id=item["claim"]["worker_id"],
        token=item["claim"]["token"], lease_seconds=7200.0, timestamp=123.5,
    )
    actual = recursive.renew_queue_item(
        bundle / "queue.json", item_id=item["item_id"], worker_id=item["claim"]["worker_id"],
        token=item["claim"]["token"], lease_seconds=7200.0, now=123.5,
    )

    assert actual == expected
    renewed = next(value for value in actual["items"] if value["item_id"] == item["item_id"])
    assert renewed["claim"]["lease_expires_at"] == 123.5 + 7200.0


def test_prepared_certification_recovers_the_atomic_queue_write_gap(tmp_path: Path) -> None:
    bundle, _manifest, before, claimed = _claimed_queue(tmp_path)
    item = claimed["item"]
    certificate, validation = _certificate_for(item)
    worker = {
        "worker_id": item["claim"]["worker_id"],
        "token": item["claim"]["token"],
        "worker_sha256": "b" * 64,
    }
    loaded = {
        "root": bundle,
        "bundle": {"bundle_sha256": "c" * 64},
        "plan": {"record_sha256": "d" * 64, "steps": [{"item_id": item["item_id"], "worker": worker}]},
        "initial_commit": {"record_sha256": "e" * 64},
        "initial_final_queue": before,
    }
    timestamp = 123.5
    binding = {
        "worker_id": worker["worker_id"],
        "token": worker["token"],
        "worker_sha256": worker["worker_sha256"],
        "queue_item_sha256_before": item["item_sha256"],
        "timestamp": timestamp,
        "proof_mode": "NORMAL",
        "certificate": certificate,
        "validation": validation,
    }
    after = lifecycle._expected_certified_queue(
        before, item_id=item["item_id"], worker_id=worker["worker_id"], token=worker["token"],
        certificate=certificate, validation=validation, timestamp=timestamp,
    )
    prepared = lifecycle._prepare_value(
        loaded, sequence=0, previous_record_sha256=loaded["plan"]["record_sha256"],
        action="CERTIFY_CHILD", item_id=item["item_id"], before=before, after=after, binding=binding,
    )
    prepare_path = lifecycle._prepare_path(bundle, 0)
    supervisor._publish_json(prepare_path, prepared)

    # Simulate a crash immediately after the public atomic queue replacement.
    actual = recursive.certify_queue_item(
        bundle / "queue.json", item_id=item["item_id"], worker_id=worker["worker_id"],
        token=worker["token"], certificate=certificate, validation=validation, now=timestamp,
    )
    assert actual == after
    interrupted = lifecycle._read_transition_state(loaded)
    assert interrupted["pending"] == prepared
    assert interrupted["current_queue"] == after

    transition = lifecycle._transition_value(loaded, prepared)
    supervisor._publish_json(lifecycle._transition_path(bundle, 0), transition)
    recovered = lifecycle._read_transition_state(loaded)
    assert recovered["pending"] is None
    assert recovered["committed_queue"] == after
