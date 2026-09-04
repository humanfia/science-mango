from __future__ import annotations

import shutil
from pathlib import Path

import pytest

from investigations import paper400_dic5_recursive_split_v1 as recursive


PARENT_DIMACS = b"""c small structural test instance
p cnf 4 4
1 -2 0
2 3 0
-3 4 0
-1 -4 0
"""


def _manifest(fanout: int = 4) -> tuple[dict, dict[str, bytes]]:
    return recursive.build_split_manifest(
        PARENT_DIMACS,
        parent_id="parent-leaf",
        fanout=fanout,
        split_variables=[1, 2, 3][: recursive.fanout_depth(fanout)],
    )


def _certificate(leaf: dict) -> dict:
    """A minimal complete envelope for queue/aggregate schema tests.

    These unit tests exercise the recursive binding layer, rather than
    substituting this fixture for a real DRAT/LRAT verification certificate.
    """

    return recursive.seal(
        {
            "leaf_id": leaf["leaf_id"],
            "leaf_sha256": leaf["leaf_sha256"],
            "child_cnf_sha256": leaf["child_cnf_sha256"],
            "child_dimacs_sha256": leaf["child_dimacs_sha256"],
            "child_num_variables": leaf["child_num_variables"],
            "child_num_clauses": leaf["child_num_clauses"],
            "child_dimacs_bytes": leaf["child_dimacs_bytes"],
            "valid": True,
            "strict_proof_unsat": True,
            "fresh_proof_replay": True,
            "hardness_only": False,
            "solver_terminal_claim": True,
        },
        "certificate_sha256",
    )


@pytest.mark.parametrize("fanout", [2, 4, 8])
def test_binary_cover_is_exhaustive_and_exact_for_all_supported_fanouts(
    fanout: int,
) -> None:
    manifest, payloads = _manifest(fanout)

    verification = recursive.verify_cover(manifest, PARENT_DIMACS)
    assert verification["valid"] is True
    assert [leaf["path"] for leaf in manifest["leaves"]] == recursive.frontier_paths(
        fanout
    )
    assert set(payloads) == set(recursive.frontier_paths(fanout))
    for path, payload in payloads.items():
        assert payload == recursive.render_leaf_payload(manifest, PARENT_DIMACS, path)
        assert payload.endswith(b"\n")


def test_cover_tampering_cannot_be_resealed_as_the_same_manifest() -> None:
    manifest, _ = _manifest(4)
    tampered = dict(manifest)
    leaves = [dict(leaf) for leaf in manifest["leaves"]]
    leaves[0]["assumptions"] = [-1, 2]
    leaves[0] = recursive.seal(
        {key: value for key, value in leaves[0].items() if key != "leaf_sha256"},
        "leaf_sha256",
    )
    tampered["leaves"] = leaves
    tampered = recursive.seal(
        {key: value for key, value in tampered.items() if key != "manifest_sha256"},
        "manifest_sha256",
    )
    with pytest.raises(recursive.RecursiveSplitError):
        recursive.verify_cover(tampered, PARENT_DIMACS)


def test_timing_ledger_never_charges_checkpoint_or_pid_reuse_intervals() -> None:
    ledger = recursive.new_timing_ledger("parent-leaf", timeout_seconds=10)
    # The first observation establishes a baseline; historical /proc time is
    # intentionally not silently adopted.
    ledger = recursive.update_timing_ledger(
        ledger,
        {
            "state": "RUNNING",
            "generation": 0,
            "pid": 11,
            "proc_start_ticks": 101,
            "cpu_seconds": 99.0,
            "observed_monotonic": 1.0,
        },
    )
    assert recursive.effective_solver_seconds(ledger) == 0.0
    ledger = recursive.update_timing_ledger(
        ledger,
        {
            "state": "RUNNING",
            "generation": 0,
            "pid": 11,
            "proc_start_ticks": 101,
            "cpu_seconds": 105.5,
            "observed_monotonic": 2.0,
        },
    )
    assert recursive.effective_solver_seconds(ledger) == 6.5
    ledger = recursive.update_timing_ledger(
        ledger,
        {
            "state": "CHECKPOINTED",
            "generation": 0,
            "pid": None,
            "proc_start_ticks": None,
            "cpu_seconds": None,
            "observed_monotonic": 3.0,
        },
    )
    ledger = recursive.update_timing_ledger(
        ledger,
        {
            "state": "RUNNING",
            "generation": 1,
            "pid": 11,
            "proc_start_ticks": 202,
            "cpu_seconds": 200.0,
            "observed_monotonic": 4.0,
        },
    )
    # Same numerical PID but a new start tick/generation is a new baseline.
    assert recursive.effective_solver_seconds(ledger) == 6.5
    ledger = recursive.update_timing_ledger(
        ledger,
        {
            "state": "RUNNING",
            "generation": 1,
            "pid": 11,
            "proc_start_ticks": 202,
            "cpu_seconds": 204.0,
            "observed_monotonic": 5.0,
        },
    )
    assert recursive.effective_solver_seconds(ledger) == 10.5
    assert recursive.timeout_reached(ledger) is True


def test_queue_claims_are_disjoint_and_expired_claims_are_recovered(
    tmp_path: Path,
) -> None:
    manifest, _ = _manifest(4)
    path = tmp_path / "split-queue.json"
    recursive.create_split_queue(
        path,
        manifest,
        cpu_pool=[6, 26],
        parent_manifest_sha256="a" * 64,
        now=100.0,
        lease_seconds=10.0,
    )
    first = recursive.claim_queue_item(path, worker_id="worker-a", now=101.0)
    second = recursive.claim_queue_item(path, worker_id="worker-b", now=101.0)
    assert first is not None and second is not None
    assert set(first["claim"]["cpu_ids"]).isdisjoint(second["claim"]["cpu_ids"])
    assert recursive.claim_queue_item(path, worker_id="worker-c", now=101.0) is None

    recovered = recursive.recover_split_queue(path, now=111.0)
    assert recovered["recovery_count"] == 2
    assert all(item["state"] == "PENDING" for item in recovered["items"])
    assert recursive.load_split_queue(path)["queue_sha256"] == recovered["queue_sha256"]


def test_queue_claim_renewal_preserves_identity_and_refuses_expiry(tmp_path: Path) -> None:
    manifest, _ = _manifest(2)
    path = tmp_path / "split-queue.json"
    recursive.create_split_queue(
        path, manifest, cpu_pool=[6, 26], now=100.0, lease_seconds=10.0,
    )
    claim = recursive.claim_queue_item(path, worker_id="worker-a", now=101.0)
    assert claim is not None
    renewed = recursive.renew_queue_item(
        path,
        item_id=claim["item"]["item_id"],
        worker_id="worker-a",
        token=claim["claim"]["token"],
        now=105.0,
        lease_seconds=20.0,
    )
    item = next(item for item in renewed["items"] if item["item_id"] == claim["item"]["item_id"])
    assert item["claim"]["cpu_ids"] == claim["claim"]["cpu_ids"]
    assert item["claim"]["lease_expires_at"] == 125.0
    with pytest.raises(recursive.RecursiveSplitError, match="expired"):
        recursive.renew_queue_item(
            path,
            item_id=claim["item"]["item_id"],
            worker_id="worker-a",
            token=claim["claim"]["token"],
            now=125.0,
        )


def test_queue_certification_and_parent_aggregate_require_every_exact_leaf(
    tmp_path: Path,
) -> None:
    manifest, _ = _manifest(2)
    path = tmp_path / "split-queue.json"
    recursive.create_split_queue(path, manifest, cpu_pool=[6, 26], now=10.0)
    certificates: list[dict] = []
    for index in range(2):
        claim = recursive.claim_queue_item(path, worker_id=f"worker-{index}", now=11.0)
        assert claim is not None
        leaf = manifest["leaves"][index]
        certificate = _certificate(leaf)
        certificates.append(certificate)
        recursive.certify_queue_item(
            path,
            item_id=claim["item"]["item_id"],
            worker_id=claim["claim"]["worker_id"],
            token=claim["claim"]["token"],
            certificate=certificate,
            validation={
                "valid": True,
                "strict_proof_unsat": True,
                "fresh_proof_replay": True,
                "source_toolchain_fresh": True,
                "failures": [],
            },
            now=12.0 + index,
        )
    assert recursive.split_queue_status(path)["status"] == recursive.QUEUE_STATUS_COMPLETE
    aggregate = recursive.aggregate_child_certificates(manifest, certificates)
    assert aggregate["status"] == "PARENT_CUBE_UNSAT"
    assert aggregate["parent_cube_unsat"] is True
    incomplete = recursive.aggregate_child_certificates(manifest, certificates[:1])
    assert incomplete["status"] == "UNRESOLVED"


def test_cleanup_recovers_after_crash_between_claim_and_commit(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    manifest, _ = _manifest(2)
    certificates = [_certificate(leaf) for leaf in manifest["leaves"]]
    aggregate = recursive.aggregate_child_certificates(manifest, certificates)
    root = tmp_path / "parent-root"
    root.mkdir(mode=0o700)
    root.chmod(0o700)
    (root / ".hierarchical-resume.lock").touch(mode=0o600)
    runtime = root / "runtime" / "dmtcp"
    runtime.mkdir(parents=True, mode=0o700)
    (runtime / "coordinator.log").write_bytes(b"transport-only\n")
    (runtime / "tmp").mkdir(mode=0o700)
    (runtime / "tmp" / "checkpoint.bin").write_bytes(b"x" * 64)

    plan = recursive.cleanup_parent_transport(
        root, split_manifest=manifest, aggregate=aggregate, dry_run=True,
    )
    assert plan["applied"] is False
    real_rmtree = shutil.rmtree

    def crash_after_remove(path: Path) -> None:
        real_rmtree(path)
        raise RuntimeError("simulated crash after removal")

    monkeypatch.setattr(recursive.shutil, "rmtree", crash_after_remove)
    with pytest.raises(RuntimeError, match="simulated crash"):
        recursive.cleanup_parent_transport(root, split_manifest=manifest, aggregate=aggregate)
    assert (root / recursive.CLEANUP_CLAIM_NAME).exists()
    assert not runtime.exists()
    monkeypatch.setattr(recursive.shutil, "rmtree", real_rmtree)

    commit = recursive.cleanup_parent_transport(
        root, split_manifest=manifest, aggregate=aggregate,
    )
    assert commit["runtime_absent"] is True
    assert (root / recursive.CLEANUP_COMMIT_NAME).exists()
    # Repeating a completed cleanup is read-only/idempotent.
    assert recursive.cleanup_parent_transport(
        root, split_manifest=manifest, aggregate=aggregate,
    )["cleanup_sha256"] == commit["cleanup_sha256"]
