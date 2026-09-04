#!/usr/bin/env python3
"""Recover one exact recursive child claim stranded before its first start.

This is deliberately narrower than the recursive checkpoint recovery helper.
It exists for one crash-consistent boundary in the original v1 dispatcher:
the queue claim and durable worker record were published, but the process
exited before creating the child root.  The normal v1 queue-progress bootstrap
format is reserved for a fast-terminal orphan and must not be fabricated for a
child that has never started.

The helper admits only that exact one-claim state.  It writes an immutable
intent before materialising or starting the child, so an interruption after
that point remains fail-closed.  On a fast terminal it writes the ordinary
orphan receipt; the existing v1 fast-terminal recovery can then take over.
It never resumes a parent, changes a queue claim, releases a lease, or deletes
any data.
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import os
import sys
from collections.abc import Mapping
from pathlib import Path
from typing import Any


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from investigations import paper400_dic5_recursive_split_v1 as recursive
from scripts import paper400_dic5_recursive_checkpoint_recovery_v1 as recovery
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


SCHEMA_VERSION = 1
GATE = "paper400-dic5-recursive-prestart-claim-recovery-v1"
INTENT_DIR = Path("prestart-claim-recovery-v1")
INTENT_PATH = INTENT_DIR / "000000-intent.json"
STARTED_PATH = INTENT_DIR / "000001-started.json"
INTENT_KIND = "paper400-dic5-recursive-prestart-claim-intent-v1"
STARTED_KIND = "paper400-dic5-recursive-prestart-claim-started-v1"


class PrestartClaimRecoveryError(RuntimeError):
    """The exact no-start claim recovery conditions did not hold."""


def _source_binding() -> dict[str, Any]:
    source = Path(__file__).resolve(strict=True)
    payload = supervisor._stable_bytes(source, cap=32 << 20, executable=False)
    return {
        "method": "exact-source-sha256-replay-v1",
        "prestart_recovery_script": {
            "path": str(source),
            "sha256": hashlib.sha256(payload).hexdigest(),
        },
        "checkpoint_recovery": recovery._script_binding(),
    }


def _queue_item(queue: Mapping[str, Any], item_id: str) -> dict[str, Any]:
    candidates = [
        item for item in queue.get("items", [])
        if isinstance(item, dict) and item.get("item_id") == item_id
    ]
    if len(candidates) != 1:
        raise PrestartClaimRecoveryError("queue item is absent or ambiguous")
    return candidates[0]


def _claim_context(
    loaded: Mapping[str, Any],
) -> tuple[dict[str, Any], Path, dict[str, Any], dict[str, Any]]:
    """Validate the only state in which a lost pre-start can be repaired."""

    if loaded.get("queue_progress_bootstrap_required") is not True:
        raise PrestartClaimRecoveryError("claim is not an unledgered first claim")
    bundle = Path(loaded["root"])
    queue = recursive.load_split_queue(bundle / supervisor.QUEUE)
    claimed = recovery._validate_bootstrap_queue_shape(queue)
    workers = supervisor._worker_records(loaded)
    if len(workers) != 1:
        raise PrestartClaimRecoveryError("first claim does not have exactly one worker")
    worker_path, worker = workers[0]
    item = _queue_item(queue, claimed["item_id"])
    claim = item.get("claim")
    expected_child = bundle / supervisor.CHILDREN_DIR / item.get("path", "")
    if (
        item != claimed
        or item.get("state") != "CLAIMED"
        or item.get("attempts") != 0
        or item.get("last_error") is not None
        or item.get("certificate_sha256") is not None
        or not isinstance(claim, dict)
        or worker.get("state") != "CLAIMED"
        or worker.get("error") is not None
        or worker.get("queue_sha256_at_claim") != queue.get("queue_sha256")
        or worker.get("item_id") != item.get("item_id")
        or worker.get("leaf_id") != item.get("leaf_id")
        or worker.get("leaf_sha256") != item.get("leaf_sha256")
        or worker.get("token") != claim.get("token")
        or worker.get("worker_id") != claim.get("worker_id")
        or worker.get("cpu_ids") != claim.get("cpu_ids")
        or item.get("cpu_ids") != claim.get("cpu_ids")
        or worker.get("claim_expires_at") != claim.get("lease_expires_at")
        or worker.get("child_root") != str(expected_child)
        or not recursive.is_sha256(worker.get("worker_sha256"))
    ):
        raise PrestartClaimRecoveryError("first claim and worker binding is not exact")
    if expected_child.exists() or expected_child.is_symlink():
        raise PrestartClaimRecoveryError("claimed child already has material or runtime evidence")
    orphan = worker_path.with_name(worker_path.stem + ".orphan.json")
    if orphan.exists() or orphan.is_symlink():
        raise PrestartClaimRecoveryError("claimed child already has an orphan receipt")
    workers_dir = bundle / supervisor.WORKERS_DIR
    children_dir = bundle / supervisor.CHILDREN_DIR
    if (
        sorted(path.name for path in workers_dir.iterdir()) != [worker_path.name]
        or any(children_dir.iterdir())
    ):
        raise PrestartClaimRecoveryError("first claim has unexpected child-side evidence")
    return item, worker_path, worker, queue


def _safe_sidecar_dir(bundle: Path) -> Path:
    path = bundle / INTENT_DIR
    if path.exists():
        if path.is_symlink():
            raise PrestartClaimRecoveryError("prestart recovery sidecar path is unsafe")
        try:
            return supervisor._safe_directory(path, require_mode_0700=True)
        except supervisor.RecursiveSplitSupervisorError as exc:
            raise PrestartClaimRecoveryError("prestart recovery sidecar is unsafe") from exc
    try:
        os.mkdir(path, 0o700)
        supervisor._fsync_dir(bundle)
    except OSError as exc:
        raise PrestartClaimRecoveryError("cannot create prestart recovery sidecar") from exc
    return path


def _intent_value(
    loaded: Mapping[str, Any], receipt: Mapping[str, Any], *, item: Mapping[str, Any],
    worker: Mapping[str, Any], queue: Mapping[str, Any],
) -> dict[str, Any]:
    claim = item["claim"]
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": INTENT_KIND,
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "parent_checkpoint_sha256": receipt["record_sha256"],
            "queue_sha256": queue["queue_sha256"],
            "queue_event_sequence": queue["event_sequence"],
            "item_id": item["item_id"],
            "queue_item_sha256": item["item_sha256"],
            "leaf_id": item["leaf_id"],
            "leaf_sha256": item["leaf_sha256"],
            "worker_sha256": worker["worker_sha256"],
            "claim_token": claim["token"],
            "worker_id": claim["worker_id"],
            "cpu_ids": list(claim["cpu_ids"]),
            "child_root": worker["child_root"],
            "child_root_absent": True,
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def _validate_intent(
    value: Mapping[str, Any], expected: Mapping[str, Any],
) -> dict[str, Any]:
    fields = {
        "schema_version", "kind", "gate", "bundle_sha256", "parent_checkpoint_sha256",
        "queue_sha256", "queue_event_sequence", "item_id", "queue_item_sha256",
        "leaf_id", "leaf_sha256", "worker_sha256", "claim_token", "worker_id",
        "cpu_ids", "child_root", "child_root_absent", "hardness_only",
        "solver_terminal_claim", "source_binding", "record_sha256",
    }
    if (
        set(value) != fields
        or not recursive.selfhash_valid(value, "record_sha256")
        or value.get("schema_version") != SCHEMA_VERSION
        or value.get("kind") != INTENT_KIND
        or value.get("gate") != GATE
        or value.get("source_binding") != _source_binding()
        or value.get("child_root_absent") is not True
        or value.get("hardness_only") is not True
        or value.get("solver_terminal_claim") is not False
        or any(value.get(key) != expected.get(key) for key in fields - {"record_sha256", "source_binding"})
    ):
        raise PrestartClaimRecoveryError("prestart intent does not replay the stranded claim")
    return dict(value)


def _started_value(intent: Mapping[str, Any], session: Mapping[str, Any]) -> dict[str, Any]:
    session_sha = session.get("record_sha256")
    if not recursive.is_sha256(session_sha):
        raise PrestartClaimRecoveryError("child start did not return a sealed session")
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": STARTED_KIND,
            "gate": GATE,
            "intent_sha256": intent["record_sha256"],
            "child_root": intent["child_root"],
            "expected_single_cpu": intent["cpu_ids"][0],
            "session_sha256": session_sha,
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def _validate_started(intent: Mapping[str, Any], value: Mapping[str, Any]) -> dict[str, Any]:
    fields = {
        "schema_version", "kind", "gate", "intent_sha256", "child_root",
        "expected_single_cpu", "session_sha256", "hardness_only", "solver_terminal_claim",
        "source_binding", "record_sha256",
    }
    if (
        set(value) != fields
        or not recursive.selfhash_valid(value, "record_sha256")
        or value.get("schema_version") != SCHEMA_VERSION
        or value.get("kind") != STARTED_KIND
        or value.get("gate") != GATE
        or value.get("intent_sha256") != intent.get("record_sha256")
        or value.get("child_root") != intent.get("child_root")
        or value.get("expected_single_cpu") != intent.get("cpu_ids", [None])[0]
        or not recursive.is_sha256(value.get("session_sha256"))
        or value.get("hardness_only") is not True
        or value.get("solver_terminal_claim") is not False
        or value.get("source_binding") != _source_binding()
    ):
        raise PrestartClaimRecoveryError("prestart started receipt is malformed")
    child_root = Path(intent["child_root"])
    child_loaded = supervisor.child_runner._load_static(child_root)
    session = supervisor.child_runner._load_session(child_root, child_loaded)
    if session.get("record_sha256") != value.get("session_sha256"):
        raise PrestartClaimRecoveryError("started receipt does not bind the child session")
    return dict(value)


def _orphan_value(
    loaded: Mapping[str, Any], *, item: Mapping[str, Any], worker: Mapping[str, Any],
    queue: Mapping[str, Any], error: BaseException,
) -> dict[str, Any]:
    claim = {"item": item, "claim": item["claim"], "queue_sha256": queue["queue_sha256"]}
    return supervisor._worker_value(
        loaded, claim, child_root=Path(worker["child_root"]), state="ORPHAN_UNRESOLVED",
        error=f"{type(error).__name__}: {error}",
    )


def recover_prestart_claim(
    bundle: Path, *, control_root: Path = supervisor.CONTROL_ROOT,
) -> dict[str, Any]:
    """Start one exact worker that never reached child-root creation."""

    loaded = recovery._load_recovery_bundle(bundle, control_root=control_root)
    receipt = recovery._require_checkpoint_receipt(loaded)
    root = Path(loaded["audit"]["parent_root"])
    with recovery._legacy_shared_lock(root):
        _observation, _chain = recovery._checked_checkpointed_parent(loaded)
        with supervisor._catalog_lock(Path(loaded["control_root"])):
            recovery._require_reserved_cpu_leases(loaded)
        item, worker_path, worker, queue = _claim_context(loaded)
        sidecar = _safe_sidecar_dir(Path(loaded["root"]))
        expected = _intent_value(loaded, receipt, item=item, worker=worker, queue=queue)
        intent_path = sidecar / INTENT_PATH.name
        started_path = sidecar / STARTED_PATH.name
        if intent_path.exists() or intent_path.is_symlink():
            intent = _validate_intent(supervisor._read_json(intent_path), expected)
            if not (started_path.exists() and not started_path.is_symlink()):
                raise PrestartClaimRecoveryError(
                    "prestart intent is durable but start completion is ambiguous"
                )
            started = _validate_started(intent, supervisor._read_json(started_path))
            return supervisor.seal(
                {
                    "schema_version": SCHEMA_VERSION,
                    "kind": "paper400-dic5-recursive-prestart-claim-recovery-result-v1",
                    "gate": GATE,
                    "intent_sha256": intent["record_sha256"],
                    "started_sha256": started["record_sha256"],
                    "already_started": True,
                    "hardness_only": True,
                    "solver_terminal_claim": False,
                },
                "record_sha256",
            )
        if started_path.exists() or started_path.is_symlink():
            raise PrestartClaimRecoveryError("started receipt exists without its intent")
        supervisor._publish_json(intent_path, expected)
        child_root = Path(worker["child_root"])
        try:
            supervisor.child_runner.prepare_root_from_material(
                child_root,
                parent_dimacs=loaded["parent"],
                split_manifest=loaded["manifest"],
                leaf_path=item["path"],
                parent_audit=loaded["audit"],
            )
            session = supervisor.child_runner.start_root(child_root, cpu=item["cpu_ids"][0])
        except BaseException as exc:
            orphan_path = worker_path.with_name(worker_path.stem + ".orphan.json")
            if orphan_path.exists() or orphan_path.is_symlink():
                raise PrestartClaimRecoveryError("prestart failure conflicts with an orphan receipt") from exc
            supervisor._publish_json(
                orphan_path,
                _orphan_value(loaded, item=item, worker=worker, queue=queue, error=exc),
            )
            raise
        started = _started_value(expected, session)
        supervisor._publish_json(started_path, started)
        return supervisor.seal(
            {
                "schema_version": SCHEMA_VERSION,
                "kind": "paper400-dic5-recursive-prestart-claim-recovery-result-v1",
                "gate": GATE,
                "intent_sha256": expected["record_sha256"],
                "started_sha256": started["record_sha256"],
                "already_started": False,
                "hardness_only": True,
                "solver_terminal_claim": False,
            },
            "record_sha256",
        )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--control-root", type=Path, default=supervisor.CONTROL_ROOT)
    parser.add_argument("action", choices=["recover-prestart-claim"])
    parser.add_argument("--bundle", type=Path, required=True)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    result = recover_prestart_claim(args.bundle, control_root=args.control_root)
    sys.stdout.buffer.write(supervisor.canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        PrestartClaimRecoveryError,
        recovery.RecursiveCheckpointRecoveryError,
        supervisor.RecursiveSplitSupervisorError,
        supervisor.child_runner.RecursiveChildRunnerError,
        recursive.RecursiveSplitError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
