#!/usr/bin/env python3
"""Forensic, all-sibling restart for a killed initial recursive batch.

This sidecar addresses one deliberately narrow failure mode: an initial batch
was correctly prepared and all its child ``start`` calls returned, but the
short-lived service that owned their cgroup exited and systemd consequently
killed the still-running DMTCP children.  An incomplete proof is never an
UNSAT proof and must not be resumed or overwritten in place.

For every explicitly selected, still-claimed child this helper instead:

* proves that the original child is stopped, has no terminal artifacts, and
  has a stable DRAT which the pinned checker rejects specifically as a partial
  no-conflict proof;
* writes immutable forensic records before preparing any new root;
* creates a distinct retry root for the exact same manifest leaf and retains
  the original root and proof untouched; and
* persists every retry intent before issuing any ``Popen``.  Callers running
  under systemd must pass ``--keep-alive`` so the process stays in the service
  cgroup after dispatch.  That is a transport-lifetime guard, not proof
  evidence.

It does not create a terminal claim, change a queue item, release a CPU lease,
resume a solver, or delete data.  A separate lifecycle sidecar certifies only
freshly replayed retry proofs.
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import os
import stat
import sys
import time
from collections.abc import Iterator, Mapping, Sequence
from pathlib import Path
from typing import Any


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from investigations import paper400_dic5_recursive_split_v1 as recursive
from scripts import paper400_dic5_recursive_checkpoint_recovery_v1 as recovery
from scripts import paper400_dic5_recursive_initial_batch_dispatch_v1 as initial
from scripts import paper400_dic5_recursive_initial_batch_lifecycle_v1 as base
from scripts import paper400_dic5_recursive_postbootstrap_batch_dispatch_v1 as batch
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


SCHEMA_VERSION = 1
GATE = "paper400-dic5-recursive-incomplete-child-restart-v1"
SIDECAR_DIR = Path("incomplete-child-restart-v1")
FORENSICS_DIR = SIDECAR_DIR / "forensics"
STARTS_DIR = SIDECAR_DIR / "starts"
PLAN = SIDECAR_DIR / "000000-restart-plan.json"
COMMIT = SIDECAR_DIR / "000001-restart-plan-committed.json"
LOCK = Path(".incomplete-child-restart-v1.lock")

FORENSIC_KIND = "paper400-dic5-recursive-incomplete-child-forensic-v1"
PLAN_KIND = "paper400-dic5-recursive-incomplete-child-restart-plan-v1"
COMMIT_KIND = "paper400-dic5-recursive-incomplete-child-restart-commit-v1"
INTENT_KIND = "paper400-dic5-recursive-incomplete-child-restart-intent-v1"
STARTED_KIND = "paper400-dic5-recursive-incomplete-child-restart-started-v1"
RESULT_KIND = "paper400-dic5-recursive-incomplete-child-restart-result-v1"
PARTIAL_DIAGNOSIS = "PINNED_DRAT_NO_CONFLICT_PARTIAL_PROOF"


class IncompleteChildRestartError(RuntimeError):
    """The stopped-child handoff is not exact enough to retry safely."""


_BASE_SOURCE_BINDING = base._source_binding


def _source_binding() -> dict[str, Any]:
    source = Path(__file__).resolve(strict=True)
    payload = supervisor._stable_bytes(source, cap=32 << 20, executable=False)
    child_source = PROJECT / "scripts" / "run_paper400_dic5_recursive_child_resume_proof_v1.py"
    child_payload = supervisor._stable_bytes(child_source, cap=32 << 20, executable=False)
    return {
        "method": "exact-source-sha256-replay-v1",
        "incomplete_child_restart": {
            "path": str(source),
            "sha256": hashlib.sha256(payload).hexdigest(),
        },
        "initial_batch_dispatch": initial._source_binding(),
        # The retry lifecycle temporarily replaces ``base._source_binding``
        # while it writes its own transaction records.  Capture the frozen
        # base binding at import time so source attestation never recurses
        # through that process-local adaptation.
        "initial_batch_lifecycle_base": _BASE_SOURCE_BINDING(),
        "checkpoint_recovery": recovery._script_binding(),
        "frozen_child_runner": {
            "path": str(child_source),
            "sha256": hashlib.sha256(child_payload).hexdigest(),
        },
    }


@contextlib.contextmanager
def _restart_lock(bundle: Path) -> Iterator[None]:
    """Serialize retry-plan publication independently of child-root locks."""

    path = bundle / LOCK
    try:
        fd = os.open(path, os.O_RDWR | os.O_CREAT | os.O_CLOEXEC | os.O_NOFOLLOW, 0o600)
    except OSError as exc:
        raise IncompleteChildRestartError("restart lock is unavailable") from exc
    try:
        info = os.fstat(fd)
        if (
            not stat.S_ISREG(info.st_mode)
            or info.st_uid != os.geteuid()
            or info.st_nlink != 1
            or stat.S_IMODE(info.st_mode) != 0o600
        ):
            raise IncompleteChildRestartError("restart lock metadata is unsafe")
        import fcntl

        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise IncompleteChildRestartError("another incomplete-child restart is active") from exc
        yield
    finally:
        with contextlib.suppress(OSError):
            import fcntl

            fcntl.flock(fd, fcntl.LOCK_UN)
        os.close(fd)


def _sidecar(bundle: Path, relative: Path) -> Path:
    try:
        return batch._safe_sidecar_dir(bundle, relative)
    except batch.BatchDispatchError as exc:
        raise IncompleteChildRestartError("restart sidecar directory is unsafe") from exc


def _publish_exact(path: Path, value: Mapping[str, Any], *, label: str) -> None:
    if path.exists() or path.is_symlink():
        if path.is_symlink() or supervisor._read_json(path) != value:
            raise IncompleteChildRestartError(f"existing {label} conflicts with replay")
        return
    supervisor._publish_json(path, value)


def _queue_item(queue: Mapping[str, Any], item_id: str) -> dict[str, Any]:
    try:
        return base._queue_item(queue, item_id)
    except base.InitialBatchLifecycleError as exc:
        raise IncompleteChildRestartError("restart queue item is absent or ambiguous") from exc


def _step(loaded: Mapping[str, Any], item_id: str) -> dict[str, Any]:
    try:
        return base._step_for_item(loaded, item_id)
    except base.InitialBatchLifecycleError as exc:
        raise IncompleteChildRestartError("restart item is not in the immutable initial plan") from exc


def _retry_root(bundle: Path, path: str) -> Path:
    if type(path) is not str or not path or any(char not in "01" for char in path):
        raise IncompleteChildRestartError("restart leaf path is unsafe")
    return bundle / supervisor.CHILDREN_DIR / f"retry-{path}-attempt-000001"


def _forensic_path(bundle: Path, step: Mapping[str, Any]) -> Path:
    worker = step["worker"]
    return _sidecar(bundle, FORENSICS_DIR) / f"{step['ordinal']:04d}-{worker['token'][:16]}.json"


def _start_paths(bundle: Path, entry: Mapping[str, Any]) -> tuple[Path, Path]:
    key = f"{entry['ordinal']:04d}-{entry['claim_token'][:16]}"
    directory = _sidecar(bundle, STARTS_DIR)
    return directory / f"{key}.intent.json", directory / f"{key}.started.json"


def _terminal_artifacts_absent(root: Path) -> bool:
    runner = supervisor.child_runner
    return not any(
        (root / name).exists() or (root / name).is_symlink()
        for name in (runner.TERMINAL_CLAIM, runner.CERTIFICATE, runner.VALIDATION, runner.FINAL_COMMIT)
    )


def _validate_original_child_binding(
    loaded: Mapping[str, Any], step: Mapping[str, Any], child_loaded: Mapping[str, Any],
    session: Mapping[str, Any], root: Path,
) -> dict[str, Any]:
    """Bind a stopped root to its original immutable queue worker and leaf."""

    item = _queue_item(step["after_queue"], step["item_id"])
    worker = step["worker"]
    child = child_loaded.get("static", {}).get("child")
    if (
        not isinstance(child, dict)
        or root != Path(worker.get("child_root", ""))
        or child.get("leaf_id") != item.get("leaf_id")
        or child.get("leaf_sha256") != item.get("leaf_sha256")
        or child.get("child_cnf_sha256") != item.get("child_cnf_sha256")
        or child.get("child_dimacs_sha256") != item.get("child_dimacs_sha256")
        or child.get("child_num_variables") != item.get("child_num_variables")
        or child.get("child_num_clauses") != item.get("child_num_clauses")
        or child.get("child_dimacs_bytes") != item.get("child_dimacs_bytes")
        or child_loaded.get("manifest", {}).get("manifest_sha256")
        != loaded["manifest"].get("manifest_sha256")
        or child_loaded.get("audit", {}).get("audit_sha256") != loaded["audit"].get("audit_sha256")
        or session.get("expected_single_cpu") != worker.get("cpu_ids", [None])[0]
    ):
        raise IncompleteChildRestartError("original child no longer binds its exact queue leaf")
    return item


def _partial_forensic_value(loaded: Mapping[str, Any], step: Mapping[str, Any]) -> dict[str, Any]:
    """Read one stopped partial proof under an exclusive root lock.

    The checker result is not treated as a solver result.  It is evidence that
    the inherited proof is incomplete, which is the only admitted reason to
    create a new retry root.
    """

    runner = supervisor.child_runner
    worker = step["worker"]
    root = Path(worker["child_root"])
    target = runner._safe_root(root)
    with runner._root_lock(target):
        child_loaded = runner._load_static(target)
        session = runner._load_session(target, child_loaded)
        item = _validate_original_child_binding(loaded, step, child_loaded, session, target)
        if not _terminal_artifacts_absent(target):
            raise IncompleteChildRestartError("original child has terminal artifacts and cannot be retried")
        snapshot = runner._stopped_snapshot(target, child_loaded, session)
        if snapshot.get("transport_state") != "INACTIVE_UNCHECKPOINTED":
            raise IncompleteChildRestartError("original child is not an inactive, unrecoverable transport")
        proof = snapshot.get("proof")
        if not isinstance(proof, dict) or proof.get("bytes", 0) <= 0:
            raise IncompleteChildRestartError("original stopped proof is empty, not a partial-proof retry")
        drat, stdout, stderr, _bound = runner._checker(
            target,
            child_loaded,
            role="drat-verify",
            proof_path=target / runner.RUNTIME_ROOT / "proof.drat",
            proof_record=proof,
            proof_cap=child_loaded["policy"]["proof_max_bytes"],
        )
        after = runner._stopped_snapshot(target, child_loaded, session)
        runner._require_snapshot_unchanged(snapshot, after)
        transcript = stdout + b"\n" + stderr
        if (
            drat.get("verified") is True
            or b"s NOT VERIFIED" not in transcript
            or b"no conflict" not in transcript.lower()
        ):
            raise IncompleteChildRestartError(
                "original proof is not the exact pinned no-conflict partial-proof condition"
            )
        return supervisor.seal(
            {
                "schema_version": SCHEMA_VERSION,
                "kind": FORENSIC_KIND,
                "gate": GATE,
                "bundle_sha256": loaded["bundle"]["bundle_sha256"],
                "initial_plan_sha256": loaded["plan"]["record_sha256"],
                "initial_commit_sha256": loaded["initial_commit"]["record_sha256"],
                "item_id": item["item_id"],
                "path": item["path"],
                "worker_sha256": worker["worker_sha256"],
                "claim_token": worker["token"],
                "worker_id": worker["worker_id"],
                "cpu_ids": list(worker["cpu_ids"]),
                "original_child_root": str(target),
                "original_root_identity": runner._root_identity(target),
                "original_static_sha256": child_loaded["static"]["static_sha256"],
                "original_session_sha256": session["record_sha256"],
                "original_transport_state": snapshot["transport_state"],
                "original_snapshot": snapshot,
                "drat_check": drat,
                "drat_stdout_sha256": hashlib.sha256(stdout).hexdigest(),
                "drat_stderr_sha256": hashlib.sha256(stderr).hexdigest(),
                "partial_diagnosis": PARTIAL_DIAGNOSIS,
                "terminal_artifacts_absent": True,
                "hardness_only": True,
                "solver_terminal_claim": False,
                "source_binding": _source_binding(),
            },
            "forensic_sha256",
        )


def _read_forensic(
    loaded: Mapping[str, Any], step: Mapping[str, Any], *, recheck_original: bool,
) -> dict[str, Any]:
    """Validate a persisted partial-proof receipt; optionally recheck its root."""

    bundle = Path(loaded["root"])
    path = _forensic_path(bundle, step)
    if path.is_symlink() or not path.exists():
        raise IncompleteChildRestartError("partial-proof forensic record is absent")
    value = supervisor._read_json(path)
    required = {
        "schema_version", "kind", "gate", "bundle_sha256", "initial_plan_sha256",
        "initial_commit_sha256", "item_id", "path", "worker_sha256", "claim_token",
        "worker_id", "cpu_ids", "original_child_root", "original_root_identity",
        "original_static_sha256", "original_session_sha256", "original_transport_state",
        "original_snapshot", "drat_check", "drat_stdout_sha256", "drat_stderr_sha256",
        "partial_diagnosis", "terminal_artifacts_absent", "hardness_only",
        "solver_terminal_claim", "source_binding", "forensic_sha256",
    }
    worker = step["worker"]
    item = _queue_item(step["after_queue"], step["item_id"])
    snapshot = value.get("original_snapshot")
    drat = value.get("drat_check")
    if (
        set(value) != required
        or not recursive.selfhash_valid(value, "forensic_sha256")
        or value.get("schema_version") != SCHEMA_VERSION
        or value.get("kind") != FORENSIC_KIND
        or value.get("gate") != GATE
        or value.get("bundle_sha256") != loaded["bundle"].get("bundle_sha256")
        or value.get("initial_plan_sha256") != loaded["plan"].get("record_sha256")
        or value.get("initial_commit_sha256") != loaded["initial_commit"].get("record_sha256")
        or value.get("item_id") != item.get("item_id")
        or value.get("path") != item.get("path")
        or value.get("worker_sha256") != worker.get("worker_sha256")
        or value.get("claim_token") != worker.get("token")
        or value.get("worker_id") != worker.get("worker_id")
        or value.get("cpu_ids") != worker.get("cpu_ids")
        or value.get("original_child_root") != worker.get("child_root")
        or value.get("original_transport_state") != "INACTIVE_UNCHECKPOINTED"
        or value.get("partial_diagnosis") != PARTIAL_DIAGNOSIS
        or value.get("terminal_artifacts_absent") is not True
        or value.get("hardness_only") is not True
        or value.get("solver_terminal_claim") is not False
        or value.get("source_binding") != _source_binding()
        or not isinstance(snapshot, dict)
        or not recursive.selfhash_valid(snapshot, "snapshot_sha256")
        or snapshot.get("transport_state") != "INACTIVE_UNCHECKPOINTED"
        or not isinstance(drat, dict)
        or drat.get("verified") is not False
        or not recursive.is_sha256(value.get("drat_stdout_sha256"))
        or not recursive.is_sha256(value.get("drat_stderr_sha256"))
    ):
        raise IncompleteChildRestartError("partial-proof forensic record is malformed")
    if recheck_original:
        runner = supervisor.child_runner
        root = runner._safe_root(Path(worker["child_root"]))
        with runner._root_lock(root, exclusive=False):
            child_loaded = runner._load_static(root)
            session = runner._load_session(root, child_loaded)
            _validate_original_child_binding(loaded, step, child_loaded, session, root)
            if (
                not _terminal_artifacts_absent(root)
                or runner._root_identity(root) != value.get("original_root_identity")
                or child_loaded["static"].get("static_sha256") != value.get("original_static_sha256")
                or session.get("record_sha256") != value.get("original_session_sha256")
            ):
                raise IncompleteChildRestartError("original child changed after the incomplete-proof forensic receipt")
            current = runner._stopped_snapshot(root, child_loaded, session)
            if current != snapshot:
                raise IncompleteChildRestartError("original stopped-proof snapshot changed after forensic receipt")
    return value


def _entry_value(loaded: Mapping[str, Any], step: Mapping[str, Any], forensic: Mapping[str, Any]) -> dict[str, Any]:
    bundle = Path(loaded["root"])
    worker = step["worker"]
    item = _queue_item(step["after_queue"], step["item_id"])
    return {
        "ordinal": step["ordinal"],
        "item_id": item["item_id"],
        "path": item["path"],
        "worker_sha256": worker["worker_sha256"],
        "claim_token": worker["token"],
        "worker_id": worker["worker_id"],
        "cpu_ids": list(worker["cpu_ids"]),
        "original_child_root": worker["child_root"],
        "original_session_sha256": forensic["original_session_sha256"],
        "forensic_sha256": forensic["forensic_sha256"],
        "retry_child_root": str(_retry_root(bundle, item["path"])),
    }


def _plan_value(
    loaded: Mapping[str, Any], *, item_ids: Sequence[str], forensics: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any]:
    queue = recursive.load_split_queue(Path(loaded["root"]) / supervisor.QUEUE)
    claimed = [item for item in queue["items"] if item.get("state") == "CLAIMED"]
    expected_ids = [item["item_id"] for item in claimed]
    requested = list(item_ids)
    if len(set(requested)) != len(requested) or set(requested) != set(expected_ids):
        raise IncompleteChildRestartError("restart must explicitly cover every and only currently claimed child")
    if queue != loaded["initial_final_queue"]:
        raise IncompleteChildRestartError("restart cannot begin after an unreviewed initial-batch queue mutation")
    ordered = [
        _entry_value(loaded, _step(loaded, item_id), forensics[item_id])
        for item_id in sorted(requested, key=lambda key: _step(loaded, key)["ordinal"])
    ]
    receipt = recovery._require_checkpoint_receipt(loaded)
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": PLAN_KIND,
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "root": str(loaded["root"]),
            "root_identity": supervisor._root_identity(Path(loaded["root"])),
            "initial_plan_sha256": loaded["plan"]["record_sha256"],
            "initial_commit_sha256": loaded["initial_commit"]["record_sha256"],
            "parent_checkpoint_sha256": receipt["record_sha256"],
            "queue_sha256_at_handoff": queue["queue_sha256"],
            "queue_event_sequence_at_handoff": queue["event_sequence"],
            "entries": ordered,
            "all_siblings_before_any_spawn": True,
            "persistent_service_required": True,
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _source_binding(),
        },
        "restart_plan_sha256",
    )


def _validate_entry(loaded: Mapping[str, Any], entry: Mapping[str, Any], *, ordinal: int) -> dict[str, Any]:
    required = {
        "ordinal", "item_id", "path", "worker_sha256", "claim_token", "worker_id",
        "cpu_ids", "original_child_root", "original_session_sha256", "forensic_sha256",
        "retry_child_root",
    }
    if set(entry) != required or entry.get("ordinal") != ordinal:
        raise IncompleteChildRestartError("restart plan entry is malformed")
    item_id = entry.get("item_id")
    if type(item_id) is not str:
        raise IncompleteChildRestartError("restart plan has an invalid item ID")
    step = _step(loaded, item_id)
    worker = step["worker"]
    item = _queue_item(step["after_queue"], item_id)
    bundle = Path(loaded["root"])
    forensic = _read_forensic(loaded, step, recheck_original=False)
    if (
        entry.get("path") != item.get("path")
        or entry.get("worker_sha256") != worker.get("worker_sha256")
        or entry.get("claim_token") != worker.get("token")
        or entry.get("worker_id") != worker.get("worker_id")
        or entry.get("cpu_ids") != worker.get("cpu_ids")
        or entry.get("original_child_root") != worker.get("child_root")
        or entry.get("original_session_sha256") != forensic.get("original_session_sha256")
        or entry.get("forensic_sha256") != forensic.get("forensic_sha256")
        or entry.get("retry_child_root") != str(_retry_root(bundle, item["path"]))
        or not recursive.is_sha256(entry.get("forensic_sha256"))
        or not recursive.is_sha256(entry.get("original_session_sha256"))
        or type(entry.get("cpu_ids")) is not list
        or len(entry["cpu_ids"]) != 1
        or type(entry["cpu_ids"][0]) is not int
    ):
        raise IncompleteChildRestartError("restart plan entry lost its exact worker/leaf binding")
    return dict(entry)


def _validate_plan(loaded: Mapping[str, Any], value: Mapping[str, Any]) -> dict[str, Any]:
    required = {
        "schema_version", "kind", "gate", "bundle_sha256", "root", "root_identity",
        "initial_plan_sha256", "initial_commit_sha256", "parent_checkpoint_sha256",
        "queue_sha256_at_handoff", "queue_event_sequence_at_handoff", "entries",
        "all_siblings_before_any_spawn", "persistent_service_required", "hardness_only",
        "solver_terminal_claim", "source_binding", "restart_plan_sha256",
    }
    bundle = Path(loaded["root"])
    receipt = recovery._require_checkpoint_receipt(loaded)
    if (
        set(value) != required
        or not recursive.selfhash_valid(value, "restart_plan_sha256")
        or value.get("schema_version") != SCHEMA_VERSION
        or value.get("kind") != PLAN_KIND
        or value.get("gate") != GATE
        or value.get("bundle_sha256") != loaded["bundle"].get("bundle_sha256")
        or value.get("root") != str(bundle)
        or not supervisor._same(value.get("root_identity"), supervisor._root_identity(bundle))
        or value.get("initial_plan_sha256") != loaded["plan"].get("record_sha256")
        or value.get("initial_commit_sha256") != loaded["initial_commit"].get("record_sha256")
        or value.get("parent_checkpoint_sha256") != receipt.get("record_sha256")
        or value.get("all_siblings_before_any_spawn") is not True
        or value.get("persistent_service_required") is not True
        or value.get("hardness_only") is not True
        or value.get("solver_terminal_claim") is not False
        or value.get("source_binding") != _source_binding()
        or not isinstance(value.get("entries"), list)
        or not value["entries"]
    ):
        raise IncompleteChildRestartError("restart plan is malformed")
    entries = [_validate_entry(loaded, entry, ordinal=index) for index, entry in enumerate(value["entries"])]
    expected = [item["item_id"] for item in loaded["initial_final_queue"]["items"]]
    if [entry["item_id"] for entry in entries] != expected:
        raise IncompleteChildRestartError("restart plan does not cover the immutable initial frontier")
    if (
        value.get("queue_sha256_at_handoff") != loaded["initial_final_queue"].get("queue_sha256")
        or value.get("queue_event_sequence_at_handoff") != loaded["initial_final_queue"].get("event_sequence")
    ):
        raise IncompleteChildRestartError("restart plan queue handoff binding is invalid")
    return dict(value)


def _commit_value(loaded: Mapping[str, Any], plan: Mapping[str, Any]) -> dict[str, Any]:
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": COMMIT_KIND,
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "restart_plan_sha256": plan["restart_plan_sha256"],
            "forensic_sha256s": [entry["forensic_sha256"] for entry in plan["entries"]],
            "all_siblings_before_any_spawn": True,
            "persistent_service_required": True,
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def _validate_commit(loaded: Mapping[str, Any], plan: Mapping[str, Any], value: Mapping[str, Any]) -> dict[str, Any]:
    expected = _commit_value(loaded, plan)
    if value != expected:
        raise IncompleteChildRestartError("restart commit is absent or does not replay its plan")
    return dict(value)


def _intent_value(plan: Mapping[str, Any], entry: Mapping[str, Any]) -> dict[str, Any]:
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": INTENT_KIND,
            "gate": GATE,
            "restart_plan_sha256": plan["restart_plan_sha256"],
            "item_id": entry["item_id"],
            "forensic_sha256": entry["forensic_sha256"],
            "retry_child_root": entry["retry_child_root"],
            "expected_single_cpu": entry["cpu_ids"][0],
            "all_siblings_before_any_spawn": True,
            "persistent_service_required": True,
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def _validate_retry_static(loaded: Mapping[str, Any], entry: Mapping[str, Any]) -> dict[str, Any]:
    runner = supervisor.child_runner
    target = runner._safe_root(Path(entry["retry_child_root"]))
    child_loaded = runner._load_static(target)
    item = _queue_item(loaded["initial_final_queue"], entry["item_id"])
    child = child_loaded.get("static", {}).get("child")
    if (
        not isinstance(child, dict)
        or child.get("leaf_id") != item.get("leaf_id")
        or child.get("leaf_sha256") != item.get("leaf_sha256")
        or child.get("child_cnf_sha256") != item.get("child_cnf_sha256")
        or child.get("child_dimacs_sha256") != item.get("child_dimacs_sha256")
        or child.get("child_num_variables") != item.get("child_num_variables")
        or child.get("child_num_clauses") != item.get("child_num_clauses")
        or child.get("child_dimacs_bytes") != item.get("child_dimacs_bytes")
        or child_loaded.get("manifest", {}).get("manifest_sha256")
        != loaded["manifest"].get("manifest_sha256")
        or child_loaded.get("audit", {}).get("audit_sha256") != loaded["audit"].get("audit_sha256")
    ):
        raise IncompleteChildRestartError("retry root no longer binds the original leaf material")
    return child_loaded


def _started_value(intent: Mapping[str, Any], session: Mapping[str, Any]) -> dict[str, Any]:
    if not recursive.is_sha256(session.get("record_sha256")):
        raise IncompleteChildRestartError("retry start did not return a sealed session")
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": STARTED_KIND,
            "gate": GATE,
            "intent_sha256": intent["record_sha256"],
            "retry_child_root": intent["retry_child_root"],
            "expected_single_cpu": intent["expected_single_cpu"],
            "retry_session_sha256": session["record_sha256"],
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def _read_started(
    loaded: Mapping[str, Any], plan: Mapping[str, Any], entry: Mapping[str, Any],
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    """Replay a retry intent, sealed session, and started receipt exactly."""

    bundle = Path(loaded["root"])
    intent_path, started_path = _start_paths(bundle, entry)
    if any(path.is_symlink() or not path.exists() for path in (intent_path, started_path)):
        raise IncompleteChildRestartError("retry start intent or receipt is absent")
    intent = supervisor._read_json(intent_path)
    expected_intent = _intent_value(plan, entry)
    if intent != expected_intent:
        raise IncompleteChildRestartError("retry start intent changed")
    runner = supervisor.child_runner
    root = runner._safe_root(Path(entry["retry_child_root"]))
    with runner._root_lock(root, exclusive=False):
        child_loaded = _validate_retry_static(loaded, entry)
        session = runner._load_session(root, child_loaded)
        if session.get("expected_single_cpu") != entry["cpu_ids"][0]:
            raise IncompleteChildRestartError("retry session CPU differs from the retained lease")
        expected_started = _started_value(intent, session)
    started = supervisor._read_json(started_path)
    if started != expected_started:
        raise IncompleteChildRestartError("retry started receipt changed")
    return intent, started, session


def _load_restart(
    loaded: Mapping[str, Any], *, require_started: bool, recheck_original: bool,
) -> dict[str, Any]:
    bundle = Path(loaded["root"])
    _sidecar(bundle, SIDECAR_DIR)
    plan_path = bundle / PLAN
    commit_path = bundle / COMMIT
    if any(path.is_symlink() or not path.exists() for path in (plan_path, commit_path)):
        raise IncompleteChildRestartError("restart plan or commit is absent")
    plan = _validate_plan(loaded, supervisor._read_json(plan_path))
    commit = _validate_commit(loaded, plan, supervisor._read_json(commit_path))
    entries: list[dict[str, Any]] = []
    for entry in plan["entries"]:
        step = _step(loaded, entry["item_id"])
        forensic = _read_forensic(loaded, step, recheck_original=recheck_original)
        if forensic["forensic_sha256"] != entry["forensic_sha256"]:
            raise IncompleteChildRestartError("restart entry forensic binding changed")
        evidence: dict[str, Any] = {"entry": dict(entry), "forensic": forensic}
        if require_started:
            intent, started, session = _read_started(loaded, plan, entry)
            evidence.update({"intent": intent, "started": started, "session": session})
        entries.append(evidence)
    return {"plan": plan, "commit": commit, "entries": entries}


# Public to the lifecycle sidecar.  Keeping this name stable makes the
# handoff source explicit in its own source binding.
load_restart = _load_restart


def _ensure_plan(
    loaded: Mapping[str, Any], *, item_ids: Sequence[str],
) -> tuple[dict[str, Any], dict[str, Any]]:
    bundle = Path(loaded["root"])
    plan_path = bundle / PLAN
    if plan_path.exists() or plan_path.is_symlink():
        plan = _validate_plan(loaded, supervisor._read_json(plan_path))
        if set(item_ids) != {entry["item_id"] for entry in plan["entries"]}:
            raise IncompleteChildRestartError("existing restart plan covers a different child set")
    else:
        forensics: dict[str, Mapping[str, Any]] = {}
        for item_id in item_ids:
            step = _step(loaded, item_id)
            forensic = _partial_forensic_value(loaded, step)
            _publish_exact(_forensic_path(bundle, step), forensic, label="partial-proof forensic receipt")
            forensics[item_id] = _read_forensic(loaded, step, recheck_original=True)
        plan = _plan_value(loaded, item_ids=item_ids, forensics=forensics)
        _publish_exact(plan_path, plan, label="restart plan")
    commit = _commit_value(loaded, plan)
    _publish_exact(bundle / COMMIT, commit, label="restart commit")
    return plan, commit


def _prepare_or_validate_retry_root(loaded: Mapping[str, Any], entry: Mapping[str, Any]) -> bool:
    """Return true only when this entry still needs a new external start."""

    runner = supervisor.child_runner
    root = Path(entry["retry_child_root"])
    if root.exists() or root.is_symlink():
        if root.is_symlink():
            raise IncompleteChildRestartError("retry root is a symlink")
        with runner._root_lock(runner._safe_root(root)):
            child_loaded = _validate_retry_static(loaded, entry)
            if (root / runner.SESSION_COMMIT).exists() or (root / runner.SESSION_COMMIT).is_symlink():
                # A durable session plus a missing receipt is an interrupted
                # publisher, not a reason to spawn a second solver.
                runner._load_session(root, child_loaded)
                return False
            if (root / runner.START_CLAIM).exists() or (root / runner.START_CLAIM).is_symlink():
                raise IncompleteChildRestartError("retry root has an unsealed start claim and needs manual audit")
            if (root / runner.RUNTIME_ROOT).exists() or (root / runner.RUNTIME_ROOT).is_symlink():
                raise IncompleteChildRestartError("retry root has unresolved transport state")
            return True
    runner.prepare_root_from_material(
        root,
        parent_dimacs=loaded["parent"],
        split_manifest=loaded["manifest"],
        leaf_path=entry["path"],
        parent_audit=loaded["audit"],
    )
    return True


def _dispatch_all(loaded: Mapping[str, Any], plan: Mapping[str, Any]) -> list[dict[str, Any]]:
    """Publish every retry intent, prepare every root, then spawn every sibling."""

    bundle = Path(loaded["root"])
    entries = list(plan["entries"])
    pending: list[dict[str, Any]] = []
    results: list[dict[str, Any]] = []
    # No materialisation or process start is allowed until every durable intent
    # exists.  This is the all-sibling barrier that the original service lacked.
    for entry in entries:
        intent, started_path = _start_paths(bundle, entry)
        _publish_exact(intent, _intent_value(plan, entry), label="retry start intent")
        if started_path.exists() or started_path.is_symlink():
            _read_started(loaded, plan, entry)
            results.append({"item_id": entry["item_id"], "state": "ALREADY_SEALED"})
        else:
            pending.append(dict(entry))
    launches: list[dict[str, Any]] = []
    for entry in pending:
        if _prepare_or_validate_retry_root(loaded, entry):
            launches.append(entry)
        else:
            intent, started_path = _start_paths(bundle, entry)
            runner = supervisor.child_runner
            root = runner._safe_root(Path(entry["retry_child_root"]))
            with runner._root_lock(root, exclusive=False):
                session = runner._load_session(root, _validate_retry_static(loaded, entry))
                _publish_exact(started_path, _started_value(supervisor._read_json(intent), session), label="retry started receipt")
            results.append({"item_id": entry["item_id"], "state": "RECOVERED_STARTED_RECEIPT"})
    processes: list[tuple[dict[str, Any], Any]] = []
    failures: list[str] = []
    # Deliberately issue all Popen calls before observing the first outcome.
    for entry in launches:
        try:
            process = batch._spawn_child_start(Path(entry["retry_child_root"]), cpu=entry["cpu_ids"][0])
            processes.append((entry, process))
        except BaseException as exc:
            failures.append(f"{entry['item_id']}: {type(exc).__name__}: {exc}")
    for entry, process in processes:
        try:
            _stdout, stderr = process.communicate()
            returncode = process.returncode
            if type(returncode) is not int:
                raise IncompleteChildRestartError("retry start process has no exit status")
            if returncode != 0:
                raise IncompleteChildRestartError(batch._external_start_error(returncode, stderr or b""))
            intent_path, started_path = _start_paths(bundle, entry)
            intent = supervisor._read_json(intent_path)
            runner = supervisor.child_runner
            root = runner._safe_root(Path(entry["retry_child_root"]))
            with runner._root_lock(root, exclusive=False):
                session = runner._load_session(root, _validate_retry_static(loaded, entry))
                _publish_exact(started_path, _started_value(intent, session), label="retry started receipt")
            results.append({
                "item_id": entry["item_id"],
                "state": "RUNNING",
                "started_sha256": _started_value(intent, session)["record_sha256"],
            })
        except BaseException as exc:
            failures.append(f"{entry['item_id']}: {type(exc).__name__}: {exc}")
    if failures:
        raise IncompleteChildRestartError(
            "one or more retry starts require forensic audit after every sibling was attempted: "
            + " | ".join(failures)
        )
    return sorted(results, key=lambda value: value["item_id"])


def dispatch_restart(
    bundle: Path, *, item_ids: Sequence[str], control_root: Path = supervisor.CONTROL_ROOT,
) -> dict[str, Any]:
    """Create a sealed retry plan and concurrently start all selected siblings."""

    target = Path(bundle)
    if not item_ids:
        raise IncompleteChildRestartError("restart requires at least one explicit item ID")
    with initial._dispatch_lock(target):
        with _restart_lock(target):
            loaded = base._load_initial_batch(target, control_root=control_root)
            receipt = recovery._require_checkpoint_receipt(loaded)
            parent_root = Path(loaded["audit"]["parent_root"])
            with recovery._legacy_shared_lock(parent_root):
                _observation, checkpoint_chain = recovery._checked_checkpointed_parent(loaded)
                with supervisor._catalog_lock(Path(loaded["control_root"])):
                    recovery._require_reserved_cpu_leases(loaded)
                plan, commit = _ensure_plan(loaded, item_ids=item_ids)
                # Recheck the original immutable partial-proof evidence after
                # plan publication and immediately before any retry root exists.
                restart = _load_restart(loaded, require_started=False, recheck_original=True)
                if restart["plan"] != plan or restart["commit"] != commit:
                    raise IncompleteChildRestartError("restart plan changed during its own replay")
                children = _dispatch_all(loaded, plan)
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": RESULT_KIND,
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "restart_plan_sha256": plan["restart_plan_sha256"],
            "restart_commit_sha256": commit["record_sha256"],
            "parent_checkpoint_sha256": receipt["record_sha256"],
            "checkpoint_manifest_sha256": checkpoint_chain["latest_checkpoint_sha256"],
            "children": children,
            "all_siblings_before_any_spawn": True,
            "persistent_service_required": True,
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--control-root", type=Path, default=supervisor.CONTROL_ROOT)
    sub = parser.add_subparsers(dest="action", required=True)
    recover = sub.add_parser("recover", allow_abbrev=False)
    recover.add_argument("--bundle", type=Path, required=True)
    recover.add_argument("--item-id", action="append", required=True)
    recover.add_argument(
        "--keep-alive",
        action="store_true",
        help="keep the systemd service cgroup alive after all siblings are dispatched",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    result = dispatch_restart(args.bundle, item_ids=args.item_id, control_root=args.control_root)
    sys.stdout.buffer.write(supervisor.canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    if args.keep_alive:
        # The unit's default KillMode=control-group is intentionally safe only
        # while this keeper remains alive.  It never observes or controls the
        # children after dispatch; lifecycle proof work is separate.
        while True:
            time.sleep(3600)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        IncompleteChildRestartError,
        base.InitialBatchLifecycleError,
        initial.InitialBatchDispatchError,
        batch.BatchDispatchError,
        recovery.RecursiveCheckpointRecoveryError,
        supervisor.RecursiveSplitSupervisorError,
        supervisor.child_runner.RecursiveChildRunnerError,
        recursive.RecursiveSplitError,
        OSError,
        ValueError,
        TypeError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
