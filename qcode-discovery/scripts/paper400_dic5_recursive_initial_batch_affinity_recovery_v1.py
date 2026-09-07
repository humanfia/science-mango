#!/usr/bin/env python3
"""Recover an all-sibling initial batch stranded by inherited CPU affinity.

The frozen initial-batch dispatcher deliberately makes every claim and start
intent durable before it launches a child.  If its *own* process is pinned to
a CPU outside the reserved child CPUs, however, each frozen child runner can
publish its immutable start claim and then fail before controller
initialisation.  The original orphan receipts must be retained, but they are
not fast-terminal proof receipts and therefore cannot be fed to the normal
proof-recovery path.

This sidecar admits only that exact, fully pre-controller state.  It requires
every sibling in an already-committed initial batch to carry the exact
``requested CPU is outside current affinity`` orphan, with no DMTCP runtime,
session, proof, or terminal material.  It records one immutable recovery plan
and every start intent before it invokes any child.  All child ``Popen`` calls
occur before any result is observed.  A completed recovery never changes a
queue claim, lease, parent checkpoint, or the original forensic orphan.

It is deliberately not a generic retry mechanism.  Any evidence of a partly
started controller, a different error, or an incomplete all-sibling recovery
is an audit stop.
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
from scripts import paper400_dic5_recursive_initial_batch_dispatch_v1 as initial
from scripts import paper400_dic5_recursive_initial_batch_lifecycle_v1 as lifecycle
from scripts import paper400_dic5_recursive_postbootstrap_batch_dispatch_v1 as batch
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


SCHEMA_VERSION = 1
GATE = "paper400-dic5-recursive-initial-batch-affinity-recovery-v1"
SIDECAR_DIR = Path("initial-batch-affinity-recovery-v1")
PLAN = SIDECAR_DIR / "000000-plan.json"
COMPLETE = SIDECAR_DIR / "000001-complete.json"
STARTS_DIR = SIDECAR_DIR / "starts"
PLAN_KIND = "paper400-dic5-recursive-initial-batch-affinity-recovery-plan-v1"
INTENT_KIND = "paper400-dic5-recursive-initial-batch-affinity-recovery-intent-v1"
STARTED_KIND = "paper400-dic5-recursive-initial-batch-affinity-recovery-started-v1"
COMPLETE_KIND = "paper400-dic5-recursive-initial-batch-affinity-recovery-complete-v1"
FAILURE_KIND = "paper400-dic5-recursive-initial-batch-affinity-recovery-failure-v1"

# This is intentionally byte-for-byte the diagnostic emitted by the frozen
# child runner when its caller's affinity mask excludes the child CPU.
AFFINITY_START_ERROR = (
    "external child start failed rc=2: ERROR: requested CPU is outside current affinity"
)


class InitialBatchAffinityRecoveryError(RuntimeError):
    """The exact no-controller affinity-recovery boundary was not present."""


def _source_binding() -> dict[str, Any]:
    source = Path(__file__).resolve(strict=True)
    payload = supervisor._stable_bytes(source, cap=32 << 20, executable=False)
    return {
        "method": "exact-source-sha256-replay-v1",
        "affinity_recovery_script": {
            "path": str(source),
            "sha256": hashlib.sha256(payload).hexdigest(),
        },
        "initial_batch_dispatch": initial._source_binding(),
        "batch_dispatch": batch._source_binding(),
        "checkpoint_recovery": recovery._script_binding(),
    }


def _safe_sidecar_dir(bundle: Path, relative: Path = SIDECAR_DIR) -> Path:
    try:
        return batch._safe_sidecar_dir(bundle, relative)
    except batch.BatchDispatchError as exc:
        raise InitialBatchAffinityRecoveryError("affinity recovery sidecar is unsafe") from exc


def _publish_exact(path: Path, value: Mapping[str, Any], *, label: str) -> None:
    if path.exists() or path.is_symlink():
        if path.is_symlink() or supervisor._read_json(path) != value:
            raise InitialBatchAffinityRecoveryError(f"existing {label} conflicts with replay")
        return
    supervisor._publish_json(path, value)


def _step_for_item(loaded: Mapping[str, Any], item_id: str) -> dict[str, Any]:
    steps = [
        step for step in loaded["plan"]["steps"]
        if isinstance(step, dict) and step.get("item_id") == item_id
    ]
    if len(steps) != 1:
        raise InitialBatchAffinityRecoveryError("initial recovery plan has no unique item step")
    return dict(steps[0])


def _orphan_path(bundle: Path, step: Mapping[str, Any]) -> Path:
    worker = step["worker"]
    return (bundle / supervisor.WORKERS_DIR / step["worker_filename"]).with_name(
        (bundle / supervisor.WORKERS_DIR / step["worker_filename"]).stem + ".orphan.json"
    )


def _require_exact_affinity_orphan(
    loaded: Mapping[str, Any], *, step: Mapping[str, Any], item: Mapping[str, Any], worker: Mapping[str, Any],
) -> dict[str, Any]:
    """Replay a frozen initial orphan, then restrict it to this one failure."""

    try:
        present = initial._existing_initial_orphan(
            loaded, item_id=str(item["item_id"]), worker=worker,
        )
    except initial.InitialBatchDispatchError as exc:
        raise InitialBatchAffinityRecoveryError("initial orphan is not bound to its immutable claim") from exc
    if not present:
        raise InitialBatchAffinityRecoveryError("initial child has no affinity-failure orphan receipt")
    path = _orphan_path(Path(loaded["root"]), step)
    if path.is_symlink() or not path.exists():
        raise InitialBatchAffinityRecoveryError("affinity-failure orphan path is unsafe")
    orphan = supervisor._read_json(path)
    if (
        not recursive.selfhash_valid(orphan, "worker_sha256")
        or orphan.get("error") != AFFINITY_START_ERROR
    ):
        raise InitialBatchAffinityRecoveryError("initial orphan is not the exact affinity failure")
    return orphan


def _require_precontroller_layout(root: Path) -> None:
    """Prove that the failed start stopped before controller initialisation."""

    runner = supervisor.child_runner
    expected_root_entries = {
        Path(runner.ROOT_LOCK).name, "static", "state", "artifacts", "runtime", "logs",
    }
    try:
        actual_root_entries = {path.name for path in root.iterdir()}
    except OSError as exc:
        raise InitialBatchAffinityRecoveryError("cannot inspect failed child root") from exc
    if actual_root_entries != expected_root_entries:
        raise InitialBatchAffinityRecoveryError("failed child root has unexpected material evidence")
    for name in ("artifacts", "runtime", "logs"):
        directory = root / name
        if directory.is_symlink() or not directory.is_dir() or any(directory.iterdir()):
            raise InitialBatchAffinityRecoveryError("failed child has controller-side evidence")
    state = root / "state"
    if state.is_symlink() or not state.is_dir() or {path.name for path in state.iterdir()} != {
        "00-recursive-static.json", "05-start.claim.json",
    }:
        raise InitialBatchAffinityRecoveryError("failed child state is not pre-controller")
    for relative in (
        runner.RUNTIME_ROOT, runner.SESSION_COMMIT, runner.TERMINAL_CLAIM,
        runner.CERTIFICATE, runner.VALIDATION, runner.FINAL_COMMIT,
    ):
        path = root / relative
        if path.exists() or path.is_symlink():
            raise InitialBatchAffinityRecoveryError("failed child has runtime, proof, or terminal evidence")


def _child_context(
    loaded: Mapping[str, Any], *, step: Mapping[str, Any], require_live_claim: bool,
    require_precontroller: bool,
) -> dict[str, Any]:
    """Bind one initial plan step to its root, orphan, and immutable claim."""

    try:
        item, worker, root = lifecycle._worker_for_item(
            loaded, loaded["queue"], str(step["item_id"]), require_live_claim=require_live_claim,
        )
    except lifecycle.InitialBatchLifecycleError as exc:
        raise InitialBatchAffinityRecoveryError("initial worker no longer binds its queue item") from exc
    if worker != step.get("worker") or root != Path(step["worker"]["child_root"]):
        raise InitialBatchAffinityRecoveryError("initial worker differs from immutable plan")
    if root.is_symlink():
        raise InitialBatchAffinityRecoveryError("failed child root is a symlink")
    runner = supervisor.child_runner
    target = runner._safe_root(root)
    child_loaded = runner._load_static(target)
    claim = runner._read_start_claim(target, child_loaded)
    cpu_ids = item.get("cpu_ids")
    if (
        not isinstance(cpu_ids, list) or len(cpu_ids) != 1 or type(cpu_ids[0]) is not int
        or claim.get("expected_single_cpu") != cpu_ids[0]
        or claim.get("leaf_id") != item.get("leaf_id")
        or claim.get("leaf_sha256") != item.get("leaf_sha256")
        or child_loaded["static"].get("static_sha256") != claim.get("static_sha256")
    ):
        raise InitialBatchAffinityRecoveryError("failed child start claim lost its queue binding")
    orphan = _require_exact_affinity_orphan(loaded, step=step, item=item, worker=worker)
    if require_precontroller:
        _require_precontroller_layout(target)
    return {
        "ordinal": step["ordinal"],
        "item_id": item["item_id"],
        "leaf_id": item["leaf_id"],
        "leaf_sha256": item["leaf_sha256"],
        "worker_sha256": worker["worker_sha256"],
        "orphan_sha256": orphan["worker_sha256"],
        "child_root": str(target),
        "static_sha256": child_loaded["static"]["static_sha256"],
        "start_claim_sha256": claim["record_sha256"],
        "expected_single_cpu": cpu_ids[0],
        "policy": child_loaded["policy"],
    }


def _entry_without_policy(context: Mapping[str, Any], *, admission: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "ordinal": context["ordinal"],
        "item_id": context["item_id"],
        "leaf_id": context["leaf_id"],
        "leaf_sha256": context["leaf_sha256"],
        "worker_sha256": context["worker_sha256"],
        "orphan_sha256": context["orphan_sha256"],
        "child_root": context["child_root"],
        "static_sha256": context["static_sha256"],
        "start_claim_sha256": context["start_claim_sha256"],
        "expected_single_cpu": context["expected_single_cpu"],
        "admission": dict(admission),
    }


def _plan_value(
    loaded: Mapping[str, Any], receipt: Mapping[str, Any], contexts: list[Mapping[str, Any]],
) -> dict[str, Any]:
    entries: list[dict[str, Any]] = []
    for context in contexts:
        root = Path(context["child_root"])
        admission = supervisor.child_runner._resource_admission(root, context["policy"])
        entries.append(_entry_without_policy(context, admission=admission))
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": PLAN_KIND,
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "initial_plan_sha256": loaded["plan"]["record_sha256"],
            "initial_commit_sha256": loaded["initial_commit"]["record_sha256"],
            "parent_checkpoint_sha256": receipt["record_sha256"],
            "affinity_start_error": AFFINITY_START_ERROR,
            "entries": entries,
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def _validate_plan(loaded: Mapping[str, Any], receipt: Mapping[str, Any], value: Mapping[str, Any]) -> dict[str, Any]:
    fields = {
        "schema_version", "kind", "gate", "bundle_sha256", "initial_plan_sha256",
        "initial_commit_sha256", "parent_checkpoint_sha256", "affinity_start_error", "entries",
        "hardness_only", "solver_terminal_claim", "source_binding", "record_sha256",
    }
    if (
        set(value) != fields or not recursive.selfhash_valid(value, "record_sha256")
        or value.get("schema_version") != SCHEMA_VERSION or value.get("kind") != PLAN_KIND
        or value.get("gate") != GATE
        or value.get("bundle_sha256") != loaded["bundle"].get("bundle_sha256")
        or value.get("initial_plan_sha256") != loaded["plan"].get("record_sha256")
        or value.get("initial_commit_sha256") != loaded["initial_commit"].get("record_sha256")
        or value.get("parent_checkpoint_sha256") != receipt.get("record_sha256")
        or value.get("affinity_start_error") != AFFINITY_START_ERROR
        or value.get("hardness_only") is not True or value.get("solver_terminal_claim") is not False
        or value.get("source_binding") != _source_binding()
        or not isinstance(value.get("entries"), list)
        or len(value["entries"]) != len(loaded["plan"]["steps"])
    ):
        raise InitialBatchAffinityRecoveryError("affinity recovery plan is malformed")
    expected_fields = {
        "ordinal", "item_id", "leaf_id", "leaf_sha256", "worker_sha256", "orphan_sha256",
        "child_root", "static_sha256", "start_claim_sha256", "expected_single_cpu", "admission",
    }
    for ordinal, entry in enumerate(value["entries"]):
        if not isinstance(entry, dict) or set(entry) != expected_fields:
            raise InitialBatchAffinityRecoveryError("affinity recovery plan entry is malformed")
        step = _step_for_item(loaded, str(entry.get("item_id")))
        if step.get("ordinal") != ordinal or entry.get("ordinal") != ordinal:
            raise InitialBatchAffinityRecoveryError("affinity recovery plan order changed")
        context = _child_context(
            loaded, step=step, require_live_claim=False, require_precontroller=False,
        )
        expected = _entry_without_policy(context, admission=entry["admission"])
        if entry != expected or not supervisor.child_runner._validate_resource_admission(
            entry["admission"], context["policy"],
        ):
            raise InitialBatchAffinityRecoveryError("affinity recovery plan no longer replays its child")
    return dict(value)


def _start_paths(bundle: Path, entry: Mapping[str, Any]) -> tuple[Path, Path, Path]:
    key = f"{entry['ordinal']:04d}-{str(entry['orphan_sha256'])[:16]}"
    starts = _safe_sidecar_dir(bundle, STARTS_DIR)
    return (
        starts / f"{key}.intent.json",
        starts / f"{key}.started.json",
        starts / f"{key}.failure.json",
    )


def _intent_value(plan: Mapping[str, Any], entry: Mapping[str, Any]) -> dict[str, Any]:
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": INTENT_KIND,
            "gate": GATE,
            "plan_sha256": plan["record_sha256"],
            "ordinal": entry["ordinal"],
            "item_id": entry["item_id"],
            "worker_sha256": entry["worker_sha256"],
            "orphan_sha256": entry["orphan_sha256"],
            "child_root": entry["child_root"],
            "static_sha256": entry["static_sha256"],
            "start_claim_sha256": entry["start_claim_sha256"],
            "expected_single_cpu": entry["expected_single_cpu"],
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def _started_value(intent: Mapping[str, Any], session: Mapping[str, Any]) -> dict[str, Any]:
    session_sha = session.get("record_sha256")
    if not recursive.is_sha256(session_sha):
        raise InitialBatchAffinityRecoveryError("recovered child did not provide a sealed session")
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": STARTED_KIND,
            "gate": GATE,
            "intent_sha256": intent["record_sha256"],
            "child_root": intent["child_root"],
            "expected_single_cpu": intent["expected_single_cpu"],
            "session_sha256": session_sha,
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def _validate_started(
    loaded: Mapping[str, Any], plan: Mapping[str, Any], entry: Mapping[str, Any],
    intent: Mapping[str, Any], value: Mapping[str, Any],
) -> dict[str, Any]:
    expected_intent = _intent_value(plan, entry)
    fields = {
        "schema_version", "kind", "gate", "intent_sha256", "child_root", "expected_single_cpu",
        "session_sha256", "hardness_only", "solver_terminal_claim", "source_binding", "record_sha256",
    }
    if (
        intent != expected_intent or set(value) != fields
        or not recursive.selfhash_valid(value, "record_sha256")
        or value.get("schema_version") != SCHEMA_VERSION or value.get("kind") != STARTED_KIND
        or value.get("gate") != GATE or value.get("intent_sha256") != intent.get("record_sha256")
        or value.get("child_root") != entry.get("child_root")
        or value.get("expected_single_cpu") != entry.get("expected_single_cpu")
        or value.get("hardness_only") is not True or value.get("solver_terminal_claim") is not False
        or value.get("source_binding") != _source_binding()
        or not recursive.is_sha256(value.get("session_sha256"))
    ):
        raise InitialBatchAffinityRecoveryError("recovered child start receipt is malformed")
    session = batch._sealed_session_after_external_start(Path(entry["child_root"]))
    if (
        session.get("record_sha256") != value.get("session_sha256")
        or session.get("expected_single_cpu") != entry.get("expected_single_cpu")
    ):
        raise InitialBatchAffinityRecoveryError("recovered child session no longer matches its receipt")
    return dict(value)


def _failure_value(intent: Mapping[str, Any], *, error: str) -> dict[str, Any]:
    if not error or len(error) > 4096:
        raise InitialBatchAffinityRecoveryError("recovery start error is unsafe")
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": FAILURE_KIND,
            "gate": GATE,
            "intent_sha256": intent["record_sha256"],
            "child_root": intent["child_root"],
            "expected_single_cpu": intent["expected_single_cpu"],
            "error": error,
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def _require_affinity(entries: list[Mapping[str, Any]]) -> None:
    allowed = os.sched_getaffinity(0)
    requested = {entry["expected_single_cpu"] for entry in entries}
    if len(requested) != len(entries) or not requested.issubset(allowed):
        raise InitialBatchAffinityRecoveryError(
            "recovery process affinity excludes one or more reserved child CPUs"
        )


def _launch_all(loaded: Mapping[str, Any], plan: Mapping[str, Any]) -> list[dict[str, Any]]:
    """Publish all intents, issue all starts, then observe all results."""

    bundle = Path(loaded["root"])
    entries = list(plan["entries"])
    _require_affinity(entries)
    pending: list[tuple[dict[str, Any], dict[str, Any], Path, Path, Path]] = []
    started: list[dict[str, Any]] = []
    for entry in entries:
        step = _step_for_item(loaded, str(entry["item_id"]))
        # A queued child must still be claimed immediately before a material
        # action.  This also replays the original orphan and static bindings.
        context = _child_context(
            loaded, step=step, require_live_claim=True, require_precontroller=False,
        )
        if any(
            context[key] != entry[key]
            for key in (
                "ordinal", "item_id", "leaf_id", "leaf_sha256", "worker_sha256", "orphan_sha256",
                "child_root", "static_sha256", "start_claim_sha256", "expected_single_cpu",
            )
        ):
            raise InitialBatchAffinityRecoveryError("recovery child changed after plan publication")
        intent_path, started_path, failure_path = _start_paths(bundle, entry)
        intent = _intent_value(plan, entry)
        _publish_exact(intent_path, intent, label="affinity recovery start intent")
        if failure_path.exists() or failure_path.is_symlink():
            raise InitialBatchAffinityRecoveryError("prior affinity recovery start failed and needs audit")
        if started_path.exists() or started_path.is_symlink():
            if started_path.is_symlink():
                raise InitialBatchAffinityRecoveryError("recovered child start receipt is unsafe")
            started.append(_validate_started(
                loaded, plan, entry, intent, supervisor._read_json(started_path),
            ))
            continue
        root = Path(entry["child_root"])
        session_path = root / supervisor.child_runner.SESSION_COMMIT
        if session_path.exists() or session_path.is_symlink():
            if session_path.is_symlink():
                raise InitialBatchAffinityRecoveryError("recovered child session path is unsafe")
            session = batch._sealed_session_after_external_start(root)
            receipt = _started_value(intent, session)
            _publish_exact(started_path, receipt, label="recovered child start receipt")
            started.append(receipt)
            continue
        # A second attempt is allowed only if no controller-side artifact has
        # appeared since the immutable affinity-failure orphan.
        _require_precontroller_layout(root)
        supervisor.child_runner._resource_admission(root, context["policy"])
        pending.append((entry, intent, started_path, failure_path, root))

    processes: list[tuple[dict[str, Any], dict[str, Any], Path, Path, Any]] = []
    for entry, intent, started_path, failure_path, root in pending:
        try:
            process = batch._spawn_child_start(root, cpu=entry["expected_single_cpu"])
        except BaseException as exc:
            error = f"{type(exc).__name__}: {exc}"
            _publish_exact(failure_path, _failure_value(intent, error=error), label="affinity recovery failure")
        else:
            processes.append((entry, intent, started_path, failure_path, process))

    failures: list[str] = []
    for entry, intent, started_path, failure_path, process in processes:
        try:
            _stdout, stderr = process.communicate()
            returncode = process.returncode
            if type(returncode) is not int:
                raise InitialBatchAffinityRecoveryError("recovery child start process has no exit status")
            if returncode != 0:
                raise InitialBatchAffinityRecoveryError(batch._external_start_error(returncode, stderr or b""))
            session = batch._sealed_session_after_external_start(Path(entry["child_root"]))
            receipt = _started_value(intent, session)
            _publish_exact(started_path, receipt, label="recovered child start receipt")
            started.append(receipt)
        except BaseException as exc:
            error = f"{type(exc).__name__}: {exc}"
            _publish_exact(failure_path, _failure_value(intent, error=error), label="affinity recovery failure")
            failures.append(str(entry["item_id"]))
    if failures:
        raise InitialBatchAffinityRecoveryError(
            "one or more affinity-recovery child starts need audit after all siblings were attempted: "
            + ",".join(failures)
        )
    if len(started) != len(entries):
        raise InitialBatchAffinityRecoveryError("affinity recovery did not seal every sibling start")
    return sorted(started, key=lambda value: value["expected_single_cpu"])


def _complete_value(plan: Mapping[str, Any], started: list[Mapping[str, Any]]) -> dict[str, Any]:
    by_cpu = {value["expected_single_cpu"]: value for value in started}
    if len(by_cpu) != len(plan["entries"]):
        raise InitialBatchAffinityRecoveryError("affinity recovery started receipts are ambiguous")
    ordered = [by_cpu[entry["expected_single_cpu"]] for entry in plan["entries"]]
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": COMPLETE_KIND,
            "gate": GATE,
            "plan_sha256": plan["record_sha256"],
            "item_ids": [entry["item_id"] for entry in plan["entries"]],
            "orphan_sha256s": [entry["orphan_sha256"] for entry in plan["entries"]],
            "started_sha256s": [value["record_sha256"] for value in ordered],
            "all_siblings_started": True,
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def _load_complete(loaded: Mapping[str, Any], receipt: Mapping[str, Any]) -> tuple[dict[str, Any], dict[str, Any]] | None:
    bundle = Path(loaded["root"])
    plan_path = bundle / PLAN
    complete_path = bundle / COMPLETE
    if not plan_path.exists() and not plan_path.is_symlink() and not complete_path.exists() and not complete_path.is_symlink():
        return None
    if (
        plan_path.is_symlink() or complete_path.is_symlink()
        or not plan_path.exists() or not complete_path.exists()
    ):
        raise InitialBatchAffinityRecoveryError("affinity recovery sidecar is incomplete or unsafe")
    plan = _validate_plan(loaded, receipt, supervisor._read_json(plan_path))
    complete = supervisor._read_json(complete_path)
    fields = {
        "schema_version", "kind", "gate", "plan_sha256", "item_ids", "orphan_sha256s",
        "started_sha256s", "all_siblings_started", "hardness_only", "solver_terminal_claim",
        "source_binding", "record_sha256",
    }
    if (
        set(complete) != fields or not recursive.selfhash_valid(complete, "record_sha256")
        or complete.get("schema_version") != SCHEMA_VERSION or complete.get("kind") != COMPLETE_KIND
        or complete.get("gate") != GATE or complete.get("plan_sha256") != plan.get("record_sha256")
        or complete.get("item_ids") != [entry["item_id"] for entry in plan["entries"]]
        or complete.get("orphan_sha256s") != [entry["orphan_sha256"] for entry in plan["entries"]]
        or complete.get("all_siblings_started") is not True
        or complete.get("hardness_only") is not True or complete.get("solver_terminal_claim") is not False
        or complete.get("source_binding") != _source_binding()
        or not isinstance(complete.get("started_sha256s"), list)
        or len(complete["started_sha256s"]) != len(plan["entries"])
    ):
        raise InitialBatchAffinityRecoveryError("affinity recovery completion is malformed")
    observed: list[str] = []
    for entry in plan["entries"]:
        intent_path, started_path, failure_path = _start_paths(bundle, entry)
        if failure_path.exists() or failure_path.is_symlink() or intent_path.is_symlink() or started_path.is_symlink():
            raise InitialBatchAffinityRecoveryError("affinity recovery start evidence is unsafe")
        if not intent_path.exists() or not started_path.exists():
            raise InitialBatchAffinityRecoveryError("affinity recovery start evidence is incomplete")
        started = _validate_started(
            loaded, plan, entry, supervisor._read_json(intent_path), supervisor._read_json(started_path),
        )
        observed.append(started["record_sha256"])
    if observed != complete["started_sha256s"]:
        raise InitialBatchAffinityRecoveryError("affinity recovery completion does not bind every session")
    return plan, dict(complete)


def completed_recovery_for_item(loaded: Mapping[str, Any], *, item_id: str) -> bool:
    """Return true only for a fully replayable all-sibling recovery result.

    The v3 lifecycle uses this narrowly to distinguish the retained forensic
    affinity orphan from a proof-related fast-terminal orphan.
    """

    receipt = recovery._require_checkpoint_receipt(loaded)
    result = _load_complete(loaded, receipt)
    if result is None:
        return False
    plan, _complete = result
    return any(entry["item_id"] == item_id for entry in plan["entries"])


def audit_affinity_batch(
    bundle: Path, *, control_root: Path = supervisor.CONTROL_ROOT,
) -> dict[str, Any]:
    """Read-only admission audit for a prospective affinity-batch recovery."""

    target = Path(bundle)
    with initial._dispatch_lock(target):
        loaded = lifecycle._load_initial_batch(target, control_root=control_root)
        receipt = recovery._require_checkpoint_receipt(loaded)
        parent_root = Path(loaded["audit"]["parent_root"])
        with recovery._legacy_shared_lock(parent_root):
            recovery._checked_checkpointed_parent(loaded)
            with supervisor._catalog_lock(Path(loaded["control_root"])):
                recovery._require_reserved_cpu_leases(loaded)
            plan_path = Path(loaded["root"]) / PLAN
            complete_path = Path(loaded["root"]) / COMPLETE
            if complete_path.exists() or complete_path.is_symlink():
                plan_and_complete = _load_complete(loaded, receipt)
                if plan_and_complete is None:  # pragma: no cover - guarded above
                    raise InitialBatchAffinityRecoveryError("affinity completion disappeared during audit")
                plan, complete = plan_and_complete
                disposition = "COMPLETE"
                entries = plan["entries"]
            elif plan_path.exists() or plan_path.is_symlink():
                if plan_path.is_symlink():
                    raise InitialBatchAffinityRecoveryError("affinity recovery plan path is unsafe")
                plan = _validate_plan(loaded, receipt, supervisor._read_json(plan_path))
                complete = None
                disposition = "PLANNED"
                entries = plan["entries"]
            else:
                contexts = [
                    _child_context(
                        loaded, step=step, require_live_claim=True, require_precontroller=True,
                    )
                    for step in loaded["plan"]["steps"]
                ]
                _require_affinity(contexts)
                complete = None
                disposition = "ADMITTED_PRECONTROLLER"
                entries = [
                    _entry_without_policy(
                        context,
                        admission=supervisor.child_runner._resource_admission(
                            Path(context["child_root"]), context["policy"],
                        ),
                    )
                    for context in contexts
                ]
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-dic5-recursive-initial-batch-affinity-recovery-audit-v1",
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "parent_checkpoint_sha256": receipt["record_sha256"],
            "disposition": disposition,
            "entries": entries,
            "completion_sha256": None if complete is None else complete["record_sha256"],
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def recover_affinity_batch(
    bundle: Path, *, control_root: Path = supervisor.CONTROL_ROOT,
) -> dict[str, Any]:
    """Recover every sibling in one exact affinity-stranded initial batch."""

    target = Path(bundle)
    with initial._dispatch_lock(target):
        loaded = lifecycle._load_initial_batch(target, control_root=control_root)
        receipt = recovery._require_checkpoint_receipt(loaded)
        parent_root = Path(loaded["audit"]["parent_root"])
        with recovery._legacy_shared_lock(parent_root):
            recovery._checked_checkpointed_parent(loaded)
            with supervisor._catalog_lock(Path(loaded["control_root"])):
                recovery._require_reserved_cpu_leases(loaded)
            sidecar = _safe_sidecar_dir(Path(loaded["root"]))
            plan_path = sidecar / PLAN.name
            if plan_path.exists() or plan_path.is_symlink():
                if plan_path.is_symlink():
                    raise InitialBatchAffinityRecoveryError("affinity recovery plan path is unsafe")
                plan = _validate_plan(loaded, receipt, supervisor._read_json(plan_path))
            else:
                contexts = []
                for step in loaded["plan"]["steps"]:
                    contexts.append(_child_context(
                        loaded, step=step, require_live_claim=True, require_precontroller=True,
                    ))
                _require_affinity(contexts)
                plan = _plan_value(loaded, receipt, contexts)
                _publish_exact(plan_path, plan, label="affinity recovery plan")
            started = _launch_all(loaded, plan)
            complete = _complete_value(plan, started)
            _publish_exact(sidecar / COMPLETE.name, complete, label="affinity recovery completion")
    return supervisor.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-dic5-recursive-initial-batch-affinity-recovery-result-v1",
            "gate": GATE,
            "bundle_sha256": loaded["bundle"]["bundle_sha256"],
            "plan_sha256": plan["record_sha256"],
            "completion_sha256": complete["record_sha256"],
            "all_siblings_started": True,
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
    audit = sub.add_parser("audit-affinity-batch", allow_abbrev=False)
    audit.add_argument("--bundle", type=Path, required=True)
    recover = sub.add_parser("recover-affinity-batch", allow_abbrev=False)
    recover.add_argument("--bundle", type=Path, required=True)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.action == "audit-affinity-batch":
        result = audit_affinity_batch(args.bundle, control_root=args.control_root)
    elif args.action == "recover-affinity-batch":
        result = recover_affinity_batch(args.bundle, control_root=args.control_root)
    else:  # pragma: no cover - argparse guards this
        raise InitialBatchAffinityRecoveryError("unsupported affinity recovery action")
    sys.stdout.buffer.write(supervisor.canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        InitialBatchAffinityRecoveryError,
        initial.InitialBatchDispatchError,
        lifecycle.InitialBatchLifecycleError,
        recovery.RecursiveCheckpointRecoveryError,
        batch.BatchDispatchError,
        supervisor.RecursiveSplitSupervisorError,
        supervisor.child_runner.RecursiveChildRunnerError,
        recursive.RecursiveSplitError,
        OSError,
        ValueError,
        TypeError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
