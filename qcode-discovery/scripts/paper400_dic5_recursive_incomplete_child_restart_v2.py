#!/usr/bin/env python3
"""Second-attempt recovery for a visibility-raced recursive retry launch.

This module is intentionally narrower than the first incomplete-child retry
sidecar.  It accepts only a v1 retry plan whose first retry roots have an
unsealed generation-zero ``start.commit`` and were subsequently stopped by a
short-lived service cgroup.  Those first retry roots are retained as forensic
evidence.  A fresh ``attempt-000002`` root is materialised for the same leaf.

Unlike v1, the startup result path invokes the audited live-session
compatibility sealer for the one known controller-schema visibility race.
Every child ``Popen`` is still issued before any result is observed, and a
``--keep-alive`` service remains in the cgroup after dispatch.  A stopped or
ambiguous second attempt is never auto-retried in place.
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
from scripts import paper400_dic5_recursive_incomplete_child_restart_v1 as prior
from scripts import paper400_dic5_recursive_initial_batch_dispatch_v1 as initial
from scripts import paper400_dic5_recursive_initial_batch_lifecycle_v1 as base
from scripts import paper400_dic5_recursive_live_session_compat_v1 as compat
from scripts import paper400_dic5_recursive_postbootstrap_batch_dispatch_v1 as batch
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


SCHEMA_VERSION = 2
GATE = "paper400-dic5-recursive-incomplete-child-restart-v2"
SIDECAR_DIR = Path("incomplete-child-restart-v2")
FORENSICS_DIR = SIDECAR_DIR / "forensics"
STARTS_DIR = SIDECAR_DIR / "starts"
PLAN = SIDECAR_DIR / "000000-restart-plan.json"
COMMIT = SIDECAR_DIR / "000001-restart-plan-committed.json"
LOCK = Path(".incomplete-child-restart-v2.lock")

FORENSIC_KIND = "paper400-dic5-recursive-incomplete-child-retry-attempt-forensic-v2"
PLAN_KIND = "paper400-dic5-recursive-incomplete-child-retry-plan-v2"
COMMIT_KIND = "paper400-dic5-recursive-incomplete-child-retry-commit-v2"
INTENT_KIND = "paper400-dic5-recursive-incomplete-child-retry-intent-v2"
STARTED_KIND = "paper400-dic5-recursive-incomplete-child-retry-started-v2"
RESULT_KIND = "paper400-dic5-recursive-incomplete-child-retry-result-v2"
PARTIAL_DIAGNOSIS = "UNSEALED_START_COMMIT_NO_CONFLICT_PARTIAL_PROOF"


class IncompleteChildRestartV2Error(RuntimeError):
    """The v1 retry failure cannot be handed off to a fresh second attempt."""


def _source_binding() -> dict[str, Any]:
    source = Path(__file__).resolve(strict=True)
    payload = supervisor._stable_bytes(source, cap=32 << 20, executable=False)
    compat_source = PROJECT / "scripts" / "paper400_dic5_recursive_live_session_compat_v1.py"
    compat_payload = supervisor._stable_bytes(compat_source, cap=32 << 20, executable=False)
    return {
        "method": "exact-source-sha256-replay-v1",
        "incomplete_child_restart_v2": {
            "path": str(source),
            "sha256": hashlib.sha256(payload).hexdigest(),
        },
        "prior_incomplete_child_restart_v1": prior._source_binding(),
        "live_session_compat": {
            "path": str(compat_source),
            "sha256": hashlib.sha256(compat_payload).hexdigest(),
        },
        "initial_batch_dispatch": initial._source_binding(),
        "checkpoint_recovery": recovery._script_binding(),
    }


@contextlib.contextmanager
def _restart_lock(bundle: Path) -> Iterator[None]:
    path = bundle / LOCK
    try:
        fd = os.open(path, os.O_RDWR | os.O_CREAT | os.O_CLOEXEC | os.O_NOFOLLOW, 0o600)
    except OSError as exc:
        raise IncompleteChildRestartV2Error("v2 restart lock is unavailable") from exc
    try:
        info = os.fstat(fd)
        if (
            not stat.S_ISREG(info.st_mode)
            or info.st_uid != os.geteuid()
            or info.st_nlink != 1
            or stat.S_IMODE(info.st_mode) != 0o600
        ):
            raise IncompleteChildRestartV2Error("v2 restart lock metadata is unsafe")
        import fcntl

        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise IncompleteChildRestartV2Error("another v2 restart is active") from exc
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
        raise IncompleteChildRestartV2Error("v2 restart sidecar is unsafe") from exc


def _publish_exact(path: Path, value: Mapping[str, Any], *, label: str) -> None:
    if path.exists() or path.is_symlink():
        if path.is_symlink() or supervisor._read_json(path) != value:
            raise IncompleteChildRestartV2Error(f"existing {label} conflicts with replay")
        return
    supervisor._publish_json(path, value)


def _retry_root(bundle: Path, path: str) -> Path:
    if type(path) is not str or not path or any(char not in "01" for char in path):
        raise IncompleteChildRestartV2Error("v2 retry leaf path is unsafe")
    return bundle / supervisor.CHILDREN_DIR / f"retry-{path}-attempt-000002"


def _forensic_path(bundle: Path, entry: Mapping[str, Any]) -> Path:
    return _sidecar(bundle, FORENSICS_DIR) / f"{entry['ordinal']:04d}-{entry['claim_token'][:16]}.json"


def _start_paths(bundle: Path, entry: Mapping[str, Any]) -> tuple[Path, Path]:
    key = f"{entry['ordinal']:04d}-{entry['claim_token'][:16]}"
    directory = _sidecar(bundle, STARTS_DIR)
    return directory / f"{key}.intent.json", directory / f"{key}.started.json"


def _prior_handoff(loaded: Mapping[str, Any], *, recheck_original: bool) -> dict[str, Any]:
    try:
        return prior.load_restart(
            loaded, require_started=False, recheck_original=recheck_original,
        )
    except prior.IncompleteChildRestartError as exc:
        raise IncompleteChildRestartV2Error("prior v1 restart handoff is not replayable") from exc


def _prior_entry(prior_handoff: Mapping[str, Any], item_id: str) -> dict[str, Any]:
    matches = [
        evidence for evidence in prior_handoff.get("entries", [])
        if isinstance(evidence, dict) and evidence.get("entry", {}).get("item_id") == item_id
    ]
    if len(matches) != 1:
        raise IncompleteChildRestartV2Error("prior v1 handoff has no unique frontier entry")
    value = matches[0]
    if not isinstance(value.get("entry"), dict) or not isinstance(value.get("forensic"), dict):
        raise IncompleteChildRestartV2Error("prior v1 entry evidence is malformed")
    return value


def _terminal_artifacts_absent(root: Path) -> bool:
    runner = supervisor.child_runner
    return not any(
        (root / name).exists() or (root / name).is_symlink()
        for name in (
            runner.SESSION_COMMIT,
            runner.TERMINAL_CLAIM,
            runner.CERTIFICATE,
            runner.VALIDATION,
            runner.FINAL_COMMIT,
        )
    )


def _unsealed_partial_context(
    root: Path, child_loaded: Mapping[str, Any], *, cpu: int,
) -> dict[str, Any]:
    """Replay one exactly stopped, unsealed generation-zero partial proof."""

    runner = supervisor.child_runner
    target = runner._safe_root(root)
    if not _terminal_artifacts_absent(target):
        raise IncompleteChildRestartV2Error("first retry root has sealed state and cannot be retried")
    claim = runner._read_start_claim(target, child_loaded)
    if claim.get("expected_single_cpu") != cpu:
        raise IncompleteChildRestartV2Error("first retry start claim has the wrong CPU")
    config = runner._load_expected_controller_config(target)
    runtime = target / runner.RUNTIME_ROOT
    with runner._clean_controller_environment():
        status = runner.controller.inspect(runtime, verify_hashes=True)
    generations = status.get("generations")
    if (
        status.get("root") != str(runtime)
        or status.get("config_manifest_sha256") != config.get("self_sha256")
        or status.get("state") != "INACTIVE_UNCHECKPOINTED"
        or not isinstance(generations, list)
        or len(generations) != 1
        or not isinstance(generations[0], dict)
    ):
        raise IncompleteChildRestartV2Error("first retry transport is not exactly one inactive start")
    generation = generations[0]
    generation_dir = runner.controller._generation_dir(runtime, 0)
    active = runner.controller._active_commit(generation_dir, 0)
    controller_claim = runner.controller.read_manifest(
        generation_dir / "start.claim.json", expected_kind="start.claim",
    )
    if (
        generation.get("generation") != 0
        or generation.get("active_kind") != "start.commit"
        or generation.get("active_manifest_sha256") != active.get("self_sha256")
        or generation.get("pid_identity_alive") is not False
        or generation.get("checkpointed") is not False
        or generation.get("poison_claim") is not None
        or generation.get("stale_tail_injected") is not False
        or active.get("kind") != "start.commit"
        or active.get("generation") != 0
        or active.get("claim_sha256") != controller_claim.get("self_sha256")
        or controller_claim.get("generation") != 0
        or controller_claim.get("init_manifest_sha256") != config.get("self_sha256")
        or type(active.get("pid")) is not int
        or active["pid"] <= 0
        or type(active.get("proc_start_ticks")) is not int
        or active["proc_start_ticks"] < 0
        or active.get("single_process_peer_count") != 1
        or type(active.get("coordinator_port")) is not int
        or not 1 <= active["coordinator_port"] <= 65535
    ):
        raise IncompleteChildRestartV2Error("first retry start commit is not an exact singleton")
    if any((generation_dir / name).exists() or (generation_dir / name).is_symlink() for name in (
        "checkpoint.claim.json", "checkpoint.commit.json", "resume.claim.json", "resume.commit.json",
    )):
        raise IncompleteChildRestartV2Error("first retry has checkpoint or resume ambiguity")
    images = generation_dir / "images"
    if images.exists() and any(images.iterdir()):
        raise IncompleteChildRestartV2Error("first retry retained unexpected checkpoint images")
    stdout_path = runtime / "solver.stdout"
    stderr_path = runtime / "solver.stderr"
    if (
        recovery._read_regular_bytes(stdout_path, cap=recovery.MAX_SOLVER_TRANSCRIPT_BYTES) != b""
        or recovery._read_regular_bytes(stderr_path, cap=recovery.MAX_SOLVER_TRANSCRIPT_BYTES) != b""
    ):
        raise IncompleteChildRestartV2Error("first retry transcript is not the expected silent cgroup interruption")
    proof_path = runtime / "proof.drat"
    holders = runner._writable_holders(proof_path)
    if holders:
        raise IncompleteChildRestartV2Error(f"first retry proof has writable holders: {holders}")
    proof = runner.v2._physical_record(
        proof_path, target, "raw-binary-drat", cap=child_loaded["policy"]["proof_max_bytes"],
    )
    if proof.get("bytes", 0) <= 0:
        raise IncompleteChildRestartV2Error("first retry proof is empty, not a partial-proof handoff")
    snapshot = runner.seal(
        {
            "schema_version": runner.SCHEMA_VERSION,
            "kind": "paper400-dic5-recursive-stopped-proof-snapshot-v1",
            "transport_state": "INACTIVE_UNCHECKPOINTED",
            "controller_status_sha256": recursive.canonical_sha256(status),
            "latest_generation": 0,
            "latest_pid": active["pid"],
            "latest_proc_start_ticks": active["proc_start_ticks"],
            "latest_pid_identity_alive": False,
            "proof": proof,
            "writable_holders": [],
        },
        "snapshot_sha256",
    )
    return {
        "root": target,
        "claim": claim,
        "config": config,
        "status": status,
        "active": active,
        "snapshot": snapshot,
        "stdout": runner.v2._physical_record(
            stdout_path, target, "solver-stdout", cap=recovery.MAX_SOLVER_TRANSCRIPT_BYTES,
        ),
        "stderr": runner.v2._physical_record(
            stderr_path, target, "solver-stderr", cap=recovery.MAX_SOLVER_TRANSCRIPT_BYTES,
        ),
    }


def _attempt_forensic_value(
    loaded: Mapping[str, Any], prior_handoff: Mapping[str, Any], prior_evidence: Mapping[str, Any],
) -> dict[str, Any]:
    """Record why the v1 attempt is preserved but cannot be reused."""

    prior_entry = prior_evidence["entry"]
    prior_forensic = prior_evidence["forensic"]
    item_id = prior_entry["item_id"]
    root = Path(prior_entry["retry_child_root"])
    runner = supervisor.child_runner
    target = runner._safe_root(root)
    with runner._root_lock(target):
        child_loaded = prior._validate_retry_static(loaded, prior_entry)
        context = _unsealed_partial_context(target, child_loaded, cpu=prior_entry["cpu_ids"][0])
        proof = context["snapshot"]["proof"]
        drat, stdout, stderr, _bound = runner._checker(
            target,
            child_loaded,
            role="drat-verify",
            proof_path=target / runner.RUNTIME_ROOT / "proof.drat",
            proof_record=proof,
            proof_cap=child_loaded["policy"]["proof_max_bytes"],
        )
        after = _unsealed_partial_context(target, child_loaded, cpu=prior_entry["cpu_ids"][0])
        if context["snapshot"] != after["snapshot"]:
            raise IncompleteChildRestartV2Error("first retry stopped-proof snapshot changed during DRAT preflight")
        transcript = stdout + b"\n" + stderr
        if (
            drat.get("verified") is True
            or b"s NOT VERIFIED" not in transcript
            or b"no conflict" not in transcript.lower()
        ):
            raise IncompleteChildRestartV2Error("first retry proof is not the exact no-conflict partial proof")
        return supervisor.seal(
            {
                "schema_version": SCHEMA_VERSION,
                "kind": FORENSIC_KIND,
                "gate": GATE,
                "bundle_sha256": loaded["bundle"]["bundle_sha256"],
                "prior_restart_plan_sha256": prior_handoff["plan"]["restart_plan_sha256"],
                "prior_restart_commit_sha256": prior_handoff["commit"]["record_sha256"],
                "prior_forensic_sha256": prior_forensic["forensic_sha256"],
                "item_id": item_id,
                "path": prior_entry["path"],
                "worker_sha256": prior_entry["worker_sha256"],
                "claim_token": prior_entry["claim_token"],
                "worker_id": prior_entry["worker_id"],
                "cpu_ids": list(prior_entry["cpu_ids"]),
                "first_retry_root": str(target),
                "first_retry_root_identity": runner._root_identity(target),
                "first_retry_static_sha256": child_loaded["static"]["static_sha256"],
                "first_retry_start_claim_sha256": context["claim"]["record_sha256"],
                "controller_config_sha256": context["config"]["self_sha256"],
                "controller_start_sha256": context["active"]["self_sha256"],
                "snapshot": context["snapshot"],
                "solver_stdout": context["stdout"],
                "solver_stderr": context["stderr"],
                "drat_check": drat,
                "drat_stdout_sha256": hashlib.sha256(stdout).hexdigest(),
                "drat_stderr_sha256": hashlib.sha256(stderr).hexdigest(),
                "partial_diagnosis": PARTIAL_DIAGNOSIS,
                "session_absent": True,
                "terminal_artifacts_absent": True,
                "hardness_only": True,
                "solver_terminal_claim": False,
                "source_binding": _source_binding(),
            },
            "forensic_sha256",
        )


def _read_attempt_forensic(
    loaded: Mapping[str, Any], prior_handoff: Mapping[str, Any], prior_evidence: Mapping[str, Any],
    *, recheck: bool,
) -> dict[str, Any]:
    prior_entry = prior_evidence["entry"]
    prior_forensic = prior_evidence["forensic"]
    bundle = Path(loaded["root"])
    path = _forensic_path(bundle, prior_entry)
    if path.is_symlink() or not path.exists():
        raise IncompleteChildRestartV2Error("first retry partial-proof forensic receipt is absent")
    value = supervisor._read_json(path)
    required = {
        "schema_version", "kind", "gate", "bundle_sha256", "prior_restart_plan_sha256",
        "prior_restart_commit_sha256", "prior_forensic_sha256", "item_id", "path",
        "worker_sha256", "claim_token", "worker_id", "cpu_ids", "first_retry_root",
        "first_retry_root_identity", "first_retry_static_sha256", "first_retry_start_claim_sha256",
        "controller_config_sha256", "controller_start_sha256", "snapshot", "solver_stdout",
        "solver_stderr", "drat_check", "drat_stdout_sha256", "drat_stderr_sha256",
        "partial_diagnosis", "session_absent", "terminal_artifacts_absent", "hardness_only",
        "solver_terminal_claim", "source_binding", "forensic_sha256",
    }
    snapshot = value.get("snapshot")
    drat = value.get("drat_check")
    if (
        set(value) != required
        or not recursive.selfhash_valid(value, "forensic_sha256")
        or value.get("schema_version") != SCHEMA_VERSION
        or value.get("kind") != FORENSIC_KIND
        or value.get("gate") != GATE
        or value.get("bundle_sha256") != loaded["bundle"].get("bundle_sha256")
        or value.get("prior_restart_plan_sha256") != prior_handoff["plan"].get("restart_plan_sha256")
        or value.get("prior_restart_commit_sha256") != prior_handoff["commit"].get("record_sha256")
        or value.get("prior_forensic_sha256") != prior_forensic.get("forensic_sha256")
        or any(value.get(key) != prior_entry.get(key) for key in (
            "item_id", "path", "worker_sha256", "claim_token", "worker_id", "cpu_ids",
        ))
        or value.get("first_retry_root") != prior_entry.get("retry_child_root")
        or value.get("partial_diagnosis") != PARTIAL_DIAGNOSIS
        or value.get("session_absent") is not True
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
        raise IncompleteChildRestartV2Error("first retry partial-proof forensic receipt is malformed")
    if recheck:
        runner = supervisor.child_runner
        root = runner._safe_root(Path(prior_entry["retry_child_root"]))
        with runner._root_lock(root, exclusive=False):
            child_loaded = prior._validate_retry_static(loaded, prior_entry)
            context = _unsealed_partial_context(root, child_loaded, cpu=prior_entry["cpu_ids"][0])
            if (
                runner._root_identity(root) != value.get("first_retry_root_identity")
                or child_loaded["static"].get("static_sha256") != value.get("first_retry_static_sha256")
                or context["claim"].get("record_sha256") != value.get("first_retry_start_claim_sha256")
                or context["config"].get("self_sha256") != value.get("controller_config_sha256")
                or context["active"].get("self_sha256") != value.get("controller_start_sha256")
                or context["snapshot"] != snapshot
                or context["stdout"] != value.get("solver_stdout")
                or context["stderr"] != value.get("solver_stderr")
            ):
                raise IncompleteChildRestartV2Error("first retry evidence changed after its forensic receipt")
    return value


def _entry_value(
    loaded: Mapping[str, Any], prior_evidence: Mapping[str, Any], forensic: Mapping[str, Any],
) -> dict[str, Any]:
    prior_entry = prior_evidence["entry"]
    return {
        "ordinal": prior_entry["ordinal"],
        "item_id": prior_entry["item_id"],
        "path": prior_entry["path"],
        "worker_sha256": prior_entry["worker_sha256"],
        "claim_token": prior_entry["claim_token"],
        "worker_id": prior_entry["worker_id"],
        "cpu_ids": list(prior_entry["cpu_ids"]),
        "original_child_root": prior_entry["original_child_root"],
        "original_session_sha256": prior_entry["original_session_sha256"],
        "forensic_sha256": forensic["forensic_sha256"],
        "retry_child_root": str(_retry_root(Path(loaded["root"]), prior_entry["path"])),
    }


def _plan_value(
    loaded: Mapping[str, Any], prior_handoff: Mapping[str, Any], *, item_ids: Sequence[str],
    forensics: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any]:
    queue = recursive.load_split_queue(Path(loaded["root"]) / supervisor.QUEUE)
    expected_ids = [item["item_id"] for item in queue["items"] if item.get("state") == "CLAIMED"]
    requested = list(item_ids)
    if len(set(requested)) != len(requested) or set(requested) != set(expected_ids):
        raise IncompleteChildRestartV2Error("v2 restart must explicitly cover every and only claimed child")
    if queue != loaded["initial_final_queue"]:
        raise IncompleteChildRestartV2Error("v2 restart cannot follow an unreviewed queue mutation")
    prior_entries = {
        evidence["entry"]["item_id"]: evidence for evidence in prior_handoff["entries"]
    }
    entries = [
        _entry_value(loaded, prior_entries[item_id], forensics[item_id])
        for item_id in sorted(requested, key=lambda value: prior_entries[value]["entry"]["ordinal"])
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
            "prior_restart_plan_sha256": prior_handoff["plan"]["restart_plan_sha256"],
            "prior_restart_commit_sha256": prior_handoff["commit"]["record_sha256"],
            "parent_checkpoint_sha256": receipt["record_sha256"],
            "queue_sha256_at_handoff": queue["queue_sha256"],
            "queue_event_sequence_at_handoff": queue["event_sequence"],
            "entries": entries,
            "all_siblings_before_any_spawn": True,
            "persistent_service_required": True,
            "live_session_compatibility_required": True,
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _source_binding(),
        },
        "restart_plan_sha256",
    )


def _validate_entry(
    loaded: Mapping[str, Any], prior_handoff: Mapping[str, Any], entry: Mapping[str, Any], *, ordinal: int,
) -> dict[str, Any]:
    required = {
        "ordinal", "item_id", "path", "worker_sha256", "claim_token", "worker_id",
        "cpu_ids", "original_child_root", "original_session_sha256", "forensic_sha256",
        "retry_child_root",
    }
    if set(entry) != required or entry.get("ordinal") != ordinal or type(entry.get("item_id")) is not str:
        raise IncompleteChildRestartV2Error("v2 restart plan entry is malformed")
    evidence = _prior_entry(prior_handoff, entry["item_id"])
    prior_entry = evidence["entry"]
    forensic = _read_attempt_forensic(loaded, prior_handoff, evidence, recheck=False)
    if (
        any(entry.get(key) != prior_entry.get(key) for key in (
            "ordinal", "item_id", "path", "worker_sha256", "claim_token", "worker_id",
            "cpu_ids", "original_child_root", "original_session_sha256",
        ))
        or entry.get("forensic_sha256") != forensic.get("forensic_sha256")
        or entry.get("retry_child_root") != str(_retry_root(Path(loaded["root"]), prior_entry["path"]))
    ):
        raise IncompleteChildRestartV2Error("v2 restart entry lost its v1/handoff binding")
    return dict(entry)


def _validate_plan(loaded: Mapping[str, Any], prior_handoff: Mapping[str, Any], value: Mapping[str, Any]) -> dict[str, Any]:
    required = {
        "schema_version", "kind", "gate", "bundle_sha256", "root", "root_identity",
        "prior_restart_plan_sha256", "prior_restart_commit_sha256", "parent_checkpoint_sha256",
        "queue_sha256_at_handoff", "queue_event_sequence_at_handoff", "entries",
        "all_siblings_before_any_spawn", "persistent_service_required",
        "live_session_compatibility_required", "hardness_only", "solver_terminal_claim",
        "source_binding", "restart_plan_sha256",
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
        or value.get("prior_restart_plan_sha256") != prior_handoff["plan"].get("restart_plan_sha256")
        or value.get("prior_restart_commit_sha256") != prior_handoff["commit"].get("record_sha256")
        or value.get("parent_checkpoint_sha256") != receipt.get("record_sha256")
        or value.get("all_siblings_before_any_spawn") is not True
        or value.get("persistent_service_required") is not True
        or value.get("live_session_compatibility_required") is not True
        or value.get("hardness_only") is not True
        or value.get("solver_terminal_claim") is not False
        or value.get("source_binding") != _source_binding()
        or not isinstance(value.get("entries"), list)
        or not value["entries"]
    ):
        raise IncompleteChildRestartV2Error("v2 restart plan is malformed")
    entries = [
        _validate_entry(loaded, prior_handoff, entry, ordinal=index)
        for index, entry in enumerate(value["entries"])
    ]
    expected = [entry["entry"]["item_id"] for entry in prior_handoff["entries"]]
    if [entry["item_id"] for entry in entries] != expected:
        raise IncompleteChildRestartV2Error("v2 restart plan does not cover the v1 frontier")
    if (
        value.get("queue_sha256_at_handoff") != loaded["initial_final_queue"].get("queue_sha256")
        or value.get("queue_event_sequence_at_handoff") != loaded["initial_final_queue"].get("event_sequence")
    ):
        raise IncompleteChildRestartV2Error("v2 restart plan queue handoff binding is invalid")
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
            "live_session_compatibility_required": True,
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


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
            "live_session_compatibility_required": True,
            "hardness_only": True,
            "solver_terminal_claim": False,
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def _validate_retry_static(loaded: Mapping[str, Any], entry: Mapping[str, Any]) -> dict[str, Any]:
    """The v1 static checker is independent of which retry attempt owns the root."""

    try:
        return prior._validate_retry_static(loaded, entry)
    except prior.IncompleteChildRestartError as exc:
        raise IncompleteChildRestartV2Error("v2 retry root lost its original leaf material") from exc


def _started_value(intent: Mapping[str, Any], session: Mapping[str, Any]) -> dict[str, Any]:
    if not recursive.is_sha256(session.get("record_sha256")):
        raise IncompleteChildRestartV2Error("v2 retry start has no sealed session")
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
    bundle = Path(loaded["root"])
    intent_path, started_path = _start_paths(bundle, entry)
    if any(path.is_symlink() or not path.exists() for path in (intent_path, started_path)):
        raise IncompleteChildRestartV2Error("v2 retry start intent or receipt is absent")
    intent = supervisor._read_json(intent_path)
    if intent != _intent_value(plan, entry):
        raise IncompleteChildRestartV2Error("v2 retry start intent changed")
    runner = supervisor.child_runner
    root = runner._safe_root(Path(entry["retry_child_root"]))
    with runner._root_lock(root, exclusive=False):
        child_loaded = _validate_retry_static(loaded, entry)
        session = runner._load_session(root, child_loaded)
        if session.get("expected_single_cpu") != entry["cpu_ids"][0]:
            raise IncompleteChildRestartV2Error("v2 retry session CPU differs from its retained lease")
        expected = _started_value(intent, session)
    if supervisor._read_json(started_path) != expected:
        raise IncompleteChildRestartV2Error("v2 retry started receipt changed")
    return intent, expected, session


def _load_restart(
    loaded: Mapping[str, Any], *, require_started: bool, recheck_original: bool,
) -> dict[str, Any]:
    bundle = Path(loaded["root"])
    prior_handoff = _prior_handoff(loaded, recheck_original=recheck_original)
    _sidecar(bundle, SIDECAR_DIR)
    plan_path, commit_path = bundle / PLAN, bundle / COMMIT
    if any(path.is_symlink() or not path.exists() for path in (plan_path, commit_path)):
        raise IncompleteChildRestartV2Error("v2 restart plan or commit is absent")
    plan = _validate_plan(loaded, prior_handoff, supervisor._read_json(plan_path))
    commit = _commit_value(loaded, plan)
    if supervisor._read_json(commit_path) != commit:
        raise IncompleteChildRestartV2Error("v2 restart commit does not replay its plan")
    entries: list[dict[str, Any]] = []
    for entry in plan["entries"]:
        evidence = _prior_entry(prior_handoff, entry["item_id"])
        forensic = _read_attempt_forensic(loaded, prior_handoff, evidence, recheck=recheck_original)
        if forensic.get("forensic_sha256") != entry.get("forensic_sha256"):
            raise IncompleteChildRestartV2Error("v2 restart plan forensic binding changed")
        result: dict[str, Any] = {"entry": dict(entry), "forensic": forensic}
        if require_started:
            intent, started, session = _read_started(loaded, plan, entry)
            result.update({"intent": intent, "started": started, "session": session})
        entries.append(result)
    return {"plan": plan, "commit": commit, "entries": entries}


load_restart = _load_restart


def _ensure_plan(
    loaded: Mapping[str, Any], prior_handoff: Mapping[str, Any], *, item_ids: Sequence[str],
) -> tuple[dict[str, Any], dict[str, Any]]:
    bundle = Path(loaded["root"])
    plan_path = bundle / PLAN
    if plan_path.exists() or plan_path.is_symlink():
        plan = _validate_plan(loaded, prior_handoff, supervisor._read_json(plan_path))
        if set(item_ids) != {entry["item_id"] for entry in plan["entries"]}:
            raise IncompleteChildRestartV2Error("existing v2 plan covers a different child set")
    else:
        forensics: dict[str, Mapping[str, Any]] = {}
        for item_id in item_ids:
            evidence = _prior_entry(prior_handoff, item_id)
            forensic = _attempt_forensic_value(loaded, prior_handoff, evidence)
            _publish_exact(_forensic_path(bundle, evidence["entry"]), forensic, label="first retry forensic receipt")
            forensics[item_id] = _read_attempt_forensic(loaded, prior_handoff, evidence, recheck=True)
        plan = _plan_value(loaded, prior_handoff, item_ids=item_ids, forensics=forensics)
        _publish_exact(plan_path, plan, label="v2 restart plan")
    commit = _commit_value(loaded, plan)
    _publish_exact(bundle / COMMIT, commit, label="v2 restart commit")
    return plan, commit


def _prepare_or_validate_retry_root(loaded: Mapping[str, Any], entry: Mapping[str, Any]) -> bool:
    runner = supervisor.child_runner
    root = Path(entry["retry_child_root"])
    if root.exists() or root.is_symlink():
        if root.is_symlink():
            raise IncompleteChildRestartV2Error("v2 retry root is a symlink")
        with runner._root_lock(runner._safe_root(root)):
            child_loaded = _validate_retry_static(loaded, entry)
            if (root / runner.SESSION_COMMIT).exists() or (root / runner.SESSION_COMMIT).is_symlink():
                runner._load_session(root, child_loaded)
                return False
            if (root / runner.START_CLAIM).exists() or (root / runner.START_CLAIM).is_symlink():
                raise IncompleteChildRestartV2Error("v2 retry root has an unsealed start claim and needs audit")
            if (root / runner.RUNTIME_ROOT).exists() or (root / runner.RUNTIME_ROOT).is_symlink():
                raise IncompleteChildRestartV2Error("v2 retry root has unresolved transport state")
            return True
    runner.prepare_root_from_material(
        root,
        parent_dimacs=loaded["parent"],
        split_manifest=loaded["manifest"],
        leaf_path=entry["path"],
        parent_audit=loaded["audit"],
    )
    return True


def _sealed_session_after_start(
    loaded: Mapping[str, Any], entry: Mapping[str, Any], *, error: str | None,
) -> dict[str, Any]:
    """Read a normal session or seal the one admitted live visibility race."""

    runner = supervisor.child_runner
    root = runner._safe_root(Path(entry["retry_child_root"]))
    if error is not None:
        if error != recovery.FAST_START_ERROR:
            raise IncompleteChildRestartV2Error(error)
        try:
            return compat.seal_live_session(root, cpu=entry["cpu_ids"][0])["session"]
        except compat.LiveSessionCompatError as exc:
            raise IncompleteChildRestartV2Error("v2 retry live-session compatibility seal failed") from exc
    with runner._root_lock(root, exclusive=False):
        return runner._load_session(root, _validate_retry_static(loaded, entry))


def _dispatch_all(loaded: Mapping[str, Any], plan: Mapping[str, Any]) -> list[dict[str, Any]]:
    """Start every second-attempt sibling before inspecting any launch result."""

    bundle = Path(loaded["root"])
    pending: list[dict[str, Any]] = []
    results: list[dict[str, Any]] = []
    for entry in plan["entries"]:
        intent_path, started_path = _start_paths(bundle, entry)
        _publish_exact(intent_path, _intent_value(plan, entry), label="v2 retry start intent")
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
            intent_path, started_path = _start_paths(bundle, entry)
            runner = supervisor.child_runner
            root = runner._safe_root(Path(entry["retry_child_root"]))
            with runner._root_lock(root, exclusive=False):
                session = runner._load_session(root, _validate_retry_static(loaded, entry))
                _publish_exact(started_path, _started_value(supervisor._read_json(intent_path), session), label="v2 retry started receipt")
            results.append({"item_id": entry["item_id"], "state": "RECOVERED_STARTED_RECEIPT"})
    processes: list[tuple[dict[str, Any], Any]] = []
    failures: list[str] = []
    for entry in launches:
        try:
            processes.append((entry, batch._spawn_child_start(Path(entry["retry_child_root"]), cpu=entry["cpu_ids"][0])))
        except BaseException as exc:
            failures.append(f"{entry['item_id']}: {type(exc).__name__}: {exc}")
    for entry, process in processes:
        try:
            _stdout, stderr = process.communicate()
            returncode = process.returncode
            if type(returncode) is not int:
                raise IncompleteChildRestartV2Error("v2 retry start process has no exit status")
            error = None if returncode == 0 else batch._external_start_error(returncode, stderr or b"")
            session = _sealed_session_after_start(loaded, entry, error=error)
            intent_path, started_path = _start_paths(bundle, entry)
            intent = supervisor._read_json(intent_path)
            started = _started_value(intent, session)
            _publish_exact(started_path, started, label="v2 retry started receipt")
            results.append({
                "item_id": entry["item_id"],
                "state": "RUNNING" if error is None else "LIVE_SESSION_SEALED_SCHEMA_COMPAT",
                "started_sha256": started["record_sha256"],
            })
        except BaseException as exc:
            failures.append(f"{entry['item_id']}: {type(exc).__name__}: {exc}")
    if failures:
        raise IncompleteChildRestartV2Error(
            "one or more v2 retry starts require forensic audit after every sibling was attempted: "
            + " | ".join(failures)
        )
    return sorted(results, key=lambda value: value["item_id"])


def dispatch_restart(
    bundle: Path, *, item_ids: Sequence[str], control_root: Path = supervisor.CONTROL_ROOT,
) -> dict[str, Any]:
    target = Path(bundle)
    if not item_ids:
        raise IncompleteChildRestartV2Error("v2 restart requires explicit item IDs")
    with initial._dispatch_lock(target):
        with _restart_lock(target):
            loaded = base._load_initial_batch(target, control_root=control_root)
            receipt = recovery._require_checkpoint_receipt(loaded)
            parent_root = Path(loaded["audit"]["parent_root"])
            with recovery._legacy_shared_lock(parent_root):
                _observation, chain = recovery._checked_checkpointed_parent(loaded)
                with supervisor._catalog_lock(Path(loaded["control_root"])):
                    recovery._require_reserved_cpu_leases(loaded)
                prior_handoff = _prior_handoff(loaded, recheck_original=True)
                plan, commit = _ensure_plan(loaded, prior_handoff, item_ids=item_ids)
                handoff = _load_restart(loaded, require_started=False, recheck_original=True)
                if handoff["plan"] != plan or handoff["commit"] != commit:
                    raise IncompleteChildRestartV2Error("v2 restart plan changed during its own replay")
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
            "checkpoint_manifest_sha256": chain["latest_checkpoint_sha256"],
            "children": children,
            "all_siblings_before_any_spawn": True,
            "persistent_service_required": True,
            "live_session_compatibility_required": True,
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
    recover.add_argument("--keep-alive", action="store_true")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    result = dispatch_restart(args.bundle, item_ids=args.item_id, control_root=args.control_root)
    sys.stdout.buffer.write(supervisor.canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    if args.keep_alive:
        while True:
            time.sleep(3600)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        IncompleteChildRestartV2Error,
        prior.IncompleteChildRestartError,
        base.InitialBatchLifecycleError,
        initial.InitialBatchDispatchError,
        compat.LiveSessionCompatError,
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
