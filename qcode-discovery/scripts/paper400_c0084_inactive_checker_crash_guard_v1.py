#!/usr/bin/env python3
"""Fail-closed shared guard for the inactive c0084 checker-crash root.

This is a control-plane guard, not a proof checker and not a terminal claim.
It admits exactly r4 b0020/l1 (semantic c0084) only after an immutable record
binds the legacy 00/10/11/start.commit chain, both stale PIDs, the unchanged
cube/proof/checker identities, terminal absence, and at least 58 deterministic
SIGSEGV checker results.  A SIGSEGV is used only as scheduling/hardness
evidence; the old DRAT is never treated as verified or as an UNSAT result.

The process opens the already-existing root lock with O_NOFOLLOW, acquires a
nonblocking shared flock, replays every held pathname edge, and only then
notifies systemd.  An active legacy harvest owns the same lock exclusively,
so this helper exits EX_TEMPFAIL and leaves it untouched.  Once acquired, the
shared lock blocks future exclusive legacy retries without stopping or
modifying their saturator.  This program never creates, writes, renames,
deletes, checkpoints, signals, or launches anything.
"""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
import re
import socket
import sys
import time
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Any


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from scripts import paper400_drat_segv_quarantine_guard_v1 as quarantine


SCHEMA_VERSION = 1
GATE = "paper400-c0084-inactive-checker-crash-guard-v1"
ADMISSION_KIND = "paper400-c0084-inactive-checker-crash-admission-v1"
EXPECTED_ROOT = Path(
    "/home/jing/paper400-runs/"
    "paper400-batch-0020-local-20260902-r4/lanes/lane-1"
)
EXPECTED_ENTRY_ID = "r4-c0084-b0020-l1"
EXPECTED_CHILD_ID = "paper400-p00-w10-c0084"
EXPECTED_CHILD_INDEX = 84
EXPECTED_CPU = 33
EXPECTED_QUARANTINE_MANIFEST = Path(
    "/home/jing/paper400-runs/"
    ".paper400-drat-segv-quarantine-candidates-v1.6LME5I/"
    "paper400-drat-segv-quarantine-manifest-v1.json"
)
EXPECTED_QUARANTINE_FILE_SHA256 = (
    "1359908202c5b3ab4989b2fa5f1e9f3a9bdd40103ddecbd312c94fd6d86ba4a1"
)
EXPECTED_QUARANTINE_RECORD_SHA256 = (
    "bd0b0b1d288d8504de40bb42f0db172eb78120f80909280e3ed990966491fd05"
)
EXPECTED_BASE_SIGSEGV_ATTEMPTS = 57
MINIMUM_SIGSEGV_ATTEMPTS = 59
# These are the first two post-manifest failures.  Binding their journal
# identity and sealed result chain means a renderer cannot invent the two
# events that take the reviewed 57-attempt baseline to the admitted 59.
EXPECTED_SUPPLEMENTAL_JOURNAL_ATTEMPTS = (
    {
        "unit": "paper400-r4-auto-h-b0020-l1-1788745926729814348.service",
        "cursor": (
            "s=6b913c34c2ee4fe98e5d53057752d1d0;i=26eef6;"
            "b=d66c2ed7fb0a479b88e023d32335bdac;m=63078c957b;"
            "t=65adb059d835e;x=2cf437f23d36e3d6"
        ),
        "realtime_usec": 1_788_746_598_810_462,
        "boot_id": "d66c2ed7fb0a479b88e023d32335bdac",
        "invocation_id": "e5b5c9d42ed5487d9a71ce8173a75616",
        "preflight_record_sha256": (
            "efd54dea2a99f35bf3d1f8d301663610fcd108dc1aec5f6ff219dcda93bcf5e4"
        ),
        "checker_result_sha256": (
            "cdbc7dace71b4d0cb529fe50bb9efd26e2ac723662f177ed9d7bbb2ef6b09689"
        ),
        "process_record_sha256": (
            "86cba52dbd99975b6d9c0114ef32be8a9795189d0feb640706e9cdff60d30e3f"
        ),
        "child_pid": 2_375_555,
        "supervisor_pid": 2_177_091,
        "elapsed_ns": 407_554_882_440,
    },
    {
        "unit": "paper400-r4-auto-h-b0020-l1-1788747728451738603.service",
        "cursor": (
            "s=6b913c34c2ee4fe98e5d53057752d1d0;i=271813;"
            "b=d66c2ed7fb0a479b88e023d32335bdac;m=63720c4e35;"
            "t=65adb701d3c18;x=3b18dfe30cd75c85"
        ),
        "realtime_usec": 1_788_748_385_565_720,
        "boot_id": "d66c2ed7fb0a479b88e023d32335bdac",
        "invocation_id": "838e2115b13e4186afe846d106cb73ed",
        "preflight_record_sha256": (
            "c599c7d77ecc71204bff5e223e41aa8089f4ca78c7d13c78dc394543341411b7"
        ),
        "checker_result_sha256": (
            "c2beb93c7639c46b7dca606b7793bc73db06a5cf130f22883a7d74aa16b2170b"
        ),
        "process_record_sha256": (
            "fd60d9dd04a11397c5d476de72a4e133311f6c2fe8a8b5631769cd536f0c795a"
        ),
        "child_pid": 3_525_604,
        "supervisor_pid": 3_380_810,
        "elapsed_ns": 413_589_778_711,
    },
)
MAX_SMALL_RECORD_BYTES = 4 << 20
EX_TEMPFAIL = 75
HEX = re.compile(r"[0-9a-f]{64}\Z")

REQUIRED_RECORD_PATHS = {
    "static": "state/00-resume-static.json",
    "start_claim": "state/10-start.claim",
    "session": "state/11-session.json",
    "controller_start": "runtime/dmtcp/generations/000000/start.commit.json",
}
REQUIRED_ABSENT = tuple(sorted({
    *quarantine.REQUIRED_ABSENT,
    "state/30-transport-prune.claim.json",
    "state/31-transport-prune.json",
}))


class C0084RecoveryGuardError(RuntimeError):
    """The c0084 recovery admission or one of its bound paths changed."""


class C0084RecoveryBusyError(C0084RecoveryGuardError):
    """The current legacy action still owns the root exclusively."""


@dataclass
class HeldRecoveryGuard:
    admission: quarantine.HeldPath
    quarantine_guard: quarantine.HeldQuarantine
    records: dict[str, quarantine.HeldPath]
    stale_pids: tuple[int, ...]


_FAULT_HOOK: Callable[[str, Path], None] = lambda _stage, _path: None


def _canonical(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
        allow_nan=False,
    ).encode("ascii")


def seal(value: Mapping[str, Any]) -> dict[str, Any]:
    """Seal an admission record; exposed for an offline renderer and tests."""

    result = dict(value)
    if "record_sha256" in result:
        raise C0084RecoveryGuardError("record is already sealed")
    result["record_sha256"] = hashlib.sha256(_canonical(result)).hexdigest()
    return result


def payload(value: Mapping[str, Any]) -> bytes:
    return _canonical(value) + b"\n"


def _valid_seal(value: Any, field: str) -> bool:
    if type(value) is not dict:
        return False
    digest = value.get(field)
    if type(digest) is not str or HEX.fullmatch(digest) is None:
        return False
    unsigned = dict(value)
    unsigned.pop(field)
    return hashlib.sha256(_canonical(unsigned)).hexdigest() == digest


def _file_binding(path: Path) -> dict[str, Any]:
    target = Path(path).resolve(strict=True)
    data = target.read_bytes()
    if len(data) > 32 << 20:
        raise C0084RecoveryGuardError("guard source exceeds the source cap")
    return {
        "path": str(target),
        "bytes": len(data),
        "sha256": hashlib.sha256(data).hexdigest(),
    }


def source_binding() -> dict[str, Any]:
    return {
        "method": "exact-source-sha256-replay-v1",
        "c0084_guard": _file_binding(Path(__file__)),
        "quarantine_guard": _file_binding(Path(quarantine.__file__)),
    }


def _same(left: Any, right: Any) -> bool:
    return type(left) is type(right) and _canonical(left) == _canonical(right)


def _natural(value: Any, label: str, *, positive: bool = False) -> int:
    if type(value) is not int or value < (1 if positive else 0):
        raise C0084RecoveryGuardError(f"{label} is invalid")
    return value


def _sha(value: Any, label: str) -> str:
    if type(value) is not str or HEX.fullmatch(value) is None:
        raise C0084RecoveryGuardError(f"{label} is not a SHA-256 digest")
    return value


def _read_held_json(
    held: quarantine.HeldPath, *, cap: int = MAX_SMALL_RECORD_BYTES,
) -> dict[str, Any]:
    size = held.expected.size
    if type(size) is not int or not 1 <= size <= cap:
        raise C0084RecoveryGuardError("bound JSON size is outside its cap")
    position = os.lseek(held.descriptor, 0, os.SEEK_CUR)
    try:
        os.lseek(held.descriptor, 0, os.SEEK_SET)
        data = b""
        while len(data) < size:
            chunk = os.read(held.descriptor, min(1 << 20, size - len(data)))
            if not chunk:
                raise C0084RecoveryGuardError("bound JSON was truncated")
            data += chunk
        if os.read(held.descriptor, 1):
            raise C0084RecoveryGuardError("bound JSON grew during replay")
    finally:
        os.lseek(held.descriptor, position, os.SEEK_SET)
    try:
        value = json.loads(data)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise C0084RecoveryGuardError("bound record is not JSON") from exc
    if type(value) is not dict or data not in {_canonical(value), payload(value)}:
        raise C0084RecoveryGuardError("bound record is not canonical JSON")
    return value


def _admission_schema(value: Mapping[str, Any]) -> None:
    required = {
        "schema_version", "kind", "gate", "root", "global_child_id",
        "global_child_index", "quarantine_binding", "records",
        "stale_processes", "incident", "claim_scope", "source_binding",
        "record_sha256",
    }
    if (
        set(value) != required
        or not _valid_seal(value, "record_sha256")
        or value.get("schema_version") != SCHEMA_VERSION
        or value.get("kind") != ADMISSION_KIND
        or value.get("gate") != GATE
        or value.get("root") != str(EXPECTED_ROOT)
        or value.get("global_child_id") != "c0084"
        or value.get("global_child_index") != EXPECTED_CHILD_INDEX
        or not _same(value.get("source_binding"), source_binding())
    ):
        raise C0084RecoveryGuardError("c0084 admission schema/source binding is invalid")
    scope = value.get("claim_scope")
    if type(scope) is not dict or scope != {
        "hardness_only": True,
        "solver_terminal_claim": False,
        "unsat_claim": False,
        "old_proof_certified": False,
        "recursive_children_require_fresh_proof": True,
        "terminal_publication_authorized": False,
        "root_guard_blocks_only_exclusive_legacy_actions": True,
        "saturator_stop_required": False,
    }:
        raise C0084RecoveryGuardError("c0084 admission weakens the nonterminal claim scope")


def _record_spec(
    value: Any, *, role: str,
) -> tuple[str, quarantine.Identity, str, str]:
    if type(value) is not dict or set(value) != {
        "relative_path", "identity", "file_sha256", "self_hash_field",
        "self_hash",
    }:
        raise C0084RecoveryGuardError(f"{role} record specification is malformed")
    relative = quarantine._relative(value.get("relative_path"))
    if relative != REQUIRED_RECORD_PATHS[role]:
        raise C0084RecoveryGuardError(f"{role} record pathname changed")
    identity = quarantine._identity(value.get("identity"), full=True)
    if identity.size is None or not 1 <= identity.size <= MAX_SMALL_RECORD_BYTES:
        raise C0084RecoveryGuardError(f"{role} record exceeds the small-record cap")
    file_digest = _sha(value.get("file_sha256"), f"{role} record file")
    record_digest = _sha(value.get("self_hash"), f"{role} record self-hash")
    expected_field = "self_sha256" if role == "controller_start" else "record_sha256"
    if value.get("self_hash_field") != expected_field:
        raise C0084RecoveryGuardError(f"{role} self-hash field changed")
    return relative, identity, file_digest, record_digest


def _open_record(
    root: quarantine.HeldPath, value: Any, *, role: str,
) -> tuple[quarantine.HeldPath, dict[str, Any]]:
    relative, identity, file_digest, record_digest = _record_spec(
        value, role=role,
    )
    held = quarantine._open_relative(root, relative, identity)
    try:
        if (
            quarantine._digest_descriptor(held.descriptor, identity.size or 0)
            != file_digest
        ):
            raise C0084RecoveryGuardError(f"{role} record SHA-256 changed")
        record = _read_held_json(held)
        field = value["self_hash_field"]
        if not _valid_seal(record, field) or record.get(field) != record_digest:
            raise C0084RecoveryGuardError(f"{role} record self-hash changed")
        return held, record
    except BaseException:
        quarantine._close_path(held)
        raise


def _validate_record_chain(records: Mapping[str, Mapping[str, Any]]) -> tuple[int, ...]:
    static = records["static"]
    claim = records["start_claim"]
    session = records["session"]
    started = records["controller_start"]
    child = static.get("child")
    cnf = static.get("cnf_artifact")
    peer = session.get("started_peer_rlimits")
    if (
        static.get("state") != "RESUMABLE_STATIC_SEALED"
        or static.get("root") != str(EXPECTED_ROOT)
        or type(child) is not dict
        or child.get("child_id") != EXPECTED_CHILD_ID
        or child.get("global_leaf_id") != EXPECTED_CHILD_ID
        or child.get("global_leaf_index") != EXPECTED_CHILD_INDEX
        or child.get("child_index") != EXPECTED_CHILD_INDEX
        or type(cnf) is not dict
        or cnf.get("relative_path") != "static/cube.cnf"
        or cnf.get("sha256") != child.get("child_dimacs_sha256")
        or cnf.get("bytes") != child.get("child_dimacs_bytes")
    ):
        raise C0084RecoveryGuardError("state/00 does not bind semantic c0084")
    stage_pid = claim.get("pid")
    solver_pid = started.get("pid")
    if (
        claim.get("action") != "start"
        or claim.get("terminal") is not False
        or claim.get("root") != str(EXPECTED_ROOT)
        or _natural(stage_pid, "stage claim PID", positive=True) != stage_pid
        or session.get("state") != "RUNNING"
        or session.get("root") != str(EXPECTED_ROOT)
        or session.get("resume_static_sha256") != static.get("record_sha256")
        or session.get("start_claim_sha256") != claim.get("record_sha256")
        or session.get("controller_start_sha256") != started.get("self_sha256")
        or session.get("child_dimacs_sha256") != child.get("child_dimacs_sha256")
        or session.get("expected_single_cpu") != EXPECTED_CPU
        or type(peer) is not dict
        or peer.get("verified") is not True
        or peer.get("pid") != solver_pid
        or started.get("kind") != "start.commit"
        or started.get("generation") != 0
        or _natural(solver_pid, "solver PID", positive=True) != solver_pid
        or type(started.get("proc_start_ticks")) is not int
        or started["proc_start_ticks"] < 0
        or started.get("single_process_peer_count") != 1
    ):
        raise C0084RecoveryGuardError("00/10/11/start.commit chain is inconsistent")
    return stage_pid, solver_pid


def _validate_stale_processes(value: Any, expected_pids: Sequence[int]) -> tuple[int, ...]:
    if type(value) is not list or len(value) != 2:
        raise C0084RecoveryGuardError("stale process set is incomplete")
    roles = {"stage_claim", "solver"}
    observed: dict[str, int] = {}
    for entry in value:
        if type(entry) is not dict or set(entry) != {
            "role", "pid", "expected_absent", "proc_start_ticks",
        }:
            raise C0084RecoveryGuardError("stale process entry is malformed")
        role = entry.get("role")
        pid = entry.get("pid")
        ticks = entry.get("proc_start_ticks")
        if (
            role not in roles or role in observed
            or _natural(pid, "stale PID", positive=True) != pid
            or entry.get("expected_absent") is not True
            or (role == "solver" and (type(ticks) is not int or ticks < 0))
            or (role == "stage_claim" and ticks is not None)
        ):
            raise C0084RecoveryGuardError("stale process identity is malformed")
        observed[role] = pid
    if tuple(observed[role] for role in ("stage_claim", "solver")) != tuple(expected_pids):
        raise C0084RecoveryGuardError("stale process set does not bind the start chain")
    return tuple(expected_pids)


def _pid_absent(pid: int) -> None:
    try:
        os.stat(f"/proc/{pid}", follow_symlinks=False)
    except FileNotFoundError:
        return
    except OSError as exc:
        raise C0084RecoveryGuardError("cannot establish stale PID absence") from exc
    raise C0084RecoveryGuardError(f"bound stale PID is present: {pid}")


def _validate_incident(
    incident: Any, quarantine_manifest: Mapping[str, Any],
    quarantine_entry: Mapping[str, Any],
) -> None:
    required = {
        "base_attempts", "supplemental_attempts", "total_attempts",
        "same_proof_cube_checker", "required_signal", "proof_sha256",
        "cube_sha256", "checker_sha256", "proof_content_hash_replay",
    }
    if type(incident) is not dict or set(incident) != required:
        raise C0084RecoveryGuardError("checker-crash incident is malformed")
    base = quarantine_entry.get("incident", {}).get("deterministic_attempts")
    qproof = quarantine_entry.get("proof", {}).get("sha256")
    qcube = quarantine_entry.get("cube", {}).get("sha256")
    qchecker = quarantine_entry.get("checker", {}).get("sha256")
    supplements = incident.get("supplemental_attempts")
    total = incident.get("total_attempts")
    if (
        _natural(base, "base attempt count") != EXPECTED_BASE_SIGSEGV_ATTEMPTS
        or incident.get("base_attempts") != EXPECTED_BASE_SIGSEGV_ATTEMPTS
        or type(supplements) is not list
        or len(supplements) != len(EXPECTED_SUPPLEMENTAL_JOURNAL_ATTEMPTS)
        or total != base + len(supplements)
        or type(total) is not int or total < MINIMUM_SIGSEGV_ATTEMPTS
        or incident.get("same_proof_cube_checker") is not True
        or incident.get("required_signal") != 11
        or incident.get("proof_sha256") != qproof
        or incident.get("cube_sha256") != qcube
        or incident.get("checker_sha256") != qchecker
        or incident.get("proof_content_hash_replay") != "journal-bound-stat-only"
        or quarantine_manifest.get("bad_checker_sha256") != qchecker
    ):
        raise C0084RecoveryGuardError("checker-crash incident lacks 59 exact failures")
    fields = {
        "unit", "cursor", "realtime_usec", "boot_id", "invocation_id",
        "preflight_record_sha256", "checker_result_sha256",
        "process_record_sha256", "proof_sha256", "cube_sha256",
        "checker_sha256", "exit_code", "signal", "drat_verified",
        "child_pid", "supervisor_pid", "elapsed_ns", "terminal_claim_created",
        "verification_retry_allowed",
    }
    uniqueness: set[tuple[str, str, str]] = set()
    journal_fields = set(EXPECTED_SUPPLEMENTAL_JOURNAL_ATTEMPTS[0])
    for index, attempt in enumerate(supplements):
        if type(attempt) is not dict or set(attempt) != fields:
            raise C0084RecoveryGuardError("supplemental checker attempt is malformed")
        unit = attempt.get("unit")
        cursor = attempt.get("cursor")
        realtime = attempt.get("realtime_usec")
        if (
            type(unit) is not str
            or not unit.startswith("paper400-r4-auto-h-b0020-l1-")
            or not unit.endswith(".service")
            or type(cursor) is not str or not cursor
            or type(realtime) is not int or realtime <= 0
            or type(attempt.get("boot_id")) is not str
            or re.fullmatch(r"[0-9a-f]{32}", attempt["boot_id"]) is None
            or type(attempt.get("invocation_id")) is not str
            or re.fullmatch(r"[0-9a-f]{32}", attempt["invocation_id"]) is None
            or any(
                _sha(attempt.get(key), key) != attempt.get(key)
                for key in (
                    "preflight_record_sha256", "checker_result_sha256",
                    "process_record_sha256",
                )
            )
            or attempt.get("proof_sha256") != qproof
            or attempt.get("cube_sha256") != qcube
            or attempt.get("checker_sha256") != qchecker
            or attempt.get("exit_code") != -11
            or attempt.get("signal") != 11
            or _natural(attempt.get("child_pid"), "checker child PID", positive=True)
            != attempt.get("child_pid")
            or _natural(attempt.get("supervisor_pid"), "checker supervisor PID", positive=True)
            != attempt.get("supervisor_pid")
            or _natural(attempt.get("elapsed_ns"), "checker elapsed ns", positive=True)
            != attempt.get("elapsed_ns")
            or attempt.get("drat_verified") is not False
            or attempt.get("terminal_claim_created") is not False
            or attempt.get("verification_retry_allowed") is not True
        ):
            raise C0084RecoveryGuardError("supplemental attempt is not the exact SIGSEGV shape")
        observed_journal = {field: attempt[field] for field in journal_fields}
        if not _same(
            observed_journal, EXPECTED_SUPPLEMENTAL_JOURNAL_ATTEMPTS[index],
        ):
            raise C0084RecoveryGuardError(
                "supplemental attempt does not match the fixed journal identity"
            )
        key = (unit, cursor, attempt["process_record_sha256"])
        if key in uniqueness:
            raise C0084RecoveryGuardError("supplemental checker attempts are duplicated")
        uniqueness.add(key)


def _load_admission(
    path: Path, expected_sha256: str,
) -> tuple[quarantine.HeldPath, dict[str, Any]]:
    try:
        held, value = quarantine._load_manifest(path, expected_sha256)
    except quarantine.QuarantineGuardError as exc:
        raise C0084RecoveryGuardError(str(exc)) from exc
    try:
        _admission_schema(value)
        return held, value
    except BaseException:
        quarantine._close_path(held)
        raise


def _load_quarantine_binding(
    value: Mapping[str, Any],
) -> tuple[Path, str, dict[str, Any], dict[str, Any]]:
    binding = value.get("quarantine_binding")
    if type(binding) is not dict or set(binding) != {
        "manifest_path", "manifest_file_sha256", "manifest_record_sha256",
        "entry_id", "base_attempts",
    }:
        raise C0084RecoveryGuardError("quarantine binding is malformed")
    path = Path(binding.get("manifest_path", ""))
    digest = _sha(binding.get("manifest_file_sha256"), "quarantine manifest")
    if (
        binding.get("entry_id") != EXPECTED_ENTRY_ID
        or path != EXPECTED_QUARANTINE_MANIFEST
        or digest != EXPECTED_QUARANTINE_FILE_SHA256
        or binding.get("manifest_record_sha256")
        != EXPECTED_QUARANTINE_RECORD_SHA256
        or binding.get("base_attempts") != EXPECTED_BASE_SIGSEGV_ATTEMPTS
    ):
        raise C0084RecoveryGuardError(
            "quarantine binding is not the fixed reviewed c0084 manifest"
        )
    held: quarantine.HeldPath | None = None
    try:
        held, manifest = quarantine._load_manifest(path, digest)
        entry = quarantine._entry(manifest, EXPECTED_ENTRY_ID)
        if (
            manifest.get("record_sha256") != binding.get("manifest_record_sha256")
            or entry.get("root") != str(EXPECTED_ROOT)
            or entry.get("global_child_id") != "c0084"
            or entry.get("global_child_index") != EXPECTED_CHILD_INDEX
            or entry.get("incident", {}).get("deterministic_attempts")
            != binding.get("base_attempts")
        ):
            raise C0084RecoveryGuardError("quarantine manifest no longer binds c0084")
        return path, digest, manifest, dict(entry)
    except quarantine.QuarantineGuardError as exc:
        raise C0084RecoveryGuardError(str(exc)) from exc
    finally:
        quarantine._close_path(held)


def close(held: HeldRecoveryGuard | None) -> None:
    if held is None:
        return
    for record in reversed(list(held.records.values())):
        quarantine._close_path(record)
    quarantine.close(held.quarantine_guard)
    quarantine._close_path(held.admission)


def acquire(
    admission_path: Path, admission_sha256: str,
) -> HeldRecoveryGuard:
    admission_held: quarantine.HeldPath | None = None
    quarantine_held: quarantine.HeldQuarantine | None = None
    records: dict[str, quarantine.HeldPath] = {}
    result: HeldRecoveryGuard | None = None
    try:
        admission_held, admission = _load_admission(
            admission_path, admission_sha256,
        )
        qpath, qdigest, qmanifest, qentry = _load_quarantine_binding(admission)
        try:
            quarantine_held = quarantine.acquire(
                qpath, qdigest, EXPECTED_ENTRY_ID,
            )
        except quarantine.QuarantineBusyError as exc:
            raise C0084RecoveryBusyError(
                "c0084 hierarchy lock is exclusively busy; current action was not interrupted"
            ) from exc
        _FAULT_HOOK("after_shared_lock", EXPECTED_ROOT)
        specs = admission.get("records")
        if type(specs) is not dict or set(specs) != set(REQUIRED_RECORD_PATHS):
            raise C0084RecoveryGuardError("bound legacy record set is incomplete")
        values: dict[str, dict[str, Any]] = {}
        for role in REQUIRED_RECORD_PATHS:
            records[role], values[role] = _open_record(
                quarantine_held.root, specs[role], role=role,
            )
        stale_pids = _validate_record_chain(values)
        declared_pids = _validate_stale_processes(
            admission.get("stale_processes"), stale_pids,
        )
        solver_process = next(
            item for item in admission["stale_processes"]
            if item["role"] == "solver"
        )
        if solver_process["proc_start_ticks"] != values[
            "controller_start"
        ]["proc_start_ticks"]:
            raise C0084RecoveryGuardError("solver start ticks changed")
        for pid in declared_pids:
            _pid_absent(pid)
        _validate_incident(admission.get("incident"), qmanifest, qentry)
        quarantine._assert_absent(quarantine_held.root, REQUIRED_ABSENT)
        result = HeldRecoveryGuard(
            admission_held, quarantine_held, records, declared_pids,
        )
        replay(result)
        return result
    except BaseException:
        if result is not None:
            close(result)
        else:
            for record in reversed(list(records.values())):
                quarantine._close_path(record)
            quarantine.close(quarantine_held)
            quarantine._close_path(admission_held)
        raise


def replay(held: HeldRecoveryGuard) -> None:
    quarantine._replay_path(held.admission)
    quarantine.replay(held.quarantine_guard)
    for role, record in held.records.items():
        quarantine._replay_relative(
            held.quarantine_guard.root, record, REQUIRED_RECORD_PATHS[role],
        )
    for pid in held.stale_pids:
        _pid_absent(pid)
    quarantine._assert_absent(held.quarantine_guard.root, REQUIRED_ABSENT)


def _notify_ready(held: HeldRecoveryGuard) -> None:
    address = os.environ.get("NOTIFY_SOCKET")
    if not address:
        raise C0084RecoveryGuardError("systemd notify socket is absent")
    if address.startswith("@"):
        address = "\0" + address[1:]
    channel = socket.socket(socket.AF_UNIX, socket.SOCK_DGRAM | socket.SOCK_CLOEXEC)
    try:
        channel.connect(address)
        channel.sendall(
            b"READY=1\nSTATUS=c0084 inactive-checker-crash root held shared; "
            b"legacy exclusive retries fenced\n"
        )
    except OSError as exc:
        raise C0084RecoveryGuardError("cannot notify systemd after guard replay") from exc
    finally:
        channel.close()


def hold(
    admission_path: Path, admission_sha256: str, *, replay_seconds: float = 1.0,
) -> None:
    if (
        type(replay_seconds) not in {int, float}
        or not 0.1 <= float(replay_seconds) <= 60.0
    ):
        raise C0084RecoveryGuardError("guard replay interval is unsafe")
    held = acquire(admission_path, admission_sha256)
    try:
        replay(held)
        _notify_ready(held)
        while True:
            time.sleep(float(replay_seconds))
            replay(held)
    finally:
        close(held)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--admission", required=True, type=Path)
    parser.add_argument("--admission-sha256", required=True)
    parser.add_argument("--replay-seconds", type=float, default=1.0)
    parser.add_argument("--version", action="version", version=GATE)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    hold(
        args.admission, args.admission_sha256,
        replay_seconds=args.replay_seconds,
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except C0084RecoveryBusyError as exc:
        print(f"BUSY: {exc}", file=sys.stderr)
        raise SystemExit(EX_TEMPFAIL)
    except (
        C0084RecoveryGuardError, quarantine.QuarantineGuardError,
        OSError, ValueError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
