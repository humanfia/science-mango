#!/usr/bin/env python3
"""Observe a running batch, then build immutable adaptive-v5 materials.

``observe`` takes a short, lock-protected observation of the four RUNNING
generation identities and publishes an operator-only current-generation age
receipt.  It is not cumulative solver timing and makes no timeout claim.
``build`` consumes that exact receipt only after action 000006 has
checkpoint-stopped the same generations.  It exact-loads externally pinned
sources, lets switch-v3 replay the stopped old batch, builds four one-variable
overlays, atomically reserves a fresh output directory, and publishes COMMIT
last.  The directory is visible before completion; without a valid COMMIT it
is not material and must never be resumed, reused, or completed in place.

Neither command acquires a launch lease, retires an old entrypoint, or starts
a solver.  The result is not launch authority or a scientific certificate.
Every new root must still pass v5 ``prepare``; all eight first launches
still require the switch-v3 atomic lease.  If publication fails, use a new
unique output path; consumers accept only a fully verified COMMIT, self-hash,
and exact inventory.
"""

from __future__ import annotations

import argparse
import datetime as dt
import decimal
import hashlib
import json
import math
import os
import stat
import sys
import time
import types
import uuid
from collections.abc import Mapping, Sequence
from pathlib import Path, PurePosixPath
from typing import Any


PROJECT = Path(__file__).resolve().parent.parent
SWITCH_V3_RELATIVE = Path(
    "scripts/paper400_dic5_adaptive_switch_evidence_v3.py"
)
SWITCH_V2_RELATIVE = Path(
    "scripts/paper400_dic5_adaptive_switch_evidence_v2.py"
)
OVERLAY_V2_RELATIVE = Path(
    "investigations/paper400_dic5_adaptive_leaf_overlay_v2.py"
)
ADAPTIVE_V2_MODULE = "investigations.paper400_dic5_adaptive_cnc_v2"
SCHEMA_VERSION = 1
RECEIPT_KIND = "paper400-dic5-adaptive-elapsed-operator-receipt-v1"
OBSERVATION_BUNDLE_KIND = "paper400-dic5-adaptive-observation-bundle-v1"
BUNDLE_KIND = "paper400-dic5-adaptive-child-material-bundle-v1"
PLAN_KIND = "paper400-dic5-adaptive-v5-prepare-plan-v1"
AUTHORITY = "CANDIDATE_ONLY_ATOMIC_LEASE_REQUIRED"
LANE_COUNT = 4
DESCENDANT_COUNT = 2
TARGET_KEYS = tuple(
    (lane, descendant)
    for descendant in range(DESCENDANT_COUNT)
    for lane in range(LANE_COUNT)
)
ACTION_SEQUENCE = 6
OBSERVATION_ACTION_SEQUENCE = 5
PROOF_MAX_BYTES = 64 << 30
MAX_SOURCE_BYTES = 16 << 20
MAX_JSON_BYTES = 1 << 30
HASH_CHUNK_BYTES = 1 << 20


RECEIPT_FIELDS = frozenset({
    "schema_version", "kind", "batch_root", "batch_manifest_sha256",
    "observation_action_sequence", "observation_action_result_sha256",
    "timeout_seconds", "elapsed_seconds_by_lane",
    "elapsed_seconds_json_sha256", "annotation_source", "timed_out",
    "hardness_only", "measurement_method", "boot_id_sha256",
    "clock_ticks_per_second", "proc_uptime_seconds_decimal",
    "clock_boottime_seconds_decimal",
    "sample_utc_before", "sample_utc_after", "observer_source_sha256",
    "switch_v3_source_sha256", "switch_v2_source_sha256", "lanes",
    "authenticated", "launch_authorized", "scientific_claim",
    "record_sha256",
})
RECEIPT_LANE_FIELDS = frozenset({
    "lane_index", "global_leaf_index", "session_sha256",
    "resume_lane_outcome_sha256", "active_generation", "pid",
    "proc_start_ticks", "active_manifest_sha256",
    "current_generation_elapsed_upper_bound_seconds_decimal",
    "conservative_elapsed_seconds",
})


class AdaptiveMaterialBuildError(RuntimeError):
    """A source, receipt, old action, overlay, or publication is invalid."""


_BUILDER_SOURCE_PATH = Path(__file__).resolve(strict=True)


def _is_sha256(value: Any) -> bool:
    return (
        type(value) is str and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


def _require_sha256(value: Any, label: str) -> str:
    if not _is_sha256(value):
        raise AdaptiveMaterialBuildError(f"{label} is not a SHA-256")
    return value


def _canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
        allow_nan=False,
    ).encode("ascii")


def _canonical_sha256(value: Any) -> str:
    return hashlib.sha256(_canonical_bytes(value)).hexdigest()


def _seal(value: Mapping[str, Any]) -> dict[str, Any]:
    result = dict(value)
    if "record_sha256" in result:
        raise AdaptiveMaterialBuildError("record already has a self-hash")
    result["record_sha256"] = _canonical_sha256(result)
    return result


def _selfhash_valid(value: Any) -> bool:
    if type(value) is not dict or not _is_sha256(value.get("record_sha256")):
        return False
    unsigned = dict(value)
    stored = unsigned.pop("record_sha256")
    return _canonical_sha256(unsigned) == stored


def _stat_identity(info: os.stat_result) -> tuple[int, ...]:
    return (
        int(info.st_dev), int(info.st_ino), int(info.st_mode),
        int(info.st_uid), int(info.st_gid), int(info.st_nlink),
        int(info.st_size), int(info.st_mtime_ns), int(info.st_ctime_ns),
    )


def _stable_bytes(path: Path, *, cap: int, owned: bool = True) -> bytes:
    candidate = Path(path)
    try:
        lexical = candidate.lstat()
        resolved = candidate.resolve(strict=True)
    except (FileNotFoundError, OSError, RuntimeError) as exc:
        raise AdaptiveMaterialBuildError(f"cannot resolve {candidate}") from exc
    if (
        stat.S_ISLNK(lexical.st_mode) or not stat.S_ISREG(lexical.st_mode)
        or lexical.st_nlink != 1 or lexical.st_size > cap
        or (owned and lexical.st_uid != os.geteuid())
    ):
        raise AdaptiveMaterialBuildError(f"unsafe or oversized file: {candidate}")
    fd = os.open(resolved, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    chunks: list[bytes] = []
    observed = 0
    try:
        before = os.fstat(fd)
        if _stat_identity(before) != _stat_identity(lexical):
            raise AdaptiveMaterialBuildError("file changed before open")
        while True:
            chunk = os.read(fd, min(HASH_CHUNK_BYTES, cap + 1 - observed))
            if not chunk:
                break
            chunks.append(chunk)
            observed += len(chunk)
            if observed > cap:
                raise AdaptiveMaterialBuildError("file exceeded cap")
        after = os.fstat(fd)
    finally:
        os.close(fd)
    if _stat_identity(before) != _stat_identity(after) or observed != before.st_size:
        raise AdaptiveMaterialBuildError("file changed while reading")
    return b"".join(chunks)


_BUILDER_SOURCE_PAYLOAD = _stable_bytes(
    _BUILDER_SOURCE_PATH, cap=MAX_SOURCE_BYTES,
)

def _strict_json(value: Any) -> None:
    if value is None or type(value) in (bool, int, str):
        return
    if type(value) is float:
        if not math.isfinite(value):
            raise AdaptiveMaterialBuildError("JSON contains a non-finite float")
        return
    if type(value) is list:
        for item in value:
            _strict_json(item)
        return
    if type(value) is dict:
        if any(type(key) is not str for key in value):
            raise AdaptiveMaterialBuildError("JSON object key is not a string")
        for item in value.values():
            _strict_json(item)
        return
    raise AdaptiveMaterialBuildError("JSON contains a non-plain value")


def _read_json(path: Path, *, cap: int = MAX_JSON_BYTES) -> dict[str, Any]:
    payload = _stable_bytes(path, cap=cap)
    try:
        value = json.loads(payload)
    except (json.JSONDecodeError, UnicodeDecodeError) as exc:
        raise AdaptiveMaterialBuildError(f"invalid JSON: {path}") from exc
    if type(value) is not dict:
        raise AdaptiveMaterialBuildError(f"JSON is not an object: {path}")
    _strict_json(value)
    if payload not in {_canonical_bytes(value), _canonical_bytes(value) + b"\n"}:
        raise AdaptiveMaterialBuildError(f"JSON is not canonical: {path}")
    return value


def _read_float_file(path: Path) -> tuple[list[float], bytes]:
    payload = _stable_bytes(path, cap=4096)
    try:
        value = json.loads(payload)
    except (json.JSONDecodeError, UnicodeDecodeError) as exc:
        raise AdaptiveMaterialBuildError("elapsed JSON is invalid") from exc
    if (
        type(value) is not list or len(value) != LANE_COUNT
        or any(
            type(item) is not float or not math.isfinite(item) or item < 0
            or not item.is_integer() or item > float(1 << 53)
            for item in value
        )
    ):
        raise AdaptiveMaterialBuildError(
            "elapsed JSON must contain four nonnegative exact integer floats"
        )
    canonical = _canonical_bytes(value) + b"\n"
    if payload != canonical:
        raise AdaptiveMaterialBuildError(
            "elapsed JSON must be canonical ASCII with one trailing newline"
        )
    return value, payload


def _read_kernel_bytes(path: Path, *, cap: int) -> bytes:
    fd = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    chunks: list[bytes] = []
    observed = 0
    try:
        before = os.fstat(fd)
        if not stat.S_ISREG(before.st_mode) or before.st_uid != 0:
            raise AdaptiveMaterialBuildError(f"unsafe kernel file: {path}")
        while True:
            chunk = os.read(fd, min(4096, cap + 1 - observed))
            if not chunk:
                break
            chunks.append(chunk)
            observed += len(chunk)
            if observed > cap:
                raise AdaptiveMaterialBuildError(f"oversized kernel file: {path}")
        after = os.fstat(fd)
    finally:
        os.close(fd)
    stable_fields = ("st_dev", "st_ino", "st_mode", "st_uid", "st_gid", "st_nlink")
    if any(getattr(before, field) != getattr(after, field) for field in stable_fields):
        raise AdaptiveMaterialBuildError(f"kernel file identity changed: {path}")
    return b"".join(chunks)


def _boot_id_sha256() -> str:
    payload = _read_kernel_bytes(
        Path("/proc/sys/kernel/random/boot_id"), cap=128,
    )
    try:
        value = payload.decode("ascii").strip()
        parsed = uuid.UUID(value)
    except (UnicodeDecodeError, ValueError) as exc:
        raise AdaptiveMaterialBuildError("kernel boot id is malformed") from exc
    if str(parsed) != value:
        raise AdaptiveMaterialBuildError("kernel boot id is not canonical")
    return hashlib.sha256(payload).hexdigest()


def _decimal_text(value: decimal.Decimal) -> str:
    if not value.is_finite() or value < 0:
        raise AdaptiveMaterialBuildError("elapsed decimal is invalid")
    text = format(value, "f")
    if "." in text:
        text = text.rstrip("0").rstrip(".")
    return text or "0"


def _parse_decimal_text(value: Any, label: str) -> decimal.Decimal:
    if type(value) is not str:
        raise AdaptiveMaterialBuildError(f"{label} is not a decimal string")
    try:
        parsed = decimal.Decimal(value)
    except decimal.InvalidOperation as exc:
        raise AdaptiveMaterialBuildError(f"{label} is invalid") from exc
    if _decimal_text(parsed) != value:
        raise AdaptiveMaterialBuildError(f"{label} is not canonical")
    return parsed


def _generation_elapsed(
    uptime: decimal.Decimal, start_ticks: int, clock_ticks: int,
) -> decimal.Decimal:
    with decimal.localcontext() as context:
        context.prec = 80
        observed = uptime - (
            decimal.Decimal(start_ticks) / decimal.Decimal(clock_ticks)
        )
    if not observed.is_finite() or observed < 0:
        raise AdaptiveMaterialBuildError("process start time exceeds uptime")
    return observed


def _generation_elapsed_upper_bound(
    boottime: decimal.Decimal, start_ticks: int, clock_ticks: int,
) -> decimal.Decimal:
    with decimal.localcontext() as context:
        context.prec = 80
        return _generation_elapsed(
            boottime, start_ticks, clock_ticks,
        ) + decimal.Decimal(1) / decimal.Decimal(clock_ticks)


def _parse_utc(value: Any, label: str) -> dt.datetime:
    if type(value) is not str or not value.endswith("Z"):
        raise AdaptiveMaterialBuildError(f"{label} is not canonical UTC")
    try:
        parsed = dt.datetime.fromisoformat(value[:-1] + "+00:00")
    except ValueError as exc:
        raise AdaptiveMaterialBuildError(f"{label} is invalid") from exc
    if (
        parsed.tzinfo != dt.timezone.utc
        or parsed.strftime("%Y-%m-%dT%H:%M:%S.%fZ") != value
    ):
        raise AdaptiveMaterialBuildError(f"{label} is not canonical UTC")
    return parsed


def _validate_receipt(
    receipt: Any, *, batch_root: Path, batch_pin: str,
    observation_result_pin: str, timeout_seconds: float,
    elapsed: Sequence[float], elapsed_payload: bytes,
    expected_switch_v3_source_sha256: str,
    expected_switch_v2_source_sha256: str,
) -> dict[str, Any]:
    expected_builder_source = hashlib.sha256(_BUILDER_SOURCE_PAYLOAD).hexdigest()
    current_clock_ticks = os.sysconf("SC_CLK_TCK")
    if type(current_clock_ticks) is not int or current_clock_ticks <= 0:
        raise AdaptiveMaterialBuildError("SC_CLK_TCK is invalid")
    if (
        type(receipt) is not dict or set(receipt) != RECEIPT_FIELDS
        or not _selfhash_valid(receipt)
        or receipt.get("schema_version") != SCHEMA_VERSION
        or receipt.get("kind") != RECEIPT_KIND
        or receipt.get("batch_root") != str(batch_root)
        or receipt.get("batch_manifest_sha256") != batch_pin
        or receipt.get("observation_action_sequence")
        != OBSERVATION_ACTION_SEQUENCE
        or receipt.get("observation_action_result_sha256")
        != observation_result_pin
        or type(receipt.get("timeout_seconds")) is not float
        or receipt.get("timeout_seconds") != timeout_seconds
        or type(receipt.get("elapsed_seconds_by_lane")) is not list
        or any(
            type(item) is not float
            for item in receipt.get("elapsed_seconds_by_lane", [])
        )
        or receipt.get("elapsed_seconds_by_lane") != list(elapsed)
        or receipt.get("elapsed_seconds_json_sha256")
        != hashlib.sha256(elapsed_payload).hexdigest()
        or receipt.get("annotation_source")
        != "operator-annotation-not-solver-result-v2"
        or receipt.get("timed_out") is not False
        or receipt.get("hardness_only") is not True
        or receipt.get("measurement_method")
        != (
            "operator-current-generation-clock-boottime-plus-one-tick-"
            "conservative-ceil-v1"
        )
        or receipt.get("boot_id_sha256") != _boot_id_sha256()
        or receipt.get("clock_ticks_per_second") != current_clock_ticks
        or receipt.get("observer_source_sha256") != expected_builder_source
        or receipt.get("switch_v3_source_sha256")
        != expected_switch_v3_source_sha256
        or receipt.get("switch_v2_source_sha256")
        != expected_switch_v2_source_sha256
        or receipt.get("authenticated") is not False
        or receipt.get("launch_authorized") is not False
        or receipt.get("scientific_claim") is not False
    ):
        raise AdaptiveMaterialBuildError("measurement receipt binding mismatch")
    before = _parse_utc(receipt.get("sample_utc_before"), "sample start UTC")
    after = _parse_utc(receipt.get("sample_utc_after"), "sample end UTC")
    if after < before:
        raise AdaptiveMaterialBuildError("measurement UTC interval is negative")
    proc_uptime = _parse_decimal_text(
        receipt.get("proc_uptime_seconds_decimal"), "proc uptime",
    )
    boottime = _parse_decimal_text(
        receipt.get("clock_boottime_seconds_decimal"), "clock boottime",
    )
    if abs(proc_uptime - boottime) > decimal.Decimal(1):
        raise AdaptiveMaterialBuildError(
            "proc uptime and CLOCK_BOOTTIME observation diverge"
        )
    lanes = receipt.get("lanes")
    if type(lanes) is not list or len(lanes) != LANE_COUNT:
        raise AdaptiveMaterialBuildError("measurement receipt lane count mismatch")
    for index, lane in enumerate(lanes):
        if type(lane) is not dict or set(lane) != RECEIPT_LANE_FIELDS:
            raise AdaptiveMaterialBuildError("measurement lane schema mismatch")
        if (
            lane.get("lane_index") != index
            or type(lane.get("global_leaf_index")) is not int
            or lane["global_leaf_index"] < 0
            or not _is_sha256(lane.get("session_sha256"))
            or not _is_sha256(lane.get("resume_lane_outcome_sha256"))
            or type(lane.get("active_generation")) is not int
            or lane["active_generation"] < 0
            or type(lane.get("pid")) is not int or lane["pid"] <= 0
            or type(lane.get("proc_start_ticks")) is not int
            or lane["proc_start_ticks"] <= 0
            or not _is_sha256(lane.get("active_manifest_sha256"))
            or type(lane.get("conservative_elapsed_seconds")) is not float
            or not math.isfinite(lane["conservative_elapsed_seconds"])
            or lane["conservative_elapsed_seconds"] < 0
            or not lane["conservative_elapsed_seconds"].is_integer()
            or lane["conservative_elapsed_seconds"] > float(1 << 53)
        ):
            raise AdaptiveMaterialBuildError("measurement lane value malformed")
        observed = _parse_decimal_text(
            lane["current_generation_elapsed_upper_bound_seconds_decimal"],
            "current generation elapsed upper bound",
        )
        expected_observed = _generation_elapsed_upper_bound(
            boottime, lane["proc_start_ticks"], current_clock_ticks,
        )
        conservative = int(
            observed.to_integral_value(rounding=decimal.ROUND_CEILING)
        )
        if (
            observed != expected_observed
            or conservative > (1 << 53)
            or lane["conservative_elapsed_seconds"] != float(conservative)
        ):
            raise AdaptiveMaterialBuildError(
                "measurement lane is not the reproducible conservative ceil"
            )
        if lane["conservative_elapsed_seconds"] != elapsed[index]:
            raise AdaptiveMaterialBuildError("measurement lane/elapsed file mismatch")
    return dict(receipt)


def _canonical_root(path: Path, *, label: str) -> Path:
    candidate = Path(path)
    if not candidate.is_absolute() or str(candidate) != os.path.abspath(str(candidate)):
        raise AdaptiveMaterialBuildError(f"{label} must be normalized absolute")
    try:
        lexical = candidate.lstat()
        resolved = candidate.resolve(strict=True)
    except (FileNotFoundError, OSError, RuntimeError) as exc:
        raise AdaptiveMaterialBuildError(f"cannot resolve {label}") from exc
    if (
        resolved != candidate or stat.S_ISLNK(lexical.st_mode)
        or not stat.S_ISDIR(lexical.st_mode) or lexical.st_uid != os.geteuid()
        or stat.S_IMODE(lexical.st_mode) != 0o700
    ):
        raise AdaptiveMaterialBuildError(f"{label} must be owned canonical mode-0700")
    return candidate


def _new_bundle_path(path: Path) -> tuple[Path, Path]:
    target = Path(path)
    if not target.is_absolute() or str(target) != os.path.abspath(str(target)):
        raise AdaptiveMaterialBuildError("output directory must be normalized absolute")
    if target.exists() or target.is_symlink():
        raise AdaptiveMaterialBuildError("output directory already exists")
    parent = _canonical_root(target.parent, label="output parent")
    return target, parent


def _load_exact_switch_v3(
    expected_sha256: str, expected_v2_sha256: str,
) -> tuple[Any, dict[str, Any], dict[str, Any]]:
    expected = _require_sha256(expected_sha256, "switch-v3 source pin")
    expected_v2 = _require_sha256(
        expected_v2_sha256, "switch-v2 source pin",
    )
    path = (PROJECT / SWITCH_V3_RELATIVE).resolve(strict=True)
    v2_path = (PROJECT / SWITCH_V2_RELATIVE).resolve(strict=True)
    payload = _stable_bytes(path, cap=MAX_SOURCE_BYTES)
    v2_payload = _stable_bytes(v2_path, cap=MAX_SOURCE_BYTES)
    digest = hashlib.sha256(payload).hexdigest()
    v2_digest = hashlib.sha256(v2_payload).hexdigest()
    if digest != expected:
        raise AdaptiveMaterialBuildError("switch-v3 source pin mismatch before exec")
    if v2_digest != expected_v2:
        raise AdaptiveMaterialBuildError("switch-v2 source pin mismatch before exec")
    name = f"_paper400_material_switch_v3_{digest}"
    module = types.ModuleType(name)
    module.__file__ = str(path)
    module.__package__ = "scripts"
    module.__loader__ = None
    sys.modules[name] = module
    try:
        exec(compile(payload, str(path), "exec", dont_inherit=True), module.__dict__)
    except BaseException:
        sys.modules.pop(name, None)
        raise
    source = getattr(module, "_V3_SOURCE_RECORD", None)
    base_source = getattr(module, "_BASE_SOURCE_RECORD", None)
    if (
        type(source) is not dict or source.get("sha256") != digest
        or type(base_source) is not dict
        or base_source.get("sha256") != v2_digest
        or base_source.get("relative_path") != SWITCH_V2_RELATIVE.as_posix()
        or _stable_bytes(v2_path, cap=MAX_SOURCE_BYTES) != v2_payload
        or getattr(module, "TARGET_KEYS", None) != TARGET_KEYS
    ):
        sys.modules.pop(name, None)
        raise AdaptiveMaterialBuildError("switch-v3 exact execution binding mismatch")
    return module, {
        "role": "adaptive_switch_evidence_v3_source",
        "relative_path": SWITCH_V3_RELATIVE.as_posix(),
        "sha256": digest, "bytes": len(payload),
        "execution": "compile-exact-source-bytes-material-builder-v1",
    }, dict(base_source)


def _load_exact_sources(
    *, expected_switch_v3_sha256: str, expected_switch_v2_sha256: str,
    expected_overlay_v2_sha256: str, expected_adaptive_v2_sha256: str,
) -> tuple[Any, Any, dict[str, Any]]:
    overlay_pin = _require_sha256(
        expected_overlay_v2_sha256, "overlay-v2 source pin",
    )
    adaptive_pin = _require_sha256(
        expected_adaptive_v2_sha256, "adaptive-v2 source pin",
    )
    overlay_path = (PROJECT / OVERLAY_V2_RELATIVE).resolve(strict=True)
    adaptive_path = PROJECT.joinpath(
        *ADAPTIVE_V2_MODULE.split("."),
    ).with_suffix(".py").resolve(strict=True)
    if hashlib.sha256(_stable_bytes(
        overlay_path, cap=MAX_SOURCE_BYTES,
    )).hexdigest() != overlay_pin:
        raise AdaptiveMaterialBuildError("overlay-v2 source pin mismatch before exec")
    if hashlib.sha256(_stable_bytes(
        adaptive_path, cap=MAX_SOURCE_BYTES,
    )).hexdigest() != adaptive_pin:
        raise AdaptiveMaterialBuildError("adaptive-v2 source pin mismatch before exec")
    switch, switch_record, switch_v2_record = _load_exact_switch_v3(
        expected_switch_v3_sha256, expected_switch_v2_sha256,
    )
    overlay, overlay_record, executed = switch._load_overlay_exact()
    if overlay_record.get("sha256") != _require_sha256(
        expected_overlay_v2_sha256, "overlay-v2 source pin"
    ):
        raise AdaptiveMaterialBuildError("overlay-v2 source pin mismatch")
    adaptive_records = [
        record for record in executed
        if record.get("module") == ADAPTIVE_V2_MODULE
    ]
    if (
        len(adaptive_records) != 1
        or adaptive_records[0].get("sha256") != _require_sha256(
            expected_adaptive_v2_sha256, "adaptive-v2 source pin"
        )
        or getattr(overlay, "adaptive", None) is None
    ):
        raise AdaptiveMaterialBuildError("adaptive-v2 exact source pin mismatch")
    return switch, overlay, _seal({
        "schema_version": SCHEMA_VERSION,
        "method": "externally-pinned-exact-source-execution-v1",
        "sources": [
            switch_record, switch_v2_record, dict(overlay_record),
            adaptive_records[0],
        ],
    })


def _reject_action_publish_temporaries(batch_root: Path) -> None:
    actions = batch_root / "actions"
    for action_dir in actions.iterdir():
        if action_dir.is_symlink() or not action_dir.is_dir():
            raise AdaptiveMaterialBuildError("old action directory is unsafe")
        for entry in action_dir.iterdir():
            if entry.name.startswith(".") and ".publish-" in entry.name:
                raise AdaptiveMaterialBuildError(
                    "old action has a publication temporary; run audited recovery first"
                )


def _running_lane_state(
    child: Any, lane_root: Path, session: Mapping[str, Any],
    caps: Mapping[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    chain = child.validate_transport_chain(
        lane_root, session, caps, requirement=child.CHAIN_REQUIRE_STATUS,
    )
    with child._fixed_environment():
        inspection = child.controller.inspect(
            lane_root / child.RUNTIME_ROOT, verify_hashes=True,
        )
    generations = chain.get("generations")
    inspected = inspection.get("generations")
    latest = generations[-1] if type(generations) is list and generations else None
    active = inspected[-1] if type(inspected) is list and inspected else None
    if (
        chain.get("state") != "RUNNING"
        or type(latest) is not dict
        or latest.get("pid_identity_alive") is not True
        or type(active) is not dict
        or inspection.get("state") != "RUNNING"
        or inspection.get("hash_verification_requested") is not True
        or active.get("pid_identity_alive") is not True
        or active.get("checkpointed") is not False
        or active.get("poison_claim") is not None
        or active.get("active_error") is not None
        or active.get("checkpoint_error") is not None
        or active.get("generation") != latest.get("generation")
        or active.get("active_manifest_sha256")
        != latest.get("active_manifest_sha256")
        or active.get("pid_identity_alive") != latest.get("pid_identity_alive")
    ):
        raise AdaptiveMaterialBuildError("lane is not a fresh verified RUNNING peer")
    return chain, inspection


def _running_snapshot_locked(
    root: Path, coordinator: Any, child: Any,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    _reject_action_publish_temporaries(root)
    loaded = coordinator._load_batch(root, instance=None, strict_base=True)
    manifest = loaded.get("manifest")
    if type(manifest) is not dict:
        raise AdaptiveMaterialBuildError("legacy replay returned no batch manifest")
    completed, incomplete = coordinator._action_directories(root, manifest)
    if (
        incomplete is not None or type(completed) is not list
        or len(completed) != OBSERVATION_ACTION_SEQUENCE + 1
    ):
        raise AdaptiveMaterialBuildError(
            "observation requires exactly completed actions 000000..000005"
        )
    previous: str | None = None
    latest_claim: dict[str, Any] | None = None
    latest_outcomes: list[dict[str, Any]] | None = None
    latest_result: dict[str, Any] | None = None
    for sequence, action_dir in enumerate(completed):
        claim = coordinator._read_action_claim(
            action_dir / "claim.json", root=root, manifest=manifest,
            sequence=sequence, previous_sha=previous,
        )
        outcomes = [
            coordinator._read_lane_outcome(
                action_dir / f"lane-{lane['lane_index']}.json",
                lane=lane, action=claim["action"], sequence=sequence,
                claim_sha256=claim["record_sha256"],
            )
            for lane in manifest["lanes"]
        ]
        result = coordinator._read_action_result(
            action_dir / "result.json", root=root, manifest=manifest,
            claim=claim, outcomes=outcomes,
        )
        previous = result["record_sha256"]
        latest_claim, latest_outcomes, latest_result = claim, outcomes, result
    if (
        latest_claim is None or latest_outcomes is None or latest_result is None
        or latest_claim.get("action_sequence") != OBSERVATION_ACTION_SEQUENCE
        or latest_claim.get("action") != "resume"
        or latest_result.get("all_lanes_succeeded") is not True
        or latest_result.get("all_lanes_goal_satisfied") is not True
        or latest_result.get("goal_satisfied_lane_count") != LANE_COUNT
        or latest_result.get("action_history_complete") is not True
    ):
        raise AdaptiveMaterialBuildError("action 000005 is not a completed resume")
    contexts: list[dict[str, Any]] = []
    audit_lanes: list[dict[str, Any]] = []
    for index, lane in enumerate(manifest.get("lanes", [])):
        outcome = latest_outcomes[index]
        lane_root = root / "lanes" / f"lane-{index}"
        if (
            type(lane) is not dict or lane.get("lane_index") != index
            or lane.get("child_root") != str(lane_root)
            or type(outcome) is not dict or outcome.get("lane_index") != index
            or outcome.get("action_sequence") != OBSERVATION_ACTION_SEQUENCE
            or outcome.get("action") != "resume"
            or outcome.get("success") is not True
            or outcome.get("goal_satisfied") is not True
            or outcome.get("transport_state_after") != "RUNNING"
            or outcome.get("child_result_state") != "RUNNING"
            or outcome.get("terminal_claimed_after") is not False
            or outcome.get("terminal_committed_after") is not False
        ):
            raise AdaptiveMaterialBuildError("action 000005 lane mismatch")
        checked = child._action_static_kwargs(
            lane_root, loaded["static_kwargs"],
        )
        child_loaded, session = child._load_session(lane_root, **checked)
        caps = child_loaded["record"]["resource_policy"]
        chain, inspection = _running_lane_state(
            child, lane_root, session, caps,
        )
        generations = chain["generations"]
        latest = generations[-1]
        child_result = outcome.get("child_result")
        if (
            type(child_result) is not dict
            or child_result.get("kind")
            != "paper400-nested-width10-resume-admission-v1"
            or child_result.get("generation") != latest.get("generation")
            or child_result.get("session_sha256")
            != session.get("record_sha256")
            or child_result.get("resume_manifest_sha256")
            != latest.get("active_manifest_sha256")
            or child_result.get("root") != str(lane_root)
            or session.get("resume_static_sha256")
            != lane.get("resume_static_sha256")
            or (lane_root / child.TERMINAL_CLAIM).exists()
            or (lane_root / child.FINAL_COMMIT).exists()
        ):
            raise AdaptiveMaterialBuildError("running lane/session/action mismatch")
        audit = {
            "lane_index": index,
            "global_leaf_index": lane["global_leaf_index"],
            "session_sha256": session["record_sha256"],
            "resume_lane_outcome_sha256": outcome["record_sha256"],
            "active_generation": latest["generation"],
            "pid": latest["pid"],
            "proc_start_ticks": latest["proc_start_ticks"],
            "active_manifest_sha256": latest["active_manifest_sha256"],
        }
        contexts.append({
            "root": lane_root, "session": session, "caps": caps,
            "chain": chain, "inspection": inspection, "audit": audit,
        })
        audit_lanes.append(audit)
    if len(contexts) != LANE_COUNT:
        raise AdaptiveMaterialBuildError("running batch lane count mismatch")
    return {
        "manifest": manifest,
        "observation_claim": latest_claim,
        "observation_result": latest_result,
        "observation_lanes": latest_outcomes,
        "lanes": audit_lanes,
    }, contexts


def _proc_stat_identity(pid: int) -> dict[str, Any]:
    if type(pid) is not int or pid <= 0:
        raise AdaptiveMaterialBuildError("PID is invalid")
    try:
        payload = _read_kernel_bytes(Path(f"/proc/{pid}/stat"), cap=1 << 16)
    except (FileNotFoundError, ProcessLookupError) as exc:
        raise AdaptiveMaterialBuildError(f"process disappeared: {pid}") from exc
    opening = payload.find(b" (")
    closing = payload.rfind(b")")
    if opening <= 0 or closing <= opening:
        raise AdaptiveMaterialBuildError("malformed /proc PID stat")
    try:
        recorded_pid = int(payload[:opening])
        fields = payload[closing + 2:].decode("ascii").split()
        state = fields[0]
        start_ticks = int(fields[19])
    except (UnicodeDecodeError, ValueError, IndexError) as exc:
        raise AdaptiveMaterialBuildError("malformed /proc PID stat fields") from exc
    if (
        recorded_pid != pid or len(state) != 1 or state in {"Z", "X", "x"}
        or start_ticks <= 0
    ):
        raise AdaptiveMaterialBuildError("process identity is not live")
    return {"pid": pid, "state": state, "proc_start_ticks": start_ticks}


def _parse_proc_uptime_payload(payload: bytes) -> decimal.Decimal:
    try:
        fields = payload.decode("ascii").strip().split()
    except UnicodeDecodeError as exc:
        raise AdaptiveMaterialBuildError("/proc/uptime is malformed") from exc
    if len(fields) != 2:
        raise AdaptiveMaterialBuildError("/proc/uptime field count mismatch")
    for value in fields:
        pieces = value.split(".")
        if (
            len(pieces) != 2 or not pieces[0] or not pieces[0].isdigit()
            or len(pieces[1]) != 2 or not pieces[1].isdigit()
        ):
            raise AdaptiveMaterialBuildError(
                "/proc/uptime is not fixed-two-decimal kernel format"
            )
    value = decimal.Decimal(fields[0])
    if not value.is_finite() or value < 0:
        raise AdaptiveMaterialBuildError("/proc/uptime is invalid")
    return value


def _proc_uptime() -> decimal.Decimal:
    return _parse_proc_uptime_payload(
        _read_kernel_bytes(Path("/proc/uptime"), cap=256)
    )


def _clock_boottime() -> decimal.Decimal:
    clock = getattr(time, "CLOCK_BOOTTIME", None)
    if type(clock) is not int:
        raise AdaptiveMaterialBuildError("CLOCK_BOOTTIME is unavailable")
    value = time.clock_gettime_ns(clock)
    if type(value) is not int or value < 0:
        raise AdaptiveMaterialBuildError("CLOCK_BOOTTIME sample is invalid")
    return decimal.Decimal(value) / decimal.Decimal(1_000_000_000)


def _utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).strftime(
        "%Y-%m-%dT%H:%M:%S.%fZ"
    )


def _sample_running_processes(
    expected_lanes: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    before = [_proc_stat_identity(lane["pid"]) for lane in expected_lanes]
    for expected, observed in zip(expected_lanes, before, strict=True):
        if (
            observed["pid"] != expected["pid"]
            or observed["proc_start_ticks"] != expected["proc_start_ticks"]
        ):
            raise AdaptiveMaterialBuildError(
                "live PID/start-ticks miss the action/controller replay"
            )
    sample_utc_before = _utc_now()
    boot_id_sha256 = _boot_id_sha256()
    clock_ticks = os.sysconf("SC_CLK_TCK")
    if type(clock_ticks) is not int or clock_ticks <= 0:
        raise AdaptiveMaterialBuildError("SC_CLK_TCK is invalid")
    proc_uptime = _proc_uptime()
    boottime = _clock_boottime()
    if abs(proc_uptime - boottime) > decimal.Decimal(1):
        raise AdaptiveMaterialBuildError(
            "/proc/uptime and CLOCK_BOOTTIME diverge"
        )
    sample_utc_after = _utc_now()
    after = [_proc_stat_identity(lane["pid"]) for lane in expected_lanes]
    if before != after:
        raise AdaptiveMaterialBuildError(
            "live process identity changed during observation"
        )
    elapsed: list[float] = []
    lane_observations: list[dict[str, Any]] = []
    for expected in expected_lanes:
        observed = _generation_elapsed_upper_bound(
            boottime, expected["proc_start_ticks"], clock_ticks,
        )
        conservative = int(
            observed.to_integral_value(rounding=decimal.ROUND_CEILING)
        )
        if conservative > (1 << 53):
            raise AdaptiveMaterialBuildError("observed elapsed exceeds exact-float range")
        elapsed.append(float(conservative))
        lane_observations.append({
            **dict(expected),
            "current_generation_elapsed_upper_bound_seconds_decimal": (
                _decimal_text(observed)
            ),
            "conservative_elapsed_seconds": float(conservative),
        })
    return {
        "sample_utc_before": sample_utc_before,
        "sample_utc_after": sample_utc_after,
        "boot_id_sha256": boot_id_sha256,
        "clock_ticks_per_second": clock_ticks,
        "proc_uptime_seconds_decimal": _decimal_text(proc_uptime),
        "clock_boottime_seconds_decimal": _decimal_text(boottime),
        "elapsed_seconds_by_lane": elapsed,
        "lanes": lane_observations,
        "proc_identities": before,
    }


def _reverify_running_snapshot(
    child: Any, contexts: Sequence[Mapping[str, Any]],
    sampled: Mapping[str, Any],
) -> None:
    if len(contexts) != LANE_COUNT:
        raise AdaptiveMaterialBuildError("running context count mismatch")
    for context, proc_identity in zip(
        contexts, sampled["proc_identities"], strict=True,
    ):
        chain, inspection = _running_lane_state(
            child, context["root"], context["session"], context["caps"],
        )
        if (
            not child.static_v1.json_type_equal(chain, context["chain"])
            or not child.static_v1.json_type_equal(
                inspection, context["inspection"],
            )
            or _proc_stat_identity(context["audit"]["pid"]) != proc_identity
        ):
            raise AdaptiveMaterialBuildError(
                "lane/controller/process changed after observation"
            )


def _action_000006(
    switch: Any, batch_root: Path, *, expected_batch_pin: str,
) -> tuple[
    dict[str, Any], dict[str, Any], list[dict[str, Any]],
    dict[str, Any], list[dict[str, Any]],
]:
    base = switch.base
    batch = base._read_json(batch_root / "batch.json")
    claim = base._read_json(batch_root / "actions/000006/claim.json")
    lanes = [
        base._read_json(batch_root / f"actions/000006/lane-{index}.json")
        for index in range(LANE_COUNT)
    ]
    result = base._read_json(batch_root / "actions/000006/result.json")
    previous = base._read_json(batch_root / "actions/000005/result.json")
    previous_lanes = [
        base._read_json(batch_root / f"actions/000005/lane-{index}.json")
        for index in range(LANE_COUNT)
    ]
    if (
        batch.get("record_sha256") != expected_batch_pin
        or previous.get("action_sequence") != OBSERVATION_ACTION_SEQUENCE
        or previous.get("action") != "resume"
        or previous.get("batch_manifest_sha256") != expected_batch_pin
        or previous.get("lane_outcome_sha256s")
        != [lane.get("record_sha256") for lane in previous_lanes]
        or previous.get("all_lanes_succeeded") is not True
        or previous.get("all_lanes_goal_satisfied") is not True
        or previous.get("goal_satisfied_lane_count") != LANE_COUNT
        or previous.get("action_history_complete") is not True
        or [lane.get("lane_index") for lane in previous_lanes]
        != list(range(LANE_COUNT))
        or any(
            lane.get("action_sequence") != OBSERVATION_ACTION_SEQUENCE
            or lane.get("action") != "resume"
            or lane.get("claim_sha256") != previous.get("claim_sha256")
            or lane.get("transport_state_after") != "RUNNING"
            or lane.get("child_result_state") != "RUNNING"
            or lane.get("success") is not True
            or lane.get("goal_satisfied") is not True
            or lane.get("terminal_claimed_after") is not False
            or lane.get("terminal_committed_after") is not False
            for lane in previous_lanes
        )
        or claim.get("action_sequence") != ACTION_SEQUENCE
        or claim.get("action") != "checkpoint-stop"
        or claim.get("batch_manifest_sha256") != expected_batch_pin
        or claim.get("previous_action_result_sha256")
        != previous.get("record_sha256")
        or [lane.get("lane_index") for lane in lanes] != list(range(LANE_COUNT))
        or any(
            lane.get("action_sequence") != ACTION_SEQUENCE
            or lane.get("action") != "checkpoint-stop"
            or lane.get("claim_sha256") != claim.get("record_sha256")
            or lane.get("transport_state_after") != "CHECKPOINTED"
            or lane.get("child_result_state") != "CHECKPOINTED"
            or lane.get("success") is not True
            or lane.get("goal_satisfied") is not True
            or lane.get("terminal_claimed_after") is not False
            or lane.get("terminal_committed_after") is not False
            for lane in lanes
        )
        or result.get("claim_sha256") != claim.get("record_sha256")
        or result.get("previous_action_result_sha256")
        != previous.get("record_sha256")
        or result.get("lane_outcome_sha256s")
        != [lane.get("record_sha256") for lane in lanes]
        or result.get("all_lanes_succeeded") is not True
        or result.get("all_lanes_goal_satisfied") is not True
        or result.get("goal_satisfied_lane_count") != LANE_COUNT
        or result.get("action_history_complete") is not True
    ):
        raise AdaptiveMaterialBuildError("old actions 000005/000006 binding mismatch")
    return batch, result, lanes, previous, previous_lanes


def _json_payload(value: Any) -> bytes:
    return _canonical_bytes(value) + b"\n"


def _file_record(relative: str, role: str, payload: bytes) -> dict[str, Any]:
    return {
        "relative_path": relative, "role": role,
        "sha256": hashlib.sha256(payload).hexdigest(),
        "bytes": len(payload), "mode": 0o600,
    }


def _manifest_hash(value: Mapping[str, Any], label: str) -> str:
    result = value.get("manifest_sha256")
    return _require_sha256(result, f"{label} manifest pin")


def _build_values(
    *, switch: Any, overlay: Any, source_binding: Mapping[str, Any],
    batch_root: Path, output_dir: Path, receipt: Mapping[str, Any],
    receipt_payload: bytes, elapsed: list[float], elapsed_payload: bytes,
    observation_commit: Mapping[str, Any], timeout_seconds: float,
    candidate_variables: Sequence[int],
    expected_batch_manifest_sha256: str,
    expected_switch_v3_source_sha256: str,
    expected_switch_v2_source_sha256: str,
) -> tuple[dict[str, bytes], dict[str, Any]]:
    candidates = list(candidate_variables)
    if (
        len(candidates) != LANE_COUNT
        or any(type(item) is not int or not 1 <= item <= 400 for item in candidates)
    ):
        raise AdaptiveMaterialBuildError(
            "candidate variables must be four physical DIMACS integers"
        )
    _reject_action_publish_temporaries(batch_root)
    (
        batch, action_result, action_lanes,
        observation_result, observation_lanes,
    ) = _action_000006(
        switch, batch_root,
        expected_batch_pin=expected_batch_manifest_sha256,
    )
    validated_receipt = _validate_receipt(
        receipt, batch_root=batch_root,
        batch_pin=expected_batch_manifest_sha256,
        observation_result_pin=observation_result["record_sha256"],
        timeout_seconds=timeout_seconds, elapsed=elapsed,
        elapsed_payload=elapsed_payload,
        expected_switch_v3_source_sha256=(
            expected_switch_v3_source_sha256
        ),
        expected_switch_v2_source_sha256=(
            expected_switch_v2_source_sha256
        ),
    )
    for receipt_lane, stopped, resumed in zip(
        validated_receipt["lanes"], action_lanes, observation_lanes,
        strict=True,
    ):
        resumed_child = resumed.get("child_result")
        chain = stopped.get("child_result")
        if type(chain) is dict and type(chain.get("chain")) is dict:
            chain = chain["chain"]
        generations = chain.get("generations") if type(chain) is dict else None
        latest = (
            generations[-1]
            if type(generations) is list and generations else None
        )
        if (
            type(resumed_child) is not dict
            or resumed.get("record_sha256")
            != receipt_lane["resume_lane_outcome_sha256"]
            or resumed.get("global_leaf_index")
            != receipt_lane["global_leaf_index"]
            or resumed_child.get("session_sha256")
            != receipt_lane["session_sha256"]
            or resumed_child.get("generation")
            != receipt_lane["active_generation"]
            or resumed_child.get("resume_manifest_sha256")
            != receipt_lane["active_manifest_sha256"]
            or type(latest) is not dict
            or chain.get("state") != "CHECKPOINTED"
            or latest.get("generation") != receipt_lane["active_generation"]
            or latest.get("active_manifest_sha256")
            != receipt_lane["active_manifest_sha256"]
            or latest.get("pid") != receipt_lane["pid"]
            or latest.get("proc_start_ticks")
            != receipt_lane["proc_start_ticks"]
            or latest.get("pid_identity_alive") is not False
        ):
            raise AdaptiveMaterialBuildError(
                "measurement receipt misses action000005/stopped process identity"
            )
    switch_record = switch.build_switch_evidence_record(
        batch_root, timeout_seconds=timeout_seconds,
        elapsed_seconds_by_lane=elapsed, strict_base=True,
    )
    history = switch_record.get("action_history", {})
    switch_lanes = switch_record.get("lanes")
    if (
        switch_record.get("batch_manifest_sha256")
        != expected_batch_manifest_sha256
        or history.get("checkpoint_stop_result_sha256")
        != action_result.get("record_sha256")
        or history.get("completed_action_count") != ACTION_SEQUENCE + 1
        or type(history.get("actions")) is not list
        or len(history["actions"]) != ACTION_SEQUENCE + 1
        or history["actions"][-2].get("sequence")
        != OBSERVATION_ACTION_SEQUENCE
        or history["actions"][-2].get("result_sha256")
        != observation_result["record_sha256"]
        or history["actions"][-2].get("lane_outcome_sha256s")
        != [lane["record_sha256"] for lane in observation_lanes]
        or history["actions"][-1].get("sequence") != ACTION_SEQUENCE
        or history["actions"][-1].get("lane_outcome_sha256s")
        != [lane["record_sha256"] for lane in action_lanes]
        or type(switch_lanes) is not list or len(switch_lanes) != LANE_COUNT
    ):
        raise AdaptiveMaterialBuildError("fresh switch replay/action binding mismatch")
    parent = switch.base._read_json(batch_root / "static/parent-manifest.json")
    width6 = switch.base._read_json(batch_root / "static/width6-campaign.json")
    width10 = switch.base._read_json(batch_root / "static/width10-campaign.json")
    if (
        _manifest_hash(parent, "parent") != switch_record["parent_manifest_sha256"]
        or _manifest_hash(width6, "width6") != switch_record["width6_campaign_sha256"]
        or _manifest_hash(width10, "width10") != switch_record["width10_campaign_sha256"]
    ):
        raise AdaptiveMaterialBuildError("campaign material/switch pin mismatch")
    instance = overlay.optimized.build_optimized_instance()
    files: dict[str, bytes] = {
        "batch-manifest.json": _json_payload(batch),
        "parent-manifest.json": _json_payload(parent),
        "width6-campaign.json": _json_payload(width6),
        "width10-campaign.json": _json_payload(width10),
        "measurement-receipt.json": receipt_payload,
        "elapsed-seconds-by-lane.json": elapsed_payload,
        "switch-evidence.json": _json_payload(switch_record),
    }
    lane_materials: list[dict[str, Any]] = []
    with overlay.acquire_campaign_replay_token(
        width10, width6, parent, instance,
        expected_width10_campaign_sha256=width10["manifest_sha256"],
        expected_width6_campaign_sha256=width6["manifest_sha256"],
        expected_parent_manifest_sha256=parent["manifest_sha256"],
        parent_cube_index=overlay.width10.TARGET_PARENT_CUBE_INDEX,
        strict_base=True,
    ) as token:
        for index, lane in enumerate(switch_lanes):
            hard = lane["hard_evidence"]
            hard_pin = lane["hard_evidence_sha256"]
            candidate_list = [candidates[index]]
            manifest = overlay.build_overlay_manifest(
                width10, width6, parent, instance,
                global_leaf_index=lane["global_leaf_index"],
                hard_evidence=hard,
                expected_hard_evidence_sha256=hard_pin,
                candidate_variables=candidate_list, strict_base=True,
                _campaign_replay_token=token,
            )
            verification = overlay.verify_overlay_manifest(
                manifest, width10, width6, parent, instance,
                global_leaf_index=lane["global_leaf_index"],
                hard_evidence=hard,
                expected_hard_evidence_sha256=hard_pin,
                candidate_variables=candidate_list,
                expected_overlay_sha256=manifest["manifest_sha256"],
                strict_base=True, _campaign_replay_token=token,
            )
            if (
                verification.get("valid") is not True
                or verification.get("current_source_exact_replay") is not True
                or verification.get("launch_authorized") is not False
            ):
                raise AdaptiveMaterialBuildError("overlay replay did not validate")
            lane_dir = f"lane-{index}"
            files[f"{lane_dir}/hard-evidence.json"] = _json_payload(hard)
            files[f"{lane_dir}/overlay.json"] = _json_payload(manifest)
            files[f"{lane_dir}/overlay-verification.json"] = _json_payload(
                verification
            )
            descendants = manifest["descendants"]
            lane_materials.append(_seal({
                "schema_version": SCHEMA_VERSION,
                "lane_index": index,
                "global_leaf_index": lane["global_leaf_index"],
                "cpu": lane["cpu"],
                "candidate_variables": candidate_list,
                "selected_variable": manifest["candidate_policy"][
                    "selected_variable"
                ],
                "hard_evidence_path": f"{lane_dir}/hard-evidence.json",
                "hard_evidence_sha256": hard_pin,
                "overlay_manifest_path": f"{lane_dir}/overlay.json",
                "overlay_manifest_sha256": manifest["manifest_sha256"],
                "overlay_verification_path": (
                    f"{lane_dir}/overlay-verification.json"
                ),
                "overlay_verification_sha256": verification["record_sha256"],
                "descendant_sha256s": [
                    descendant["descendant_sha256"]
                    for descendant in descendants
                ],
            }))
    prepare_entries: list[dict[str, Any]] = []
    for lane_index, descendant_index in TARGET_KEYS:
        lane = lane_materials[lane_index]
        prepare_entries.append({
            "target_key": [lane_index, descendant_index],
            "v5_prepare_cli": {
                "subcommand": "prepare",
                "required_operator_cli_args": ["root"],
                "provided_cli_args": {
                    "batch_root": str(batch_root),
                    "parent_manifest": str(
                        output_dir / "parent-manifest.json"
                    ),
                    "width6_campaign": str(
                        output_dir / "width6-campaign.json"
                    ),
                    "width10_campaign": str(
                        output_dir / "width10-campaign.json"
                    ),
                    "overlay_manifest": str(
                        output_dir / lane["overlay_manifest_path"]
                    ),
                    "hard_evidence": str(
                        output_dir / lane["hard_evidence_path"]
                    ),
                    "switch_evidence": str(
                        output_dir / "switch-evidence.json"
                    ),
                    "elapsed_seconds_by_lane_json": str(
                        output_dir / "elapsed-seconds-by-lane.json"
                    ),
                    "expected_overlay_sha256": (
                        lane["overlay_manifest_sha256"]
                    ),
                    "expected_hard_evidence_sha256": (
                        lane["hard_evidence_sha256"]
                    ),
                    "expected_switch_evidence_sha256": (
                        switch_record["record_sha256"]
                    ),
                    "expected_batch_manifest_sha256": (
                        expected_batch_manifest_sha256
                    ),
                    "descendant_index": descendant_index,
                    "candidate_variable": list(
                        lane["candidate_variables"]
                    ),
                    "timeout_seconds": timeout_seconds,
                    "proof_max_bytes": PROOF_MAX_BYTES,
                },
            },
            "postconditions": {
                "lane_index": lane_index,
                "global_leaf_index": lane["global_leaf_index"],
                "descendant_index": descendant_index,
                "expected_descendant_sha256": lane[
                    "descendant_sha256s"
                ][descendant_index],
                "expected_start_batch_cpu": lane["cpu"],
                "prepared_root_must_fresh_replay_all_material": True,
            },
        })
    plan = _seal({
        "schema_version": SCHEMA_VERSION, "kind": PLAN_KIND,
        "target_keys": [list(key) for key in TARGET_KEYS],
        "canonical_order": "descendant-major-then-lane-v1",
        "entries": prepare_entries, "launch_authorized": False,
        "scientific_claim": False,
    })
    files["prepare-plan.json"] = _json_payload(plan)
    role_by_path = {
        "batch-manifest.json": "old_batch_manifest",
        "parent-manifest.json": "parent_manifest",
        "width6-campaign.json": "width6_campaign",
        "width10-campaign.json": "width10_campaign",
        "measurement-receipt.json": "operator_measurement_receipt",
        "elapsed-seconds-by-lane.json": "exact_elapsed_float_array",
        "switch-evidence.json": "switch_evidence_candidate",
        "prepare-plan.json": "v5_prepare_plan",
    }
    inventory = [
        _file_record(
            relative,
            role_by_path.get(
                relative,
                "hard_evidence" if relative.endswith("hard-evidence.json")
                else "overlay_verification"
                if relative.endswith("overlay-verification.json")
                else "overlay_manifest",
            ),
            payload,
        )
        for relative, payload in sorted(files.items())
    ]
    if _stable_bytes(
        _BUILDER_SOURCE_PATH, cap=MAX_SOURCE_BYTES,
    ) != _BUILDER_SOURCE_PAYLOAD:
        raise AdaptiveMaterialBuildError("builder source changed since module load")
    builder_payload = _BUILDER_SOURCE_PAYLOAD
    commit = _seal({
        "schema_version": SCHEMA_VERSION, "kind": BUNDLE_KIND,
        "authority": AUTHORITY, "test_only": True,
        "production_eligible": False, "authenticated": False,
        "launch_authorized": False, "scientific_claim": False,
        "bundle_root": str(output_dir), "batch_root": str(batch_root),
        "batch_manifest_sha256": expected_batch_manifest_sha256,
        "observation_action_sequence": OBSERVATION_ACTION_SEQUENCE,
        "observation_action_result_sha256": (
            validated_receipt["observation_action_result_sha256"]
        ),
        "checkpoint_stop_action_sequence": ACTION_SEQUENCE,
        "checkpoint_stop_result_sha256": action_result["record_sha256"],
        "observation_bundle_sha256": observation_commit["record_sha256"],
        "measurement_receipt_sha256": validated_receipt["record_sha256"],
        "elapsed_seconds_json_sha256": hashlib.sha256(
            elapsed_payload
        ).hexdigest(),
        "timeout_seconds": timeout_seconds,
        "elapsed_seconds_by_lane": list(elapsed),
        "switch_evidence_sha256": switch_record["record_sha256"],
        "hard_evidence_sha256s": [
            lane["hard_evidence_sha256"] for lane in lane_materials
        ],
        "overlay_manifest_sha256s": [
            lane["overlay_manifest_sha256"] for lane in lane_materials
        ],
        "candidate_variables_by_lane": [
            lane["candidate_variables"] for lane in lane_materials
        ],
        "candidate_selection_policy": (
            "operator-selected-performance-hint-not-coverage-trust-v1"
        ),
        "lane_materials": lane_materials,
        "prepare_plan_sha256": plan["record_sha256"],
        "target_keys": [list(key) for key in TARGET_KEYS],
        "files": inventory,
        "source_binding": dict(source_binding),
        "builder_source": {
            "relative_path": Path(__file__).resolve().relative_to(PROJECT).as_posix(),
            "sha256": hashlib.sha256(builder_payload).hexdigest(),
            "bytes": len(builder_payload),
        },
        "v5_prepare_requires_fresh_full_replay": True,
        "launch_requires_nonserializable_switch_v3_lease": True,
    })
    return files, commit


def _publish_new_file(path: Path, payload: bytes) -> None:
    fd = os.open(
        path,
        os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW,
        0o600,
    )
    try:
        os.fchmod(fd, 0o600)
        view = memoryview(payload)
        offset = 0
        while offset < len(view):
            written = os.write(fd, view[offset:])
            if written <= 0:
                raise AdaptiveMaterialBuildError("short material publication")
            offset += written
        observed = os.fstat(fd)
        if (
            not stat.S_ISREG(observed.st_mode)
            or stat.S_IMODE(observed.st_mode) != 0o600
            or observed.st_uid != os.geteuid()
            or observed.st_nlink != 1
        ):
            raise AdaptiveMaterialBuildError("published file mode/owner mismatch")
        os.fsync(fd)
    finally:
        os.close(fd)


def _fsync_directory(path: Path) -> None:
    fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)



def _safe_relative(value: str) -> PurePosixPath:
    path = PurePosixPath(value)
    if path.is_absolute() or not path.parts or any(
        part in {"", ".", ".."} for part in path.parts
    ):
        raise AdaptiveMaterialBuildError("bundle relative path is unsafe")
    return path


def _verify_published_bundle(
    target: Path, expected_commit: Mapping[str, Any],
) -> None:
    root = _canonical_root(target, label="published bundle")
    observed = _read_json(root / "COMMIT.json")
    if (
        observed != expected_commit or not _selfhash_valid(observed)
        or stat.S_IMODE((root / "COMMIT.json").lstat().st_mode) != 0o600
    ):
        raise AdaptiveMaterialBuildError("published bundle commit changed")
    inventory = observed.get("files")
    if type(inventory) is not list:
        raise AdaptiveMaterialBuildError("published inventory is missing")
    expected_paths = {"COMMIT.json"}
    for record in inventory:
        if (
            type(record) is not dict
            or type(record.get("relative_path")) is not str
            or not _is_sha256(record.get("sha256"))
            or type(record.get("bytes")) is not int
            or record["bytes"] < 0
            or record.get("mode") != 0o600
        ):
            raise AdaptiveMaterialBuildError("published inventory record malformed")
        relative = record["relative_path"]
        if relative in expected_paths:
            raise AdaptiveMaterialBuildError("published inventory path duplicated")
        expected_paths.add(relative)
        path = root.joinpath(*_safe_relative(relative).parts)
        payload = _stable_bytes(path, cap=MAX_JSON_BYTES)
        info = path.lstat()
        if (
            hashlib.sha256(payload).hexdigest() != record["sha256"]
            or len(payload) != record["bytes"]
            or stat.S_IMODE(info.st_mode) != 0o600
        ):
            raise AdaptiveMaterialBuildError("published file binding mismatch")
    observed_paths: set[str] = set()
    for path in root.rglob("*"):
        relative = path.relative_to(root).as_posix()
        info = path.lstat()
        if stat.S_ISDIR(info.st_mode):
            if (
                info.st_uid != os.geteuid()
                or stat.S_IMODE(info.st_mode) != 0o700
            ):
                raise AdaptiveMaterialBuildError(
                    "published directory mode/owner mismatch"
                )
        elif stat.S_ISREG(info.st_mode):
            if info.st_uid != os.geteuid() or info.st_nlink != 1:
                raise AdaptiveMaterialBuildError(
                    "published file owner/link mismatch"
                )
            observed_paths.add(relative)
        else:
            raise AdaptiveMaterialBuildError("published tree has a special file")
    if observed_paths != expected_paths:
        raise AdaptiveMaterialBuildError("published tree inventory mismatch")


def _load_observation_bundle(
    receipt_path: Path, elapsed_path: Path, *, batch_root: Path,
    batch_pin: str, timeout_seconds: float,
) -> tuple[
    dict[str, Any], bytes, list[float], bytes, dict[str, Any],
]:
    receipt_candidate = Path(receipt_path)
    elapsed_candidate = Path(elapsed_path)
    for candidate, label in (
        (receipt_candidate, "measurement receipt"),
        (elapsed_candidate, "elapsed array"),
    ):
        if (
            not candidate.is_absolute()
            or str(candidate) != os.path.abspath(str(candidate))
        ):
            raise AdaptiveMaterialBuildError(
                f"{label} path must be normalized absolute"
            )
    root = _canonical_root(
        receipt_candidate.parent, label="observation bundle",
    )
    if (
        receipt_candidate != root / "measurement-receipt.json"
        or elapsed_candidate != root / "elapsed-seconds-by-lane.json"
    ):
        raise AdaptiveMaterialBuildError(
            "receipt and elapsed array must be canonical observation peers"
        )
    commit = _read_json(root / "COMMIT.json")
    _verify_published_bundle(root, commit)
    inventory = commit.get("files")
    if type(inventory) is not list:
        raise AdaptiveMaterialBuildError("observation inventory is missing")
    by_path = {
        record.get("relative_path"): record
        for record in inventory if type(record) is dict
    }
    expected_roles = {
        "measurement-receipt.json": "operator_measurement_receipt",
        "elapsed-seconds-by-lane.json": "exact_elapsed_float_array",
    }
    if (
        len(inventory) != len(expected_roles)
        or set(by_path) != set(expected_roles)
        or any(
            by_path[path].get("role") != role
            for path, role in expected_roles.items()
        )
    ):
        raise AdaptiveMaterialBuildError(
            "observation inventory does not bind the two canonical files"
        )
    elapsed, elapsed_payload = _read_float_file(elapsed_candidate)
    receipt_payload = _stable_bytes(receipt_candidate, cap=1 << 20)
    receipt = _read_json(receipt_candidate, cap=1 << 20)
    if receipt_payload != _json_payload(receipt):
        raise AdaptiveMaterialBuildError(
            "measurement receipt changed between stable reads or is noncanonical"
        )
    if (
        commit.get("schema_version") != SCHEMA_VERSION
        or commit.get("kind") != OBSERVATION_BUNDLE_KIND
        or commit.get("authority") != AUTHORITY
        or commit.get("observation_root") != str(root)
        or commit.get("batch_root") != str(batch_root)
        or commit.get("batch_manifest_sha256") != batch_pin
        or commit.get("observation_action_sequence")
        != OBSERVATION_ACTION_SEQUENCE
        or commit.get("observation_action_result_sha256")
        != receipt.get("observation_action_result_sha256")
        or commit.get("measurement_receipt_sha256")
        != receipt.get("record_sha256")
        or commit.get("elapsed_seconds_json_sha256")
        != hashlib.sha256(elapsed_payload).hexdigest()
        or commit.get("timeout_seconds") != timeout_seconds
        or commit.get("elapsed_seconds_by_lane") != elapsed
        or type(commit.get("source_binding")) is not dict
        or type(commit.get("claim_scope")) is not dict
        or type(commit.get("observation_lane_outcome_sha256s")) is not list
        or len(commit["observation_lane_outcome_sha256s"]) != LANE_COUNT
        or any(
            not _is_sha256(value)
            for value in commit["observation_lane_outcome_sha256s"]
        )
        or commit.get("authenticated") is not False
        or commit.get("launch_authorized") is not False
        or commit.get("scientific_claim") is not False
    ):
        raise AdaptiveMaterialBuildError(
            "observation COMMIT/receipt binding mismatch"
        )
    return receipt, receipt_payload, elapsed, elapsed_payload, commit


def _publish_bundle(
    output_dir: Path, files: Mapping[str, bytes], commit: Mapping[str, Any],
) -> None:
    target, parent = _new_bundle_path(output_dir)
    try:
        os.mkdir(target, 0o700)
    except FileExistsError as exc:
        raise AdaptiveMaterialBuildError(
            "output directory raced into existence"
        ) from exc
    os.chmod(target, 0o700, follow_symlinks=False)
    _fsync_directory(parent)
    created_dirs: set[Path] = {target}
    for relative, payload in sorted(files.items()):
        pure = _safe_relative(relative)
        current = target
        for part in pure.parts[:-1]:
            current = current / part
            if current not in created_dirs:
                os.mkdir(current, 0o700)
                os.chmod(current, 0o700, follow_symlinks=False)
                created_dirs.add(current)
        _publish_new_file(target.joinpath(*pure.parts), payload)
    for directory in sorted(
        created_dirs, key=lambda item: len(item.parts), reverse=True,
    ):
        _fsync_directory(directory)
    _publish_new_file(target / "COMMIT.json", _json_payload(commit))
    _fsync_directory(target)
    _fsync_directory(parent)
    _verify_published_bundle(target, commit)


def observe_running_batch(
    *, batch_root: Path, output_dir: Path, timeout_seconds: float,
    expected_batch_manifest_sha256: str,
    expected_switch_v3_source_sha256: str,
    expected_switch_v2_source_sha256: str,
    publish: bool = True,
) -> dict[str, Any]:
    if (
        type(timeout_seconds) is not float or not math.isfinite(timeout_seconds)
        or timeout_seconds <= 0
    ):
        raise AdaptiveMaterialBuildError("timeout must be a positive exact float")
    batch_pin = _require_sha256(
        expected_batch_manifest_sha256, "batch manifest pin",
    )
    switch_pin = _require_sha256(
        expected_switch_v3_source_sha256, "switch-v3 source pin",
    )
    switch_v2_pin = _require_sha256(
        expected_switch_v2_source_sha256, "switch-v2 source pin",
    )
    root = _canonical_root(batch_root, label="old batch root")
    target, _ = _new_bundle_path(output_dir)
    switch, switch_source, switch_v2_source = _load_exact_switch_v3(
        switch_pin, switch_v2_pin,
    )
    locks: list[Any] = []
    try:
        locks, _ = switch.base._acquire_all_locks(root)
        discovery = switch.base._discover_sources(
            root, expected_batch_manifest_sha256=batch_pin,
        )
        coordinator, child, legacy_executed = (
            switch.base._load_exact_modules(discovery)
        )
        running, contexts = _running_snapshot_locked(
            root, coordinator, child,
        )
        if running["manifest"].get("record_sha256") != batch_pin:
            raise AdaptiveMaterialBuildError(
                "live observation batch manifest pin mismatch"
            )
        sampled = _sample_running_processes(running["lanes"])
        _reverify_running_snapshot(child, contexts, sampled)
        elapsed = list(sampled["elapsed_seconds_by_lane"])
        elapsed_payload = _json_payload(elapsed)
        receipt = _seal({
            "schema_version": SCHEMA_VERSION,
            "kind": RECEIPT_KIND,
            "batch_root": str(root),
            "batch_manifest_sha256": batch_pin,
            "observation_action_sequence": OBSERVATION_ACTION_SEQUENCE,
            "observation_action_result_sha256": (
                running["observation_result"]["record_sha256"]
            ),
            "timeout_seconds": timeout_seconds,
            "elapsed_seconds_by_lane": elapsed,
            "elapsed_seconds_json_sha256": hashlib.sha256(
                elapsed_payload
            ).hexdigest(),
            "annotation_source": "operator-annotation-not-solver-result-v2",
            "timed_out": False,
            "hardness_only": True,
            "measurement_method": (
                "operator-current-generation-clock-boottime-plus-one-tick-"
                "conservative-ceil-v1"
            ),
            "boot_id_sha256": sampled["boot_id_sha256"],
            "clock_ticks_per_second": sampled["clock_ticks_per_second"],
            "proc_uptime_seconds_decimal": (
                sampled["proc_uptime_seconds_decimal"]
            ),
            "clock_boottime_seconds_decimal": (
                sampled["clock_boottime_seconds_decimal"]
            ),
            "sample_utc_before": sampled["sample_utc_before"],
            "sample_utc_after": sampled["sample_utc_after"],
            "observer_source_sha256": hashlib.sha256(
                _BUILDER_SOURCE_PAYLOAD
            ).hexdigest(),
            "switch_v3_source_sha256": switch_pin,
            "switch_v2_source_sha256": switch_v2_pin,
            "lanes": sampled["lanes"],
            "authenticated": False,
            "launch_authorized": False,
            "scientific_claim": False,
        })
        _validate_receipt(
            receipt, batch_root=root, batch_pin=batch_pin,
            observation_result_pin=(
                running["observation_result"]["record_sha256"]
            ),
            timeout_seconds=timeout_seconds, elapsed=elapsed,
            elapsed_payload=elapsed_payload,
            expected_switch_v3_source_sha256=switch_pin,
            expected_switch_v2_source_sha256=switch_v2_pin,
        )
        receipt_payload = _json_payload(receipt)
        files = {
            "measurement-receipt.json": receipt_payload,
            "elapsed-seconds-by-lane.json": elapsed_payload,
        }
        source_binding = _seal({
            "schema_version": SCHEMA_VERSION,
            "method": "externally-pinned-switch-and-legacy-exact-replay-v1",
            "switch_v3_source": switch_source,
            "switch_v2_source": switch_v2_source,
            "legacy_executed_sources": legacy_executed,
        })
        commit = _seal({
            "schema_version": SCHEMA_VERSION,
            "kind": OBSERVATION_BUNDLE_KIND,
            "authority": AUTHORITY,
            "observation_root": str(target),
            "batch_root": str(root),
            "batch_manifest_sha256": batch_pin,
            "observation_action_sequence": OBSERVATION_ACTION_SEQUENCE,
            "observation_action_result_sha256": (
                running["observation_result"]["record_sha256"]
            ),
            "observation_lane_outcome_sha256s": [
                lane["record_sha256"]
                for lane in running["observation_lanes"]
            ],
            "measurement_receipt_sha256": receipt["record_sha256"],
            "elapsed_seconds_json_sha256": hashlib.sha256(
                elapsed_payload
            ).hexdigest(),
            "timeout_seconds": timeout_seconds,
            "elapsed_seconds_by_lane": elapsed,
            "files": [
                _file_record(
                    relative,
                    "operator_measurement_receipt"
                    if relative == "measurement-receipt.json"
                    else "exact_elapsed_float_array",
                    payload,
                )
                for relative, payload in sorted(files.items())
            ],
            "source_binding": source_binding,
            "claim_scope": {
                "current_active_generation_age_only": True,
                "cumulative_solver_elapsed_claimed": False,
                "solver_native_timing_claimed": False,
                "timeout_claimed": False,
                "scientific_certificate": False,
            },
            "authenticated": False,
            "launch_authorized": False,
            "scientific_claim": False,
        })
        if (
            _stable_bytes(_BUILDER_SOURCE_PATH, cap=MAX_SOURCE_BYTES)
            != _BUILDER_SOURCE_PAYLOAD
            or hashlib.sha256(_stable_bytes(
                PROJECT / SWITCH_V3_RELATIVE, cap=MAX_SOURCE_BYTES,
            )).hexdigest() != switch_pin
            or hashlib.sha256(_stable_bytes(
                PROJECT / SWITCH_V2_RELATIVE, cap=MAX_SOURCE_BYTES,
            )).hexdigest() != switch_v2_pin
        ):
            raise AdaptiveMaterialBuildError(
                "observer source changed before publication"
            )
        if publish:
            _publish_bundle(target, files, commit)
        return commit
    finally:
        for held in reversed(locks):
            held.close()


def build_material_bundle(
    *, batch_root: Path, output_dir: Path, measurement_receipt_path: Path,
    elapsed_seconds_by_lane_json: Path, timeout_seconds: float,
    candidate_variables: Sequence[int], expected_batch_manifest_sha256: str,
    expected_switch_v3_source_sha256: str,
    expected_switch_v2_source_sha256: str,
    expected_overlay_v2_source_sha256: str,
    expected_adaptive_v2_source_sha256: str,
    publish: bool = True,
) -> dict[str, Any]:
    if (
        type(timeout_seconds) is not float or not math.isfinite(timeout_seconds)
        or timeout_seconds <= 0
    ):
        raise AdaptiveMaterialBuildError("timeout must be a positive exact float")
    batch_pin = _require_sha256(
        expected_batch_manifest_sha256, "batch manifest pin"
    )
    root = _canonical_root(batch_root, label="old batch root")
    target, _ = _new_bundle_path(output_dir)
    (
        receipt, receipt_payload, elapsed, elapsed_payload,
        observation_commit,
    ) = _load_observation_bundle(
        measurement_receipt_path, elapsed_seconds_by_lane_json,
        batch_root=root, batch_pin=batch_pin,
        timeout_seconds=timeout_seconds,
    )
    switch, overlay, sources = _load_exact_sources(
        expected_switch_v3_sha256=expected_switch_v3_source_sha256,
        expected_switch_v2_sha256=expected_switch_v2_source_sha256,
        expected_overlay_v2_sha256=expected_overlay_v2_source_sha256,
        expected_adaptive_v2_sha256=expected_adaptive_v2_source_sha256,
    )
    files, commit = _build_values(
        switch=switch, overlay=overlay, source_binding=sources,
        batch_root=root, output_dir=target, receipt=receipt,
        receipt_payload=receipt_payload, elapsed=elapsed,
        elapsed_payload=elapsed_payload,
        observation_commit=observation_commit,
        timeout_seconds=timeout_seconds,
        candidate_variables=candidate_variables,
        expected_batch_manifest_sha256=batch_pin,
        expected_switch_v3_source_sha256=(
            expected_switch_v3_source_sha256
        ),
        expected_switch_v2_source_sha256=(
            expected_switch_v2_source_sha256
        ),
    )
    if publish:
        _publish_bundle(target, files, commit)
    return commit


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    subparsers = parser.add_subparsers(dest="command", required=True)
    observe = subparsers.add_parser("observe", allow_abbrev=False)
    for command in (observe,):
        command.add_argument("--batch-root", type=Path, required=True)
        command.add_argument("--output-dir", type=Path, required=True)
        command.add_argument("--timeout-seconds", type=float, required=True)
        command.add_argument(
            "--expected-batch-manifest-sha256", required=True,
        )
        command.add_argument(
            "--expected-switch-v3-source-sha256", required=True,
        )
        command.add_argument(
            "--expected-switch-v2-source-sha256", required=True,
        )
    build = subparsers.add_parser("build", allow_abbrev=False)
    build.add_argument("--batch-root", type=Path, required=True)
    build.add_argument("--output-dir", type=Path, required=True)
    build.add_argument("--measurement-receipt", type=Path, required=True)
    build.add_argument(
        "--elapsed-seconds-by-lane-json", type=Path, required=True,
    )
    build.add_argument("--timeout-seconds", type=float, required=True)
    build.add_argument(
        "--candidate-variable", type=int, action="append", required=True,
    )
    build.add_argument("--expected-batch-manifest-sha256", required=True)
    build.add_argument("--expected-switch-v3-source-sha256", required=True)
    build.add_argument("--expected-switch-v2-source-sha256", required=True)
    build.add_argument("--expected-overlay-v2-source-sha256", required=True)
    build.add_argument("--expected-adaptive-v2-source-sha256", required=True)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.command == "observe":
        result = observe_running_batch(
            batch_root=args.batch_root, output_dir=args.output_dir,
            timeout_seconds=args.timeout_seconds,
            expected_batch_manifest_sha256=(
                args.expected_batch_manifest_sha256
            ),
            expected_switch_v3_source_sha256=(
                args.expected_switch_v3_source_sha256
            ),
            expected_switch_v2_source_sha256=(
                args.expected_switch_v2_source_sha256
            ),
            publish=True,
        )
    else:
        result = build_material_bundle(
            batch_root=args.batch_root, output_dir=args.output_dir,
            measurement_receipt_path=args.measurement_receipt,
            elapsed_seconds_by_lane_json=args.elapsed_seconds_by_lane_json,
            timeout_seconds=args.timeout_seconds,
            candidate_variables=args.candidate_variable,
            expected_batch_manifest_sha256=(
                args.expected_batch_manifest_sha256
            ),
            expected_switch_v3_source_sha256=(
                args.expected_switch_v3_source_sha256
            ),
            expected_switch_v2_source_sha256=(
                args.expected_switch_v2_source_sha256
            ),
            expected_overlay_v2_source_sha256=(
                args.expected_overlay_v2_source_sha256
            ),
            expected_adaptive_v2_source_sha256=(
                args.expected_adaptive_v2_source_sha256
            ),
            publish=True,
        )
    sys.stdout.buffer.write(_json_payload(result))
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    try:
        _exit = main()
    except (
        AdaptiveMaterialBuildError, OSError, ValueError, TypeError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        _exit = 2
    raise SystemExit(_exit)


__all__ = [
    "AdaptiveMaterialBuildError", "BUNDLE_KIND", "PLAN_KIND",
    "OBSERVATION_BUNDLE_KIND", "RECEIPT_KIND", "TARGET_KEYS",
    "build_material_bundle", "observe_running_batch", "main",
]
