#!/usr/bin/env python3
"""Audited reuse of *certified* recursive CPU slots.

The normal recursive lease catalog deliberately retains every CPU in a split
bundle until all siblings aggregate.  That is the safest default, but it can
leave a physically idle CPU behind a child that is already ``CERTIFIED``.
This sidecar creates a separate, durable *handoff* record for such a slot
without editing the original catalog or any hash-bound v1 source.

It is intentionally narrow:

* a donor must be a currently RESERVED v1 CPU belonging to an open bundle;
* every non-claimed slot in that bundle must correspond to a CERTIFIED item;
* the selected CPU must not be a claimed slot and must have no user process
  pinned solely to it at admission time;
* a handoff root serializes one active borrower per physical CPU; and
* a handoff can be released only after the borrower has a sealed parent
  aggregate and an all-CERTIFIED queue.

The borrower uses a separate v1 control root.  Thus the existing frozen
runner and active bundle sidecars retain their exact source bindings.  The
handoff record is scheduler evidence, not a scientific proof claim.
"""

from __future__ import annotations

import argparse
import contextlib
import fcntl
import hashlib
import json
import os
import sys
import tempfile
import time
from collections.abc import Iterator, Mapping, Sequence
from pathlib import Path
from typing import Any


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from investigations import paper400_dic5_recursive_split_v1 as recursive
from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


SCHEMA_VERSION = 1
GATE = "paper400-dic5-recursive-certified-slot-handoff-v1"
CATALOG_NAME = "certified-slot-handoffs.json"
LOCK_NAME = ".certified-slot-handoffs.lock"
CATALOG_KIND = "paper400-dic5-recursive-certified-slot-handoff-catalog-v1"
ENTRY_KIND = "paper400-dic5-recursive-certified-slot-handoff-v1"
RELEASE_KIND = "paper400-dic5-recursive-certified-slot-handoff-release-v1"
PARENT_AGGREGATE = "parent-aggregate.json"
MAX_JSON_BYTES = 64 << 20


class CertifiedSlotHandoffError(RuntimeError):
    """A donor, consumer, or durable handoff record is invalid."""


def _same(left: Any, right: Any) -> bool:
    if type(left) is not type(right):
        return False
    if type(left) is dict:
        return set(left) == set(right) and all(_same(left[key], right[key]) for key in left)
    if type(left) in {list, tuple}:
        return len(left) == len(right) and all(_same(a, b) for a, b in zip(left, right))
    return left == right


def _normalized_absolute(path: Path | str, *, label: str) -> Path:
    value = Path(path)
    if not value.is_absolute() or str(value) != os.path.abspath(str(value)):
        raise CertifiedSlotHandoffError(f"{label} must be an absolute normalized path")
    return value


def _ensure_handoff_root(path: Path | str) -> Path:
    target = _normalized_absolute(path, label="handoff root")
    try:
        target.mkdir(mode=0o700, parents=True, exist_ok=True)
        target.chmod(0o700)
    except OSError as exc:
        raise CertifiedSlotHandoffError("cannot create handoff root") from exc
    st = target.stat()
    if not target.is_dir() or target.is_symlink() or (st.st_mode & 0o777) != 0o700:
        raise CertifiedSlotHandoffError("handoff root must be a mode-0700 directory")
    return target


def _fsync_dir(path: Path) -> None:
    fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def _source_binding() -> dict[str, Any]:
    """Bind every administrative handoff to exact immutable source bytes."""

    def item(path: Path) -> dict[str, str]:
        payload = supervisor._stable_bytes(path, cap=32 << 20, executable=False)
        return {"path": str(path), "sha256": hashlib.sha256(payload).hexdigest()}

    source = Path(__file__).resolve(strict=True)
    return {
        "method": "exact-source-sha256-replay-v1",
        "certified_slot_handoff": item(source),
        "recursive_split": item(Path(recursive.__file__).resolve(strict=True)),
        "recursive_supervisor": item(Path(supervisor.__file__).resolve(strict=True)),
    }


def _read_json(path: Path) -> dict[str, Any]:
    try:
        st = path.stat()
        if not path.is_file() or path.is_symlink() or st.st_size > MAX_JSON_BYTES:
            raise CertifiedSlotHandoffError("handoff JSON path is unsafe")
        data = path.read_bytes()
        value = json.loads(data)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise CertifiedSlotHandoffError(f"cannot read JSON: {path}") from exc
    if type(value) is not dict:
        raise CertifiedSlotHandoffError("handoff JSON is not an object")
    return value


def _publish_json(path: Path, value: Mapping[str, Any]) -> None:
    payload = recursive.canonical_bytes(dict(value)) + b"\n"
    parent = path.parent
    fd = -1
    temporary = ""
    try:
        fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=parent)
        os.fchmod(fd, 0o600)
        offset = 0
        while offset < len(payload):
            offset += os.write(fd, payload[offset:])
        os.fsync(fd)
        os.close(fd)
        fd = -1
        os.replace(temporary, path)
        _fsync_dir(parent)
    except OSError as exc:
        raise CertifiedSlotHandoffError(f"cannot publish handoff JSON: {path}") from exc
    finally:
        if fd >= 0:
            os.close(fd)
        if temporary:
            try:
                os.unlink(temporary)
            except FileNotFoundError:
                pass


@contextlib.contextmanager
def _catalog_lock(root: Path) -> Iterator[None]:
    lock = root / LOCK_NAME
    fd = os.open(lock, os.O_CREAT | os.O_RDWR | os.O_CLOEXEC, 0o600)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX)
        yield
    finally:
        fcntl.flock(fd, fcntl.LOCK_UN)
        os.close(fd)


def _seal_catalog(*, primary_control_root: Path, entries: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    return recursive.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": CATALOG_KIND,
            "gate": GATE,
            "primary_control_root": str(primary_control_root),
            "source_binding": _source_binding(),
            "entries": [dict(entry) for entry in entries],
        },
        "catalog_sha256",
    )


def _validate_entry(entry: Mapping[str, Any]) -> None:
    fields = {
        "schema_version", "kind", "gate", "cpu", "primary_bundle",
        "primary_bundle_sha256", "primary_cpu_reservation_sha256",
        "provider_queue_sha256", "provider_certified_item_ids",
        "provider_claimed_cpu_ids", "consumer_control_root", "consumer_bundle_name",
        "consumer_bundle", "state", "created_at", "released_at", "source_binding", "entry_sha256",
    }
    if (
        type(entry) is not dict or set(entry) != fields
        or not recursive.selfhash_valid(entry, "entry_sha256")
        or entry.get("schema_version") != SCHEMA_VERSION
        or entry.get("kind") != ENTRY_KIND or entry.get("gate") != GATE
        or type(entry.get("cpu")) is not int or entry["cpu"] < 0
        or not all(recursive.is_sha256(entry.get(key)) for key in (
            "primary_bundle_sha256", "primary_cpu_reservation_sha256", "provider_queue_sha256",
        ))
        or type(entry.get("provider_certified_item_ids")) is not list
        or not all(type(value) is str for value in entry["provider_certified_item_ids"])
        or type(entry.get("provider_claimed_cpu_ids")) is not list
        or any(type(value) is not int or value < 0 for value in entry["provider_claimed_cpu_ids"])
        or entry["provider_claimed_cpu_ids"] != sorted(set(entry["provider_claimed_cpu_ids"]))
        or any(type(entry.get(key)) is not str or not entry[key] for key in (
            "primary_bundle", "consumer_control_root", "consumer_bundle_name", "consumer_bundle",
        ))
        or not _same(entry.get("source_binding"), _source_binding())
        or entry.get("state") not in {"RESERVED", "RELEASED"}
        or type(entry.get("created_at")) not in {int, float}
        or (entry["state"] == "RESERVED" and entry.get("released_at") is not None)
        or (entry["state"] == "RELEASED" and type(entry.get("released_at")) not in {int, float})
    ):
        raise CertifiedSlotHandoffError("handoff catalog entry is malformed")


def _load_catalog(root: Path, *, primary_control_root: Path) -> dict[str, Any]:
    path = root / CATALOG_NAME
    if not path.exists():
        return _seal_catalog(primary_control_root=primary_control_root, entries=[])
    value = _read_json(path)
    fields = {"schema_version", "kind", "gate", "primary_control_root", "source_binding", "entries", "catalog_sha256"}
    if (
        set(value) != fields or not recursive.selfhash_valid(value, "catalog_sha256")
        or value.get("schema_version") != SCHEMA_VERSION or value.get("kind") != CATALOG_KIND
        or value.get("gate") != GATE or value.get("primary_control_root") != str(primary_control_root)
        or not _same(value.get("source_binding"), _source_binding())
        or type(value.get("entries")) is not list
    ):
        raise CertifiedSlotHandoffError("handoff catalog is malformed or belongs to another control root")
    for entry in value["entries"]:
        _validate_entry(entry)
    active = [entry["cpu"] for entry in value["entries"] if entry["state"] == "RESERVED"]
    if len(active) != len(set(active)):
        raise CertifiedSlotHandoffError("handoff catalog has duplicate active CPU entries")
    return value


def _fixed_user_processes(cpus: set[int]) -> list[dict[str, Any]]:
    """Return non-kernel processes pinned solely to an offered CPU.

    We reject sleeping control processes as well as R/D workers.  Kernel worker
    threads intentionally have an empty cmdline and do not represent a
    user-space recursive lease.
    """

    observed: list[dict[str, Any]] = []
    for proc in Path("/proc").iterdir():
        if not proc.name.isdecimal():
            continue
        try:
            stat_fields = (proc / "stat").read_text().split()
            state = stat_fields[2]
            status = (proc / "status").read_text().splitlines()
            allowed = next(
                line.split(":", 1)[1].strip() for line in status
                if line.startswith("Cpus_allowed_list:")
            )
            if not allowed.isdecimal() or int(allowed) not in cpus:
                continue
            command = (proc / "cmdline").read_bytes().decode("utf-8", "replace").replace("\0", " ").strip()
            if command:
                observed.append({"cpu": int(allowed), "pid": int(proc.name), "state": state, "cmd": command[:1024]})
        except (FileNotFoundError, PermissionError, StopIteration, IndexError, UnicodeDecodeError, ValueError):
            continue
    return sorted(observed, key=lambda value: (value["cpu"], value["pid"]))


def _certified_child_artifacts(bundle: Path, item: Mapping[str, Any]) -> None:
    path = item.get("path")
    if type(path) is not str or not path or any(ch not in "01" for ch in path):
        raise CertifiedSlotHandoffError("certified queue item has unsafe path")
    child = bundle / "children" / path
    normal = (child / "state" / "30-terminal.claim.json").exists() and (child / "COMMIT.json").exists()
    fast = (child / "state" / "31-fast-terminal.claim.json").exists() and (child / "FAST-TERMINAL-COMMIT.json").exists()
    if not (normal or fast) or not (child / "certificate.json").exists() or not (child / "validation.json").exists():
        raise CertifiedSlotHandoffError("certified donor item lacks immutable terminal evidence")


def _provider_evidence(primary_control_root: Path, cpu: int) -> dict[str, Any]:
    catalog = supervisor._load_catalog(primary_control_root)
    matches = [entry for entry in catalog["leases"] if entry.get("cpu") == cpu and entry.get("state") == "RESERVED"]
    if len(matches) != 1:
        raise CertifiedSlotHandoffError("donor CPU does not have exactly one active primary reservation")
    lease = matches[0]
    bundle = _normalized_absolute(lease["bundle"], label="primary bundle")
    loaded = supervisor._load_bundle(bundle, control_root=primary_control_root)
    if (bundle / PARENT_AGGREGATE).exists():
        raise CertifiedSlotHandoffError("completed parent aggregate is not a certified-slot donor")
    queue = loaded["queue"]
    reservation = loaded["reservation"]
    pool = reservation.get("cpus")
    if type(pool) is not list or pool != sorted(set(pool)) or cpu not in pool:
        raise CertifiedSlotHandoffError("primary reservation does not bind donor CPU")
    items = queue.get("items")
    if type(items) is not list or not items:
        raise CertifiedSlotHandoffError("provider queue is malformed")
    if any(item.get("state") not in {"CERTIFIED", "CLAIMED"} for item in items):
        raise CertifiedSlotHandoffError("provider has pending or failed work")
    claimed_cpus: set[int] = set()
    certified_ids: list[str] = []
    for item in items:
        state = item.get("state")
        if state == "CLAIMED":
            item_cpus = item.get("cpu_ids")
            if type(item_cpus) is not list or len(item_cpus) != item.get("cpu_slots"):
                raise CertifiedSlotHandoffError("claimed provider item lacks its exact CPU lease")
            if any(type(value) is not int or value not in pool for value in item_cpus):
                raise CertifiedSlotHandoffError("claimed provider item has unsafe CPU lease")
            claimed_cpus.update(item_cpus)
        else:
            item_id = item.get("item_id")
            if type(item_id) is not str:
                raise CertifiedSlotHandoffError("certified provider item has no id")
            _certified_child_artifacts(bundle, item)
            certified_ids.append(item_id)
    available = set(pool) - claimed_cpus
    if cpu not in available:
        raise CertifiedSlotHandoffError("donor CPU remains assigned to claimed work")
    if len(available) != len(certified_ids):
        raise CertifiedSlotHandoffError("provider queue does not prove every offered slot is certified")
    return {
        "cpu": cpu,
        "primary_bundle": str(bundle),
        "primary_bundle_sha256": loaded["bundle"]["bundle_sha256"],
        "primary_cpu_reservation_sha256": reservation["reservation_sha256"],
        "provider_queue_sha256": queue["queue_sha256"],
        "provider_certified_item_ids": sorted(certified_ids),
        "provider_claimed_cpu_ids": sorted(claimed_cpus),
    }


def _safe_bundle_name(value: str) -> str:
    if not value or "/" in value or value.startswith("."):
        raise CertifiedSlotHandoffError("consumer bundle name is not a safe direct-child name")
    return value


def reserve_handoff(
    *, primary_control_root: Path | str, handoff_root: Path | str,
    consumer_control_root: Path | str, consumer_bundle_name: str, cpus: Sequence[int],
) -> dict[str, Any]:
    """Atomically reserve fully-certified slots for one future v1 borrower."""

    primary = _normalized_absolute(primary_control_root, label="primary control root")
    consumer = _normalized_absolute(consumer_control_root, label="consumer control root")
    root = _ensure_handoff_root(handoff_root)
    name = _safe_bundle_name(consumer_bundle_name)
    pool = list(cpus)
    if (
        type(cpus) not in {list, tuple} or len(pool) not in recursive.SUPPORTED_FANOUTS
        or any(type(cpu) is not int or cpu < 0 for cpu in pool) or pool != sorted(set(pool))
    ):
        raise CertifiedSlotHandoffError("handoff CPU pool must be sorted, unique, and 2/4/8-way")
    consumer_bundle = consumer / name
    if consumer_bundle.exists() or consumer_bundle.is_symlink():
        raise CertifiedSlotHandoffError("consumer bundle already exists")
    pinned = _fixed_user_processes(set(pool))
    if pinned:
        raise CertifiedSlotHandoffError(f"donor CPUs have fixed user processes: {pinned}")
    with _catalog_lock(root):
        catalog = _load_catalog(root, primary_control_root=primary)
        existing = [entry for entry in catalog["entries"] if entry["state"] == "RESERVED"]
        exact = [
            entry for entry in existing
            if entry["consumer_control_root"] == str(consumer)
            and entry["consumer_bundle_name"] == name
        ]
        if exact:
            if sorted(entry["cpu"] for entry in exact) != pool or len(exact) != len(pool):
                raise CertifiedSlotHandoffError("consumer already has a different active handoff")
            return recursive.seal(
                {"schema_version": SCHEMA_VERSION, "kind": ENTRY_KIND, "gate": GATE,
                 "action": "IDEMPOTENT", "consumer_bundle": str(consumer_bundle),
                 "entries": exact, "scientific_claim": False},
                "record_sha256",
            )
        active_cpus = {entry["cpu"] for entry in existing}
        overlap = sorted(active_cpus.intersection(pool))
        if overlap:
            raise CertifiedSlotHandoffError(f"donor CPU already has an active handoff: {overlap}")
        evidence = [_provider_evidence(primary, cpu) for cpu in pool]
        # Re-check immediately before publication so a just-started fixed task
        # cannot silently become a borrower competitor.
        pinned = _fixed_user_processes(set(pool))
        if pinned:
            raise CertifiedSlotHandoffError(f"donor CPUs changed during admission: {pinned}")
        now = time.time()
        entries: list[dict[str, Any]] = [dict(value) for value in catalog["entries"]]
        created: list[dict[str, Any]] = []
        for value in evidence:
            entry = recursive.seal(
                {
                    "schema_version": SCHEMA_VERSION,
                    "kind": ENTRY_KIND,
                    "gate": GATE,
                    **value,
                    "consumer_control_root": str(consumer),
                    "consumer_bundle_name": name,
                    "consumer_bundle": str(consumer_bundle),
                    "state": "RESERVED",
                    "created_at": now,
                    "released_at": None,
                    "source_binding": _source_binding(),
                },
                "entry_sha256",
            )
            entries.append(entry)
            created.append(entry)
        sealed = _seal_catalog(primary_control_root=primary, entries=entries)
        _publish_json(root / CATALOG_NAME, sealed)
    return recursive.seal(
        {"schema_version": SCHEMA_VERSION, "kind": ENTRY_KIND, "gate": GATE,
         "action": "RESERVED", "consumer_bundle": str(consumer_bundle),
         "entries": created, "scientific_claim": False},
        "record_sha256",
    )


def release_handoff(
    *, primary_control_root: Path | str, handoff_root: Path | str,
    consumer_control_root: Path | str, consumer_bundle_name: str,
) -> dict[str, Any]:
    """Release a handoff only after its borrower has a sealed aggregate."""

    primary = _normalized_absolute(primary_control_root, label="primary control root")
    consumer = _normalized_absolute(consumer_control_root, label="consumer control root")
    root = _ensure_handoff_root(handoff_root)
    name = _safe_bundle_name(consumer_bundle_name)
    bundle = consumer / name
    loaded = supervisor._load_bundle(bundle, control_root=consumer)
    queue = loaded["queue"]
    if any(item.get("state") != "CERTIFIED" for item in queue["items"]):
        raise CertifiedSlotHandoffError("consumer queue is not fully certified")
    aggregate_path = bundle / PARENT_AGGREGATE
    aggregate = _read_json(aggregate_path)
    if not recursive.selfhash_valid(aggregate, "record_sha256"):
        raise CertifiedSlotHandoffError("consumer parent aggregate is not sealed")
    with _catalog_lock(root):
        catalog = _load_catalog(root, primary_control_root=primary)
        changed: list[dict[str, Any]] = []
        entries: list[dict[str, Any]] = []
        now = time.time()
        for entry in catalog["entries"]:
            value = dict(entry)
            if (
                value["state"] == "RESERVED"
                and value["consumer_control_root"] == str(consumer)
                and value["consumer_bundle_name"] == name
            ):
                unsigned = dict(value)
                unsigned.pop("entry_sha256")
                unsigned["state"] = "RELEASED"
                unsigned["released_at"] = now
                value = recursive.seal(unsigned, "entry_sha256")
                changed.append(value)
            entries.append(value)
        if not changed:
            raise CertifiedSlotHandoffError("consumer has no active handoff to release")
        _publish_json(root / CATALOG_NAME, _seal_catalog(primary_control_root=primary, entries=entries))
    return recursive.seal(
        {"schema_version": SCHEMA_VERSION, "kind": RELEASE_KIND, "gate": GATE,
         "consumer_bundle": str(bundle), "aggregate_sha256": aggregate["record_sha256"],
         "entries": changed, "scientific_claim": False},
        "record_sha256",
    )


def handoff_status(*, primary_control_root: Path | str, handoff_root: Path | str) -> dict[str, Any]:
    primary = _normalized_absolute(primary_control_root, label="primary control root")
    root = _ensure_handoff_root(handoff_root)
    with _catalog_lock(root):
        catalog = _load_catalog(root, primary_control_root=primary)
    active = [dict(entry) for entry in catalog["entries"] if entry["state"] == "RESERVED"]
    return recursive.seal(
        {"schema_version": SCHEMA_VERSION, "kind": CATALOG_KIND, "gate": GATE,
         "catalog_sha256": catalog["catalog_sha256"], "active_entries": active,
         "active_cpu_count": len(active), "source_binding": _source_binding(),
         "scientific_claim": False},
        "record_sha256",
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--primary-control-root", type=Path, required=True)
    parser.add_argument("--handoff-root", type=Path, required=True)
    sub = parser.add_subparsers(dest="action", required=True)
    reserve = sub.add_parser("reserve", allow_abbrev=False)
    reserve.add_argument("--consumer-control-root", type=Path, required=True)
    reserve.add_argument("--consumer-bundle-name", required=True)
    reserve.add_argument("--cpu", type=int, action="append", required=True)
    release = sub.add_parser("release", allow_abbrev=False)
    release.add_argument("--consumer-control-root", type=Path, required=True)
    release.add_argument("--consumer-bundle-name", required=True)
    sub.add_parser("status", allow_abbrev=False)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.action == "reserve":
        value = reserve_handoff(
            primary_control_root=args.primary_control_root, handoff_root=args.handoff_root,
            consumer_control_root=args.consumer_control_root,
            consumer_bundle_name=args.consumer_bundle_name, cpus=args.cpu,
        )
    elif args.action == "release":
        value = release_handoff(
            primary_control_root=args.primary_control_root, handoff_root=args.handoff_root,
            consumer_control_root=args.consumer_control_root,
            consumer_bundle_name=args.consumer_bundle_name,
        )
    else:
        value = handoff_status(primary_control_root=args.primary_control_root, handoff_root=args.handoff_root)
    sys.stdout.buffer.write(recursive.canonical_bytes(value) + b"\n")
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (CertifiedSlotHandoffError, recursive.RecursiveSplitError, supervisor.RecursiveSplitSupervisorError, OSError, ValueError, TypeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
