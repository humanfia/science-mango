#!/usr/bin/env python3
"""Isolated, non-authoritative 4/8-thread GRAT pilot for Paper400.

This program deliberately has no integration with the Paper400 terminal,
queue, aggregation, cleanup, supervisor, or systemd code.  Its default mode is
``plan`` and is read-only.  ``run`` accepts only a pristine private root already
reserved by the existing Paper400 CPU catalog, runs ``gratgen`` followed by
the formally verified ``gratchk``, and publishes
only a pilot result manifest.  A pilot result is never a Paper400 certificate
or terminal claim.

The toolchain is supplied through a hash-anchored build manifest.  That
manifest and this wrapper's compiled policy jointly pin both executables and
the complete dynamic-library closure reported by ``ldd``.
Inputs are held open, addressed through /proc/self/fd, and checked by size,
SHA-256, real path, device, inode, and full stat identity before and after both
stages.
"""

from __future__ import annotations

import argparse
import contextlib
import ctypes
import dataclasses
import datetime as dt
import errno
import fcntl
import hashlib
import json
import math
import os
import re
import resource
import signal
import stat
import subprocess
import sys
import time
import uuid
from collections.abc import Iterator, Mapping, Sequence
from pathlib import Path
from typing import Any


SCHEMA_VERSION = 1
GATE = "paper400-grat-parallel-pilot-v1"
PLAN_KIND = "paper400-grat-parallel-pilot-plan-v1"
RESULT_KIND = "paper400-grat-parallel-pilot-result-v1"
WRAPPER_SOURCE_PATH = Path(__file__).resolve()
MAX_WRAPPER_SOURCE_BYTES = 8 << 20
TRUSTED_BUILD_MANIFEST_PATH = Path(
    "/home/jing/paper400-toolchain/grat-1.3.3-pilot-v1/BUILD-MANIFEST.json"
)
TRUSTED_BUILD_MANIFEST_BYTES = 2_245
TRUSTED_BUILD_MANIFEST_SHA256 = (
    "f53178ab4f5372c213411f2acb344133a91995b6e6000674792a20e7ffdfe057"
)
OFFICIAL_SOURCE_ARCHIVE_SHA256 = {
    "gratgen.tgz": "27673b4a87f1651aba9a5d366de2c2bf999f7bb9e11fd84830416cb022aa017f",
    "gratchk-sml.tgz": "0d2f1ef904c4b34711e31f7d5fcfd7f726f60c4fac5e6afa11ef6b3ea86295e1",
}

HASH_CHUNK_BYTES = 8 << 20
MAX_LOCK_BYTES = 8 << 20
MAX_TOOL_BYTES = 2 << 30
MAX_RUNTIME_LIBRARY_BYTES = 4 << 30
DEFAULT_CNF_MAX_BYTES = 16 << 30
DEFAULT_PROOF_MAX_BYTES = 256 << 30
DEFAULT_LOG_LIMIT_BYTES = 64 << 20
DEFAULT_MEMORY_RESERVE_BYTES = 32 << 30
DEFAULT_DISK_RESERVE_BYTES = 64 << 30
MIN_MEMORY_LIMIT_BYTES = {4: 64 << 30, 8: 128 << 30}
MIN_STAGE_TIMEOUT_SECONDS = 60
PRODUCTION_RUN_ROOT = Path("/home/jing/paper400-runs")
TRUSTED_LEASE_CATALOGS = tuple(sorted((
    PRODUCTION_RUN_ROOT / ".paper400-recursive-split-v1/cpu-leases.json",
    PRODUCTION_RUN_ROOT
    / ".paper400-recursive-certified-slot-handoffs-v1/borrow-control/cpu-leases.json",
    PRODUCTION_RUN_ROOT
    / ".paper400-recursive-nested-certified-slot-handoffs-v2/cpu-leases.json",
), key=str))
CPU_CATALOG_KIND = "paper400-dic5-recursive-cpu-lease-catalog-v1"
CPU_RESERVATION_KIND = "paper400-dic5-recursive-cpu-reservation-v1"
CPU_RESERVATION_FIELDS = frozenset((
    "schema_version", "kind", "bundle", "cpus", "observations",
    "kernel_hardware_exclusive", "scheduler_lease_only", "created_at",
    "reservation_sha256",
))
MAX_CATALOG_DISCOVERY_ENTRIES = 16_384
QUIESCENCE_SECONDS = 2.0
MAX_MEMORY_PSI_FULL_AVG10 = 0.10
MAX_MEMORY_PSI_FULL_AVG60 = 0.10
PROCESS_TERM_GRACE_SECONDS = 5

PR_SET_PDEATHSIG = 1
CHILD_PDEATH_SIGNAL = int(signal.SIGKILL)
_LIBC = ctypes.CDLL(None, use_errno=True)
_PRCTL = _LIBC.prctl
_PRCTL.argtypes = [
    ctypes.c_int, ctypes.c_ulong, ctypes.c_ulong, ctypes.c_ulong, ctypes.c_ulong,
]
_PRCTL.restype = ctypes.c_int
F_ADD_SEALS = getattr(fcntl, "F_ADD_SEALS", 1033)
F_GET_SEALS = getattr(fcntl, "F_GET_SEALS", 1034)
F_SEAL_SEAL = getattr(fcntl, "F_SEAL_SEAL", 0x0001)
F_SEAL_SHRINK = getattr(fcntl, "F_SEAL_SHRINK", 0x0002)
F_SEAL_GROW = getattr(fcntl, "F_SEAL_GROW", 0x0004)
F_SEAL_WRITE = getattr(fcntl, "F_SEAL_WRITE", 0x0008)
REQUIRED_MEMFD_SEALS = F_SEAL_SEAL | F_SEAL_SHRINK | F_SEAL_GROW | F_SEAL_WRITE

_TRUSTED_RUNTIME_OBJECTS = {
    "ld-linux-x86-64.so.2": {
        "soname": "ld-linux-x86-64.so.2", "is_loader": True,
        "realpath": "/usr/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2",
        "bytes": 240_936,
        "sha256": "8d06f393f4a93bcf9b81145a259524d66a95522a646bf8d7e05b6ffdf2e63dcc",
    },
    "libc.so.6": {
        "soname": "libc.so.6", "is_loader": False,
        "realpath": "/usr/lib/x86_64-linux-gnu/libc.so.6", "bytes": 2_220_400,
        "sha256": "e01b1ce7be2987f3b8560e26d0df2623f9dd5cec17be923ae28a785bc0d32d50",
    },
    "libgcc_s.so.1": {
        "soname": "libgcc_s.so.1", "is_loader": False,
        "realpath": "/usr/lib/x86_64-linux-gnu/libgcc_s.so.1", "bytes": 125_488,
        "sha256": "fc9d43b2f6c20e53b009238f767c5b949d202389e20de9e202ea684b4ba3729a",
    },
    "libm.so.6": {
        "soname": "libm.so.6", "is_loader": False,
        "realpath": "/usr/lib/x86_64-linux-gnu/libm.so.6", "bytes": 940_560,
        "sha256": "df621c68dbfed7e843434ef2faedb9f4d4b0543ad161e9a55eaf4d4ce2443176",
    },
    "libstdc++.so.6": {
        "soname": "libstdc++.so.6", "is_loader": False,
        "realpath": "/usr/lib/x86_64-linux-gnu/libstdc++.so.6.0.30", "bytes": 2_260_296,
        "sha256": "ff0825e113603c3866680d5d52216bc6d8eedf3a59f52a0aef67ff01994db128",
    },
}
TRUSTED_TOOL_POLICY = {
    "gratgen": {
        "path": "/home/jing/paper400-toolchain/grat-1.3.3-pilot-v1/bin/gratgen",
        "realpath": "/home/jing/paper400-toolchain/grat-1.3.3-pilot-v1/bin/gratgen",
        "bytes": 108_832,
        "sha256": "9c945d7d4b983f3c6c2f40d73b8dd425f7c722edd48f45244f7c6c138ee6fbdb",
        "runtime_kind": "dynamic",
        "runtime_libraries": [
            _TRUSTED_RUNTIME_OBJECTS[name] for name in sorted((
                "ld-linux-x86-64.so.2", "libc.so.6", "libgcc_s.so.1",
                "libm.so.6", "libstdc++.so.6",
            ))
        ],
    },
    "gratchk": {
        "path": "/home/jing/paper400-toolchain/grat-1.3.3-pilot-v1/bin/gratchk",
        "realpath": "/home/jing/paper400-toolchain/grat-1.3.3-pilot-v1/bin/gratchk",
        "bytes": 773_128,
        "sha256": "fc4cf9f93d8b834cf14aa4dee566c39d85e128c86e6cbdeac3c184b0c5d078c1",
        "runtime_kind": "dynamic",
        "runtime_libraries": [
            _TRUSTED_RUNTIME_OBJECTS[name] for name in sorted((
                "ld-linux-x86-64.so.2", "libc.so.6", "libm.so.6",
            ))
        ],
    },
}

PILOT_ROOT_RE = re.compile(r"^paper400-grat-pilot-v1-[A-Za-z0-9][A-Za-z0-9._-]{0,95}$")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
STAGE_NAMES = frozenset(("gratgen", "gratchk"))
FORBIDDEN_ANCESTOR_MARKERS = (
    "queue.json",
    "COMMIT.json",
    "certificate.json",
    "validation.json",
    "split-manifest.json",
    "30-terminal.claim.json",
)


class GratPilotError(RuntimeError):
    """A pilot safety, identity, resource, or verification invariant failed."""


def _canonical_bytes(value: Any) -> bytes:
    try:
        return json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        ).encode("ascii")
    except (TypeError, ValueError, UnicodeEncodeError) as exc:
        raise GratPilotError(f"value is not strict canonical JSON: {exc}") from exc


def _sealed(value: Mapping[str, Any], field: str = "manifest_sha256") -> dict[str, Any]:
    if field in value:
        raise GratPilotError(f"refusing to reseal record containing {field}")
    result = dict(value)
    result[field] = hashlib.sha256(_canonical_bytes(result)).hexdigest()
    return result


def _utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z")


def _sha256_fd(fd: int) -> str:
    digest = hashlib.sha256()
    offset = 0
    while True:
        chunk = os.pread(fd, HASH_CHUNK_BYTES, offset)
        if not chunk:
            break
        digest.update(chunk)
        offset += len(chunk)
    return digest.hexdigest()


def _stat_identity(info: os.stat_result) -> tuple[int, ...]:
    return (
        int(info.st_dev),
        int(info.st_ino),
        int(info.st_mode),
        int(info.st_uid),
        int(info.st_gid),
        int(info.st_nlink),
        int(info.st_size),
        int(info.st_mtime_ns),
        int(info.st_ctime_ns),
    )


def _absolute_normalized(path: Path, role: str) -> Path:
    candidate = Path(path)
    if not candidate.is_absolute() or str(candidate) != os.path.abspath(str(candidate)):
        raise GratPilotError(f"{role} must be an absolute normalized path")
    return candidate


@dataclasses.dataclass
class PinnedFile:
    """An open regular file plus its immutable physical/content identity."""

    role: str
    requested_path: Path
    realpath: Path
    fd: int
    identity: tuple[int, ...]
    sha256: str

    @classmethod
    def open(
        cls,
        path: Path,
        *,
        role: str,
        max_bytes: int,
        require_owner: bool = True,
        require_executable: bool | None = None,
        require_single_link: bool = True,
    ) -> "PinnedFile":
        requested = _absolute_normalized(path, role)
        try:
            realpath = requested.resolve(strict=True)
            lexical = realpath.lstat()
        except (OSError, RuntimeError) as exc:
            raise GratPilotError(f"cannot resolve {role}: {requested}") from exc
        if stat.S_ISLNK(lexical.st_mode) or not stat.S_ISREG(lexical.st_mode):
            raise GratPilotError(f"{role} is not a regular file")
        if require_owner and lexical.st_uid != os.geteuid():
            raise GratPilotError(f"{role} is not owned by the current user")
        if require_single_link and lexical.st_nlink != 1:
            raise GratPilotError(f"{role} must have exactly one hard link")
        if lexical.st_size < 0 or lexical.st_size > max_bytes:
            raise GratPilotError(f"{role} exceeds its configured byte cap")
        executable = bool(lexical.st_mode & stat.S_IXUSR)
        if require_executable is not None and executable != require_executable:
            word = "executable" if require_executable else "non-executable"
            raise GratPilotError(f"{role} must be {word}")

        flags = os.O_RDONLY | os.O_CLOEXEC
        if hasattr(os, "O_NOFOLLOW"):
            flags |= os.O_NOFOLLOW
        try:
            fd = os.open(realpath, flags)
        except OSError as exc:
            raise GratPilotError(f"cannot open {role}: {realpath}") from exc
        try:
            before = os.fstat(fd)
            if _stat_identity(before) != _stat_identity(lexical):
                raise GratPilotError(f"{role} changed before secure open")
            digest = _sha256_fd(fd)
            after = os.fstat(fd)
            if _stat_identity(before) != _stat_identity(after):
                raise GratPilotError(f"{role} changed while hashing")
            if requested.resolve(strict=True) != realpath:
                raise GratPilotError(f"{role} alias changed while hashing")
            return cls(role, requested, realpath, fd, _stat_identity(before), digest)
        except BaseException:
            os.close(fd)
            raise

    @property
    def info(self) -> os.stat_result:
        return os.fstat(self.fd)

    def record(self) -> dict[str, Any]:
        info = self.info
        return {
            "role": self.role,
            "requested_path": str(self.requested_path),
            "realpath": str(self.realpath),
            "device": int(info.st_dev),
            "inode": int(info.st_ino),
            "bytes": int(info.st_size),
            "sha256": self.sha256,
            "mode": stat.S_IMODE(info.st_mode),
            "uid": int(info.st_uid),
            "gid": int(info.st_gid),
            "links": int(info.st_nlink),
            "mtime_ns": int(info.st_mtime_ns),
            "ctime_ns": int(info.st_ctime_ns),
        }

    def read_bytes(self, *, max_bytes: int) -> bytes:
        info = self.info
        if info.st_size > max_bytes:
            raise GratPilotError(f"{self.role} exceeds read cap")
        payload = bytearray()
        offset = 0
        while offset < info.st_size:
            chunk = os.pread(self.fd, min(HASH_CHUNK_BYTES, info.st_size - offset), offset)
            if not chunk:
                raise GratPilotError(f"short read from {self.role}")
            payload.extend(chunk)
            offset += len(chunk)
        return bytes(payload)

    def reverify(self, *, full_hash: bool) -> None:
        try:
            current = os.fstat(self.fd)
            resolved = self.requested_path.resolve(strict=True)
            path_info = self.realpath.lstat()
        except (OSError, RuntimeError) as exc:
            raise GratPilotError(f"{self.role} disappeared during pilot") from exc
        if resolved != self.realpath:
            raise GratPilotError(f"{self.role} alias changed during pilot")
        if _stat_identity(current) != self.identity or _stat_identity(path_info) != self.identity:
            raise GratPilotError(f"{self.role} physical identity changed during pilot")
        if full_hash and _sha256_fd(self.fd) != self.sha256:
            raise GratPilotError(f"{self.role} content hash changed during pilot")

    def close(self) -> None:
        if self.fd >= 0:
            os.close(self.fd)
            self.fd = -1

    def __enter__(self) -> "PinnedFile":
        return self

    def __exit__(self, *_: object) -> None:
        self.close()


def _require_sha256(value: Any, role: str) -> str:
    if not isinstance(value, str) or SHA256_RE.fullmatch(value) is None:
        raise GratPilotError(f"{role} must be a lowercase SHA-256 digest")
    return value


def _require_positive_int(value: Any, role: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        raise GratPilotError(f"{role} must be a positive integer")
    return value


def _load_json_object(pin: PinnedFile, *, max_bytes: int) -> dict[str, Any]:
    try:
        value = json.loads(pin.read_bytes(max_bytes=max_bytes))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise GratPilotError(f"invalid JSON in {pin.role}") from exc
    if not isinstance(value, dict):
        raise GratPilotError(f"{pin.role} must contain a JSON object")
    return value


def _probe_runtime(executable: Path) -> tuple[str, list[tuple[str, Path, bool]]]:
    """Return runtime kind and ``(soname, realpath, is_loader)`` closure."""

    ldd = Path("/usr/bin/ldd")
    if not ldd.is_file():
        raise GratPilotError("/usr/bin/ldd is required to verify runtime closure")
    completed = subprocess.run(
        [str(ldd), str(executable)],
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        env={"PATH": "/usr/bin:/bin", "LANG": "C", "LC_ALL": "C"},
        check=False,
        timeout=30,
    )
    text = completed.stdout.decode("utf-8", errors="replace")
    lowered = text.lower()
    if "not a dynamic executable" in lowered or "statically linked" in lowered:
        return "static", []
    if completed.returncode != 0:
        raise GratPilotError(f"ldd failed for pinned executable: {executable}")
    if "=> not found" in text:
        raise GratPilotError(f"unresolved runtime library for: {executable}")
    objects: dict[str, tuple[Path, bool]] = {}
    for line in text.splitlines():
        dynamic = re.match(r"\s*(\S+)\s+=>\s+(/\S+)\s+\(", line)
        direct = re.match(r"\s*(/\S+)\s+\(", line) if dynamic is None else None
        if dynamic is not None or direct is not None:
            try:
                if dynamic is not None:
                    soname = dynamic.group(1)
                    path_text = dynamic.group(2)
                else:
                    assert direct is not None
                    path_text = direct.group(1)
                    soname = Path(path_text).name
                realpath = Path(path_text).resolve(strict=True)
            except (OSError, RuntimeError) as exc:
                raise GratPilotError("runtime library disappeared during ldd") from exc
            is_loader = soname.startswith("ld-linux-") or soname.startswith("ld-musl-")
            prior = objects.get(soname)
            if prior is not None and prior != (realpath, is_loader):
                raise GratPilotError("duplicate runtime SONAME resolves ambiguously")
            objects[soname] = (realpath, is_loader)
    if not objects:
        raise GratPilotError(f"dynamic runtime closure is empty: {executable}")
    result = [
        (soname, value[0], value[1])
        for soname, value in sorted(objects.items())
    ]
    if sum(is_loader for _, _, is_loader in result) != 1:
        raise GratPilotError("dynamic runtime must have exactly one ELF loader")
    return "dynamic", result


@dataclasses.dataclass
class RuntimeObject:
    soname: str
    is_loader: bool
    file: PinnedFile

    def record(self) -> dict[str, Any]:
        return {
            "soname": self.soname,
            "is_loader": self.is_loader,
            "file": self.file.record(),
        }


@dataclasses.dataclass
class ToolBinding:
    name: str
    binary: PinnedFile
    runtime_kind: str
    libraries: list[RuntimeObject]

    def record(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "binary": self.binary.record(),
            "runtime_kind": self.runtime_kind,
            "runtime_libraries": [item.record() for item in self.libraries],
        }

    def close(self) -> None:
        for item in reversed(self.libraries):
            item.file.close()
        self.binary.close()


@dataclasses.dataclass
class ToolchainBinding:
    lock: PinnedFile
    tools: dict[str, ToolBinding]
    initial_record: dict[str, Any]

    def record(self) -> dict[str, Any]:
        return self.initial_record

    def reverify(self) -> None:
        self.lock.reverify(full_hash=True)
        for name in ("gratgen", "gratchk"):
            binding = self.tools[name]
            binding.binary.reverify(full_hash=True)
            for library in binding.libraries:
                library.file.reverify(full_hash=True)
            runtime_kind, runtime_objects = _probe_runtime(binding.binary.realpath)
            if runtime_kind != binding.runtime_kind:
                raise GratPilotError(f"{name} runtime kind changed during pilot")
            if [
                (soname, str(path), is_loader)
                for soname, path, is_loader in runtime_objects
            ] != [
                (item.soname, str(item.file.realpath), item.is_loader)
                for item in binding.libraries
            ]:
                raise GratPilotError(f"{name} runtime closure changed during pilot")

    def close(self) -> None:
        for name in reversed(("gratgen", "gratchk")):
            if name in self.tools:
                self.tools[name].close()
        self.lock.close()

    def __enter__(self) -> "ToolchainBinding":
        return self

    def __exit__(self, *_: object) -> None:
        self.close()


def _open_toolchain(lock_path: Path) -> ToolchainBinding:
    lock = PinnedFile.open(
        lock_path,
        role="toolchain lock",
        max_bytes=MAX_LOCK_BYTES,
        require_executable=False,
    )
    tools: dict[str, ToolBinding] = {}
    try:
        payload = _load_json_object(lock, max_bytes=MAX_LOCK_BYTES)
        if (
            lock.realpath != TRUSTED_BUILD_MANIFEST_PATH
            or lock.info.st_size != TRUSTED_BUILD_MANIFEST_BYTES
            or lock.sha256 != TRUSTED_BUILD_MANIFEST_SHA256
        ):
            raise GratPilotError("build manifest does not match compiled trust anchor")
        try:
            inputs = payload["inputs"]
            artifacts = payload["artifacts"]
            source_hashes = {
                name: inputs[name]["sha256"] for name in OFFICIAL_SOURCE_ARCHIVE_SHA256
            }
            artifact_hashes = {
                name: artifacts[name]["sha256"] for name in ("gratgen", "gratchk")
            }
        except (KeyError, TypeError) as exc:
            raise GratPilotError("trusted build manifest schema is incomplete") from exc
        if (
            payload.get("kind") != "paper400-grat-toolchain-build-v1"
            or payload.get("version") != SCHEMA_VERSION
            or payload.get("production_eligible") is not False
            or source_hashes != OFFICIAL_SOURCE_ARCHIVE_SHA256
            or artifact_hashes != {
                name: TRUSTED_TOOL_POLICY[name]["sha256"]
                for name in ("gratgen", "gratchk")
            }
        ):
            raise GratPilotError("trusted build manifest semantic binding failed")
        specs = TRUSTED_TOOL_POLICY

        for name in ("gratgen", "gratchk"):
            spec = specs[name]
            expected_fields = {
                "path", "realpath", "bytes", "sha256", "runtime_kind",
                "runtime_libraries",
            }
            if not isinstance(spec, dict) or set(spec) != expected_fields:
                raise GratPilotError(f"unexpected fields in {name} tool lock")
            path = Path(spec["path"]) if isinstance(spec["path"], str) else Path("")
            binary = PinnedFile.open(
                path,
                role=f"{name} binary",
                max_bytes=MAX_TOOL_BYTES,
                require_owner=False,
                require_executable=True,
                require_single_link=False,
            )
            try:
                expected_bytes = _require_positive_int(spec["bytes"], f"{name} bytes")
                expected_hash = _require_sha256(spec["sha256"], f"{name} sha256")
                if (
                    str(binary.realpath) != spec["realpath"]
                    or binary.info.st_size != expected_bytes
                    or binary.sha256 != expected_hash
                ):
                    raise GratPilotError(f"{name} binary does not match toolchain lock")
                runtime_kind, runtime_objects = _probe_runtime(binary.realpath)
                if spec["runtime_kind"] not in {"static", "dynamic"}:
                    raise GratPilotError(f"invalid runtime kind for {name}")
                if runtime_kind != spec["runtime_kind"]:
                    raise GratPilotError(f"{name} runtime kind does not match lock")
                library_specs = spec["runtime_libraries"]
                if not isinstance(library_specs, list):
                    raise GratPilotError(f"{name} runtime_libraries must be a list")
                expected_by_soname: dict[str, dict[str, Any]] = {}
                for item in library_specs:
                    if not isinstance(item, dict) or set(item) != {
                        "soname", "is_loader", "realpath", "bytes", "sha256",
                    }:
                        raise GratPilotError(f"invalid runtime library lock for {name}")
                    soname = item["soname"]
                    if (
                        not isinstance(soname, str)
                        or "/" in soname
                        or soname in {"", ".", ".."}
                        or soname in expected_by_soname
                        or type(item["is_loader"]) is not bool
                        or not isinstance(item["realpath"], str)
                    ):
                        raise GratPilotError(f"duplicate/invalid runtime library for {name}")
                    expected_by_soname[soname] = item
                observed_closure = [
                    (soname, str(path), is_loader)
                    for soname, path, is_loader in runtime_objects
                ]
                expected_closure = [
                    (
                        soname,
                        expected_by_soname[soname]["realpath"],
                        expected_by_soname[soname]["is_loader"],
                    )
                    for soname in sorted(expected_by_soname)
                ]
                if expected_closure != observed_closure:
                    raise GratPilotError(f"{name} runtime closure does not match lock")
                libraries: list[RuntimeObject] = []
                try:
                    for index, (soname, runtime_path, is_loader) in enumerate(runtime_objects):
                        item = expected_by_soname[soname]
                        library = PinnedFile.open(
                            runtime_path,
                            role=f"{name} runtime library {index}",
                            max_bytes=MAX_RUNTIME_LIBRARY_BYTES,
                            require_owner=False,
                            require_executable=None,
                            require_single_link=False,
                        )
                        if (
                            library.info.st_size
                            != _require_positive_int(item["bytes"], "runtime library bytes")
                            or library.sha256
                            != _require_sha256(item["sha256"], "runtime library sha256")
                        ):
                            raise GratPilotError(f"runtime library hash mismatch for {name}")
                        libraries.append(RuntimeObject(soname, is_loader, library))
                    tools[name] = ToolBinding(name, binary, runtime_kind, libraries)
                except BaseException:
                    for library in reversed(libraries):
                        library.file.close()
                    raise
            except BaseException:
                binary.close()
                raise

        initial = {
            "lock": lock.record(),
            "tools": {name: tools[name].record() for name in ("gratgen", "gratchk")},
        }
        return ToolchainBinding(lock, tools, initial)
    except BaseException:
        for binding in reversed(list(tools.values())):
            binding.close()
        lock.close()
        raise


@dataclasses.dataclass(frozen=True)
class PilotConfig:
    cnf: Path
    proof: Path
    expected_cnf_sha256: str
    expected_proof_sha256: str
    expected_cnf_bytes: int
    expected_proof_bytes: int
    proof_format: str
    output_root: Path
    toolchain_lock: Path
    threads: int
    cpus: tuple[int, ...]
    lease_catalogs: tuple[Path, ...]
    reservation_sha256: str
    memory_limit_bytes: int
    memory_reserve_bytes: int
    output_limit_bytes: int
    disk_reserve_bytes: int
    log_limit_bytes: int
    stage_timeout_seconds: int
    cnf_max_bytes: int = DEFAULT_CNF_MAX_BYTES
    proof_max_bytes: int = DEFAULT_PROOF_MAX_BYTES
    label: str = "paper400"


def _memory_available_bytes() -> int:
    try:
        for line in Path("/proc/meminfo").read_text(encoding="ascii").splitlines():
            if line.startswith("MemAvailable:"):
                fields = line.split()
                return int(fields[1]) * 1024
    except (OSError, ValueError, IndexError) as exc:
        raise GratPilotError("cannot read MemAvailable") from exc
    raise GratPilotError("MemAvailable is absent from /proc/meminfo")


def _read_integer_mapping(path: Path) -> dict[str, int]:
    result: dict[str, int] = {}
    try:
        lines = path.read_text(encoding="ascii").splitlines()
        for line in lines:
            key, raw = line.split()
            result[key] = int(raw)
    except (OSError, ValueError) as exc:
        raise GratPilotError(f"cannot parse cgroup counter file: {path.name}") from exc
    return result


def _read_pressure(path: Path) -> dict[str, dict[str, float | int]]:
    result: dict[str, dict[str, float | int]] = {}
    try:
        for line in path.read_text(encoding="ascii").splitlines():
            fields = line.split()
            if not fields or fields[0] not in {"some", "full"}:
                raise ValueError("invalid pressure class")
            values: dict[str, float | int] = {}
            for field in fields[1:]:
                key, raw = field.split("=", 1)
                values[key] = int(raw) if key == "total" else float(raw)
            result[fields[0]] = values
    except (OSError, ValueError) as exc:
        raise GratPilotError("cannot parse cgroup memory pressure") from exc
    return result


def _cgroup_root() -> Path:
    try:
        lines = Path("/proc/self/cgroup").read_text(encoding="ascii").splitlines()
        matches = [line.split("::", 1)[1] for line in lines if line.startswith("0::")]
    except (OSError, IndexError) as exc:
        raise GratPilotError("cannot resolve cgroup v2 membership") from exc
    if len(matches) != 1:
        raise GratPilotError("unambiguous cgroup v2 membership is unavailable")
    result = Path("/sys/fs/cgroup") / matches[0].lstrip("/")
    if not result.is_dir() or result.is_symlink():
        raise GratPilotError("cgroup v2 directory is unavailable")
    return result


def _cgroup_resource_snapshot() -> dict[str, Any]:
    cgroup = _cgroup_root()
    try:
        current = int((cgroup / "memory.current").read_text(encoding="ascii").strip())
        maximum_raw = (cgroup / "memory.max").read_text(encoding="ascii").strip()
        maximum = None if maximum_raw == "max" else int(maximum_raw)
    except (OSError, ValueError) as exc:
        raise GratPilotError("cannot read cgroup memory capacity") from exc
    if current < 0 or (maximum is not None and maximum <= 0):
        raise GratPilotError("invalid cgroup memory capacity")
    events = _read_integer_mapping(cgroup / "memory.events")
    pressure = _read_pressure(cgroup / "memory.pressure")
    full = pressure.get("full", {})
    avg10 = float(full.get("avg10", math.inf))
    avg60 = float(full.get("avg60", math.inf))
    return {
        "path": str(cgroup),
        "memory_current": current,
        "memory_max": maximum,
        "memory_events": events,
        "memory_pressure": pressure,
        "psi_full_avg10": avg10,
        "psi_full_avg60": avg60,
    }


def _assert_cgroup_unchanged(baseline: Mapping[str, Any]) -> dict[str, Any]:
    current = _cgroup_resource_snapshot()
    for name in ("oom", "oom_kill", "oom_group_kill"):
        before = int(baseline["memory_events"].get(name, 0))
        after = int(current["memory_events"].get(name, 0))
        if after != before:
            raise GratPilotError(f"cgroup {name} counter changed during pilot")
    if (
        current["psi_full_avg10"] > MAX_MEMORY_PSI_FULL_AVG10
        or current["psi_full_avg60"] > MAX_MEMORY_PSI_FULL_AVG60
    ):
        raise GratPilotError("cgroup memory pressure exceeded pilot threshold")
    return current


def _proc_start_ticks(proc: Path) -> int | None:
    try:
        raw = (proc / "stat").read_text(encoding="ascii")
        tail = raw[raw.rfind(")") + 2 :].split()
        return int(tail[19])
    except (OSError, ValueError, IndexError):
        return None


def _proof_holders(proof: PinnedFile) -> dict[str, list[dict[str, Any]]]:
    target = (proof.info.st_dev, proof.info.st_ino)
    readers: list[dict[str, Any]] = []
    writers: list[dict[str, Any]] = []
    mapped_writers: list[dict[str, Any]] = []
    for proc in sorted(Path("/proc").iterdir(), key=lambda item: item.name):
        if not proc.name.isdecimal():
            continue
        try:
            if proc.stat().st_uid != os.geteuid():
                continue
            descriptors = list((proc / "fd").iterdir())
        except (FileNotFoundError, PermissionError, ProcessLookupError):
            continue
        for descriptor in descriptors:
            try:
                info = descriptor.stat()
                if (info.st_dev, info.st_ino) != target:
                    continue
                fdinfo = (proc / "fdinfo" / descriptor.name).read_text(encoding="ascii")
                flags_line = next(line for line in fdinfo.splitlines() if line.startswith("flags:"))
                flags = int(flags_line.split()[1], 8)
                record = {
                    "pid": int(proc.name),
                    "proc_start_ticks": _proc_start_ticks(proc),
                    "fd": int(descriptor.name),
                    "access_mode": flags & os.O_ACCMODE,
                }
                (readers if record["access_mode"] == os.O_RDONLY else writers).append(record)
            except (OSError, ValueError, StopIteration):
                continue
        try:
            maps = (proc / "maps").read_text(encoding="utf-8", errors="replace").splitlines()
        except (OSError, PermissionError):
            continue
        for line in maps:
            fields = line.split(maxsplit=5)
            if len(fields) < 5 or "w" not in fields[1]:
                continue
            try:
                major_text, minor_text = fields[3].split(":", 1)
                device = os.makedev(int(major_text, 16), int(minor_text, 16))
                inode = int(fields[4])
            except ValueError:
                continue
            if (device, inode) == target:
                mapped_writers.append({
                    "pid": int(proc.name),
                    "proc_start_ticks": _proc_start_ticks(proc),
                    "permissions": fields[1],
                })
        if len(readers) + len(writers) + len(mapped_writers) > 4096:
            raise GratPilotError("proof holder inventory exceeded its bound")
    return {"readers": readers, "writers": writers, "writable_mappings": mapped_writers}


def _proof_quiescence(proof: PinnedFile) -> dict[str, Any]:
    first = _proof_holders(proof)
    if first["writers"] or first["writable_mappings"]:
        raise GratPilotError("input proof still has a writable holder")
    before = proof.identity
    time.sleep(QUIESCENCE_SECONDS)
    proof.reverify(full_hash=False)
    second = _proof_holders(proof)
    if second["writers"] or second["writable_mappings"]:
        raise GratPilotError("input proof gained a writable holder")
    if _stat_identity(proof.info) != before:
        raise GratPilotError("input proof changed during quiescence window")
    return {
        "quiescence_seconds": QUIESCENCE_SECONDS,
        "first": first,
        "second": second,
        "no_writable_fd_or_mapping": True,
        "stable_physical_identity": True,
        "transport_stopped_evidence_only": True,
    }


def _disk_available_bytes(path: Path) -> int:
    try:
        info = os.statvfs(path)
    except OSError as exc:
        raise GratPilotError(f"cannot inspect disk availability: {path}") from exc
    return int(info.f_bavail) * int(info.f_frsize)


def _validate_private_directory(path: Path, role: str) -> Path:
    candidate = _absolute_normalized(path, role)
    try:
        realpath = candidate.resolve(strict=True)
        info = candidate.lstat()
    except (OSError, RuntimeError) as exc:
        raise GratPilotError(f"cannot resolve {role}") from exc
    if (
        realpath != candidate
        or stat.S_ISLNK(info.st_mode)
        or not stat.S_ISDIR(info.st_mode)
        or info.st_uid != os.geteuid()
        or stat.S_IMODE(info.st_mode) != 0o700
    ):
        raise GratPilotError(f"{role} must be an owned, normalized mode-0700 directory")
    return candidate


def _validate_output_root(config: PilotConfig, inputs: Sequence[PinnedFile]) -> Path:
    root = _absolute_normalized(config.output_root, "output root")
    if PILOT_ROOT_RE.fullmatch(root.name) is None:
        raise GratPilotError("output root must use the paper400-grat-pilot-v1-* namespace")
    root = _validate_private_directory(root, "pre-reserved pilot output root")
    run_root = _validate_private_directory(PRODUCTION_RUN_ROOT, "Paper400 run root")
    if not root.is_relative_to(run_root) or root == run_root:
        raise GratPilotError("pilot output root must be a dedicated child of Paper400 run root")
    parent = _validate_private_directory(root.parent, "output parent")
    try:
        entries = sorted(item.name for item in root.iterdir())
    except OSError as exc:
        raise GratPilotError("cannot inventory pilot output root") from exc
    if entries != ["cpu-reservation.json"]:
        raise GratPilotError(
            "pilot output root must be pristine except for its external CPU reservation"
        )
    for ancestor in (parent, *parent.parents):
        for marker in FORBIDDEN_ANCESTOR_MARKERS:
            if (ancestor / marker).exists() or (ancestor / marker).is_symlink():
                raise GratPilotError("output root is inside a Paper400 authority/terminal tree")
    for item in inputs:
        if item.realpath.is_relative_to(root) or root.is_relative_to(item.realpath.parent):
            raise GratPilotError("output root overlaps an input tree")
    return root


def _validate_config(config: PilotConfig) -> None:
    if config.threads not in (4, 8):
        raise GratPilotError("threads must be exactly 4 or 8")
    if len(config.cpus) != config.threads or len(set(config.cpus)) != config.threads:
        raise GratPilotError("CPU list must contain one distinct CPU per GRAT thread")
    if any(isinstance(cpu, bool) or not isinstance(cpu, int) or cpu < 0 for cpu in config.cpus):
        raise GratPilotError("CPU identifiers must be non-negative integers")
    if config.cpus != tuple(sorted(config.cpus)):
        raise GratPilotError("CPU list must be strictly increasing")
    if config.lease_catalogs != TRUSTED_LEASE_CATALOGS or len(config.lease_catalogs) != 3:
        raise GratPilotError("lease catalogs must be the three compiled absolute paths in order")
    allowed = os.sched_getaffinity(0)
    if not set(config.cpus).issubset(allowed):
        raise GratPilotError("requested CPU is outside the pilot process affinity")
    if config.proof_format not in {"ascii", "binary"}:
        raise GratPilotError("proof format must be ascii or binary")
    _require_sha256(config.expected_cnf_sha256, "expected CNF sha256")
    _require_sha256(config.expected_proof_sha256, "expected proof sha256")
    _require_sha256(config.reservation_sha256, "CPU reservation sha256")
    _require_positive_int(config.expected_cnf_bytes, "expected CNF bytes")
    _require_positive_int(config.expected_proof_bytes, "expected proof bytes")
    for value, role in (
        (config.cnf_max_bytes, "CNF cap"),
        (config.proof_max_bytes, "proof cap"),
        (config.memory_limit_bytes, "memory limit"),
        (config.memory_reserve_bytes, "memory reserve"),
        (config.output_limit_bytes, "output limit"),
        (config.disk_reserve_bytes, "disk reserve"),
        (config.log_limit_bytes, "log limit"),
        (config.stage_timeout_seconds, "stage timeout"),
    ):
        _require_positive_int(value, role)
    if config.expected_cnf_bytes > config.cnf_max_bytes:
        raise GratPilotError("expected CNF exceeds cap")
    if config.expected_proof_bytes > config.proof_max_bytes:
        raise GratPilotError("expected proof exceeds cap")
    if config.memory_limit_bytes < MIN_MEMORY_LIMIT_BYTES[config.threads]:
        raise GratPilotError("memory limit is below the conservative thread-count minimum")
    if config.stage_timeout_seconds < MIN_STAGE_TIMEOUT_SECONDS:
        raise GratPilotError("stage timeout is too small")
    if not config.label or len(config.label) > 128 or any(ord(ch) < 32 for ch in config.label):
        raise GratPilotError("invalid pilot label")
    for rlimit_name, requested in (
        (resource.RLIMIT_AS, config.memory_limit_bytes),
        (resource.RLIMIT_FSIZE, max(config.output_limit_bytes, config.log_limit_bytes)),
    ):
        _, hard = resource.getrlimit(rlimit_name)
        if hard != resource.RLIM_INFINITY and requested > hard:
            raise GratPilotError("requested child resource limit exceeds current hard limit")


def _discover_lease_catalogs() -> tuple[Path, ...]:
    """Boundedly discover the existing Paper400 scheduler catalog inventory."""

    root = _validate_private_directory(PRODUCTION_RUN_ROOT, "Paper400 run root")
    discovered: set[Path] = set()
    examined = 0
    try:
        first_level = sorted(root.iterdir(), key=lambda item: item.name)
    except OSError as exc:
        raise GratPilotError("cannot inventory Paper400 lease catalogs") from exc
    for first in first_level:
        examined += 1
        if examined > MAX_CATALOG_DISCOVERY_ENTRIES:
            raise GratPilotError("lease catalog discovery exceeded its bound")
        try:
            first_info = first.lstat()
        except OSError as exc:
            raise GratPilotError("lease catalog inventory changed") from exc
        if stat.S_ISLNK(first_info.st_mode) or not stat.S_ISDIR(first_info.st_mode):
            continue
        candidate = first / "cpu-leases.json"
        if candidate.exists() or candidate.is_symlink():
            discovered.add(candidate)
        try:
            second_level = sorted(first.iterdir(), key=lambda item: item.name)
        except OSError as exc:
            raise GratPilotError("lease catalog inventory changed") from exc
        for second in second_level:
            examined += 1
            if examined > MAX_CATALOG_DISCOVERY_ENTRIES:
                raise GratPilotError("lease catalog discovery exceeded its bound")
            try:
                second_info = second.lstat()
            except OSError as exc:
                raise GratPilotError("lease catalog inventory changed") from exc
            if stat.S_ISLNK(second_info.st_mode) or not stat.S_ISDIR(second_info.st_mode):
                continue
            candidate = second / "cpu-leases.json"
            if candidate.exists() or candidate.is_symlink():
                discovered.add(candidate)
    return tuple(sorted(discovered, key=str))


def _selfhash_valid(value: Mapping[str, Any], field: str) -> bool:
    if type(value) is not dict or not _require_sha256_or_false(value.get(field)):
        return False
    unsigned = dict(value)
    digest = unsigned.pop(field)
    return hashlib.sha256(_canonical_bytes(unsigned)).hexdigest() == digest


def _require_sha256_or_false(value: Any) -> bool:
    return type(value) is str and SHA256_RE.fullmatch(value) is not None


def _read_catalog(pin: PinnedFile) -> dict[str, Any]:
    value = _load_json_object(pin, max_bytes=MAX_LOCK_BYTES)
    if (
        set(value) != {"schema_version", "kind", "leases", "updated_at", "catalog_sha256"}
        or value.get("schema_version") != SCHEMA_VERSION
        or value.get("kind") != CPU_CATALOG_KIND
        or not _selfhash_valid(value, "catalog_sha256")
        or type(value.get("leases")) is not list
        or type(value.get("updated_at")) not in {int, float}
        or not math.isfinite(float(value["updated_at"]))
    ):
        raise GratPilotError("CPU lease catalog schema/self-hash mismatch")
    seen_active: set[int] = set()
    for entry in value["leases"]:
        if (
            type(entry) is not dict
            or set(entry) != {
                "cpu", "bundle", "reservation_sha256", "state", "created_at", "released_at",
            }
            or type(entry.get("cpu")) is not int
            or entry["cpu"] < 0
            or type(entry.get("bundle")) is not str
            or not _require_sha256_or_false(entry.get("reservation_sha256"))
            or entry.get("state") not in {"RESERVED", "RELEASED"}
            or type(entry.get("created_at")) not in {int, float}
            or not math.isfinite(float(entry["created_at"]))
            or (
                entry.get("released_at") is not None
                and (
                    type(entry["released_at"]) not in {int, float}
                    or not math.isfinite(float(entry["released_at"]))
                )
            )
        ):
            raise GratPilotError("CPU lease catalog contains a malformed entry")
        if entry["state"] == "RESERVED":
            if entry["cpu"] in seen_active:
                raise GratPilotError("CPU lease catalog duplicates an active CPU")
            seen_active.add(entry["cpu"])
    return value


def _read_reservation(config: PilotConfig) -> tuple[PinnedFile, dict[str, Any]]:
    pin = PinnedFile.open(
        config.output_root / "cpu-reservation.json",
        role="external pilot CPU reservation",
        max_bytes=MAX_LOCK_BYTES,
        require_executable=False,
    )
    try:
        value = _load_json_object(pin, max_bytes=MAX_LOCK_BYTES)
        if (
            set(value) != CPU_RESERVATION_FIELDS
            or value.get("schema_version") != SCHEMA_VERSION
            or value.get("kind") != CPU_RESERVATION_KIND
            or value.get("bundle") != str(config.output_root)
            or value.get("cpus") != sorted(config.cpus)
            or type(value.get("observations")) is not list
            or value.get("kernel_hardware_exclusive") is not False
            or value.get("scheduler_lease_only") is not True
            or type(value.get("created_at")) not in {int, float}
            or not math.isfinite(float(value["created_at"]))
            or value.get("reservation_sha256") != config.reservation_sha256
            or not _selfhash_valid(value, "reservation_sha256")
        ):
            raise GratPilotError("external pilot CPU reservation is malformed or cross-bound")
        return pin, value
    except BaseException:
        pin.close()
        raise


def _open_catalog_lock(catalog: Path) -> int:
    path = catalog.with_name("cpu-leases.lock")
    flags = os.O_RDWR | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        fd = os.open(path, flags)
    except OSError as exc:
        raise GratPilotError(f"existing scheduler lock is unavailable: {path}") from exc
    try:
        info = os.fstat(fd)
        edge = path.lstat()
        if (
            not stat.S_ISREG(info.st_mode)
            or info.st_uid != os.geteuid()
            or info.st_nlink != 1
            or stat.S_IMODE(info.st_mode) != 0o600
            or (info.st_dev, info.st_ino) != (edge.st_dev, edge.st_ino)
        ):
            raise GratPilotError("existing scheduler lock metadata is unsafe")
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise GratPilotError(f"existing scheduler lock is busy: {path}") from exc
        return fd
    except BaseException:
        os.close(fd)
        raise


@contextlib.contextmanager
def _locked_catalog_authority(config: PilotConfig) -> Iterator[dict[str, Any]]:
    """Briefly hold every catalog lock and prove one exact pilot owner/CPU."""

    configured = tuple(sorted(
        (_absolute_normalized(path, "lease catalog") for path in config.lease_catalogs),
        key=str,
    ))
    if configured != TRUSTED_LEASE_CATALOGS or len(configured) != 3:
        raise GratPilotError("lease catalog set differs from the compiled three-path policy")
    if _discover_lease_catalogs() != configured:
        raise GratPilotError("configured catalogs differ from bounded production discovery")
    locks: list[int] = []
    catalogs: list[PinnedFile] = []
    reservation: PinnedFile | None = None
    try:
        for catalog_path in configured:
            locks.append(_open_catalog_lock(catalog_path))
        if _discover_lease_catalogs() != configured:
            raise GratPilotError("catalog inventory changed under scheduler locks")
        owners: dict[int, dict[str, tuple[str, str]]] = {
            cpu: {} for cpu in config.cpus
        }
        catalog_records: list[dict[str, Any]] = []
        for catalog_path in configured:
            pin = PinnedFile.open(
                catalog_path,
                role="Paper400 CPU lease catalog",
                max_bytes=MAX_LOCK_BYTES,
                require_executable=False,
            )
            catalogs.append(pin)
            if stat.S_IMODE(pin.info.st_mode) != 0o600:
                raise GratPilotError("CPU lease catalog must be mode 0600")
            value = _read_catalog(pin)
            for entry in value["leases"]:
                if entry["state"] == "RESERVED" and entry["cpu"] in owners:
                    catalog_key = str(catalog_path)
                    if catalog_key in owners[entry["cpu"]]:
                        raise GratPilotError("CPU has duplicate owners in one catalog")
                    owners[entry["cpu"]][catalog_key] = (
                        entry["bundle"], entry["reservation_sha256"],
                    )
            record = pin.record()
            record["catalog_sha256"] = value["catalog_sha256"]
            catalog_records.append(record)
        expected_catalogs = {str(path) for path in configured}
        expected_owner = (str(config.output_root), config.reservation_sha256)
        for cpu in config.cpus:
            if set(owners[cpu]) != expected_catalogs:
                raise GratPilotError(
                    f"CPU {cpu} lacks exactly one reservation in every scheduler catalog"
                )
            if any(owner != expected_owner for owner in owners[cpu].values()):
                raise GratPilotError(f"CPU {cpu} has a mismatched scheduler owner")
        reservation, reservation_value = _read_reservation(config)
        record = {
            "run_root": str(PRODUCTION_RUN_ROOT),
            "catalogs": catalog_records,
            "catalog_locks_held_during_snapshot": True,
            "reservation": reservation.record(),
            "reservation_sha256": reservation_value["reservation_sha256"],
            "bundle": str(config.output_root),
            "cpus": sorted(config.cpus),
            "scheduler_lease_only": True,
            "catalog_mutation_by_pilot": False,
        }
        yield record
        reservation.reverify(full_hash=True)
        for pin in catalogs:
            pin.reverify(full_hash=True)
        if _discover_lease_catalogs() != configured:
            raise GratPilotError("catalog inventory changed before lease release")
    finally:
        if reservation is not None:
            reservation.close()
        for pin in reversed(catalogs):
            pin.close()
        for fd in reversed(locks):
            with contextlib.suppress(OSError):
                fcntl.flock(fd, fcntl.LOCK_UN)
            with contextlib.suppress(OSError):
                os.close(fd)


def _catalog_authority_snapshot(config: PilotConfig) -> dict[str, Any]:
    """Take one short locked snapshot; no lock may span a GRAT stage."""

    with _locked_catalog_authority(config) as record:
        return record


@dataclasses.dataclass
class ValidatedContext:
    config: PilotConfig
    source: PinnedFile
    cnf: PinnedFile
    proof: PinnedFile
    toolchain: ToolchainBinding
    scheduler_authority: dict[str, Any]
    proof_quiescence: dict[str, Any]
    resources: dict[str, Any]
    plan: dict[str, Any]

    def close(self) -> None:
        try:
            self.toolchain.close()
        finally:
            try:
                self.proof.close()
            finally:
                try:
                    self.cnf.close()
                finally:
                    self.source.close()

    def __enter__(self) -> "ValidatedContext":
        return self

    def __exit__(self, *_: object) -> None:
        self.close()


def _prepare_context(config: PilotConfig) -> ValidatedContext:
    _validate_config(config)
    source = PinnedFile.open(
        WRAPPER_SOURCE_PATH,
        role="pilot wrapper source",
        max_bytes=MAX_WRAPPER_SOURCE_BYTES,
        require_executable=False,
    )
    cnf: PinnedFile | None = None
    proof: PinnedFile | None = None
    toolchain: ToolchainBinding | None = None
    try:
        if source.info.st_size == 0:
            raise GratPilotError("pilot wrapper source must be non-empty")
        cnf = PinnedFile.open(
            config.cnf,
            role="input CNF",
            max_bytes=config.cnf_max_bytes,
            require_executable=False,
        )
        proof = PinnedFile.open(
            config.proof,
            role="input DRAT proof",
            max_bytes=config.proof_max_bytes,
            require_executable=False,
        )
        if (cnf.info.st_dev, cnf.info.st_ino) == (proof.info.st_dev, proof.info.st_ino):
            raise GratPilotError("CNF and proof alias the same physical file")
        if (
            cnf.sha256 != config.expected_cnf_sha256
            or cnf.info.st_size != config.expected_cnf_bytes
        ):
            raise GratPilotError("CNF does not match expected immutable identity")
        if (
            proof.sha256 != config.expected_proof_sha256
            or proof.info.st_size != config.expected_proof_bytes
        ):
            raise GratPilotError("proof does not match expected immutable identity")

        root = _validate_output_root(config, (cnf, proof))
        toolchain = _open_toolchain(config.toolchain_lock)
        scheduler_authority = _catalog_authority_snapshot(config)
        quiescence = _proof_quiescence(proof)
        memory_available = _memory_available_bytes()
        disk_available = _disk_available_bytes(root)
        cgroup = _cgroup_resource_snapshot()
        runtime_staging_bytes = max(
            binding.binary.info.st_size
            + sum(item.file.info.st_size for item in binding.libraries)
            for binding in toolchain.tools.values()
        )
        memory_required = (
            config.memory_limit_bytes + config.memory_reserve_bytes
            + runtime_staging_bytes
        )
        child_file_limit = max(config.output_limit_bytes, config.log_limit_bytes)
        # RLIMIT_FSIZE is per file: two GRAT artifacts plus four stage logs can
        # each reach the child cap before the polling watchdog observes them.
        disk_required = 6 * child_file_limit + config.disk_reserve_bytes
        cgroup_headroom = (
            None
            if cgroup["memory_max"] is None
            else cgroup["memory_max"] - cgroup["memory_current"]
        )
        cgroup_capacity_safe = (
            cgroup_headroom is None or cgroup_headroom >= memory_required
        )
        cgroup_pressure_safe = bool(
            math.isfinite(cgroup["psi_full_avg10"])
            and math.isfinite(cgroup["psi_full_avg60"])
            and cgroup["psi_full_avg10"] <= MAX_MEMORY_PSI_FULL_AVG10
            and cgroup["psi_full_avg60"] <= MAX_MEMORY_PSI_FULL_AVG60
        )
        resources = {
            "host_available_memory_bytes": memory_available,
            "memory_limit_bytes": config.memory_limit_bytes,
            "memory_reserve_bytes": config.memory_reserve_bytes,
            "memory_required_bytes": memory_required,
            "sealed_runtime_staging_bytes": runtime_staging_bytes,
            "cgroup": cgroup,
            "cgroup_headroom_bytes": cgroup_headroom,
            "cgroup_capacity_safe": cgroup_capacity_safe,
            "cgroup_pressure_safe": cgroup_pressure_safe,
            "available_disk_bytes": disk_available,
            "output_limit_bytes": config.output_limit_bytes,
            "log_limit_bytes_per_stage": config.log_limit_bytes,
            "child_file_limit_bytes": child_file_limit,
            "disk_worst_case_file_count": 6,
            "disk_reserve_bytes": config.disk_reserve_bytes,
            "disk_required_bytes": disk_required,
            "child_nice": 19,
            "passed": bool(
                memory_available >= memory_required
                and cgroup_capacity_safe
                and cgroup_pressure_safe
                and disk_available >= disk_required
            ),
        }
        if memory_available < memory_required:
            raise GratPilotError("host memory admission gate failed")
        if not cgroup_capacity_safe:
            raise GratPilotError("cgroup memory capacity admission gate failed")
        if not cgroup_pressure_safe:
            raise GratPilotError("cgroup memory pressure admission gate failed")
        if disk_available < disk_required:
            raise GratPilotError("disk admission gate failed")

        trust = {
            "observed_lock_sha256": toolchain.lock.sha256,
            "compiled_binary_sha256": {
                name: TRUSTED_TOOL_POLICY[name]["sha256"]
                for name in ("gratgen", "gratchk")
            },
            "compiled_runtime_policy": True,
            "status": "AUDITED_NON_PRODUCTION_POLICY_MATCH",
            "run_enabled": True,
        }

        source.reverify(full_hash=True)
        plan = _sealed(
            {
                "schema_version": SCHEMA_VERSION,
                "kind": PLAN_KIND,
                "gate": GATE,
                "created_utc": _utc_now(),
                "label": config.label,
                "mode": "NON_PRODUCTION_PILOT",
                "authoritative": False,
                "terminal_publication": False,
                "aggregate_publication": False,
                "cleanup_authority": False,
                "output_root": str(root),
                "wrapper_source": source.record(),
                "wrapper_source_fd_pinned_for_context_lifetime": True,
                "wrapper_source_initial_full_hash_verified": True,
                "inputs": {"cnf": cnf.record(), "drat": proof.record()},
                "proof_quiescence": quiescence,
                "proof_format": config.proof_format,
                "threads": config.threads,
                "cpus": list(config.cpus),
                "cpu_scheduler_authority": {
                    "admission": scheduler_authority,
                    "catalog_locks_released_before_expensive_work": True,
                    "run_requires_short_locked_revalidation_at_each_boundary": True,
                },
                "resources": resources,
                "stage_timeout_seconds": config.stage_timeout_seconds,
                "toolchain": toolchain.record(),
                "toolchain_trust": trust,
                "pipeline": [
                    {
                        "stage": "gratgen",
                        "argv": [
                            "gratgen", "<PINNED_CNF_FD>", "<PINNED_DRAT_FD>",
                            "-l", "staging/pilot.gratl", "-o", "staging/pilot.gratp",
                            "--no-progress-bar",
                            *(["-b"] if config.proof_format == "binary" else []),
                            "-j", str(config.threads),
                        ],
                        "required_success_line": "s VERIFIED",
                        "status_stream": "stderr",
                        "stdout_contract": "EMPTY_WITH_NO_PROGRESS_BAR",
                        "stderr_contract": "ASCII_EXACTLY_ONE_EXPECTED_STATUS",
                    },
                    {
                        "stage": "gratchk",
                        "argv": [
                            "gratchk", "unsat", "<PINNED_CNF_FD>",
                            "<PINNED_GRATL_FD>", "<PINNED_GRATP_FD>",
                        ],
                        "required_success_line": "s VERIFIED UNSAT",
                        "status_stream": "stdout",
                        "stdout_contract": "ASCII_C_LINES_THEN_ONE_TERMINAL_STATUS",
                        "stderr_contract": "EMPTY",
                    },
                ],
            }
        )
        return ValidatedContext(
            config=config,
            source=source,
            cnf=cnf,
            proof=proof,
            toolchain=toolchain,
            scheduler_authority=scheduler_authority,
            proof_quiescence=quiescence,
            resources=resources,
            plan=plan,
        )
    except BaseException:
        if toolchain is not None:
            toolchain.close()
        if proof is not None:
            proof.close()
        if cnf is not None:
            cnf.close()
        source.close()
        raise


def plan_pilot(config: PilotConfig) -> dict[str, Any]:
    """Return a fully validated, read-only pilot plan."""

    with _prepare_context(config) as context:
        context.source.reverify(full_hash=True)
        context.cnf.reverify(full_hash=True)
        context.proof.reverify(full_hash=True)
        context.toolchain.reverify()
        return context.plan


def _atomic_write_json(path: Path, value: Mapping[str, Any]) -> None:
    if path.exists() or path.is_symlink():
        raise GratPilotError(f"refusing to overwrite immutable manifest: {path.name}")
    payload = _canonical_bytes(value)
    temporary = path.parent / f".{path.name}.tmp-{uuid.uuid4().hex}"
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    fd = os.open(temporary, flags, 0o400)
    try:
        offset = 0
        while offset < len(payload):
            offset += os.write(fd, payload[offset:])
        os.fsync(fd)
    except BaseException:
        os.close(fd)
        with contextlib.suppress(OSError):
            temporary.unlink()
        raise
    else:
        os.close(fd)
    try:
        os.link(temporary, path, follow_symlinks=False)
        temporary.unlink()
        directory_fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    except FileExistsError as exc:
        with contextlib.suppress(OSError):
            temporary.unlink()
        raise GratPilotError(f"refusing to overwrite immutable manifest: {path.name}") from exc
    except OSError as exc:
        with contextlib.suppress(OSError):
            temporary.unlink()
        raise GratPilotError(f"cannot atomically publish manifest: {path.name}") from exc
    except BaseException:
        with contextlib.suppress(OSError):
            temporary.unlink()
        raise


def _write_all(fd: int, payload: bytes) -> None:
    offset = 0
    while offset < len(payload):
        written = os.write(fd, payload[offset:])
        if written <= 0:
            raise GratPilotError("short write while staging immutable runtime")
        offset += written


def _sealed_memfd(source: PinnedFile, *, name: str, executable: bool) -> tuple[int, dict[str, Any]]:
    if not hasattr(os, "memfd_create"):
        raise GratPilotError("sealed memfd support is required")
    source.reverify(full_hash=True)
    try:
        fd = os.memfd_create(name, os.MFD_CLOEXEC | os.MFD_ALLOW_SEALING)
    except OSError as exc:
        raise GratPilotError("cannot create sealed runtime memfd") from exc
    try:
        offset = 0
        while offset < source.info.st_size:
            chunk = os.pread(source.fd, HASH_CHUNK_BYTES, offset)
            if not chunk:
                raise GratPilotError("short read while staging runtime memfd")
            _write_all(fd, chunk)
            offset += len(chunk)
        os.fchmod(fd, 0o500 if executable else 0o400)
        fcntl.fcntl(fd, F_ADD_SEALS, REQUIRED_MEMFD_SEALS)
        if fcntl.fcntl(fd, F_GET_SEALS) != REQUIRED_MEMFD_SEALS:
            raise GratPilotError("runtime memfd seal set is incomplete")
        if os.fstat(fd).st_size != source.info.st_size or _sha256_fd(fd) != source.sha256:
            raise GratPilotError("staged runtime memfd identity mismatch")
        source.reverify(full_hash=True)
        info = os.fstat(fd)
        return fd, {
            "name": name,
            "bytes": int(info.st_size),
            "sha256": source.sha256,
            "mode": stat.S_IMODE(info.st_mode),
            "seals": REQUIRED_MEMFD_SEALS,
        }
    except BaseException:
        os.close(fd)
        raise


def _cleanup_runtime_directory(
    directory: Path,
    directory_fd: int | None,
    expected_identity: tuple[int, int],
    allowed_names: frozenset[str],
    *,
    require_all: bool,
) -> None:
    """Remove only the known private symlinks and their exact directory."""

    fd = directory_fd
    try:
        if fd is None:
            flags = os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC
            if hasattr(os, "O_NOFOLLOW"):
                flags |= os.O_NOFOLLOW
            fd = os.open(directory, flags)
        info = os.fstat(fd)
        if (
            not stat.S_ISDIR(info.st_mode)
            or (int(info.st_dev), int(info.st_ino)) != expected_identity
        ):
            raise GratPilotError("private runtime directory identity changed")
        os.fchmod(fd, 0o700)
        observed = set(os.listdir(fd))
        if not observed.issubset(allowed_names) or (require_all and observed != allowed_names):
            raise GratPilotError("private runtime directory inventory changed")
        for name in sorted(observed):
            edge = os.stat(name, dir_fd=fd, follow_symlinks=False)
            if not stat.S_ISLNK(edge.st_mode):
                raise GratPilotError("private runtime library link changed type")
            os.unlink(name, dir_fd=fd)
    finally:
        if fd is not None:
            os.close(fd)
    edge = directory.lstat()
    if (
        not stat.S_ISDIR(edge.st_mode)
        or stat.S_ISLNK(edge.st_mode)
        or (int(edge.st_dev), int(edge.st_ino)) != expected_identity
    ):
        raise GratPilotError("private runtime directory path identity changed")
    directory.rmdir()


@dataclasses.dataclass
class StagedToolRuntime:
    binding: ToolBinding
    binary_fd: int
    loader_fd: int | None
    library_fds: list[int]
    library_directory_fd: int | None
    library_directory: Path | None
    library_directory_identity: tuple[int, int] | None
    library_link_names: frozenset[str]
    record: dict[str, Any]

    @property
    def pass_fds(self) -> tuple[int, ...]:
        values = [self.binary_fd, *self.library_fds]
        if self.loader_fd is not None:
            values.append(self.loader_fd)
        if self.library_directory_fd is not None:
            values.append(self.library_directory_fd)
        return tuple(values)

    def command(self, arguments: Sequence[str]) -> list[str]:
        binary = f"/proc/self/fd/{self.binary_fd}"
        if self.loader_fd is None or self.library_directory_fd is None:
            return [binary, *arguments]
        return [
            f"/proc/self/fd/{self.loader_fd}",
            "--inhibit-cache",
            "--library-path",
            f"/proc/self/fd/{self.library_directory_fd}",
            "--argv0",
            self.binding.name,
            binary,
            *arguments,
        ]

    def close(self) -> None:
        cleanup_error: BaseException | None = None
        directory_fd = self.library_directory_fd
        directory = self.library_directory
        directory_identity = self.library_directory_identity
        self.library_directory_fd = None
        self.library_directory = None
        self.library_directory_identity = None
        if directory is not None and directory_identity is not None:
            try:
                _cleanup_runtime_directory(
                    directory,
                    directory_fd,
                    directory_identity,
                    self.library_link_names,
                    require_all=True,
                )
            except BaseException as exc:
                cleanup_error = exc
        elif directory_fd is not None:
            os.close(directory_fd)
            cleanup_error = GratPilotError("incomplete private runtime directory binding")
        for fd in reversed(self.library_fds):
            os.close(fd)
        self.library_fds.clear()
        if self.loader_fd is not None:
            os.close(self.loader_fd)
            self.loader_fd = None
        if self.binary_fd >= 0:
            os.close(self.binary_fd)
            self.binary_fd = -1
        if cleanup_error is not None:
            raise cleanup_error

    def __enter__(self) -> "StagedToolRuntime":
        return self

    def __exit__(self, *_: object) -> None:
        self.close()


def _stage_tool_runtime(binding: ToolBinding, staging: Path) -> StagedToolRuntime:
    binary_fd = -1
    binary_record: dict[str, Any] = {}
    loader_fd: int | None = None
    library_fds: list[int] = []
    directory_fd: int | None = None
    directory: Path | None = None
    directory_identity: tuple[int, int] | None = None
    library_link_names: frozenset[str] = frozenset()
    object_records: list[dict[str, Any]] = []
    try:
        binary_fd, binary_record = _sealed_memfd(
            binding.binary, name=f"{binding.name}-binary", executable=True,
        )
        library_link_names = frozenset(
            item.soname for item in binding.libraries if not item.is_loader
        )
        if binding.runtime_kind == "dynamic":
            loaders = [item for item in binding.libraries if item.is_loader]
            if len(loaders) != 1:
                raise GratPilotError("dynamic tool lacks exactly one pinned loader")
            loader_fd, loader_record = _sealed_memfd(
                loaders[0].file, name=f"{binding.name}-loader", executable=True,
            )
            loader_record.update({"soname": loaders[0].soname, "is_loader": True})
            object_records.append(loader_record)
            directory = staging / f"runtime-{binding.name}"
            os.mkdir(directory, 0o700)
            flags = os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC
            if hasattr(os, "O_NOFOLLOW"):
                flags |= os.O_NOFOLLOW
            directory_fd = os.open(directory, flags)
            directory_info = os.fstat(directory_fd)
            directory_edge = directory.lstat()
            if (
                not stat.S_ISDIR(directory_info.st_mode)
                or stat.S_ISLNK(directory_edge.st_mode)
                or (directory_info.st_dev, directory_info.st_ino)
                != (directory_edge.st_dev, directory_edge.st_ino)
            ):
                raise GratPilotError("new private runtime directory identity mismatch")
            directory_identity = (
                int(directory_info.st_dev), int(directory_info.st_ino),
            )
            for item in binding.libraries:
                if item.is_loader:
                    continue
                fd, record = _sealed_memfd(
                    item.file,
                    name=f"{binding.name}-{item.soname}",
                    executable=False,
                )
                library_fds.append(fd)
                os.symlink(
                    f"/proc/self/fd/{fd}", item.soname, dir_fd=directory_fd,
                )
                record.update({"soname": item.soname, "is_loader": False})
                object_records.append(record)
            os.fchmod(directory_fd, 0o500)
        record = {
            "kind": "paper400-grat-private-runtime-v1",
            "tool": binding.name,
            "runtime_kind": binding.runtime_kind,
            "binary_memfd": binary_record,
            "runtime_objects": object_records,
            "loader_options": (
                ["--inhibit-cache", "--library-path", "--argv0"]
                if binding.runtime_kind == "dynamic" else []
            ),
            "system_loader_cache_bypassed": binding.runtime_kind == "dynamic",
        }
        return StagedToolRuntime(
            binding,
            binary_fd,
            loader_fd,
            library_fds,
            directory_fd,
            directory,
            directory_identity,
            library_link_names,
            record,
        )
    except BaseException as original:
        rollback_error: BaseException | None = None
        if directory is not None:
            try:
                if directory_identity is None:
                    edge = directory.lstat()
                    directory_identity = (int(edge.st_dev), int(edge.st_ino))
                _cleanup_runtime_directory(
                    directory,
                    directory_fd,
                    directory_identity,
                    library_link_names,
                    require_all=False,
                )
            except BaseException as exc:
                rollback_error = exc
            directory_fd = None
        elif directory_fd is not None:
            os.close(directory_fd)
        for fd in reversed(library_fds):
            with contextlib.suppress(OSError):
                os.close(fd)
        if loader_fd is not None:
            with contextlib.suppress(OSError):
                os.close(loader_fd)
        with contextlib.suppress(OSError):
            os.close(binary_fd)
        if rollback_error is not None:
            raise GratPilotError(
                "private runtime construction failed and rollback was incomplete: "
                f"{type(original).__name__}: {original}"
            ) from rollback_error
        raise


def _group_exists(pgid: int) -> bool:
    try:
        os.killpg(pgid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True


def _terminate_own_group(process: subprocess.Popen[bytes]) -> None:
    pgid = process.pid
    if not _group_exists(pgid):
        with contextlib.suppress(subprocess.TimeoutExpired):
            process.wait(timeout=0.1)
        return
    with contextlib.suppress(ProcessLookupError):
        os.killpg(pgid, signal.SIGTERM)
    deadline = time.monotonic() + PROCESS_TERM_GRACE_SECONDS
    while _group_exists(pgid) and time.monotonic() < deadline:
        time.sleep(0.05)
    if _group_exists(pgid):
        with contextlib.suppress(ProcessLookupError):
            os.killpg(pgid, signal.SIGKILL)
    with contextlib.suppress(subprocess.TimeoutExpired):
        process.wait(timeout=PROCESS_TERM_GRACE_SECONDS)
    if _group_exists(pgid):
        raise GratPilotError("pilot child process group survived cleanup")


def _child_setup(
    cpus: tuple[int, ...], memory_limit: int, file_limit: int, expected_parent_pid: int,
) -> None:
    os.umask(0o077)
    os.sched_setaffinity(0, set(cpus))
    os.setpriority(os.PRIO_PROCESS, 0, 19)
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    resource.setrlimit(resource.RLIMIT_AS, (memory_limit, memory_limit))
    resource.setrlimit(resource.RLIMIT_FSIZE, (file_limit, file_limit))
    ctypes.set_errno(0)
    if _PRCTL(PR_SET_PDEATHSIG, CHILD_PDEATH_SIGNAL, 0, 0, 0) != 0:
        error_number = ctypes.get_errno() or errno.EPERM
        raise OSError(error_number, "PR_SET_PDEATHSIG failed")
    if os.getppid() != expected_parent_pid:
        os.kill(os.getpid(), CHILD_PDEATH_SIGNAL)
        os._exit(127)
    if os.getpgrp() != os.getpid() or os.getsid(0) != os.getpid():
        raise OSError(errno.EPERM, "pilot child is not its own session/group leader")


def _watched_bytes(paths: Sequence[Path]) -> int:
    total = 0
    for path in paths:
        try:
            info = path.lstat()
        except FileNotFoundError:
            continue
        if not stat.S_ISREG(info.st_mode):
            raise GratPilotError("stage created a non-regular watched artifact")
        total += int(info.st_size)
    return total


def _ascii_lines(payload: bytes, role: str) -> list[str]:
    if b"\x00" in payload:
        raise GratPilotError(f"{role} contains NUL")
    try:
        return payload.decode("ascii").splitlines()
    except UnicodeDecodeError as exc:
        raise GratPilotError(f"{role} is not exact ASCII") from exc


def _validate_status_payload(
    stage: str,
    stdout_payload: bytes,
    stderr_payload: bytes,
    *,
    expected_threads: int | None = None,
) -> tuple[str, int | None]:
    """Enforce the distinct, observed GRAT 1.3.3 stream contracts."""

    if stage not in STAGE_NAMES:
        raise GratPilotError("unknown GRAT stage")
    if stage == "gratgen":
        if expected_threads not in {4, 8}:
            raise GratPilotError("gratgen thread evidence requires 4 or 8 expected threads")
        if stdout_payload:
            raise GratPilotError("gratgen must emit empty stdout")
        lines = _ascii_lines(stderr_payload, "gratgen stderr")
        expected = "s VERIFIED"
        if sum(line == expected for line in lines) != 1:
            raise GratPilotError("gratgen stderr lacks exactly one expected status line")
        if any(line.startswith("s ") and line != expected for line in lines):
            raise GratPilotError("gratgen stderr contains an unexpected status line")
        thread_lines = [
            line for line in lines
            if re.fullmatch(r"c Checking with [0-9]+ parallel threads", line)
        ]
        if len(thread_lines) != 1:
            raise GratPilotError("gratgen stderr lacks exactly one parallel-thread line")
        observed_threads = int(thread_lines[0].split()[3])
        if observed_threads != expected_threads:
            raise GratPilotError(
                "gratgen observed parallel thread count differs from requested count"
            )
        return expected, observed_threads

    if stderr_payload:
        raise GratPilotError("gratchk must emit empty stderr")
    lines = _ascii_lines(stdout_payload, "gratchk stdout")
    expected = "s VERIFIED UNSAT"
    if (
        not lines
        or lines[-1] != expected
        or [line for line in lines if line.startswith("s ")] != [expected]
        or any(not line.startswith("c ") for line in lines[:-1])
    ):
        raise GratPilotError(
            "gratchk stdout lacks one terminal verified status after c-lines"
        )
    return expected, None


def _run_stage(
    *,
    stage: str,
    runtime: StagedToolRuntime,
    arguments: Sequence[str],
    pass_fds: Sequence[int],
    cwd: Path,
    stdout_path: Path,
    stderr_path: Path,
    watched_paths: Sequence[Path],
    config: PilotConfig,
) -> dict[str, Any]:
    if stage not in STAGE_NAMES:
        raise GratPilotError("unknown GRAT stage")
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    stdout_fd = os.open(stdout_path, flags, 0o600)
    try:
        stderr_fd = os.open(stderr_path, flags, 0o600)
    except BaseException:
        os.close(stdout_fd)
        raise
    command = runtime.command(arguments)
    started = time.monotonic()
    expected_parent_pid = os.getpid()
    process: subprocess.Popen[bytes] | None = None
    process_identity: dict[str, Any] | None = None
    failure: str | None = None
    try:
        process = subprocess.Popen(
            command,
            executable=command[0],
            cwd=cwd,
            stdin=subprocess.DEVNULL,
            stdout=stdout_fd,
            stderr=stderr_fd,
            close_fds=True,
            pass_fds=tuple(sorted(set((*pass_fds, *runtime.pass_fds)))),
            env={"PATH": "/usr/bin:/bin", "LANG": "C", "LC_ALL": "C", "TZ": "UTC"},
            preexec_fn=lambda: _child_setup(
                config.cpus,
                config.memory_limit_bytes,
                max(config.output_limit_bytes, config.log_limit_bytes),
                expected_parent_pid,
            ),
            start_new_session=True,
        )
        start_ticks = _proc_start_ticks(Path("/proc") / str(process.pid))
        try:
            observed_affinity = sorted(os.sched_getaffinity(process.pid))
        except OSError as exc:
            raise GratPilotError("cannot observe pilot child affinity") from exc
        if start_ticks is None:
            raise GratPilotError("cannot observe pilot child start tick")
        if observed_affinity != list(config.cpus):
            raise GratPilotError("pilot child affinity differs from the requested exact set")
        process_identity = {
            "pid": process.pid,
            "proc_start_ticks": start_ticks,
            "argv": command,
            "observed_affinity": observed_affinity,
            "observed_before_wait": True,
        }
        while True:
            returncode = process.poll()
            elapsed = time.monotonic() - started
            if elapsed > config.stage_timeout_seconds:
                failure = f"{stage} exceeded wall timeout"
                break
            if _watched_bytes((stdout_path, stderr_path)) > config.log_limit_bytes:
                failure = f"{stage} exceeded log byte limit"
                break
            if _watched_bytes(watched_paths) > config.output_limit_bytes:
                failure = f"{stage} exceeded output byte limit"
                break
            if returncode is not None:
                break
            time.sleep(0.2)
        if failure is not None:
            _terminate_own_group(process)
            raise GratPilotError(failure)
        returncode = process.wait()
        if _group_exists(process.pid):
            _terminate_own_group(process)
            raise GratPilotError(f"{stage} left a lingering process-group member")
    finally:
        if process is not None and _group_exists(process.pid):
            _terminate_own_group(process)
        os.fsync(stdout_fd)
        os.fsync(stderr_fd)
        os.close(stdout_fd)
        os.close(stderr_fd)

    if returncode != 0:
        raise GratPilotError(f"{stage} exited with status {returncode}")
    if _watched_bytes((stdout_path, stderr_path)) > config.log_limit_bytes:
        raise GratPilotError(f"{stage} log exceeds byte limit")
    stdout_path.chmod(0o400)
    stderr_path.chmod(0o400)
    with PinnedFile.open(
        stdout_path,
        role=f"{stage} stdout",
        max_bytes=config.log_limit_bytes,
        require_executable=False,
    ) as stdout, PinnedFile.open(
        stderr_path,
        role=f"{stage} stderr",
        max_bytes=config.log_limit_bytes,
        require_executable=False,
    ) as stderr:
        stdout_payload = stdout.read_bytes(max_bytes=config.log_limit_bytes)
        stderr_payload = stderr.read_bytes(max_bytes=config.log_limit_bytes)
        expected, observed_threads = _validate_status_payload(
            stage,
            stdout_payload,
            stderr_payload,
            expected_threads=config.threads if stage == "gratgen" else None,
        )
        if process_identity is None:
            raise GratPilotError("pilot child process identity was not captured")
        return {
            "stage": stage,
            "exit_code": returncode,
            "elapsed_wall_seconds": time.monotonic() - started,
            "required_success_line": expected,
            "status_stream": "stderr" if stage == "gratgen" else "stdout",
            "observed_parallel_threads": observed_threads,
            "stdout": stdout.record(),
            "stderr": stderr.record(),
            "runtime": runtime.record,
            "process_identity": process_identity,
            "process_policy": {
                "new_session": True,
                "pdeathsig": CHILD_PDEATH_SIGNAL,
                "nice": 19,
                "exact_affinity": list(config.cpus),
                "require_empty_process_group": True,
            },
        }


def _pin_generated(
    path: Path, *, role: str, cap: int, allow_empty: bool = False,
) -> PinnedFile:
    try:
        info = path.lstat()
    except OSError as exc:
        raise GratPilotError(f"missing generated artifact: {role}") from exc
    if not stat.S_ISREG(info.st_mode) or (info.st_size == 0 and not allow_empty):
        raise GratPilotError(f"generated artifact is empty or non-regular: {role}")
    path.chmod(0o400)
    return PinnedFile.open(
        path,
        role=role,
        max_bytes=cap,
        require_executable=False,
    )


def _source_reverification_record(source: PinnedFile) -> dict[str, Any]:
    checked_utc = _utc_now()
    try:
        source.reverify(full_hash=True)
    except BaseException as exc:
        return {
            "checked_utc": checked_utc,
            "full_hash": True,
            "passed": False,
            "error": {
                "type": type(exc).__name__,
                "message": str(exc).replace("\n", " ")[:2048],
            },
        }
    return {"checked_utc": checked_utc, "full_hash": True, "passed": True}


def _failure_result(
    plan: Mapping[str, Any],
    exc: BaseException,
    source_reverification: Mapping[str, Any],
) -> dict[str, Any]:
    message = str(exc).replace("\n", " ")[:2048]
    return _sealed(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": RESULT_KIND,
            "gate": GATE,
            "completed_utc": _utc_now(),
            "status": "FAILED_CLOSED",
            "authoritative": False,
            "terminal_publication": False,
            "aggregate_publication": False,
            "cleanup_authority": False,
            "eligible_for_terminal_publication": False,
            "plan_sha256": plan["manifest_sha256"],
            "wrapper_source": plan["wrapper_source"],
            "wrapper_source_final_full_reverify": dict(source_reverification),
            "failure": {"type": type(exc).__name__, "message": message},
        }
    )


def run_pilot(config: PilotConfig) -> dict[str, Any]:
    """Execute one isolated pilot; never write a Paper400 authoritative record."""

    with _prepare_context(config) as context:
        if context.plan["toolchain_trust"].get("run_enabled") is not True:
            raise GratPilotError("toolchain policy is not authorized for the pilot")
        context.source.reverify(full_hash=True)
        root = config.output_root
        if sorted(item.name for item in root.iterdir()) != ["cpu-reservation.json"]:
            raise GratPilotError("pre-reserved pilot root ceased to be pristine")
        scheduler_snapshots = [_catalog_authority_snapshot(config)]
        staging = root / "staging"
        os.mkdir(staging, 0o700)
        _atomic_write_json(root / "PLAN.json", context.plan)
        gratl_path = staging / "pilot.gratl"
        gratp_path = staging / "pilot.gratp"
        try:
            context.source.reverify(full_hash=True)
            context.cnf.reverify(full_hash=True)
            context.proof.reverify(full_hash=True)
            _proof_quiescence(context.proof)
            context.toolchain.reverify()
            with _stage_tool_runtime(
                context.toolchain.tools["gratgen"], staging,
            ) as gratgen_runtime:
                gratgen_args = [
                    f"/proc/self/fd/{context.cnf.fd}",
                    f"/proc/self/fd/{context.proof.fd}",
                    "-l",
                    str(gratl_path),
                    "-o",
                    str(gratp_path),
                    "--no-progress-bar",
                ]
                if config.proof_format == "binary":
                    gratgen_args.append("-b")
                gratgen_args.extend(("-j", str(config.threads)))
                gratgen = _run_stage(
                    stage="gratgen",
                    runtime=gratgen_runtime,
                    arguments=gratgen_args,
                    pass_fds=(context.cnf.fd, context.proof.fd),
                    cwd=staging,
                    stdout_path=staging / "gratgen.stdout",
                    stderr_path=staging / "gratgen.stderr",
                    watched_paths=(gratl_path, gratp_path),
                    config=config,
                )
                if gratgen.get("exit_code") != 0 or gratgen.get("required_success_line") != "s VERIFIED":
                    raise GratPilotError("gratgen stage record is not verified")
                context.cnf.reverify(full_hash=True)
                context.proof.reverify(full_hash=True)
                context.source.reverify(full_hash=True)
                context.toolchain.reverify()
                cgroup_after_gratgen = _assert_cgroup_unchanged(
                    context.resources["cgroup"]
                )
                scheduler_snapshots.append(_catalog_authority_snapshot(config))

                with _pin_generated(
                    gratl_path,
                    role="staged GRAT lemmas",
                    cap=config.output_limit_bytes,
                    allow_empty=True,
                ) as gratl, _pin_generated(
                    gratp_path, role="staged GRAT proof", cap=config.output_limit_bytes
                ) as gratp:
                    if gratl.info.st_size + gratp.info.st_size > config.output_limit_bytes:
                        raise GratPilotError("combined GRAT artifacts exceed output limit")
                    with _stage_tool_runtime(
                        context.toolchain.tools["gratchk"], staging,
                    ) as gratchk_runtime:
                        gratchk = _run_stage(
                            stage="gratchk",
                            runtime=gratchk_runtime,
                            arguments=(
                                "unsat",
                                f"/proc/self/fd/{context.cnf.fd}",
                                f"/proc/self/fd/{gratl.fd}",
                                f"/proc/self/fd/{gratp.fd}",
                            ),
                            pass_fds=(context.cnf.fd, gratl.fd, gratp.fd),
                            cwd=staging,
                            stdout_path=staging / "gratchk.stdout",
                            stderr_path=staging / "gratchk.stderr",
                            watched_paths=(gratl_path, gratp_path),
                            config=config,
                        )
                    if (
                        gratchk.get("exit_code") != 0
                        or gratchk.get("required_success_line") != "s VERIFIED UNSAT"
                    ):
                        raise GratPilotError("gratchk stage record is not verified UNSAT")
                    context.cnf.reverify(full_hash=True)
                    context.proof.reverify(full_hash=True)
                    gratl.reverify(full_hash=True)
                    gratp.reverify(full_hash=True)
                    context.toolchain.reverify()
                    cgroup_after_gratchk = _assert_cgroup_unchanged(
                        context.resources["cgroup"]
                    )
                    scheduler_snapshots.append(_catalog_authority_snapshot(config))
                    # Make the recorded full-hash check the last mutable-input
                    # boundary before constructing and atomically publishing RESULT.
                    source_reverification = _source_reverification_record(context.source)
                    if source_reverification.get("passed") is not True:
                        raise GratPilotError("pilot wrapper source changed during run")
                    result = _sealed(
                        {
                            "schema_version": SCHEMA_VERSION,
                            "kind": RESULT_KIND,
                            "gate": GATE,
                            "completed_utc": _utc_now(),
                            "status": "GRATCHK_ACCEPTED_PILOT_ONLY",
                            "authoritative": False,
                            "terminal_publication": False,
                            "aggregate_publication": False,
                            "cleanup_authority": False,
                            "eligible_for_terminal_publication": False,
                            "artifacts_staged_only": True,
                            "plan_sha256": context.plan["manifest_sha256"],
                            "wrapper_source": context.plan["wrapper_source"],
                            "wrapper_source_final_full_reverify": source_reverification,
                            "inputs": {
                                "cnf": context.cnf.record(),
                                "drat": context.proof.record(),
                            },
                            "scheduler_boundary_snapshots": scheduler_snapshots,
                            "catalog_locks_held_across_stage": False,
                            "toolchain": context.toolchain.record(),
                            "cgroup_after_stages": [
                                cgroup_after_gratgen, cgroup_after_gratchk,
                            ],
                            "stages": [gratgen, gratchk],
                            "staged_artifacts": {
                                "gratl": gratl.record(),
                                "gratp": gratp.record(),
                            },
                        }
                    )
                _atomic_write_json(root / "RESULT.json", result)
                return result
        except BaseException as exc:
            source_reverification = _source_reverification_record(context.source)
            with contextlib.suppress(BaseException):
                _atomic_write_json(
                    root / "RESULT.json",
                    _failure_result(context.plan, exc, source_reverification),
                )
            raise


def _parse_cpus(value: str) -> tuple[int, ...]:
    if not re.fullmatch(r"[0-9]+(?:,[0-9]+)*", value):
        raise argparse.ArgumentTypeError("CPUs must be a comma-separated integer list")
    result = tuple(int(item) for item in value.split(","))
    if len(set(result)) != len(result):
        raise argparse.ArgumentTypeError("CPU list contains duplicates")
    if result != tuple(sorted(result)):
        raise argparse.ArgumentTypeError("CPU list must be strictly increasing")
    return result


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    for command in ("plan", "run"):
        child = subparsers.add_parser(
            command,
            help="read-only validation/plan" if command == "plan" else "execute isolated pilot",
        )
        child.add_argument("--cnf", type=Path, required=True)
        child.add_argument("--proof", type=Path, required=True)
        child.add_argument("--cnf-sha256", required=True)
        child.add_argument("--proof-sha256", required=True)
        child.add_argument("--cnf-bytes", type=int, required=True)
        child.add_argument("--proof-bytes", type=int, required=True)
        child.add_argument("--proof-format", choices=("ascii", "binary"), required=True)
        child.add_argument("--output-root", type=Path, required=True)
        child.add_argument("--toolchain-lock", type=Path, required=True)
        child.add_argument("--threads", type=int, choices=(4, 8), required=True)
        child.add_argument("--cpus", type=_parse_cpus, required=True)
        child.add_argument(
            "--lease-catalog", type=Path, action="append", required=True,
            help="repeat for every catalog found by bounded production discovery",
        )
        child.add_argument("--reservation-sha256", required=True)
        child.add_argument("--memory-limit-bytes", type=int, required=True)
        child.add_argument(
            "--memory-reserve-bytes", type=int, default=DEFAULT_MEMORY_RESERVE_BYTES
        )
        child.add_argument("--output-limit-bytes", type=int, required=True)
        child.add_argument("--disk-reserve-bytes", type=int, default=DEFAULT_DISK_RESERVE_BYTES)
        child.add_argument("--log-limit-bytes", type=int, default=DEFAULT_LOG_LIMIT_BYTES)
        child.add_argument("--stage-timeout-seconds", type=int, required=True)
        child.add_argument("--cnf-max-bytes", type=int, default=DEFAULT_CNF_MAX_BYTES)
        child.add_argument("--proof-max-bytes", type=int, default=DEFAULT_PROOF_MAX_BYTES)
        child.add_argument("--label", default="paper400")
    return parser


def _config_from_namespace(args: argparse.Namespace) -> PilotConfig:
    return PilotConfig(
        cnf=args.cnf,
        proof=args.proof,
        expected_cnf_sha256=args.cnf_sha256,
        expected_proof_sha256=args.proof_sha256,
        expected_cnf_bytes=args.cnf_bytes,
        expected_proof_bytes=args.proof_bytes,
        proof_format=args.proof_format,
        output_root=args.output_root,
        toolchain_lock=args.toolchain_lock,
        threads=args.threads,
        cpus=args.cpus,
        lease_catalogs=tuple(args.lease_catalog),
        reservation_sha256=args.reservation_sha256,
        memory_limit_bytes=args.memory_limit_bytes,
        memory_reserve_bytes=args.memory_reserve_bytes,
        output_limit_bytes=args.output_limit_bytes,
        disk_reserve_bytes=args.disk_reserve_bytes,
        log_limit_bytes=args.log_limit_bytes,
        stage_timeout_seconds=args.stage_timeout_seconds,
        cnf_max_bytes=args.cnf_max_bytes,
        proof_max_bytes=args.proof_max_bytes,
        label=args.label,
    )


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    config = _config_from_namespace(args)
    try:
        result = plan_pilot(config) if args.command == "plan" else run_pilot(config)
    except GratPilotError as exc:
        print(f"{GATE}: FAIL-CLOSED: {exc}", file=sys.stderr)
        return 2
    print(_canonical_bytes(result).decode("ascii"), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
