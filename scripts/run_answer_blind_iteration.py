#!/usr/bin/env python3
"""Trusted, root-side launcher for answer-blind solver and Lean verifier runs.

This module is controller code.  It must be installed outside a solver
workspace and executed by root.  It combines three controls which are easy to
accidentally lose when an agent loop is launched directly:

* a Linux Landlock ABI 4, deny-by-default filesystem policy;
* root-owned immutable input/configuration trees plus an explicit writable
  workspace surface; and
* one-iteration, hash-chained controller receipts stored outside the solver
  workspace.

Landlock deliberately does not restrict networking.  Receipts therefore say
``network_answer_blind = false``.  The solver harness still disables browser
and search tools at its own layer, but that is not represented as an operating
system network-isolation claim.

Never import or execute Python from the solver workspace in this program.
Only the root-owned runtime executable is admitted as the Archon entry point.
"""

from __future__ import annotations

import argparse
import ctypes
import errno
import fcntl
import hashlib
import http.client
import json
import os
import pwd
import re
import resource
import select
import shutil
import signal
import socket
import stat
import struct
import subprocess
import sys
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath
from typing import Any, Iterable, Mapping, NoReturn, Sequence
from urllib.parse import urlparse


SCHEMA_VERSION = 1
PROTOCOL = "icho-answer-blind-v1"
INVOCATION_PHASE = "solver_invocation"
AGGREGATE_PHASE = "solver_invocation_aggregate"
LANDLOCK_MIN_ABI = 4

VARIANT_MODELS: Mapping[str, tuple[str, str, str]] = {
    "gpt": ("openai", "gpt-5.6-sol", "codex"),
    "kimi-k3": ("moonshot", "kimi-k3[1m]", "claude-code"),
}

GENERATED_PROTECTED_FILES = (
    ".archon/config.json",
    ".archon/AGENTS.md",
    ".mcp.json",
    "ANSWER_BLIND_PROTOCOL.md",
)

SOLVER_VISIBLE_PROTECTED_TREES = (
    "reports",
    ".archon/physics-formalize",
    ".archon/prover-modes",
    ".archon/subagents",
    ".archon/prompts",
)

# The CRNT/LeanExplore index is campaign-generated rather than part of every
# legacy seed. If its parent exists, the exact file is mandatory and protected.
CONDITIONAL_SOLVER_VISIBLE_PROTECTED_FILES = (
    ".archon/lean-explore/project-index.json",
)

LAUNCH_AUTHORIZATION_FIELDS = {
    "schema_version", "protocol", "phase", "variant", "run_id", "workspace",
    "runtime_root", "dependency_root", "system_inventory",
    "system_read_only_paths", "solver_external_read_write_paths",
    "verifier_external_read_write_paths", "reviewer_external_read_write_paths",
    "required_denied_probe_paths", "allowed_model_broker_tcp_port",
}

CONTROLLER_SEAL_FIELDS = {
    "schema_version", "protocol", "phase", "solver_stopped",
    "seed_manifest_sha256", "blind_bundle", "freeze_scope",
    "generated_files", "dependency_inventory", "runtime_inventory",
    "snapshot_inventory", "launch_authorization", "model_broker", "solver",
    "isolation", "solver_invocation_receipt", "verifier_receipt",
    "independent_review_receipt",
}

INDEPENDENT_REVIEW_INVOCATION_FIELDS = {
    "schema_version", "protocol", "phase", "reviewer_uid",
    "reviewer_model_family", "reviewer_model_id", "command_argv", "exit_code",
    "solver_stopped", "descendants_stopped", "network_answer_blind",
    "dedicated_uid_quiescence", "landlock", "isolation_probes",
    "dependency_inventory_sha256", "runtime_inventory_sha256",
    "snapshot_inventory_sha256", "launch_authorization_sha256",
    "model_broker_receipt_sha256", "review_input_inventory", "review_receipt",
    "stdout_log",
}

# Direct state files are pre-created under a root-owned .archon directory.
# The solver owns the inode and can truncate it, but cannot unlink, replace, or
# create an unlisted peer.  Atomic writers for the two gate states use a safe
# in-place fallback when the parent is deliberately controller-owned.
MUTABLE_STATE_FILES = (
    ".archon/PROGRESS.md",
    ".archon/AUTO_NOTES.md",
    ".archon/FORMALIZATION_REVIEW_GATE.md",
    ".archon/PROOF_REVIEW_GATE.md",
    ".archon/formalization-review-gate.json",
    ".archon/proof-review-gate.json",
    ".archon/STRATEGY.md",
    ".archon/PROJECT_STATUS.md",
    ".archon/task_done.md",
    ".archon/task_pending.md",
    ".archon/ARCHON_MEMORY.md",
    ".archon/USER_HINTS.md",
    ".archon/last_lake_build.log",
    ".archon/sync_leanok-state.json",
)

MUTABLE_WORKSPACE_DIRS = (
    "IChO2026Problems",
    "blind_candidates",
    "blueprint",
    ".lake/build",
    ".lake/config",
    ".archon/logs",
    ".archon/task_results",
    ".archon/proof-journal",
    ".archon/iter",
    ".archon/tmp",
    ".archon/preflight",
    ".archon/git-dir",
)

MUTABLE_WORKSPACE_FILES = (
    "IChO2026Problems/All.lean",
    *MUTABLE_STATE_FILES,
)

SAFE_RUN_ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,127}$")
SHA256 = re.compile(r"^[0-9a-f]{64}$")

# Landlock filesystem rights through ABI 4.  Network rights were introduced
# later and are intentionally neither handled nor claimed here.
LANDLOCK_ACCESS_FS_EXECUTE = 1 << 0
LANDLOCK_ACCESS_FS_WRITE_FILE = 1 << 1
LANDLOCK_ACCESS_FS_READ_FILE = 1 << 2
LANDLOCK_ACCESS_FS_READ_DIR = 1 << 3
LANDLOCK_ACCESS_FS_REMOVE_DIR = 1 << 4
LANDLOCK_ACCESS_FS_REMOVE_FILE = 1 << 5
LANDLOCK_ACCESS_FS_MAKE_CHAR = 1 << 6
LANDLOCK_ACCESS_FS_MAKE_DIR = 1 << 7
LANDLOCK_ACCESS_FS_MAKE_REG = 1 << 8
LANDLOCK_ACCESS_FS_MAKE_SOCK = 1 << 9
LANDLOCK_ACCESS_FS_MAKE_FIFO = 1 << 10
LANDLOCK_ACCESS_FS_MAKE_BLOCK = 1 << 11
LANDLOCK_ACCESS_FS_MAKE_SYM = 1 << 12
LANDLOCK_ACCESS_FS_REFER = 1 << 13
LANDLOCK_ACCESS_FS_TRUNCATE = 1 << 14

LANDLOCK_HANDLED_ACCESS_FS = (1 << 15) - 1
LANDLOCK_READ_FILE_ACCESS = LANDLOCK_ACCESS_FS_EXECUTE | LANDLOCK_ACCESS_FS_READ_FILE
LANDLOCK_READ_DIR_ACCESS = (
    LANDLOCK_ACCESS_FS_EXECUTE
    | LANDLOCK_ACCESS_FS_READ_FILE
    | LANDLOCK_ACCESS_FS_READ_DIR
)
LANDLOCK_CREATE_RULESET_VERSION = 1
LANDLOCK_RULE_PATH_BENEATH = 1
LANDLOCK_RULE_NET_PORT = 2
LANDLOCK_ACCESS_NET_BIND_TCP = 1 << 0
LANDLOCK_ACCESS_NET_CONNECT_TCP = 1 << 1
LANDLOCK_HANDLED_ACCESS_NET = (
    LANDLOCK_ACCESS_NET_BIND_TCP | LANDLOCK_ACCESS_NET_CONNECT_TCP
)

SYS_LANDLOCK_CREATE_RULESET = 444
SYS_LANDLOCK_ADD_RULE = 445
SYS_LANDLOCK_RESTRICT_SELF = 446
SYS_SECCOMP = 317
PR_SET_PDEATHSIG = 1
PR_SET_CHILD_SUBREAPER = 36
PR_SET_NO_NEW_PRIVS = 38
PR_SET_SECCOMP = 22
SECCOMP_MODE_FILTER = 2
SECCOMP_SET_MODE_FILTER = 1
SECCOMP_FILTER_FLAG_NEW_LISTENER = 1 << 3
SECCOMP_RET_KILL_PROCESS = 0x80000000
SECCOMP_RET_USER_NOTIF = 0x7FC00000
SECCOMP_ADDFD_FLAG_SEND = 1 << 1
AUDIT_ARCH_X86_64 = 0xC000003E

ACCESS_NAMES = (
    "execute",
    "write_file",
    "read_file",
    "read_dir",
    "remove_dir",
    "remove_file",
    "make_char",
    "make_dir",
    "make_reg",
    "make_sock",
    "make_fifo",
    "make_block",
    "make_sym",
    "refer",
    "truncate",
)

# No broad system directory is admitted.  Every dynamically-linked runtime
# dependency outside the sealed /opt tree is named exactly and checked by the
# root controller before it becomes a Landlock rule.  Tool binaries needed by
# agents (shell, git, rg, etc.) must be copied into ``runtime_root/bin``.
SYSTEM_READ_ONLY_FILES = (
    "/etc/ssl/certs/ca-certificates.crt",
    "/etc/resolv.conf",
    "/etc/hosts",
    "/etc/nsswitch.conf",
    "/etc/host.conf",
    "/etc/gai.conf",
    "/usr/share/zoneinfo/Etc/UTC",
    "/etc/passwd",
    "/etc/group",
    "/etc/services",
    "/etc/protocols",
    "/usr/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2",
    "/usr/lib/x86_64-linux-gnu/libc.so.6",
    "/usr/lib/x86_64-linux-gnu/libdl.so.2",
    "/usr/lib/x86_64-linux-gnu/libm.so.6",
    "/usr/lib/x86_64-linux-gnu/libpthread.so.0",
    "/usr/lib/x86_64-linux-gnu/librt.so.1",
)
SYSTEM_DEVICE_FILES = (
    "/dev/null", "/dev/zero", "/dev/random", "/dev/urandom",
)

ELF_MAGIC = b"\x7fELF"


def _default_verifier_paths(controller: Path, *, variant: str) -> tuple[Path, ...]:
    prefix = f".{controller.name}-{variant}-verifier"
    return (
        controller.parent / f"{prefix}-home",
        controller.parent / f"{prefix}-tmp",
        controller.parent / f"{prefix}-output",
    )


def _default_reviewer_paths(controller: Path, *, variant: str) -> tuple[Path, ...]:
    prefix = f".{controller.name}-{variant}-reviewer"
    return (
        controller.parent / f"{prefix}-home",
        controller.parent / f"{prefix}-tmp",
        controller.parent / f"{prefix}-output",
    )


class ControllerError(RuntimeError):
    """A trusted-controller invariant was not satisfied."""


class _LandlockRulesetAttr(ctypes.Structure):
    _fields_ = [
        ("handled_access_fs", ctypes.c_uint64),
        ("handled_access_net", ctypes.c_uint64),
    ]


class _LandlockPathBeneathAttr(ctypes.Structure):
    _fields_ = [
        ("allowed_access", ctypes.c_uint64),
        ("parent_fd", ctypes.c_int32),
    ]


class _LandlockNetPortAttr(ctypes.Structure):
    _fields_ = [
        ("allowed_access", ctypes.c_uint64),
        ("port", ctypes.c_uint64),
    ]


class _SockFilter(ctypes.Structure):
    _fields_ = [
        ("code", ctypes.c_ushort),
        ("jt", ctypes.c_ubyte),
        ("jf", ctypes.c_ubyte),
        ("k", ctypes.c_uint32),
    ]


class _SockFprog(ctypes.Structure):
    _fields_ = [
        ("length", ctypes.c_ushort),
        ("filter", ctypes.POINTER(_SockFilter)),
    ]


class _SeccompData(ctypes.Structure):
    _fields_ = [
        ("nr", ctypes.c_int32),
        ("arch", ctypes.c_uint32),
        ("instruction_pointer", ctypes.c_uint64),
        ("args", ctypes.c_uint64 * 6),
    ]


class _SeccompNotif(ctypes.Structure):
    _fields_ = [
        ("id", ctypes.c_uint64),
        ("pid", ctypes.c_uint32),
        ("flags", ctypes.c_uint32),
        ("data", _SeccompData),
    ]


class _SeccompNotifResp(ctypes.Structure):
    _fields_ = [
        ("id", ctypes.c_uint64),
        ("val", ctypes.c_int64),
        ("error", ctypes.c_int32),
        ("flags", ctypes.c_uint32),
    ]


class _SeccompNotifAddfd(ctypes.Structure):
    _fields_ = [
        ("id", ctypes.c_uint64),
        ("flags", ctypes.c_uint32),
        ("srcfd", ctypes.c_uint32),
        ("newfd", ctypes.c_uint32),
        ("newfd_flags", ctypes.c_uint32),
    ]


@dataclass(frozen=True)
class SolverIdentity:
    user: str
    uid: int
    gid: int


@dataclass(frozen=True)
class LandlockPolicy:
    abi: int
    read_only_paths: tuple[Path, ...]
    read_write_paths: tuple[Path, ...]
    probe_paths: tuple[Path, ...]
    allowed_connect_tcp_ports: tuple[int, ...] = ()

    def receipt(
        self, *, connected_fd_injection_count: int = 0,
        seccomp_supervisor_fail_closed: bool = False,
        seccomp_supervisor_stopped: bool = False,
    ) -> dict[str, Any]:
        return {
            "abi": self.abi,
            "handled_access_fs": list(ACCESS_NAMES),
            "read_only_paths": [str(path) for path in self.read_only_paths],
            "read_write_paths": [str(path) for path in self.read_write_paths],
            "deny_by_default": True,
            "no_new_privs": True,
            "enforced": True,
            "handled_access_net": ["bind_tcp", "connect_tcp"],
            "allowed_bind_tcp_ports": [],
            "allowed_connect_tcp_ports": list(self.allowed_connect_tcp_ports),
            "network_deny_by_default": True,
            "seccomp_arch": "AUDIT_ARCH_X86_64",
            "socket_creation_mode": "user_notif_connected_fd_injection_v1",
            "allowed_connect_tcp_endpoints": [
                f"127.0.0.1:{port}" for port in self.allowed_connect_tcp_ports
            ],
            "inet_datagram_sockets_denied": True,
            "inet_raw_sockets_denied": True,
            "mptcp_sockets_denied": True,
            "unix_sockets_denied": True,
            "socketpair_denied": True,
            "io_uring_setup_denied": True,
            "sysv_ipc_denied": True,
            "posix_message_queues_denied": True,
            "kernel_keyring_denied": True,
            "seccomp_supervisor_fail_closed": seccomp_supervisor_fail_closed,
            "seccomp_supervisor_stopped": seccomp_supervisor_stopped,
            "connected_fd_injection_count": connected_fd_injection_count,
        }


@dataclass(frozen=True)
class ConfinedResult:
    argv: tuple[str, ...]
    started_at: str
    ended_at: str
    exit_code: int
    timed_out: bool
    solver_stopped: bool
    descendants_stopped: bool
    probes: dict[str, dict[str, Any]]
    dedicated_uid_quiescence: dict[str, Any]
    confinement_error: str | None = None
    connected_fd_injection_count: int = 0
    seccomp_supervisor_fail_closed: bool = False
    seccomp_supervisor_stopped: bool = False
    controller_watchdog: dict[str, Any] | None = None


def _fail(message: str) -> NoReturn:
    raise ControllerError(message)


def _utcnow() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(
            value,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        )
        + "\n"
    ).encode("utf-8")


def _pretty_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    ).encode("utf-8")


def _sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def _hash_index(index: Mapping[str, str]) -> str:
    """Hash an inventory exactly as the freeze controller does."""

    return _sha256_bytes(_canonical_json_bytes(dict(sorted(index.items()))))


def _require_root() -> None:
    if os.geteuid() != 0:
        _fail("answer-blind controller launcher must run as root")


def _plain_directory(raw: Path | str, *, label: str) -> Path:
    path = Path(raw)
    if path.is_symlink():
        _fail(f"{label} must not be a symbolic link: {path}")
    try:
        resolved = path.resolve(strict=True)
    except OSError as exc:
        raise ControllerError(f"{label} does not exist: {path}") from exc
    if not resolved.is_dir():
        _fail(f"{label} is not a directory: {path}")
    return resolved


def _plain_file(raw: Path | str, *, label: str, executable: bool = False) -> Path:
    path = Path(raw)
    if path.is_symlink():
        _fail(f"{label} must not be a symbolic link: {path}")
    try:
        resolved = path.resolve(strict=True)
    except OSError as exc:
        raise ControllerError(f"{label} does not exist: {path}") from exc
    if not resolved.is_file():
        _fail(f"{label} is not a regular file: {path}")
    if executable and not os.access(resolved, os.X_OK):
        _fail(f"{label} is not executable: {resolved}")
    return resolved


def _safe_relative(raw: object, *, label: str) -> str:
    value = str(raw)
    path = PurePosixPath(value)
    if (
        not value
        or "\\" in value
        or "\x00" in value
        or path.is_absolute()
        or path.as_posix() != value
        or any(part in {"", ".", ".."} for part in path.parts)
    ):
        _fail(f"{label} is not a normalized project-relative path")
    return value


def _identity(user: str) -> SolverIdentity:
    try:
        entry = pwd.getpwnam(user)
    except KeyError as exc:
        raise ControllerError(f"dedicated user does not exist: {user}") from exc
    if entry.pw_uid == 0 or entry.pw_gid == 0:
        _fail("solver/verifier identity must be non-root")
    return SolverIdentity(user=user, uid=entry.pw_uid, gid=entry.pw_gid)


def _inside(path: Path, root: Path) -> bool:
    try:
        path.relative_to(root)
    except ValueError:
        return False
    return True


def _assert_pairwise_disjoint(paths: Mapping[str, Path]) -> None:
    items = list(paths.items())
    for index, (left_label, left) in enumerate(items):
        for right_label, right in items[index + 1 :]:
            if _inside(left, right) or _inside(right, left):
                _fail(
                    f"{left_label} and {right_label} must be disjoint: "
                    f"{left}, {right}"
                )


def _validate_private_directory(
    path: Path, *, identity: SolverIdentity, label: str,
    run_id: str, variant: str, allow_credentials: bool,
) -> None:
    metadata = path.stat()
    if (
        metadata.st_uid != identity.uid
        or metadata.st_gid != identity.gid
        or stat.S_IMODE(metadata.st_mode) != 0o700
    ):
        _fail(f"{label} must be dedicated-UID-owned mode 0700")
    sentinel = path / ".answer-blind-private.json"
    if sentinel.is_symlink() or not sentinel.is_file():
        _fail(f"{label} lacks its trusted run-binding sentinel")
    binding = _load_json(sentinel, label=f"{label} run binding")
    if binding != {
        "protocol": PROTOCOL,
        "variant": variant,
        "run_id": run_id,
        "uid": identity.uid,
        "kind": "home" if "home" in label else "tmp",
    }:
        _fail(f"{label} is bound to a different run or variant")
    allowed_top = {sentinel.name}
    if allow_credentials:
        allowed_top.update({".cache", ".config", ".local", ".codex", ".claude"})
    unexpected = sorted(child.name for child in path.iterdir() if child.name not in allowed_top)
    if unexpected:
        _fail(f"{label} contains unexpected pre-run content: {unexpected}")


def _lstat_entries(root: Path) -> Iterable[Path]:
    """Yield a tree without following symlinks."""

    yield root
    for directory, names, files in os.walk(root, topdown=True, followlinks=False):
        base = Path(directory)
        for name in sorted(names):
            path = base / name
            yield path
        for name in sorted(files):
            yield base / name


def _assert_controller_tree(root: Path, *, label: str) -> None:
    """Require a root-owned tree with no group/other writable real entries."""

    for path in _lstat_entries(root):
        metadata = path.lstat()
        relative = "." if path == root else path.relative_to(root).as_posix()
        if stat.S_ISLNK(metadata.st_mode):
            if metadata.st_uid != 0:
                _fail(f"{label} symlink is not root-owned: {relative}")
            try:
                target = path.resolve(strict=True)
            except OSError as exc:
                raise ControllerError(f"{label} has dangling symlink: {relative}") from exc
            target_stat = target.stat()
            if target_stat.st_uid != 0 or stat.S_IMODE(target_stat.st_mode) & 0o022:
                _fail(f"{label} symlink target is not root-owned read-only: {relative}")
            continue
        if not (stat.S_ISDIR(metadata.st_mode) or stat.S_ISREG(metadata.st_mode)):
            _fail(f"{label} contains unsupported filesystem entry: {relative}")
        if metadata.st_uid != 0:
            _fail(f"{label} entry is not root-owned: {relative}")
        if stat.S_IMODE(metadata.st_mode) & 0o022:
            _fail(f"{label} entry is group/other writable: {relative}")


def harden_controller_tree(root: Path | str) -> None:
    """Normalize an already-curated runtime/dependency tree, then verify it.

    This is intentionally limited to an explicit path and never accepts a
    symlink root.  It does not delete or replace content.
    """

    _require_root()
    tree = _plain_directory(root, label="controller runtime tree")
    entries = list(_lstat_entries(tree))
    for path in reversed(entries):
        metadata = path.lstat()
        if stat.S_ISLNK(metadata.st_mode):
            os.lchown(path, 0, 0)
            continue
        os.chown(path, 0, 0, follow_symlinks=False)
        mode = stat.S_IMODE(metadata.st_mode) & ~0o022
        if stat.S_ISDIR(metadata.st_mode):
            mode |= stat.S_IRUSR | stat.S_IXUSR
        os.chmod(path, mode, follow_symlinks=False)
    _assert_controller_tree(tree, label="controller runtime tree")


def _inventory_tree(
    root: Path,
    *,
    exclude_roots: Sequence[Path] = (),
    max_files: int = 400_000,
    max_file_bytes: int = 2 * 1024**3,
    max_total_bytes: int = 40 * 1024**3,
) -> dict[str, str]:
    exclusions = tuple(path.resolve() for path in exclude_roots)
    root_resolved = root.resolve(strict=True)
    result: dict[str, str] = {}
    total = 0
    for directory, names, files in os.walk(root, topdown=True, followlinks=False):
        base = Path(directory)
        kept: list[str] = []
        for name in sorted(names):
            child = base / name
            if any(child.resolve() == excluded for excluded in exclusions):
                continue
            if child.is_symlink():
                relative = child.relative_to(root).as_posix()
                try:
                    resolved_target = child.resolve(strict=True)
                    resolved_target.relative_to(root_resolved)
                except (OSError, ValueError) as exc:
                    raise ControllerError(
                        f"inventory symlink escapes or is dangling: {child}"
                    ) from exc
                target = os.readlink(child).encode(
                    "utf-8", errors="surrogateescape"
                )
                result[relative] = _sha256_bytes(
                    b"symlink\0" + target
                )
            else:
                kept.append(name)
        names[:] = kept
        for name in sorted(files):
            path = base / name
            relative = path.relative_to(root).as_posix()
            if path.is_symlink():
                try:
                    resolved_target = path.resolve(strict=True)
                    resolved_target.relative_to(root_resolved)
                except (OSError, ValueError) as exc:
                    raise ControllerError(
                        f"inventory symlink escapes or is dangling: {path}"
                    ) from exc
                target = os.readlink(path).encode(
                    "utf-8", errors="surrogateescape"
                )
                result[relative] = _sha256_bytes(
                    b"symlink\0" + target
                )
                continue
            metadata = path.stat()
            if not stat.S_ISREG(metadata.st_mode):
                _fail(f"inventory contains unsupported entry: {path}")
            if metadata.st_size > max_file_bytes:
                _fail(f"inventory file exceeds size cap: {path}")
            total += metadata.st_size
            if total > max_total_bytes:
                _fail(f"inventory exceeds total byte cap: {root}")
            result[relative] = _sha256_file(path)
            if len(result) > max_files:
                _fail(f"inventory exceeds file-count cap: {root}")
    return dict(sorted(result.items()))


def _load_json(path: Path, *, label: str) -> dict[str, Any]:
    if path.is_symlink() or not path.is_file():
        _fail(f"{label} must be a plain file: {path}")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ControllerError(f"invalid {label}: {path}") from exc
    if not isinstance(value, dict):
        _fail(f"{label} must contain a JSON object")
    return value


def _seed_payload(workspace: Path) -> dict[str, str]:
    manifest = _load_json(workspace / "isolation_manifest.json", label="seed manifest")
    raw = manifest.get("payload_files")
    if (
        manifest.get("protocol") != "icho-problem-only-solver-seed-v1"
        or not isinstance(raw, dict)
        or not raw
    ):
        _fail("workspace does not contain a supported answer-blind seed manifest")
    payload: dict[str, str] = {}
    for candidate, digest in raw.items():
        relative = _safe_relative(candidate, label="seed payload path")
        if not isinstance(digest, str) or SHA256.fullmatch(digest) is None:
            _fail(f"invalid seed payload digest: {relative}")
        payload[relative] = digest
    return payload


def _protected_relative_files(workspace: Path) -> set[str]:
    payload = _seed_payload(workspace)
    protected = set(payload)
    protected.update(GENERATED_PROTECTED_FILES)
    protected.update(
        path.relative_to(workspace).as_posix()
        for relative in SOLVER_VISIBLE_PROTECTED_TREES
        for root in (workspace.joinpath(*PurePosixPath(relative).parts),)
        if root.is_dir()
        for path in root.rglob("*")
        if path.is_file() and not path.is_symlink()
    )
    for relative in CONDITIONAL_SOLVER_VISIBLE_PROTECTED_FILES:
        path = workspace.joinpath(*PurePosixPath(relative).parts)
        if path.exists() or path.parent.exists():
            protected.add(relative)
    # The generated umbrella is fixed and delegates all mutable imports to a
    # file below IChO2026Problems/, whose directory is solver-owned.
    protected.add("IChO2026Problems.lean")
    return protected


def _protected_inventory(
    workspace: Path, *, solver_gid: int | None = None,
) -> dict[str, str]:
    """Inventory immutable solver-visible authority and runtime policy files."""

    result: dict[str, str] = {}
    for relative in sorted(_protected_relative_files(workspace)):
        path = workspace.joinpath(*PurePosixPath(relative).parts)
        if path.is_symlink() or not path.is_file():
            _fail(f"protected workspace file is missing or unsafe: {relative}")
        metadata = path.stat()
        if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) & 0o022:
            _fail(f"protected workspace file is not root-owned read-only: {relative}")
        if solver_gid is not None and (
            metadata.st_gid != solver_gid
            or not stat.S_IMODE(metadata.st_mode) & stat.S_IRGRP
        ):
            _fail(f"protected workspace file is not solver-group-readable: {relative}")
        if solver_gid is not None:
            parent = path.parent
            while True:
                parent_metadata = parent.stat()
                parent_mode = stat.S_IMODE(parent_metadata.st_mode)
                traversable = bool(parent_mode & stat.S_IXOTH) or bool(
                    parent_metadata.st_gid == solver_gid
                    and parent_mode & stat.S_IXGRP
                )
                if (
                    parent_metadata.st_uid != 0
                    or parent_mode & 0o022
                    or not traversable
                ):
                    _fail(
                        "protected workspace parent is not root-owned "
                        f"solver-traversable: {parent.relative_to(workspace) or '.'}"
                    )
                if parent == workspace:
                    break
                parent = parent.parent
        result[relative] = _sha256_file(path)
    return result


def _protected_receipt(
    workspace: Path, *, solver_gid: int | None = None,
) -> dict[str, Any]:
    files = _protected_inventory(workspace, solver_gid=solver_gid)
    return {"files": files, "aggregate_sha256": _hash_index(files)}


def _ensure_owned_dir(path: Path, identity: SolverIdentity, *, mode: int = 0o700) -> None:
    if path.is_symlink() or (path.exists() and not path.is_dir()):
        _fail(f"writable path must be a plain directory: {path}")
    path.mkdir(parents=True, exist_ok=True)
    for entry in _lstat_entries(path):
        metadata = entry.lstat()
        if stat.S_ISLNK(metadata.st_mode):
            _fail(f"solver-writable tree contains a symbolic link: {entry}")
        if not (stat.S_ISDIR(metadata.st_mode) or stat.S_ISREG(metadata.st_mode)):
            _fail(f"solver-writable tree contains unsupported entry: {entry}")
        os.chown(entry, identity.uid, identity.gid, follow_symlinks=False)
        current = stat.S_IMODE(metadata.st_mode)
        os.chmod(entry, mode if stat.S_ISDIR(metadata.st_mode) else (current & 0o700 or 0o600))


def _make_root_readonly(path: Path) -> None:
    for entry in reversed(list(_lstat_entries(path))):
        metadata = entry.lstat()
        if stat.S_ISLNK(metadata.st_mode):
            os.lchown(entry, 0, 0)
            continue
        os.chown(entry, 0, 0, follow_symlinks=False)
        mode = stat.S_IMODE(metadata.st_mode) & ~0o022
        if stat.S_ISDIR(metadata.st_mode):
            mode |= 0o500
        elif mode & 0o111:
            mode |= 0o500
        else:
            mode |= 0o400
        os.chmod(entry, mode, follow_symlinks=False)


def _make_solver_visible_protected_files_readable(
    workspace: Path, identity: SolverIdentity,
) -> None:
    """Expose immutable inputs to only root and the dedicated solver group."""

    directories: set[Path] = set()
    for relative in _protected_relative_files(workspace):
        path = workspace.joinpath(*PurePosixPath(relative).parts)
        if path.is_symlink() or not path.is_file():
            _fail(f"protected workspace file is missing or unsafe: {relative}")
        metadata = path.stat(follow_symlinks=False)
        os.chown(path, 0, identity.gid, follow_symlinks=False)
        os.chmod(
            path,
            0o550 if stat.S_IMODE(metadata.st_mode) & 0o111 else 0o640,
            follow_symlinks=False,
        )
        parent = path.parent
        while parent != workspace:
            directories.add(parent)
            parent = parent.parent

    for directory in sorted(directories, key=lambda item: len(item.parts)):
        if directory.is_symlink() or not directory.is_dir():
            _fail(f"protected workspace parent is unsafe: {directory}")
        os.chown(directory, 0, identity.gid, follow_symlinks=False)
        os.chmod(directory, 0o750, follow_symlinks=False)


def harden_solver_workspace(
    *,
    workspace: Path | str,
    identity: SolverIdentity,
    dependency_root: Path | str,
    private_home: Path | str,
    private_tmp: Path | str,
    variant: str,
    run_id: str,
) -> dict[str, Any]:
    """Apply the controller/solver ownership split after trusted ingest."""

    _require_root()
    root = _plain_directory(workspace, label="solver workspace")
    dependency = _plain_directory(dependency_root, label="Lean dependency tree")
    _assert_controller_tree(dependency, label="Lean dependency tree")

    # First make the complete project controller-owned and non-writable.  This
    # revokes any overly broad ownership left by seed copying/ingest.
    _make_root_readonly(root)
    os.chmod(root, 0o755)

    archon_root = root / ".archon"
    if not archon_root.is_dir() or archon_root.is_symlink():
        _fail("trusted ingest must create a plain .archon directory")
    os.chown(archon_root, 0, 0)
    os.chmod(archon_root, 0o755)

    # A root-owned .lake parent prevents replacement of the dependency link.
    lake_root = root / ".lake"
    lake_root.mkdir(exist_ok=True)
    os.chown(lake_root, 0, 0)
    os.chmod(lake_root, 0o755)
    packages = lake_root / "packages"
    if packages.exists() or packages.is_symlink():
        if not packages.is_symlink() or packages.resolve() != dependency:
            _fail(".lake/packages must be absent or the trusted dependency symlink")
    else:
        packages.symlink_to(dependency, target_is_directory=True)
    os.lchown(packages, 0, 0)

    # Trusted preparation commonly runs under umask 077. Normalize immutable
    # solver-visible inputs so non-root can read them without gaining writes.
    _make_solver_visible_protected_files_readable(root, identity)

    for relative in MUTABLE_WORKSPACE_DIRS:
        _ensure_owned_dir(
            root.joinpath(*PurePosixPath(relative).parts), identity, mode=0o700
        )

    all_file = root / "IChO2026Problems/All.lean"
    if not all_file.exists():
        all_file.write_text(
            "import IChO2026Chem\n\n/-! Solver-owned target umbrella. -/\n",
            encoding="utf-8",
        )
    for relative in MUTABLE_WORKSPACE_FILES:
        path = root.joinpath(*PurePosixPath(relative).parts)
        if path.is_symlink() or (path.exists() and not path.is_file()):
            _fail(f"mutable state path is unsafe: {relative}")
        if not path.exists():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.touch(mode=0o600)
        os.chown(path, identity.uid, identity.gid)
        os.chmod(path, 0o600)

    # Reassert the parent boundaries after recursive writable-dir ownership.
    for protected_parent in (root, archon_root, lake_root):
        os.chown(protected_parent, 0, 0)
        os.chmod(protected_parent, 0o755)

    if variant not in VARIANT_MODELS or SAFE_RUN_ID.fullmatch(run_id) is None:
        _fail("private directory binding needs an approved variant/run_id")
    home = Path(private_home)
    temporary = Path(private_tmp)
    raw_private = {"private home": home.absolute(), "private tmp": temporary.absolute()}
    _assert_pairwise_disjoint(
        {
            "solver workspace": root,
            "Lean dependency tree": dependency,
            **raw_private,
        }
    )
    for path, label in ((home, "private home"), (temporary, "private tmp")):
        if path.exists() or path.is_symlink():
            _fail(f"{label} must be a fresh, absent controller-selected path")
        if path.parent.is_symlink() or not path.parent.is_dir():
            _fail(f"{label} parent must be an existing plain directory")
        path.mkdir(mode=0o700)
        os.chown(path, identity.uid, identity.gid)
        sentinel = path / ".answer-blind-private.json"
        _atomic_new_controller_file(
            sentinel,
            _pretty_json_bytes(
                {
                    "protocol": PROTOCOL,
                    "variant": variant,
                    "run_id": run_id,
                    "uid": identity.uid,
                    "kind": "home" if label == "private home" else "tmp",
                }
            ),
            mode=0o600,
        )
        os.chown(sentinel, identity.uid, identity.gid)
        _validate_private_directory(
            path.resolve(),
            identity=identity,
            label=label,
            run_id=run_id,
            variant=variant,
            allow_credentials=label == "private home",
        )

    protected = _protected_receipt(root, solver_gid=identity.gid)
    return {
        "workspace": str(root),
        "uid": identity.uid,
        "gid": identity.gid,
        "protected": protected,
        "writable_directories": list(MUTABLE_WORKSPACE_DIRS),
        "writable_files": list(MUTABLE_WORKSPACE_FILES),
        "dependency_root": str(dependency),
    }


def _libc() -> ctypes.CDLL:
    library = ctypes.CDLL(None, use_errno=True)
    library.syscall.restype = ctypes.c_long
    library.prctl.restype = ctypes.c_int
    return library


def landlock_abi() -> int:
    library = _libc()
    result = library.syscall(
        SYS_LANDLOCK_CREATE_RULESET,
        ctypes.c_void_p(),
        ctypes.c_size_t(0),
        ctypes.c_uint32(LANDLOCK_CREATE_RULESET_VERSION),
    )
    if result < 0:
        error = ctypes.get_errno()
        raise ControllerError(f"Landlock ABI query failed: {os.strerror(error)}")
    return int(result)


def _create_ruleset() -> int:
    attribute = _LandlockRulesetAttr(
        LANDLOCK_HANDLED_ACCESS_FS, LANDLOCK_HANDLED_ACCESS_NET
    )
    result = _libc().syscall(
        SYS_LANDLOCK_CREATE_RULESET,
        ctypes.byref(attribute),
        ctypes.sizeof(attribute),
        ctypes.c_uint32(0),
    )
    if result < 0:
        error = ctypes.get_errno()
        raise OSError(error, os.strerror(error))
    return int(result)


def _add_landlock_path(ruleset_fd: int, path: Path, *, writable: bool) -> None:
    flags = os.O_PATH | os.O_CLOEXEC
    path_fd = os.open(path, flags)
    try:
        if writable and path.is_dir():
            access = LANDLOCK_HANDLED_ACCESS_FS
        elif writable:
            # LANDLOCK_RULE_PATH_BENEATH rejects directory-only rights (for
            # example MAKE_DIR and REMOVE_DIR) when parent_fd names a regular
            # file.  State-file grants must consequently contain file rights
            # only.  They deliberately do not make state files executable.
            access = (
                LANDLOCK_ACCESS_FS_READ_FILE
                | LANDLOCK_ACCESS_FS_WRITE_FILE
                | LANDLOCK_ACCESS_FS_TRUNCATE
            )
        elif path.is_dir():
            access = LANDLOCK_READ_DIR_ACCESS
        else:
            access = LANDLOCK_READ_FILE_ACCESS
        attribute = _LandlockPathBeneathAttr(access, path_fd)
        result = _libc().syscall(
            SYS_LANDLOCK_ADD_RULE,
            ruleset_fd,
            LANDLOCK_RULE_PATH_BENEATH,
            ctypes.byref(attribute),
            ctypes.c_uint32(0),
        )
        if result < 0:
            error = ctypes.get_errno()
            raise OSError(error, f"Landlock rule failed for {path}: {os.strerror(error)}")
    finally:
        os.close(path_fd)


def _apply_landlock(policy: LandlockPolicy) -> None:
    ruleset_fd = _create_ruleset()
    try:
        for path in policy.read_only_paths:
            _add_landlock_path(ruleset_fd, path, writable=False)
        for path in policy.read_write_paths:
            _add_landlock_path(ruleset_fd, path, writable=True)
        for port in policy.allowed_connect_tcp_ports:
            if not 1 <= port <= 65535:
                raise ValueError(f"invalid authorized TCP port: {port}")
            attribute = _LandlockNetPortAttr(
                LANDLOCK_ACCESS_NET_CONNECT_TCP, port
            )
            result = _libc().syscall(
                SYS_LANDLOCK_ADD_RULE,
                ruleset_fd,
                LANDLOCK_RULE_NET_PORT,
                ctypes.byref(attribute),
                ctypes.c_uint32(0),
            )
            if result < 0:
                error = ctypes.get_errno()
                raise OSError(
                    error,
                    f"Landlock TCP rule failed for port {port}: {os.strerror(error)}",
                )
        library = _libc()
        if library.prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0:
            error = ctypes.get_errno()
            raise OSError(error, os.strerror(error))
        result = library.syscall(
            SYS_LANDLOCK_RESTRICT_SELF, ruleset_fd, ctypes.c_uint32(0)
        )
        if result < 0:
            error = ctypes.get_errno()
            raise OSError(error, os.strerror(error))
    finally:
        os.close(ruleset_fd)


def _seccomp_ioc(direction: int, number: int, size: int) -> int:
    return (direction << 30) | (size << 16) | (ord("!") << 8) | number


SECCOMP_IOCTL_NOTIF_RECV = _seccomp_ioc(3, 0, ctypes.sizeof(_SeccompNotif))
SECCOMP_IOCTL_NOTIF_SEND = _seccomp_ioc(3, 1, ctypes.sizeof(_SeccompNotifResp))
SECCOMP_IOCTL_NOTIF_ADDFD = _seccomp_ioc(1, 3, ctypes.sizeof(_SeccompNotifAddfd))


def _seccomp_filter_program() -> tuple[Any, _SockFprog]:
    """Build the fail-closed syscall and connected-FD broker filter."""

    errno_result = 0x00050000 | errno.EPERM
    instructions: list[_SockFilter] = [
        _SockFilter(0x20, 0, 0, 4),                    # LD arch
        _SockFilter(0x15, 1, 0, AUDIT_ARCH_X86_64),   # exact x86_64 only
        _SockFilter(0x06, 0, 0, SECCOMP_RET_KILL_PROCESS),
        _SockFilter(0x20, 0, 0, 0),                   # LD syscall nr
        _SockFilter(0x45, 0, 1, 0x40000000),          # reject x32 namespace
        _SockFilter(0x06, 0, 0, SECCOMP_RET_KILL_PROCESS),
    ]
    # Host-global IPC and alternate socket/concurrency interfaces are denied.
    # They otherwise bypass Landlock's path and TCP mediation entirely.
    denied = (
        29, 30, 31,                 # shmget, shmat, shmctl
        43, 49, 50, 53,             # accept, bind, listen, socketpair
        64, 65, 66, 67,             # semget, semop, semctl, shmdt
        68, 69, 70, 71,             # msgget, msgsnd, msgrcv, msgctl
        220,                         # semtimedop
        240, 241, 242, 243, 244, 245, # POSIX mq_*
        248, 249, 250,               # add_key, request_key, keyctl
        288,                         # accept4
        425,                         # io_uring_setup
        438,                         # pidfd_getfd
    )
    for number in denied:
        instructions.extend(
            (_SockFilter(0x15, 0, 1, number), _SockFilter(0x06, 0, 0, errno_result))
        )
    for number in (41, 42):          # socket, connect -> root supervisor
        instructions.extend(
            (
                _SockFilter(0x15, 0, 1, number),
                _SockFilter(0x06, 0, 0, SECCOMP_RET_USER_NOTIF),
            )
        )
    instructions.append(_SockFilter(0x06, 0, 0, 0x7FFF0000))  # ALLOW
    array = (_SockFilter * len(instructions))(*instructions)
    return array, _SockFprog(len(instructions), array)


def _install_seccomp_connected_fd_filter() -> int:
    """Install the filter and return its USER_NOTIF listener descriptor."""

    if os.uname().machine not in {"x86_64", "amd64"}:
        raise OSError(errno.ENOTSUP, "answer-blind seccomp supports x86_64 only")
    _array, program = _seccomp_filter_program()
    result = _libc().syscall(
        SYS_SECCOMP,
        ctypes.c_uint32(SECCOMP_SET_MODE_FILTER),
        ctypes.c_uint32(SECCOMP_FILTER_FLAG_NEW_LISTENER),
        ctypes.byref(program),
    )
    if result < 0:
        error = ctypes.get_errno()
        raise OSError(error, f"cannot install answer-blind seccomp: {os.strerror(error)}")
    return int(result)


def _send_fd(channel_fd: int, descriptor: int) -> None:
    channel = socket.socket(fileno=channel_fd)
    try:
        channel.sendmsg(
            [b"S"],
            [(socket.SOL_SOCKET, socket.SCM_RIGHTS, struct.pack("i", descriptor))],
        )
    finally:
        channel.detach()


def _receive_fd(channel: socket.socket, *, timeout_s: float) -> int | None:
    channel.settimeout(timeout_s)
    try:
        payload, ancillary, _flags, _address = channel.recvmsg(
            1, socket.CMSG_SPACE(struct.calcsize("i"))
        )
    except (TimeoutError, socket.timeout):
        return None
    if payload != b"S":
        return None
    for level, kind, data in ancillary:
        if level == socket.SOL_SOCKET and kind == socket.SCM_RIGHTS:
            descriptor = int(struct.unpack("i", data[: struct.calcsize("i")])[0])
            flags = fcntl.fcntl(descriptor, fcntl.F_GETFL)
            fcntl.fcntl(descriptor, fcntl.F_SETFL, flags | os.O_NONBLOCK)
            return descriptor
    return None


def _seccomp_ioctl(fd: int, request: int, argument: Any) -> int:
    result = _libc().ioctl(fd, request, ctypes.byref(argument))
    if result < 0:
        error = ctypes.get_errno()
        raise OSError(error, os.strerror(error))
    return int(result)


def _seccomp_respond(listener_fd: int, notification_id: int, *, error: int = 0) -> None:
    response = _SeccompNotifResp(notification_id, 0, -abs(error), 0)
    _seccomp_ioctl(listener_fd, SECCOMP_IOCTL_NOTIF_SEND, response)


def _service_seccomp_notification(
    listener_fd: int, *, broker_port: int | None,
) -> int:
    """Service one notification; return one when a broker FD was injected."""

    notification = _SeccompNotif()
    try:
        _seccomp_ioctl(listener_fd, SECCOMP_IOCTL_NOTIF_RECV, notification)
    except OSError as exc:
        if exc.errno in {errno.ENOENT, errno.EINTR, errno.EAGAIN}:
            return 0
        raise
    if notification.data.arch != AUDIT_ARCH_X86_64:
        _seccomp_respond(listener_fd, notification.id, error=errno.EPERM)
        return 0
    if notification.data.nr == 42:  # connect: FD is already broker-connected.
        _seccomp_respond(listener_fd, notification.id)
        return 0
    if notification.data.nr != 41 or broker_port is None:
        _seccomp_respond(listener_fd, notification.id, error=errno.EPERM)
        return 0
    family, requested_type, protocol = (
        int(notification.data.args[index]) for index in range(3)
    )
    base_type = requested_type & 0xF
    permitted_flags = socket.SOCK_NONBLOCK | socket.SOCK_CLOEXEC
    if (
        family != socket.AF_INET
        or base_type != socket.SOCK_STREAM
        or requested_type & ~(0xF | permitted_flags)
        or protocol not in {0, socket.IPPROTO_TCP}
    ):
        _seccomp_respond(listener_fd, notification.id, error=errno.EPERM)
        return 0
    connected = socket.socket(socket.AF_INET, socket.SOCK_STREAM, socket.IPPROTO_TCP)
    try:
        connected.settimeout(5.0)
        connected.connect(("127.0.0.1", broker_port))
        connected.settimeout(None)
        if requested_type & socket.SOCK_NONBLOCK:
            connected.setblocking(False)
        addfd = _SeccompNotifAddfd(
            notification.id,
            SECCOMP_ADDFD_FLAG_SEND,
            connected.fileno(),
            0,
            os.O_CLOEXEC if requested_type & socket.SOCK_CLOEXEC else 0,
        )
        _seccomp_ioctl(listener_fd, SECCOMP_IOCTL_NOTIF_ADDFD, addfd)
    except OSError:
        try:
            _seccomp_respond(listener_fd, notification.id, error=errno.ECONNREFUSED)
        except OSError:
            pass
        return 0
    finally:
        connected.close()
    return 1


def _deny_non_tcp_inet_sockets() -> None:
    """Legacy name retained for callers; USER_NOTIF installation is separate.

    The confined process starts with no inherited network sockets.  Landlock
    restricts TCP connect to the hash-bound broker port; this filter closes
    UDP/QUIC/raw/MPTCP/SCTP escape surfaces which Landlock ABI 4 does not
    mediate as CONNECT_TCP.  It also rejects every ``socketpair`` call and all
    non-Internet socket families.  In particular, AF_UNIX pathname and abstract
    sockets would otherwise provide an unmediated bidirectional channel to a
    hostile host service.  Inherited pipes and already-open descriptors remain
    usable by the trusted controller/model protocol.
    """

    # This function intentionally cannot install the filter because a trusted
    # parent must retain the returned listener FD.  ``_preexec`` uses
    # ``_install_seccomp_connected_fd_filter`` and transfers that listener.

    raise RuntimeError("seccomp USER_NOTIF requires a controller supervisor")


def _existing_paths(paths: Iterable[Path]) -> tuple[Path, ...]:
    result: list[Path] = []
    seen: set[Path] = set()
    for raw in paths:
        try:
            path = raw.resolve(strict=True)
        except OSError:
            continue
        if path not in seen:
            result.append(path)
            seen.add(path)
    return tuple(result)


def _assert_exact_system_file(path: Path) -> Path:
    if path.is_symlink():
        _fail(f"system allowlist path must not be a symlink: {path}")
    resolved = _plain_file(path, label="system allowlist file")
    metadata = resolved.stat()
    if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) & 0o022:
        _fail(f"system allowlist file is not root-owned read-only: {resolved}")
    return resolved


def _system_readonly_inventory(
    runtime_root: Path | None = None,
) -> tuple[tuple[Path, ...], dict[str, str]]:
    paths = tuple(_assert_exact_system_file(Path(raw)) for raw in SYSTEM_READ_ONLY_FILES)
    if runtime_root is not None:
        paths = tuple(sorted(set(paths) | set(_runtime_external_elf_dependencies(runtime_root))))
    inventory = {str(path): _sha256_file(path) for path in paths}
    return paths, dict(sorted(inventory.items()))


def _elf_dynamic_names(path: Path) -> tuple[set[str], str | None]:
    """Read DT_NEEDED and PT_INTERP without executing an untrusted helper."""

    payload = path.read_bytes()
    if not payload.startswith(ELF_MAGIC) or len(payload) < 64:
        return set(), None
    elf_class, endian = payload[4], payload[5]
    if elf_class != 2 or endian not in {1, 2}:
        _fail(f"unsupported ELF class/endianness in sealed runtime: {path}")
    order = "<" if endian == 1 else ">"
    header = struct.unpack_from(order + "HHIQQQIHHHHHH", payload, 16)
    phoff, phentsize, phnum = header[4], header[8], header[9]
    segments: list[tuple[int, int, int, int]] = []
    interpreter: str | None = None
    dynamic: tuple[int, int] | None = None
    for index in range(phnum):
        offset = phoff + index * phentsize
        p_type, _flags, p_offset, p_vaddr, _paddr, p_filesz, _memsz, _align = (
            struct.unpack_from(order + "IIQQQQQQ", payload, offset)
        )
        segments.append((p_vaddr, p_offset, p_filesz, p_type))
        if p_type == 3:
            interpreter = payload[p_offset : p_offset + p_filesz].rstrip(b"\0").decode()
        elif p_type == 2:
            dynamic = (p_offset, p_filesz)
    if dynamic is None:
        return set(), interpreter
    strtab_addr: int | None = None
    needed_offsets: list[int] = []
    dyn_offset, dyn_size = dynamic
    for offset in range(dyn_offset, dyn_offset + dyn_size, 16):
        tag, value = struct.unpack_from(order + "qQ", payload, offset)
        if tag == 0:
            break
        if tag == 1:
            needed_offsets.append(value)
        elif tag == 5:
            strtab_addr = value
    if strtab_addr is None:
        return set(), interpreter
    strtab_offset: int | None = None
    for vaddr, file_offset, file_size, _kind in segments:
        if vaddr <= strtab_addr < vaddr + file_size:
            strtab_offset = file_offset + (strtab_addr - vaddr)
            break
    if strtab_offset is None:
        _fail(f"cannot map ELF dynamic string table: {path}")
    names: set[str] = set()
    for relative in needed_offsets:
        start = strtab_offset + relative
        end = payload.find(b"\0", start)
        if end < 0:
            _fail(f"unterminated ELF DT_NEEDED entry: {path}")
        names.add(payload[start:end].decode("utf-8"))
    return names, interpreter


def _runtime_external_elf_dependencies(runtime_root: Path) -> tuple[Path, ...]:
    search_roots = (Path("/usr/lib/x86_64-linux-gnu"), Path("/usr/lib64"))
    pending: list[Path] = []
    for path in _lstat_entries(runtime_root):
        if path.is_symlink() or not path.is_file():
            continue
        try:
            with path.open("rb") as stream:
                if stream.read(4) == ELF_MAGIC:
                    pending.append(path)
        except OSError as exc:
            raise ControllerError(f"cannot inspect sealed runtime ELF: {path}") from exc
    found: dict[Path, Path] = {}
    inspected: set[Path] = set()
    while pending:
        binary = pending.pop()
        if binary in inspected:
            continue
        inspected.add(binary)
        needed, interpreter = _elf_dynamic_names(binary)
        candidates = list(needed)
        if interpreter:
            candidates.append(Path(interpreter).name)
        for name in candidates:
            matches = [
                child
                for root in search_roots
                for child in (root / name,)
                if child.exists()
            ]
            if not matches:
                # The dependency may be shipped next to the binary itself.
                if any((binary.parent / name).exists() for _unused in (0,)):
                    continue
                if any(path.name == name for path in _lstat_entries(runtime_root)):
                    continue
                _fail(f"cannot resolve sealed runtime ELF dependency {name!r} for {binary}")
            resolved = _assert_exact_system_file(matches[0].resolve(strict=True))
            found[resolved] = resolved
            pending.append(resolved)
    return tuple(sorted(found))


def build_landlock_policy(
    *,
    workspace: Path,
    runtime_root: Path,
    dependency_root: Path,
    private_home: Path,
    private_tmp: Path,
    controller_dir: Path,
    sibling_workspace: Path | None = None,
    verifier_readonly: bool = False,
    verifier_output_dir: Path | None = None,
    required_probe_paths: Sequence[Path] | None = None,
    allowed_connect_tcp_ports: Sequence[int] = (),
) -> LandlockPolicy:
    abi = landlock_abi()
    if abi < LANDLOCK_MIN_ABI:
        _fail(f"Landlock ABI {LANDLOCK_MIN_ABI}+ required; kernel reports {abi}")
    system_readonly, _system_inventory = _system_readonly_inventory(runtime_root)
    device_readonly = _existing_paths(Path(raw) for raw in SYSTEM_DEVICE_FILES)
    readonly = _existing_paths(
        [*system_readonly, *device_readonly, runtime_root, dependency_root, workspace]
    )
    if verifier_readonly:
        if verifier_output_dir is None:
            _fail("verifier output directory is required for verifier policy")
        writable = _existing_paths([private_home, private_tmp, verifier_output_dir])
    else:
        writable = _existing_paths(
            [
                private_home,
                private_tmp,
                *(workspace.joinpath(*PurePosixPath(path).parts) for path in MUTABLE_WORKSPACE_DIRS),
                *(workspace.joinpath(*PurePosixPath(path).parts) for path in MUTABLE_WORKSPACE_FILES),
            ]
        )
    if required_probe_paths is None:
        probes = [
            Path("/root"), Path("/tmp"), Path("/var/tmp"), Path("/dev/shm"),
            Path("/dev/tty"),
            Path("/proc/1/environ"), controller_dir,
        ]
        if sibling_workspace is not None:
            probes.append(sibling_workspace)
    else:
        probes = list(required_probe_paths)
    # The authorization deliberately contains only stable paths so it can be
    # reused by every one-iteration controller process.  Each actual receipt
    # additionally proves its own root controller process environment denied.
    probes.append(Path(f"/proc/{os.getpid()}/environ"))
    return LandlockPolicy(
        abi=abi,
        read_only_paths=readonly,
        read_write_paths=writable,
        probe_paths=_existing_paths(probes),
        allowed_connect_tcp_ports=tuple(sorted(set(allowed_connect_tcp_ports))),
    )


def _probe_denials(paths: Sequence[Path]) -> dict[str, dict[str, Any]]:
    results: dict[str, dict[str, Any]] = {}
    for path in paths:
        flags = os.O_RDONLY | os.O_CLOEXEC
        if path.is_dir():
            flags |= os.O_DIRECTORY
        try:
            descriptor = os.open(path, flags)
        except OSError as exc:
            results[str(path)] = {
                "open_read_denied": exc.errno in {errno.EACCES, errno.EPERM},
                "errno": int(exc.errno or 0),
            }
        else:
            os.close(descriptor)
            results[str(path)] = {"open_read_denied": False, "errno": 0}
    return results


def _preexec(
    *, policy: LandlockPolicy, identity: SolverIdentity, probe_fd: int,
    seccomp_channel_fd: int, rlimit_nproc: int,
):
    controller_pid = os.getpid()

    def prepare() -> None:
        listener_fd = -1
        try:
            _apply_landlock(policy)
            listener_fd = _install_seccomp_connected_fd_filter()
            _send_fd(seccomp_channel_fd, listener_fd)
            os.close(listener_fd)
            listener_fd = -1
            os.close(seccomp_channel_fd)
            os.setgroups([])
            os.setgid(identity.gid)
            os.setuid(identity.uid)
            # set*id clears PDEATHSIG on Linux.  Rearm it after the credential
            # transition and close the race by checking the original parent.
            library = _libc()
            if library.prctl(PR_SET_PDEATHSIG, signal.SIGKILL, 0, 0, 0) != 0:
                error = ctypes.get_errno()
                raise OSError(error, f"cannot arm PDEATHSIG: {os.strerror(error)}")
            if os.getppid() != controller_pid:
                raise OSError(errno.ESRCH, "trusted controller died during child setup")
            resource.setrlimit(
                resource.RLIMIT_NPROC, (rlimit_nproc, rlimit_nproc)
            )
            probes = _probe_denials(policy.probe_paths)
            failed = sorted(
                path
                for path, result in probes.items()
                if result.get("open_read_denied") is not True
            )
            if failed:
                payload = _canonical_json_bytes(
                    {
                        "ok": False,
                        "error": "negative open/read probe succeeded: "
                        + ", ".join(failed),
                        "probes": probes,
                    }
                )
            else:
                payload = _canonical_json_bytes({"ok": True, "probes": probes})
        except BaseException as exc:
            if listener_fd >= 0:
                os.close(listener_fd)
            try:
                os.close(seccomp_channel_fd)
            except OSError:
                pass
            payload = _canonical_json_bytes(
                {"ok": False, "error": f"{type(exc).__name__}: {exc}"}
            )
        try:
            os.write(probe_fd, payload)
        finally:
            os.close(probe_fd)
        if json.loads(payload).get("ok") is not True:
            os._exit(126)

    return prepare


def _proc_parent_map() -> dict[int, int]:
    result: dict[int, int] = {}
    for child in Path("/proc").iterdir():
        if not child.name.isdigit():
            continue
        try:
            text = (child / "stat").read_text(encoding="utf-8")
            tail = text[text.rfind(")") + 2 :].split()
            result[int(child.name)] = int(tail[1])
        except (OSError, ValueError, IndexError):
            continue
    return result


def _descendants(roots: set[int], parent_map: Mapping[int, int]) -> set[int]:
    found: set[int] = set()
    changed = True
    while changed:
        changed = False
        for pid, parent in parent_map.items():
            if pid not in found and (parent in roots or parent in found):
                found.add(pid)
                changed = True
    return found


def _alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def _real_uid_pids(uid: int) -> list[int]:
    """Return all processes whose real UID is ``uid``.

    Parent/PGID tracking is intentionally insufficient: a hostile child can
    double-fork, call setsid(), and reparent between scans.  A dedicated UID is
    the kernel-stable membership boundary available on hosts whose cgroup v2
    hierarchy is not delegated to this controller.
    """

    result: list[int] = []
    for child in Path("/proc").iterdir():
        if not child.name.isdigit():
            continue
        try:
            for line in (child / "status").read_text(encoding="utf-8").splitlines():
                if line.startswith("Uid:"):
                    if int(line.split()[1]) == uid:
                        result.append(int(child.name))
                    break
        except (OSError, ValueError, IndexError):
            continue
    return sorted(result)


def _require_uid_quiescent_before(identity: SolverIdentity) -> list[int]:
    pids = _real_uid_pids(identity.uid)
    if pids:
        _fail(
            f"dedicated solver UID {identity.uid} is already active: {pids}"
        )
    return pids


def _reap_controller_children(pids: Iterable[int]) -> None:
    for pid in pids:
        try:
            os.waitpid(pid, os.WNOHANG)
        except ChildProcessError:
            continue


def _kill_dedicated_uid(
    *, identity: SolverIdentity, process: subprocess.Popen[Any],
    rlimit_nproc: int, quiet_period_ms: int = 600,
) -> dict[str, Any]:
    """Freeze fork capacity, pidfd-kill, and prove a dedicated UID is empty."""

    if not 1 <= rlimit_nproc <= 256:
        _fail("dedicated UID RLIMIT_NPROC must be between 1 and 256")
    if not hasattr(os, "pidfd_open") or not hasattr(signal, "pidfd_send_signal"):
        _fail("pidfd_open and pidfd_send_signal are required for UID quiescence")
    kill_rounds = 0
    prlimit_ok = True
    deadline = time.monotonic() + 10.0
    quiet_since: float | None = None
    while time.monotonic() < deadline:
        pids = _real_uid_pids(identity.uid)
        if not pids:
            if quiet_since is None:
                quiet_since = time.monotonic()
            if (time.monotonic() - quiet_since) * 1000 >= quiet_period_ms:
                break
            time.sleep(0.025)
            continue
        quiet_since = None
        kill_rounds += 1
        for pid in pids:
            try:
                resource.prlimit(pid, resource.RLIMIT_NPROC, (0, 0))
            except ProcessLookupError:
                continue
            except (PermissionError, OSError):
                prlimit_ok = False
                # Lack of CAP_SYS_RESOURCE/SYS_PTRACE invalidates the signed
                # attestation, but must never prevent best-effort cleanup.
                # pidfd still avoids a PID-reuse race and the caller will fail
                # this invocation closed after the UID is empty.
            try:
                pidfd = os.pidfd_open(pid, 0)
            except ProcessLookupError:
                continue
            try:
                signal.pidfd_send_signal(pidfd, signal.SIGKILL)
            except ProcessLookupError:
                pass
            finally:
                os.close(pidfd)
        try:
            process.wait(timeout=0.05)
        except subprocess.TimeoutExpired:
            pass
        _reap_controller_children(pids)
        time.sleep(0.025)
    after = _real_uid_pids(identity.uid)
    return {
        "mechanism": "dedicated_uid_prlimit_pidfd_v1",
        "uid": identity.uid,
        "rlimit_nproc": rlimit_nproc,
        "quiescent_before": True,
        "before_pids": [],
        "prlimit_zero_applied": prlimit_ok,
        "pidfd_kill_used": True,
        "kill_rounds": kill_rounds,
        "quiet_period_ms": quiet_period_ms,
        "after_pids": after,
        "quiescent_after": not after,
    }


def run_confined_command(
    *,
    argv: Sequence[str],
    cwd: Path,
    environment: Mapping[str, str],
    identity: SolverIdentity,
    policy: LandlockPolicy,
    log_path: Path,
    timeout_s: int,
    rlimit_nproc: int = 256,
) -> ConfinedResult:
    """Run one command under Landlock and prove its process tree is stopped."""

    _require_root()
    if not argv or not Path(argv[0]).is_absolute():
        _fail("confined command executable must be absolute")
    if timeout_s < 1:
        _fail("timeout must be positive")
    if not 1 <= rlimit_nproc <= 256:
        _fail("RLIMIT_NPROC must be between 1 and 256")
    _require_uid_quiescent_before(identity)
    for path in (*policy.read_only_paths, *policy.read_write_paths):
        if not path.exists():
            _fail(f"Landlock allow path disappeared: {path}")
    if log_path.exists() or log_path.is_symlink():
        _fail(f"controller log must be a new path: {log_path}")
    if log_path.parent.is_symlink() or not log_path.parent.is_dir():
        _fail("controller log parent must be an existing plain directory")

    library = _libc()
    if library.prctl(PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0) != 0:
        error = ctypes.get_errno()
        raise ControllerError(f"cannot enable child subreaper: {os.strerror(error)}")
    read_fd, write_fd = os.pipe()
    os.set_inheritable(write_fd, True)
    supervisor_parent, supervisor_child = socket.socketpair(
        socket.AF_UNIX, socket.SOCK_SEQPACKET | socket.SOCK_CLOEXEC
    )
    os.set_inheritable(supervisor_child.fileno(), True)
    started_at = _utcnow()
    timed_out = False
    supervisor_error: str | None = None
    connected_fd_injection_count = 0
    listener_fd: int | None = None
    with log_path.open("xb") as log:
        try:
            process = subprocess.Popen(
                list(argv),
                cwd=cwd,
                env=dict(environment),
                stdin=subprocess.DEVNULL,
                stdout=log,
                stderr=subprocess.STDOUT,
                start_new_session=True,
                pass_fds=(write_fd, supervisor_child.fileno()),
                preexec_fn=_preexec(
                    policy=policy,
                    identity=identity,
                    probe_fd=write_fd,
                    seccomp_channel_fd=supervisor_child.fileno(),
                    rlimit_nproc=rlimit_nproc,
                ),
            )
        finally:
            os.close(write_fd)
            supervisor_child.close()
        listener_fd = _receive_fd(supervisor_parent, timeout_s=5.0)
        supervisor_parent.close()
        if listener_fd is None:
            supervisor_error = "seccomp child did not return a USER_NOTIF listener"
        deadline = time.monotonic() + timeout_s
        while process.poll() is None and time.monotonic() < deadline:
            if listener_fd is None:
                time.sleep(0.025)
                continue
            try:
                readable, _writable, _exceptional = select.select(
                    [listener_fd], [], [], 0.05
                )
                if readable:
                    connected_fd_injection_count += _service_seccomp_notification(
                        listener_fd,
                        broker_port=(
                            policy.allowed_connect_tcp_ports[0]
                            if len(policy.allowed_connect_tcp_ports) == 1
                            else None
                        ),
                    )
            except OSError as exc:
                supervisor_error = f"seccomp USER_NOTIF supervisor failed: {exc}"
                break
        if process.poll() is None and time.monotonic() >= deadline:
            timed_out = True
        if supervisor_error is not None and process.poll() is None:
            # Closing the listener makes every pending/future notified syscall
            # fail closed; UID cleanup below terminates all descendants.
            os.close(listener_fd) if listener_fd is not None else None
            listener_fd = None
        quiescence = _kill_dedicated_uid(
            identity=identity,
            process=process,
            rlimit_nproc=rlimit_nproc,
        )
        try:
            process.wait(timeout=2)
        except subprocess.TimeoutExpired:
            pass
        solver_stopped = not _alive(process.pid)
        descendants_stopped = bool(quiescence["quiescent_after"])
        exit_code = int(process.returncode if process.returncode is not None else -signal.SIGKILL)
        log.flush()
        os.fsync(log.fileno())
    seccomp_supervisor_stopped = False
    if listener_fd is not None:
        os.close(listener_fd)
        seccomp_supervisor_stopped = True
    elif supervisor_error is not None:
        # A failed supervisor is closed/fail-closed, but not a passing
        # attestation.  The caller records the forensic error.
        seccomp_supervisor_stopped = True
    probe_payload = b""
    while True:
        chunk = os.read(read_fd, 65536)
        if not chunk:
            break
        probe_payload += chunk
    os.close(read_fd)
    confinement_error: str | None = None
    try:
        probe_result = json.loads(probe_payload.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ControllerError("Landlock child did not return a valid probe receipt") from exc
    if probe_result.get("ok") is not True:
        confinement_error = f"Landlock child setup failed: {probe_result.get('error')}"
    probes = probe_result.get("probes")
    if not isinstance(probes, dict) or not probes:
        probes = {}
        confinement_error = confinement_error or "Landlock child returned no isolation probes"
    for path, result in probes.items():
        if not isinstance(result, dict) or result.get("open_read_denied") is not True:
            confinement_error = confinement_error or (
                f"Landlock negative open/read probe unexpectedly succeeded: {path}"
            )
    if quiescence["prlimit_zero_applied"] is not True:
        confinement_error = confinement_error or (
            "kernel denied RLIMIT_NPROC freeze for a dedicated-UID process"
        )
    if quiescence["quiescent_after"] is not True:
        confinement_error = confinement_error or "dedicated UID is not quiescent"
    if supervisor_error is not None:
        confinement_error = confinement_error or supervisor_error
    os.chown(log_path, 0, 0)
    os.chmod(log_path, 0o400)
    return ConfinedResult(
        argv=tuple(argv),
        started_at=started_at,
        ended_at=_utcnow(),
        exit_code=exit_code,
        timed_out=timed_out,
        solver_stopped=solver_stopped,
        descendants_stopped=descendants_stopped,
        probes=probes,
        dedicated_uid_quiescence=quiescence,
        confinement_error=confinement_error,
        connected_fd_injection_count=connected_fd_injection_count,
        seccomp_supervisor_fail_closed=(
            supervisor_error is None and seccomp_supervisor_stopped
        ),
        seccomp_supervisor_stopped=seccomp_supervisor_stopped,
    )


def _minimal_environment(
    *,
    home: Path,
    temporary: Path,
    runtime_root: Path,
    credential_values: Mapping[str, str] | None = None,
) -> dict[str, str]:
    environment = {
        "HOME": str(home),
        "TMPDIR": str(temporary),
        "TMP": str(temporary),
        "TEMP": str(temporary),
        "XDG_CACHE_HOME": str(home / ".cache"),
        "XDG_CONFIG_HOME": str(home / ".config"),
        "CODEX_HOME": str(home / ".codex"),
        "CLAUDE_CONFIG_DIR": str(home / ".claude"),
        "PATH": (
            f"{runtime_root}/bin:{runtime_root}/lean-v4.31.0/bin:"
            f"{runtime_root}/venv/bin"
        ),
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
        "TZ": "UTC",
        "SSL_CERT_FILE": "/etc/ssl/certs/ca-certificates.crt",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_CONFIG_GLOBAL": "/dev/null",
        "GIT_DISCOVERY_ACROSS_FILESYSTEM": "0",
        "PYTHONDONTWRITEBYTECODE": "1",
        "PYTHONNOUSERSITE": "1",
        "PYTHONHASHSEED": "0",
    }
    if credential_values:
        environment.update(credential_values)
    return environment


def _load_credentials(path: Path | None, *, variant: str) -> dict[str, str]:
    """Load only public loopback-broker coordinates and dummy credentials.

    Real provider keys must remain in a controller-side proxy process under a
    different UID.  Any process able to elaborate solver-written Lean can read
    its own environment, so passing real keys here would invalidate the blind
    boundary regardless of wrapper-level scrubbing.
    """

    if path is None:
        _fail("a root-owned loopback model-broker environment is mandatory")
    source = _plain_file(path, label="model broker environment file")
    metadata = source.stat()
    if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) & 0o077:
        _fail("credential environment file must be root-owned mode 0600")
    allowed = (
        {"ANTHROPIC_AUTH_TOKEN", "ANTHROPIC_API_KEY", "ANTHROPIC_BASE_URL"}
        if variant == "kimi-k3"
        else {
            "ANSWER_BLIND_MODEL_BASE_URL",
            "ANSWER_BLIND_MODEL_DUMMY_KEY",
        }
    )
    result: dict[str, str] = {}
    for number, raw_line in enumerate(source.read_text(encoding="utf-8").splitlines(), 1):
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("export "):
            line = line[len("export ") :]
        name, separator, value = line.partition("=")
        name = name.strip()
        if not separator or name not in allowed or not value:
            _fail(f"unsupported credential entry on line {number}")
        if name in result:
            _fail(f"duplicate credential entry: {name}")
        result[name] = value.strip().strip("'\"")
    from urllib.parse import urlparse

    base_key = (
        "ANTHROPIC_BASE_URL"
        if variant == "kimi-k3"
        else "ANSWER_BLIND_MODEL_BASE_URL"
    )
    secret_keys = (
        ("ANTHROPIC_AUTH_TOKEN", "ANTHROPIC_API_KEY")
        if variant == "kimi-k3"
        else ("ANSWER_BLIND_MODEL_DUMMY_KEY",)
    )
    parsed = urlparse(result.get(base_key, ""))
    if parsed.scheme not in {"http", "https"} or parsed.hostname not in {
        "127.0.0.1", "::1", "localhost"
    } or parsed.username or parsed.password:
        _fail("model broker base URL must be an explicit loopback HTTP(S) URL")
    if len([key for key in secret_keys if result.get(key)]) != 1:
        _fail("model broker environment needs exactly one dummy credential")
    dummy = next(result[key] for key in secret_keys if result.get(key))
    if dummy != "answer-blind-public-dummy-token":
        _fail("solver credential must be the fixed public model-broker dummy token")
    return result


def _validate_model_broker_receipt(
    path: Path | None, *, variant: str, run_id: str, model: str,
    broker_environment: Mapping[str, str],
    runtime_files: Mapping[str, str],
    request_profile: str = "agent_harness_v1",
) -> str:
    if path is None:
        _fail("a root-owned model broker receipt is mandatory")
    receipt_path = _plain_file(path, label="model broker receipt")
    metadata = receipt_path.stat()
    if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) & 0o077:
        _fail("model broker receipt must be root-owned mode 0400")
    receipt = _load_json(receipt_path, label="model broker receipt")
    fields = {
        "schema_version", "protocol", "phase", "variant", "run_id",
        "listen_url", "upstream_origin", "allowed_model",
        "public_dummy_key_sha256", "broker_uid", "broker_binary_sha256",
        "request_profile", "started_at",
    }
    if set(receipt) != fields:
        _fail("model broker receipt has invalid fields")
    # Claude Code accepts the long-context selector kimi-k3[1m] in the sealed
    # workspace config, but normalizes its provider request to kimi-k3.
    # Structured controller calls send their configured model id unchanged.
    broker_model = (
        "kimi-k3"
        if variant == "kimi-k3" and request_profile == "agent_harness_v1"
        else model
    )
    if (
        receipt.get("schema_version") != SCHEMA_VERSION
        or receipt.get("protocol") != PROTOCOL
        or receipt.get("phase") != "model_broker_ready"
        or receipt.get("variant") != variant
        or receipt.get("run_id") != run_id
        or receipt.get("allowed_model") != broker_model
        or receipt.get("request_profile") != request_profile
    ):
        _fail("model broker receipt provenance mismatch")
    base_key = (
        "ANTHROPIC_BASE_URL"
        if variant == "kimi-k3"
        else "ANSWER_BLIND_MODEL_BASE_URL"
    )
    if receipt.get("listen_url") != broker_environment.get(base_key):
        _fail("model broker URL differs from the solver's loopback URL")
    dummy_sha = _sha256_bytes(b"answer-blind-public-dummy-token")
    if receipt.get("public_dummy_key_sha256") != dummy_sha:
        _fail("model broker public dummy token binding is invalid")
    for field in ("broker_binary_sha256",):
        if not isinstance(receipt.get(field), str) or SHA256.fullmatch(receipt[field]) is None:
            _fail(f"model broker receipt {field} is invalid")
    broker_uid = receipt.get("broker_uid")
    if not isinstance(broker_uid, int) or isinstance(broker_uid, bool) or broker_uid == 0:
        _fail("model broker must use a dedicated non-root UID")
    if not isinstance(receipt.get("upstream_origin"), str) or not receipt["upstream_origin"]:
        _fail("model broker upstream origin is missing")
    expected_origin = (
        "https://chatgpt.com"
        if variant == "gpt"
        else "https://api.moonshot.cn"
    )
    if receipt["upstream_origin"] != expected_origin:
        _fail("model broker upstream origin is not the pinned release endpoint")
    if receipt["broker_binary_sha256"] not in set(runtime_files.values()):
        _fail("model broker binary is not present in the sealed runtime inventory")
    if not isinstance(receipt.get("started_at"), str) or not receipt["started_at"]:
        _fail("model broker started_at is missing")
    return _sha256_file(receipt_path)


def _probe_model_broker(receipt_path: Path, *, expected_sha256: str) -> None:
    """Prove the hash-bound loopback listener is live without sending a prompt."""

    if _sha256_file(receipt_path) != expected_sha256:
        _fail("model broker ready receipt drifted before health check")
    receipt = _load_json(receipt_path, label="model broker receipt")
    parsed = urlparse(str(receipt.get("listen_url") or ""))
    if parsed.hostname not in {"127.0.0.1", "::1", "localhost"} or parsed.port is None:
        _fail("model broker receipt has no explicit loopback port")
    connection_type = (
        http.client.HTTPSConnection if parsed.scheme == "https"
        else http.client.HTTPConnection
    )
    connection = connection_type(parsed.hostname, parsed.port, timeout=2)
    try:
        connection.request(
            "GET", "/__answer_blind_health",
            headers={"Authorization": "Bearer answer-blind-public-dummy-token"},
        )
        response = connection.getresponse()
        payload = response.read(64 * 1024)
        if response.status != 200:
            _fail(f"model broker health endpoint returned HTTP {response.status}")
        health = json.loads(payload)
    except (OSError, http.client.HTTPException, json.JSONDecodeError) as exc:
        raise ControllerError("hash-bound model broker health check failed") from exc
    finally:
        connection.close()
    expected_health = {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        "phase": "model_broker_health",
        "variant": receipt.get("variant"),
        "run_id": receipt.get("run_id"),
        "allowed_model": receipt.get("allowed_model"),
        "broker_binary_sha256": receipt.get("broker_binary_sha256"),
    }
    if health != expected_health:
        _fail("model broker health identity differs from its ready receipt")
    if _sha256_file(receipt_path) != expected_sha256:
        _fail("model broker ready receipt drifted during health check")


def _validate_model_broker_transcript(
    path: Path | str, *, variant: str, run_id: str, ready_sha256: str,
) -> str:
    transcript_path = _plain_file(path, label="model broker transcript")
    metadata = transcript_path.stat()
    if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) != 0o400:
        _fail("model broker transcript must be root-owned mode 0400")
    value = _load_json(transcript_path, label="model broker transcript")
    expected = {
        "schema_version", "protocol", "phase", "variant", "run_id",
        "ready_receipt_sha256", "request_count",
        "request_response_chain_sha256", "started_at", "stopped_at",
        "broker_stopped",
    }
    if set(value) != expected:
        _fail("model broker transcript has invalid fields")
    if (
        value.get("schema_version") != SCHEMA_VERSION
        or value.get("protocol") != PROTOCOL
        or value.get("phase") != "model_broker_transcript"
        or value.get("variant") != variant
        or value.get("run_id") != run_id
        or value.get("ready_receipt_sha256") != ready_sha256
        or value.get("broker_stopped") is not True
    ):
        _fail("model broker transcript provenance/stopped attestation mismatch")
    count = value.get("request_count")
    if not isinstance(count, int) or isinstance(count, bool) or count < 1:
        _fail("model broker transcript must attest at least one request")
    if not isinstance(value.get("request_response_chain_sha256"), str) or SHA256.fullmatch(
        value["request_response_chain_sha256"]
    ) is None:
        _fail("model broker transcript chain digest is invalid")
    for field in ("started_at", "stopped_at"):
        if not isinstance(value.get(field), str) or not value[field]:
            _fail(f"model broker transcript {field} is invalid")
    return _sha256_file(transcript_path)


def _validate_variant_config(workspace: Path, *, variant: str) -> tuple[str, str]:
    family, model, runner = VARIANT_MODELS[variant]
    config = _load_json(workspace / ".archon/config.json", label="Archon config")
    blind = config.get("answer_blind")
    loop = config.get("loop")
    harnesses = config.get("harnesses")
    if not isinstance(blind, dict) or not isinstance(loop, dict) or not isinstance(harnesses, dict):
        _fail("Archon config is missing answer-blind loop/harness sections")
    if (
        blind.get("protocol") != PROTOCOL
        or blind.get("official_answer_seen") is not False
        or blind.get("authority") != "problem-only"
    ):
        _fail("Archon config is not pinned to problem-only answer-blind mode")
    harness_name = loop.get("harness")
    descriptor = harnesses.get(harness_name)
    if (
        loop.get("model") != model
        or not isinstance(descriptor, dict)
        or descriptor.get("model") != model
        or descriptor.get("runner") != runner
    ):
        _fail("Archon config variant/model/runner provenance mismatch")
    if variant == "gpt" and descriptor.get("lean_lsp_mcp_bin") != "lean-lsp-mcp-trusted":
        _fail("GPT must use the trusted Lean MCP launcher; uv fallback is forbidden")
    mcp = _load_json(workspace / ".mcp.json", label="MCP config")
    lean_lsp = mcp.get("mcpServers", {}).get("lean-lsp")
    if not isinstance(lean_lsp, dict) or lean_lsp.get("command") != "lean-lsp-mcp-trusted":
        _fail("workspace MCP config must use the trusted Lean MCP launcher")
    return family, model


def _atomic_new_controller_file(path: Path, payload: bytes, *, mode: int) -> None:
    if path.exists() or path.is_symlink():
        _fail(f"controller artifact must be new: {path}")
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, mode)
    try:
        with os.fdopen(descriptor, "wb", closefd=False) as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
    finally:
        os.close(descriptor)
    os.chown(path, 0, 0)
    os.chmod(path, mode)


def _controller_dir(raw: Path | str) -> Path:
    root = _plain_directory(raw, label="controller receipt directory")
    metadata = root.stat()
    if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) & 0o077:
        _fail("controller receipt directory must be root-owned mode 0700")
    return root


def _launch_authorization_path(controller: Path, *, variant: str) -> Path:
    return controller / f"{variant}-landlock-launch-authorization.json"


def _load_or_create_launch_authorization(
    *, controller: Path, variant: str, run_id: str, workspace: Path,
    runtime: Path, dependency: Path, home: Path, temporary: Path,
    sibling: Path, allowed_model_broker_tcp_port: int,
    verifier_external_rw: Sequence[Path] = (),
    reviewer_external_rw: Sequence[Path] = (),
) -> tuple[dict[str, Any], str]:
    system_paths, system_files = _system_readonly_inventory(runtime)
    devices = _existing_paths(Path(raw) for raw in SYSTEM_DEVICE_FILES)
    required_probes = _existing_paths(
        [
            Path("/root"), Path("/tmp"), Path("/var/tmp"), Path("/dev/shm"),
            Path("/dev/tty"),
            Path("/proc/1/environ"),
            controller, sibling,
        ]
    )
    authorization = {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        "phase": "landlock_launch_authorization",
        "variant": variant,
        "run_id": run_id,
        "workspace": str(workspace),
        "runtime_root": str(runtime),
        "dependency_root": str(dependency),
        "system_inventory": {
            "files": system_files,
            "files_sha256": _hash_index(system_files),
        },
        "system_read_only_paths": [
            *(str(path) for path in system_paths),
            *(str(path) for path in devices),
        ],
        "solver_external_read_write_paths": [str(home), str(temporary)],
        "verifier_external_read_write_paths": [
            str(path.resolve()) for path in verifier_external_rw
        ],
        "reviewer_external_read_write_paths": [
            str(path.resolve()) for path in reviewer_external_rw
        ],
        "required_denied_probe_paths": [str(path) for path in required_probes],
        "allowed_model_broker_tcp_port": allowed_model_broker_tcp_port,
    }
    if set(authorization) != LAUNCH_AUTHORIZATION_FIELDS:
        _fail("internal Landlock launch authorization schema drift")
    path = _launch_authorization_path(controller, variant=variant)
    expected_payload = _pretty_json_bytes(authorization)
    if path.exists():
        metadata = path.stat()
        if (
            path.is_symlink()
            or not path.is_file()
            or metadata.st_uid != 0
            or stat.S_IMODE(metadata.st_mode) & 0o077
            or path.read_bytes() != expected_payload
        ):
            _fail("existing Landlock launch authorization drift")
    else:
        _atomic_new_controller_file(path, expected_payload, mode=0o400)
    return authorization, _sha256_file(path)


def _authorized_probe_paths(authorization: Mapping[str, Any]) -> tuple[Path, ...]:
    raw = authorization.get("required_denied_probe_paths")
    if not isinstance(raw, list) or not raw:
        _fail("Landlock launch authorization has no required deny probes")
    paths: list[Path] = []
    for item in raw:
        if not isinstance(item, str) or not Path(item).is_absolute():
            _fail("Landlock authorized deny probe must be an absolute path")
        paths.append(Path(item))
    return tuple(paths)


def _prepare_verifier_directories(
    *, controller: Path, variant: str, identity: SolverIdentity,
) -> tuple[Path, Path, Path]:
    paths = _default_verifier_paths(controller, variant=variant)
    for path in paths:
        if path.is_symlink() or (path.exists() and not path.is_dir()):
            _fail(f"verifier private path is unsafe: {path}")
        if not path.exists():
            path.mkdir(mode=0o700)
            os.chown(path, identity.uid, identity.gid)
        metadata = path.stat()
        if (
            metadata.st_uid != identity.uid
            or metadata.st_gid != identity.gid
            or stat.S_IMODE(metadata.st_mode) != 0o700
        ):
            _fail(f"verifier private path ownership/mode drift: {path}")
        if any(path.iterdir()):
            _fail(f"verifier private path must be fresh/empty before launch: {path}")
    return paths


def _prepare_private_directories(
    *, paths: Sequence[Path], identity: SolverIdentity, label: str,
) -> tuple[Path, ...]:
    for path in paths:
        if path.is_symlink() or (path.exists() and not path.is_dir()):
            _fail(f"{label} private path is unsafe: {path}")
        if not path.exists():
            path.mkdir(mode=0o700)
            os.chown(path, identity.uid, identity.gid)
        metadata = path.stat()
        if (
            metadata.st_uid != identity.uid
            or metadata.st_gid != identity.gid
            or stat.S_IMODE(metadata.st_mode) != 0o700
        ):
            _fail(f"{label} private path ownership/mode drift: {path}")
        if any(path.iterdir()):
            _fail(f"{label} private path must be fresh/empty before launch: {path}")
    return tuple(paths)


def _receipt_paths(controller: Path, *, variant: str, invocation: int) -> tuple[Path, Path, Path]:
    receipt = controller / f"{variant}-iteration-{invocation:04d}.json"
    aggregate = controller / f"{variant}-invocations.json"
    ledger = controller / f"{variant}-invocations.jsonl"
    return receipt, aggregate, ledger


def _read_aggregate(path: Path, *, variant: str, run_id: str) -> dict[str, Any] | None:
    if not path.exists():
        return None
    aggregate = _load_json(path, label="solver invocation aggregate")
    if (
        aggregate.get("schema_version") != SCHEMA_VERSION
        or aggregate.get("protocol") != PROTOCOL
        or aggregate.get("phase") != AGGREGATE_PHASE
        or aggregate.get("variant") != variant
        or aggregate.get("run_id") != run_id
    ):
        _fail("existing solver invocation aggregate does not match this run")
    return aggregate


def _chain_sha256(receipt_without_chain: Mapping[str, Any], previous_chain: str | None) -> str:
    core_sha = _sha256_bytes(_canonical_json_bytes(dict(receipt_without_chain)))
    return _sha256_bytes(
        _canonical_json_bytes(
            {
                "previous_chain_sha256": previous_chain,
                "receipt_core_sha256": core_sha,
            }
        )
    )


def _validate_prior_receipt_chain(
    *, aggregate: Mapping[str, Any], controller: Path,
    variant: str, family: str, model: str, run_id: str,
    identity: SolverIdentity, dependency_digest: str, runtime_digest: str,
    authorization_sha: str,
    broker_receipt_sha: str,
) -> list[dict[str, str]]:
    """Recompute every root-side receipt before extending the chain."""

    expected_fields = {
        "schema_version", "protocol", "phase", "variant", "model_family",
        "model_id", "run_id", "uid", "invocation_count", "receipts",
        "chain_sha256", "all_exit_zero", "all_protected_unchanged",
        "all_stopped", "all_uid_quiescent",
        "filesystem_answer_blind", "network_answer_blind",
        "dependency_inventory_sha256", "runtime_inventory_sha256",
        "launch_authorization_sha256",
        "model_broker_receipt_sha256",
    }
    if set(aggregate) != expected_fields:
        _fail("existing solver invocation aggregate has invalid fields")
    if (
        aggregate.get("variant") != variant
        or aggregate.get("model_family") != family
        or aggregate.get("model_id") != model
        or aggregate.get("run_id") != run_id
        or aggregate.get("uid") != identity.uid
        or aggregate.get("dependency_inventory_sha256") != dependency_digest
        or aggregate.get("runtime_inventory_sha256") != runtime_digest
        or aggregate.get("launch_authorization_sha256") != authorization_sha
        or aggregate.get("model_broker_receipt_sha256") != broker_receipt_sha
        or aggregate.get("filesystem_answer_blind") is not True
        or aggregate.get("network_answer_blind") is not False
    ):
        _fail("existing solver invocation aggregate provenance drift")
    raw_specs = aggregate.get("receipts")
    if (
        not isinstance(raw_specs, list)
        or not raw_specs
        or aggregate.get("invocation_count") != len(raw_specs)
    ):
        _fail("existing solver invocation aggregate count is invalid")
    specs: list[dict[str, str]] = []
    previous_receipt_sha: str | None = None
    previous_chain: str | None = None
    for invocation, raw_spec in enumerate(raw_specs, start=1):
        if not isinstance(raw_spec, dict) or set(raw_spec) != {"path", "sha256"}:
            _fail("existing invocation receipt locator is invalid")
        raw_path = raw_spec.get("path")
        raw_sha = raw_spec.get("sha256")
        if not isinstance(raw_path, str) or not Path(raw_path).is_absolute():
            _fail("existing invocation receipt path must be absolute")
        path = _plain_file(Path(raw_path), label="existing invocation receipt")
        if path.parent != controller:
            _fail("existing invocation receipt is outside controller directory")
        metadata = path.stat()
        if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) & 0o077:
            _fail("existing invocation receipt is not root-only")
        payload = path.read_bytes()
        if not isinstance(raw_sha, str) or _sha256_bytes(payload) != raw_sha:
            _fail("existing invocation receipt hash drift")
        try:
            receipt = json.loads(payload)
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise ControllerError("existing invocation receipt is invalid JSON") from exc
        if not isinstance(receipt, dict):
            _fail("existing invocation receipt must be a JSON object")
        if (
            receipt.get("schema_version") != SCHEMA_VERSION
            or receipt.get("protocol") != PROTOCOL
            or receipt.get("phase") != INVOCATION_PHASE
            or receipt.get("variant") != variant
            or receipt.get("model_family") != family
            or receipt.get("model_id") != model
            or receipt.get("run_id") != run_id
            or receipt.get("uid") != identity.uid
            or receipt.get("invocation") != invocation
            or receipt.get("previous_receipt_sha256") != previous_receipt_sha
            or receipt.get("dependency_inventory_sha256") != dependency_digest
            or receipt.get("runtime_inventory_sha256") != runtime_digest
            or receipt.get("launch_authorization_sha256") != authorization_sha
            or receipt.get("model_broker_receipt_sha256") != broker_receipt_sha
        ):
            _fail("existing invocation receipt provenance drift")
        without_chain = dict(receipt)
        claimed_chain = without_chain.pop("chain_sha256", None)
        if claimed_chain != _chain_sha256(without_chain, previous_chain):
            _fail("existing invocation receipt chain drift")
        quiescence = receipt.get("dedicated_uid_quiescence")
        if (
            not isinstance(quiescence, dict)
            or quiescence.get("quiescent_before") is not True
            or quiescence.get("quiescent_after") is not True
            or quiescence.get("before_pids") != []
            or quiescence.get("after_pids") != []
        ):
            _fail("existing invocation receipt lacks UID quiescence")
        previous_receipt_sha = raw_sha
        previous_chain = claimed_chain
        specs.append({"path": str(path), "sha256": raw_sha})
    if aggregate.get("chain_sha256") != previous_chain:
        _fail("existing aggregate final chain drift")
    return specs


def _replace_controller_json(path: Path, payload: bytes) -> None:
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    if temporary.exists() or temporary.is_symlink():
        _fail(f"unsafe controller temporary path: {temporary}")
    _atomic_new_controller_file(temporary, payload, mode=0o400)
    os.replace(temporary, path)
    os.chown(path, 0, 0)
    os.chmod(path, 0o400)


def _append_ledger(path: Path, row: Mapping[str, Any]) -> None:
    flags = os.O_WRONLY | os.O_CREAT | os.O_APPEND | os.O_CLOEXEC
    descriptor = os.open(path, flags, 0o600)
    try:
        metadata = os.fstat(descriptor)
        if metadata.st_uid != 0:
            _fail("invocation ledger is not root-owned")
        os.write(descriptor, _canonical_json_bytes(dict(row)))
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    os.chown(path, 0, 0)
    os.chmod(path, 0o400)


def run_solver_iteration(
    *,
    workspace: Path | str,
    variant: str,
    solver_user: str,
    runtime_root: Path | str,
    dependency_root: Path | str,
    private_home: Path | str,
    private_tmp: Path | str,
    controller_receipts: Path | str,
    run_id: str,
    timeout_s: int,
    sibling_workspace: Path | str | None = None,
    credential_env_file: Path | None = None,
    verifier_user: str,
    reviewer_user: str,
    model_broker_receipt: Path | None = None,
) -> dict[str, Any]:
    """Launch exactly one Archon iteration and append its controller chain."""

    _fail(
        "legacy arbitrary-shell solver execution is permanently disabled; "
        "use run_answer_blind_structured_solver.py"
    )
    _require_root()
    if variant not in VARIANT_MODELS:
        _fail(f"unsupported solver variant: {variant}")
    if SAFE_RUN_ID.fullmatch(run_id) is None:
        _fail("run_id contains unsafe characters")
    identity = _identity(solver_user)
    verifier_identity = _identity(verifier_user)
    reviewer_identity = _identity(reviewer_user)
    if len({identity.uid, verifier_identity.uid, reviewer_identity.uid}) != 3:
        _fail("solver, verifier, and reviewer must use distinct dedicated UIDs")
    project = _plain_directory(workspace, label="solver workspace")
    runtime = _plain_directory(runtime_root, label="answer-blind runtime")
    dependency = _plain_directory(dependency_root, label="Lean dependency tree")
    home = _plain_directory(private_home, label="private solver home")
    temporary = _plain_directory(private_tmp, label="private solver tmp")
    controller = _controller_dir(controller_receipts)
    finalized_marker = controller / f"{variant}-finalized.json"
    if finalized_marker.exists() or finalized_marker.is_symlink():
        _fail("run is finalized and may not be resumed or requeued")
    sibling = (
        _plain_directory(sibling_workspace, label="sibling solver workspace")
        if sibling_workspace is not None
        else None
    )
    boundary_paths = {
        "solver workspace": project,
        "private solver home": home,
        "private solver tmp": temporary,
        "controller receipts": controller,
    }
    if sibling is not None:
        boundary_paths["sibling solver workspace"] = sibling
    _assert_pairwise_disjoint(boundary_paths)
    for private_label, private in (
        ("private solver home", home),
        ("private solver tmp", temporary),
    ):
        for protected_label, protected in (
            ("answer-blind runtime", runtime),
            ("Lean dependency tree", dependency),
        ):
            if _inside(private, protected) or _inside(protected, private):
                _fail(f"{private_label} overlaps {protected_label}")
    if _inside(project, runtime) or _inside(runtime, project):
        _fail("workspace must be disjoint from runtime")
    if sibling is None:
        _fail("sibling workspace is mandatory for two-variant isolation")
    _validate_private_directory(
        home,
        identity=identity,
        label="private solver home",
        run_id=run_id,
        variant=variant,
        allow_credentials=True,
    )
    _validate_private_directory(
        temporary,
        identity=identity,
        label="private solver tmp",
        run_id=run_id,
        variant=variant,
        allow_credentials=False,
    )
    _assert_controller_tree(runtime, label="answer-blind runtime")
    _assert_controller_tree(dependency, label="Lean dependency tree")
    family, model = _validate_variant_config(project, variant=variant)

    # Ownership and protected hashes are checked before any model process is
    # created.  The same bytes are checked again after every descendant dies.
    protected_before = _protected_receipt(project, solver_gid=identity.gid)
    dependency_files = _inventory_tree(dependency)
    dependency_digest = _hash_index(dependency_files)
    runtime_files = _inventory_tree(runtime, exclude_roots=(dependency,))
    runtime_digest = _hash_index(runtime_files)
    verifier_paths = _prepare_verifier_directories(
        controller=controller, variant=variant, identity=verifier_identity
    )
    reviewer_paths = _prepare_private_directories(
        paths=_default_reviewer_paths(controller, variant=variant),
        identity=reviewer_identity,
        label="reviewer",
    )
    credentials = _load_credentials(credential_env_file, variant=variant)
    broker_receipt_sha = _validate_model_broker_receipt(
        model_broker_receipt,
        variant=variant,
        run_id=run_id,
        model=model,
        broker_environment=credentials,
        runtime_files=runtime_files,
        request_profile="agent_harness_v1",
    )
    broker_receipt_path = _plain_file(
        model_broker_receipt, label="model broker receipt"
    )
    broker_ready = _load_json(broker_receipt_path, label="model broker receipt")
    if broker_ready.get("broker_uid") in {
        identity.uid, verifier_identity.uid, reviewer_identity.uid,
    }:
        _fail("broker, solver, verifier, and reviewer must use distinct UIDs")
    broker_port = urlparse(
        str(broker_ready["listen_url"])
    ).port
    if broker_port is None:
        _fail("model broker ready receipt has no TCP port")
    authorization, authorization_sha = _load_or_create_launch_authorization(
        controller=controller,
        variant=variant,
        run_id=run_id,
        workspace=project,
        runtime=runtime,
        dependency=dependency,
        home=home,
        temporary=temporary,
        sibling=sibling,
        allowed_model_broker_tcp_port=broker_port,
        verifier_external_rw=verifier_paths,
        reviewer_external_rw=reviewer_paths,
    )
    _probe_model_broker(broker_receipt_path, expected_sha256=broker_receipt_sha)

    aggregate_path = controller / f"{variant}-invocations.json"
    prior = _read_aggregate(aggregate_path, variant=variant, run_id=run_id)
    receipts = (
        _validate_prior_receipt_chain(
            aggregate=prior,
            controller=controller,
            variant=variant,
            family=family,
            model=model,
            run_id=run_id,
            identity=identity,
            dependency_digest=dependency_digest,
            runtime_digest=runtime_digest,
            authorization_sha=authorization_sha,
            broker_receipt_sha=broker_receipt_sha,
        )
        if prior
        else []
    )
    invocation = len(receipts) + 1
    previous_receipt_sha256 = receipts[-1]["sha256"] if receipts else None
    previous_chain = prior.get("chain_sha256") if prior else None
    receipt_path, aggregate_path, ledger_path = _receipt_paths(
        controller, variant=variant, invocation=invocation
    )
    log_path = controller / f"{variant}-iteration-{invocation:04d}.log"

    policy = build_landlock_policy(
        workspace=project,
        runtime_root=runtime,
        dependency_root=dependency,
        private_home=home,
        private_tmp=temporary,
        controller_dir=controller,
        sibling_workspace=sibling,
        required_probe_paths=_authorized_probe_paths(authorization),
        allowed_connect_tcp_ports=(broker_port,),
    )
    # A brokered run never consults native provider login material.  The
    # credential-free HOME is still writable for ordinary CLI caches/state.
    for native_auth in (home / ".codex/auth.json", home / ".claude/.credentials.json"):
        if native_auth.exists() or native_auth.is_symlink():
            _fail(f"native model credential file is forbidden: {native_auth}")
    environment = _minimal_environment(
        home=home,
        temporary=temporary,
        runtime_root=runtime,
        credential_values=credentials,
    )
    environment["ANSWER_BLIND_MCP_RUNTIME_ROOT"] = str(runtime)
    environment["ANSWER_BLIND_MCP_DEPENDENCY_ROOT"] = str(dependency)
    environment["ANSWER_BLIND_MCP_WORKSPACE"] = str(project)
    archon = _plain_file(runtime / "bin/archon", label="trusted Archon", executable=True)
    argv = (
        str(archon),
        "loop",
        ".",
        "--max-iterations",
        "1",
        "--no-dashboard",
        "--model",
        model,
    )
    outcome = run_confined_command(
        argv=argv,
        cwd=project,
        environment=environment,
        identity=identity,
        policy=policy,
        log_path=log_path,
        timeout_s=timeout_s,
    )
    _probe_model_broker(broker_receipt_path, expected_sha256=broker_receipt_sha)

    protected_after = _protected_receipt(project, solver_gid=identity.gid)
    protected_unchanged = protected_before == protected_after
    # Root-only trees should be invariant too.  Re-inventorying catches host
    # drift and configuration mistakes even though the solver cannot write
    # these paths under Unix permissions or Landlock.
    dependency_after = _hash_index(_inventory_tree(dependency))
    runtime_after = _hash_index(_inventory_tree(runtime, exclude_roots=(dependency,)))
    broker_receipt_after = _sha256_file(broker_receipt_path)
    if (
        dependency_after != dependency_digest
        or runtime_after != runtime_digest
        or broker_receipt_after != broker_receipt_sha
    ):
        protected_unchanged = False
    effective_exit_code = 126 if outcome.confinement_error else outcome.exit_code

    receipt: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        "phase": INVOCATION_PHASE,
        "receipt_type": "trusted-controller-one-iteration",
        "variant": variant,
        "model_family": family,
        "model_id": model,
        "run_id": run_id,
        "invocation": invocation,
        "uid": identity.uid,
        "gid": identity.gid,
        "user": identity.user,
        "command_argv": list(argv),
        "started_at": outcome.started_at,
        "ended_at": outcome.ended_at,
        "exit_code": effective_exit_code,
        "solver_stopped": outcome.solver_stopped,
        "descendants_stopped": outcome.descendants_stopped,
        "isolation": {
            "filesystem_answer_blind": True,
            "network_answer_blind": False,
        },
        "protected_before": protected_before,
        "protected_after": protected_after,
        "protected_unchanged": protected_unchanged,
        "dependency_inventory_sha256": dependency_digest,
        "runtime_inventory_sha256": runtime_digest,
        "launch_authorization_sha256": authorization_sha,
        "model_broker_receipt_sha256": broker_receipt_sha,
        "isolation_probes": outcome.probes,
        "landlock": policy.receipt(
            connected_fd_injection_count=outcome.connected_fd_injection_count,
            seccomp_supervisor_fail_closed=outcome.seccomp_supervisor_fail_closed,
            seccomp_supervisor_stopped=outcome.seccomp_supervisor_stopped,
        ),
        "stdout_log": {
            "path": str(log_path),
            "sha256": _sha256_file(log_path),
            "size": log_path.stat().st_size,
        },
        "dedicated_uid_quiescence": outcome.dedicated_uid_quiescence,
        "previous_receipt_sha256": previous_receipt_sha256,
    }
    receipt["chain_sha256"] = _chain_sha256(receipt, previous_chain)
    receipt_payload = _pretty_json_bytes(receipt)
    receipt_sha = _sha256_bytes(receipt_payload)
    _atomic_new_controller_file(receipt_path, receipt_payload, mode=0o400)
    _atomic_new_controller_file(
        Path(str(receipt_path) + ".sha256"),
        f"{receipt_sha}  {receipt_path.name}\n".encode("ascii"),
        mode=0o400,
    )
    receipts.append({"path": str(receipt_path), "sha256": receipt_sha})
    aggregate = {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        "phase": AGGREGATE_PHASE,
        "variant": variant,
        "model_family": family,
        "model_id": model,
        "run_id": run_id,
        "uid": identity.uid,
        "invocation_count": len(receipts),
        "receipts": receipts,
        "chain_sha256": receipt["chain_sha256"],
        "all_exit_zero": bool(prior.get("all_exit_zero", True) if prior else True)
        and effective_exit_code == 0,
        "all_protected_unchanged": bool(
            prior.get("all_protected_unchanged", True) if prior else True
        )
        and protected_unchanged,
        "all_stopped": bool(prior.get("all_stopped", True) if prior else True)
        and outcome.solver_stopped
        and outcome.descendants_stopped,
        "all_uid_quiescent": bool(
            prior.get("all_uid_quiescent", True) if prior else True
        )
        and outcome.dedicated_uid_quiescence["quiescent_before"]
        and outcome.dedicated_uid_quiescence["quiescent_after"]
        and outcome.dedicated_uid_quiescence["prlimit_zero_applied"],
        "dependency_inventory_sha256": dependency_digest,
        "runtime_inventory_sha256": runtime_digest,
        "launch_authorization_sha256": authorization_sha,
        "model_broker_receipt_sha256": broker_receipt_sha,
        "filesystem_answer_blind": True,
        "network_answer_blind": False,
    }
    _replace_controller_json(aggregate_path, _pretty_json_bytes(aggregate))
    _append_ledger(
        ledger_path,
        {
            "invocation": invocation,
            "path": str(receipt_path),
            "sha256": receipt_sha,
            "previous_receipt_sha256": previous_receipt_sha256,
            "chain_sha256": receipt["chain_sha256"],
        },
    )
    if (
        effective_exit_code != 0
        or outcome.confinement_error is not None
        or outcome.timed_out
        or not outcome.solver_stopped
        or not outcome.descendants_stopped
        or not outcome.dedicated_uid_quiescence["quiescent_after"]
        or not outcome.dedicated_uid_quiescence["prlimit_zero_applied"]
        or not protected_unchanged
    ):
        _fail(
            f"solver iteration failed closed; inspect controller receipt {receipt_path}"
        )
    return aggregate


def run_landlock_version_probe(
    *,
    executable: Path | str,
    workspace: Path | str,
    runtime_root: Path | str,
    dependency_root: Path | str,
    private_home: Path | str,
    private_tmp: Path | str,
    controller_dir: Path | str,
    user: str,
    log_name: str,
) -> ConfinedResult:
    """Controller diagnostic used to validate Codex/Claude in the jail."""

    _require_root()
    identity = _identity(user)
    project = _plain_directory(workspace, label="probe workspace")
    runtime = _plain_directory(runtime_root, label="probe runtime")
    dependency = _plain_directory(dependency_root, label="probe dependency tree")
    home = _plain_directory(private_home, label="probe home")
    temporary = _plain_directory(private_tmp, label="probe tmp")
    controller = _controller_dir(controller_dir)
    binary = _plain_file(executable, label="probe executable", executable=True)
    if not _inside(binary, runtime):
        _fail("version probe executable must be inside the trusted runtime")
    policy = build_landlock_policy(
        workspace=project,
        runtime_root=runtime,
        dependency_root=dependency,
        private_home=home,
        private_tmp=temporary,
        controller_dir=controller,
    )
    return run_confined_command(
        argv=(str(binary), "--version"),
        cwd=project,
        environment=_minimal_environment(
            home=home, temporary=temporary, runtime_root=runtime
        ),
        identity=identity,
        policy=policy,
        log_path=controller / log_name,
        timeout_s=60,
    )


def run_verifier(
    *,
    project: Path | str,
    candidate_dir: str,
    output: Path | str,
    controller_receipt: Path | str,
    verifier_user: str,
    runtime_root: Path | str,
    dependency_root: Path | str,
    private_home: Path | str,
    private_tmp: Path | str,
    expected_dependency_inventory_sha256: str,
    expected_runtime_inventory_sha256: str,
    expected_snapshot_inventory_sha256: str,
    expected_launch_authorization_sha256: str,
    variant: str,
    run_id: str,
    scope_ids: Sequence[str],
    timeout_s: int,
) -> dict[str, Any]:
    """Run the non-root Lean verifier through the same Landlock boundary."""

    _require_root()
    identity = _identity(verifier_user)
    workspace = _plain_directory(project, label="frozen verifier project")
    runtime = _plain_directory(runtime_root, label="answer-blind runtime")
    dependency = _plain_directory(dependency_root, label="Lean dependency tree")
    home = _plain_directory(private_home, label="private verifier home")
    temporary = _plain_directory(private_tmp, label="private verifier tmp")
    receipt_path = Path(controller_receipt).resolve()
    receipt_parent = _controller_dir(receipt_path.parent)
    output_path = Path(output).resolve()
    if output_path.parent == receipt_parent:
        _fail("verifier output needs a dedicated non-root staging directory")
    output_parent = _plain_directory(output_path.parent, label="verifier output staging")
    if (home, temporary, output_parent) != _default_verifier_paths(
        receipt_parent, variant=variant
    ):
        _fail("verifier home/tmp/output do not match the pre-run authorization")
    output_metadata = output_parent.stat()
    if (
        output_metadata.st_uid != identity.uid
        or stat.S_IMODE(output_metadata.st_mode) & 0o077
    ):
        _fail("verifier output staging must be verifier-owned mode 0700")
    if output_path.exists() or output_path.is_symlink():
        _fail("verifier output receipt must be new")
    _assert_controller_tree(runtime, label="answer-blind runtime")
    _assert_controller_tree(dependency, label="Lean dependency tree")
    _assert_controller_tree(workspace, label="frozen verifier project")
    if any(
        SHA256.fullmatch(digest) is None
        for digest in (
            expected_dependency_inventory_sha256,
            expected_runtime_inventory_sha256,
            expected_snapshot_inventory_sha256,
            expected_launch_authorization_sha256,
        )
    ):
        _fail("verifier expected inventory hashes must be SHA-256 values")
    dependency_digest = _hash_index(_inventory_tree(dependency))
    runtime_digest = _hash_index(_inventory_tree(runtime, exclude_roots=(dependency,)))
    snapshot_digest = _hash_index(_inventory_tree(workspace, exclude_roots=(dependency,)))
    if dependency_digest != expected_dependency_inventory_sha256:
        _fail("verifier dependency inventory drift")
    if runtime_digest != expected_runtime_inventory_sha256:
        _fail("verifier runtime inventory drift")
    if snapshot_digest != expected_snapshot_inventory_sha256:
        _fail("verifier snapshot inventory drift")
    authorization_path = _launch_authorization_path(receipt_parent, variant=variant)
    if (
        not authorization_path.is_file()
        or _sha256_file(authorization_path) != expected_launch_authorization_sha256
    ):
        _fail("verifier launch authorization hash drift")
    authorization = _load_json(
        authorization_path, label="Landlock launch authorization"
    )
    if authorization.get("run_id") != run_id:
        _fail("verifier launch authorization run_id drift")
    ids = sorted(set(scope_ids))
    if not ids or len(ids) != len(scope_ids):
        _fail("verifier scope IDs must be non-empty and unique")

    archon = _plain_file(runtime / "bin/archon", label="trusted Archon", executable=True)
    lake = _plain_file(
        runtime / "lean-v4.31.0/bin/lake", label="trusted Lake", executable=True
    )
    argv: list[str] = [
        str(archon),
        "blind-verify-lean",
        "--project",
        str(workspace),
        "--candidate-dir",
        candidate_dir,
        "--output",
        str(output_path),
        "--runtime-executable",
        str(lake),
        "--runtime-root",
        str(runtime),
        "--dependency-root",
        str(dependency),
        "--expected-dependency-inventory-sha256",
        expected_dependency_inventory_sha256,
        "--expected-runtime-inventory-sha256",
        expected_runtime_inventory_sha256,
        "--expected-snapshot-inventory-sha256",
        expected_snapshot_inventory_sha256,
        "--expected-launch-authorization-sha256",
        expected_launch_authorization_sha256,
    ]
    for scope_id in ids:
        argv.extend(["--scope-id", scope_id])
    verifier_controller_dir = receipt_parent
    policy = build_landlock_policy(
        workspace=workspace,
        runtime_root=runtime,
        dependency_root=dependency,
        private_home=home,
        private_tmp=temporary,
        controller_dir=verifier_controller_dir,
        verifier_readonly=True,
        verifier_output_dir=output_parent,
        required_probe_paths=_authorized_probe_paths(authorization),
        allowed_connect_tcp_ports=(),
    )
    log_path = receipt_parent / f"{receipt_path.stem}.log"
    outcome = run_confined_command(
        argv=argv,
        cwd=workspace,
        environment=_minimal_environment(
            home=home, temporary=temporary, runtime_root=runtime
        ),
        identity=identity,
        policy=policy,
        log_path=log_path,
        timeout_s=timeout_s,
    )
    if (
        outcome.exit_code != 0
        or outcome.confinement_error is not None
        or not outcome.solver_stopped
        or not outcome.descendants_stopped
    ):
        _fail("confined Lean verifier failed closed")
    if output_path.is_symlink() or not output_path.is_file():
        _fail("confined Lean verifier did not produce its receipt")
    os.chown(output_path, 0, 0)
    os.chmod(output_path, 0o400)
    controller = {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        "phase": "lean_verifier_invocation",
        "verifier_uid": identity.uid,
        "command_argv": argv,
        "exit_code": outcome.exit_code,
        "solver_stopped": outcome.solver_stopped,
        "descendants_stopped": outcome.descendants_stopped,
        "landlock": policy.receipt(
            connected_fd_injection_count=outcome.connected_fd_injection_count,
            seccomp_supervisor_fail_closed=outcome.seccomp_supervisor_fail_closed,
            seccomp_supervisor_stopped=outcome.seccomp_supervisor_stopped,
        ),
        "isolation_probes": outcome.probes,
        "network_answer_blind": False,
        "verifier_receipt": {
            "path": str(output_path),
            "sha256": _sha256_file(output_path),
        },
        "stdout_log": {
            "path": str(log_path),
            "sha256": _sha256_file(log_path),
            "size": log_path.stat().st_size,
        },
        "dependency_inventory_sha256": dependency_digest,
        "runtime_inventory_sha256": runtime_digest,
        "snapshot_inventory_sha256": snapshot_digest,
        "dedicated_uid_quiescence": outcome.dedicated_uid_quiescence,
        "launch_authorization_sha256": expected_launch_authorization_sha256,
    }
    _atomic_new_controller_file(receipt_path, _pretty_json_bytes(controller), mode=0o400)
    return controller


_CLEAN_DROP_DIRECTORIES = {
    ".git", ".lake/build", ".lake/config", ".archon/logs",
    ".archon/task_results", ".archon/proof-journal", ".archon/iter",
    ".archon/tmp", ".archon/preflight", ".archon/git-dir",
    "__pycache__", ".pytest_cache", ".mypy_cache",
}


def _bundle_scope(project: Path, requested_ids: Sequence[str]) -> tuple[dict[str, Any], list[str]]:
    manifest = _load_json(project / "isolation_manifest.json", label="seed manifest")
    bundle = manifest.get("blind_bundle")
    if not isinstance(bundle, dict):
        _fail("seed manifest has no blind bundle binding")
    relative = _safe_relative(bundle.get("path"), label="blind bundle path")
    bundle_path = project.joinpath(*PurePosixPath(relative).parts)
    ids: list[str] = []
    for number, line in enumerate(bundle_path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:
            raise ControllerError(f"invalid blind bundle line {number}") from exc
        record_id = row.get("id") if isinstance(row, dict) else None
        if not isinstance(record_id, str) or SAFE_RUN_ID.fullmatch(record_id) is None:
            _fail(f"invalid blind bundle id on line {number}")
        ids.append(record_id)
    if ids != sorted(set(ids)):
        _fail("blind bundle IDs must be sorted and unique")
    scope = sorted(set(requested_ids)) if requested_ids else ids
    if not scope or len(scope) != len(requested_ids) and requested_ids:
        _fail("finalize scope IDs must be unique")
    if not set(scope).issubset(ids):
        _fail("finalize scope is not a subset of the blind bundle")
    if (
        bundle.get("row_count") != len(ids)
        or bundle.get("sha256") != _sha256_file(bundle_path)
    ):
        _fail("seed manifest blind bundle metadata drift")
    return {
        "path": relative,
        "sha256": _sha256_file(bundle_path),
        "row_count": len(ids),
        "ids": ids,
    }, scope


def _scoped_reports(source: Path, scope_ids: Sequence[str]) -> tuple[set[str], list[str]]:
    wanted = set(scope_ids)
    report_paths: set[str] = set()
    modules: list[str] = []
    found: set[str] = set()
    reports = source / "reports"
    for path in sorted(reports.rglob("*.source.json")):
        report = _load_json(path, label="source report")
        entry = report.get("entry")
        record_id = entry.get("id") if isinstance(entry, dict) else None
        if record_id not in wanted:
            continue
        if record_id in found:
            _fail(f"duplicate source report for scoped id: {record_id}")
        found.add(record_id)
        report_paths.add(path.relative_to(source).as_posix())
        target = _safe_relative(report.get("output_lean"), label="source report output_lean")
        if not target.endswith(".lean"):
            _fail(f"scoped target is not a Lean source: {target}")
        target_path = source.joinpath(*PurePosixPath(target).parts)
        if target_path.is_symlink() or not target_path.is_file():
            _fail(f"scoped Lean target is missing or unsafe: {target}")
        module = target[:-5].replace("/", ".")
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", module):
            _fail(f"scoped Lean target has an invalid module name: {target}")
        modules.append(module)
    if found != wanted:
        _fail(f"source-report scope mismatch: missing={sorted(wanted - found)}")
    return report_paths, sorted(modules)


def _copy_clean_snapshot(
    *, source: Path, destination: Path, dependency: Path, scope_ids: Sequence[str],
) -> None:
    """Copy only source/provenance state; never reuse solver build artifacts."""

    report_paths, modules = _scoped_reports(source, scope_ids)
    if destination.exists() or destination.is_symlink():
        _fail(f"clean snapshot destination must be absent: {destination}")
    destination.mkdir(mode=0o755)
    total_bytes = 0
    file_count = 0
    for directory, names, files in os.walk(source, topdown=True, followlinks=False):
        base = Path(directory)
        relative_base = base.relative_to(source)
        kept: list[str] = []
        for name in sorted(names):
            child = base / name
            relative = child.relative_to(source).as_posix()
            if (
                relative in _CLEAN_DROP_DIRECTORIES
                or name in _CLEAN_DROP_DIRECTORIES
                or any(relative.startswith(prefix + "/") for prefix in _CLEAN_DROP_DIRECTORIES)
            ):
                continue
            if child.is_symlink():
                if relative == ".lake/packages" and child.resolve(strict=True) == dependency:
                    continue
                _fail(f"clean snapshot source contains unapproved symlink: {relative}")
            if not child.is_dir():
                _fail(f"clean snapshot source contains special directory entry: {relative}")
            kept.append(name)
            target = destination / child.relative_to(source)
            target.mkdir(mode=0o755, parents=True, exist_ok=True)
        names[:] = kept
        target_base = destination / relative_base
        target_base.mkdir(mode=0o755, parents=True, exist_ok=True)
        for name in sorted(files):
            source_file = base / name
            relative = source_file.relative_to(source).as_posix()
            if (
                source_file.suffix in {".olean", ".ilean", ".pyc", ".pyo"}
                or (relative.startswith("reports/") and relative.endswith(".source.json") and relative not in report_paths)
                or (relative.startswith("blind_candidates/") and relative.endswith(".json") and source_file.stem not in set(scope_ids))
            ):
                continue
            if source_file.is_symlink() or not source_file.is_file():
                _fail(f"clean snapshot source contains unsafe file: {relative}")
            metadata = source_file.stat(follow_symlinks=False)
            if metadata.st_size > 2 * 1024**3:
                _fail(f"clean snapshot file exceeds size cap: {relative}")
            total_bytes += metadata.st_size
            file_count += 1
            if total_bytes > 40 * 1024**3 or file_count > 400_000:
                _fail("clean snapshot exceeds controller size/count caps")
            target = destination / source_file.relative_to(source)
            target.parent.mkdir(mode=0o755, parents=True, exist_ok=True)
            shutil.copyfile(source_file, target)
            os.chmod(target, 0o644)
    lake = destination / ".lake"
    lake.mkdir(mode=0o755, exist_ok=True)
    packages = lake / "packages"
    packages.symlink_to(dependency, target_is_directory=True)
    os.lchown(packages, 0, 0)
    all_path = destination / "IChO2026Problems/All.lean"
    all_path.parent.mkdir(mode=0o755, parents=True, exist_ok=True)
    all_path.write_text(
        "/-! Controller-generated scoped target umbrella. -/\n"
        + "".join(f"import {module}\n" for module in modules),
        encoding="utf-8",
    )
    os.chmod(all_path, 0o644)
    _make_root_readonly(destination)
    os.chmod(destination, 0o755)


def _snapshot_inventory(project: Path, *, dependency: Path) -> dict[str, str]:
    result: dict[str, str] = {}
    total = 0
    for directory, names, files in os.walk(project, topdown=True, followlinks=False):
        base = Path(directory)
        kept: list[str] = []
        for name in sorted(names):
            child = base / name
            relative = child.relative_to(project).as_posix()
            if relative in {".lake/build", ".lake/config"}:
                _fail(f"clean snapshot retains solver Lake state: {relative}")
            if child.is_symlink():
                if relative == ".lake/packages" and child.resolve(strict=True) == dependency:
                    continue
                _fail(f"clean snapshot contains unapproved symlink: {relative}")
            if not child.is_dir():
                _fail(f"clean snapshot contains special directory: {relative}")
            kept.append(name)
        names[:] = kept
        for name in sorted(files):
            path = base / name
            relative = path.relative_to(project).as_posix()
            if path.suffix in {".olean", ".ilean"}:
                _fail(f"clean snapshot contains compiled Lean artifact: {relative}")
            if path.is_symlink() or not path.is_file():
                _fail(f"clean snapshot contains unsafe file: {relative}")
            metadata = path.stat(follow_symlinks=False)
            if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) & 0o022:
                _fail(f"clean snapshot file is not controller-owned read-only: {relative}")
            total += metadata.st_size
            if len(result) >= 400_000 or total > 40 * 1024**3:
                _fail("clean snapshot exceeds inventory limits")
            result[relative] = _sha256_file(path)
    if not result:
        _fail("clean snapshot is empty")
    return dict(sorted(result.items()))


def _copy_review_input(
    *, project: Path, destination: Path, scope_ids: Sequence[str],
) -> dict[str, str]:
    """Create the exact problem-only independent Review projection."""

    if destination.exists() or destination.is_symlink():
        _fail("independent Review input destination must be absent")
    selected: set[str] = set(_seed_payload(project))
    selected.add("isolation_manifest.json")
    selected.update(GENERATED_PROTECTED_FILES)
    reports, _modules = _scoped_reports(project, scope_ids)
    for relative in reports:
        report_path = project.joinpath(*PurePosixPath(relative).parts)
        report = _load_json(report_path, label="independent Review source report")
        record_id = str(report["entry"]["id"])
        target = _safe_relative(report.get("output_lean"), label="Review target")
        candidate = f"blind_candidates/{record_id}.json"
        if not project.joinpath(*PurePosixPath(candidate).parts).is_file():
            _fail(f"independent Review candidate is missing: {candidate}")
        target_parts = PurePosixPath(target).with_suffix("").parts
        blueprint = f"blueprint/src/chapters/{'_'.join(target_parts)}.tex"
        selected.update({relative, target, candidate, blueprint})
    destination.mkdir(mode=0o755)
    for relative in sorted(selected):
        source = project.joinpath(*PurePosixPath(relative).parts)
        if source.is_symlink() or not source.is_file():
            _fail(f"independent Review input file is missing/unsafe: {relative}")
        target = destination.joinpath(*PurePosixPath(relative).parts)
        target.parent.mkdir(mode=0o755, parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        os.chmod(target, 0o644)
    _make_root_readonly(destination)
    os.chmod(destination, 0o755)
    files = _inventory_tree(destination)
    if set(files) != selected:
        _fail("independent Review projection contains unexpected/missing files")
    return files


def run_independent_reviewer(
    *, project: Path, review_input: Path, output: Path,
    controller_receipt: Path, reviewer_user: str, runtime: Path,
    dependency: Path, home: Path, temporary: Path,
    dependency_digest: str, runtime_digest: str, snapshot_digest: str,
    authorization_sha: str, broker_ready_path: Path, broker_ready_sha: str,
    variant: str, run_id: str, family: str, model: str,
    scope_ids: Sequence[str], candidate_dir: str, timeout_s: int,
) -> dict[str, Any]:
    identity = _identity(reviewer_user)
    controller = _controller_dir(controller_receipt.parent)
    authorization_path = _plain_file(
        _launch_authorization_path(controller, variant=variant),
        label="Landlock launch authorization",
    )
    if _sha256_file(authorization_path) != authorization_sha:
        _fail("independent Review launch authorization drift")
    authorization = _load_json(authorization_path, label="Landlock launch authorization")
    if (home, temporary, output.parent) != _default_reviewer_paths(
        controller, variant=variant
    ):
        _fail("independent reviewer paths differ from pre-run authorization")
    for path in (home, temporary, output.parent):
        metadata = _plain_directory(path, label="independent reviewer private path").stat()
        if metadata.st_uid != identity.uid or stat.S_IMODE(metadata.st_mode) != 0o700:
            _fail("independent reviewer private path ownership/mode drift")
    if output.exists() or output.is_symlink() or controller_receipt.exists():
        _fail("independent Review receipts must be new")
    review_files = _inventory_tree(review_input)
    review_digest = _hash_index(review_files)
    broker = _load_json(broker_ready_path, label="model broker ready receipt")
    parsed = urlparse(str(broker.get("listen_url") or ""))
    if parsed.port != authorization.get("allowed_model_broker_tcp_port"):
        _fail("independent reviewer broker port differs from launch authorization")
    policy = build_landlock_policy(
        workspace=review_input, runtime_root=runtime, dependency_root=dependency,
        private_home=home, private_tmp=temporary, controller_dir=controller,
        verifier_readonly=True, verifier_output_dir=output.parent,
        required_probe_paths=_authorized_probe_paths(authorization),
        allowed_connect_tcp_ports=(parsed.port,),
    )
    reviewer = _plain_file(
        runtime / "bin/answer-blind-independent-review",
        label="trusted independent Review runner", executable=True,
    )
    argv = [
        str(reviewer), "--review-input", str(review_input), "--output", str(output),
        "--runtime-root", str(runtime), "--variant", variant,
        "--reviewer-model-family", family, "--reviewer-model-id", model,
        "--broker-url", str(broker["listen_url"]),
        "--snapshot-inventory-sha256", snapshot_digest,
        "--review-input-inventory-sha256", review_digest,
        "--candidate-dir", candidate_dir, "--timeout-s", str(timeout_s),
    ]
    for record_id in sorted(scope_ids):
        argv.extend(["--scope-id", record_id])
    log_path = controller / f"{variant}-independent-review.log"
    outcome = run_confined_command(
        argv=argv, cwd=review_input,
        environment=_minimal_environment(
            home=home, temporary=temporary, runtime_root=runtime
        ),
        identity=identity, policy=policy, log_path=log_path,
        timeout_s=max(timeout_s * len(scope_ids) * 2, timeout_s),
    )
    if (
        outcome.exit_code != 0 or outcome.confinement_error is not None
        or not outcome.solver_stopped or not outcome.descendants_stopped
        or not outcome.dedicated_uid_quiescence["quiescent_after"]
    ):
        _fail("independent reviewer failed closed")
    if output.is_symlink() or not output.is_file():
        _fail("independent reviewer produced no semantic receipt")
    semantic = _load_json(output, label="independent Review semantic receipt")
    if (
        semantic.get("phase") != "independent_problem_only_review"
        or semantic.get("reviewer_uid") != identity.uid
        or semantic.get("scope_ids") != sorted(scope_ids)
    ):
        _fail("independent Review semantic receipt provenance mismatch")
    os.chown(output, 0, 0)
    os.chmod(output, 0o400)
    wrapper = {
        "schema_version": SCHEMA_VERSION, "protocol": PROTOCOL,
        "phase": "independent_review_invocation",
        "reviewer_uid": identity.uid, "reviewer_model_family": family,
        "reviewer_model_id": model, "command_argv": argv,
        "exit_code": outcome.exit_code, "solver_stopped": outcome.solver_stopped,
        "descendants_stopped": outcome.descendants_stopped,
        "network_answer_blind": False,
        "dedicated_uid_quiescence": outcome.dedicated_uid_quiescence,
        "landlock": policy.receipt(
            connected_fd_injection_count=outcome.connected_fd_injection_count,
            seccomp_supervisor_fail_closed=outcome.seccomp_supervisor_fail_closed,
            seccomp_supervisor_stopped=outcome.seccomp_supervisor_stopped,
        ), "isolation_probes": outcome.probes,
        "dependency_inventory_sha256": dependency_digest,
        "runtime_inventory_sha256": runtime_digest,
        "snapshot_inventory_sha256": snapshot_digest,
        "launch_authorization_sha256": authorization_sha,
        "model_broker_receipt_sha256": broker_ready_sha,
        "review_input_inventory": {
            "root": str(review_input), "files": review_files,
            "files_sha256": review_digest,
        },
        "review_receipt": {"path": str(output), "sha256": _sha256_file(output)},
        "stdout_log": {
            "path": str(log_path), "sha256": _sha256_file(log_path),
            "size": log_path.stat().st_size,
        },
    }
    if set(wrapper) != INDEPENDENT_REVIEW_INVOCATION_FIELDS:
        _fail("internal independent Review invocation schema drift")
    _atomic_new_controller_file(
        controller_receipt, _pretty_json_bytes(wrapper), mode=0o400
    )
    return wrapper


def finalize_solver_run(
    *, workspace: Path | str, variant: str, solver_user: str,
    verifier_user: str, reviewer_user: str, runtime_root: Path | str,
    dependency_root: Path | str,
    controller_receipts: Path | str, run_id: str, sibling_workspace: Path | str,
    model_broker_receipt: Path | str, model_broker_transcript: Path | str,
    quarantine_workspace: Path | str, scope_kind: str, scope_ids: Sequence[str],
    candidate_dir: str, timeout_s: int,
) -> dict[str, Any]:
    """Irreversibly close solve, build a clean snapshot, verify, seal, freeze."""

    _fail(
        "legacy arbitrary-shell finalize is permanently disabled; structured "
        "solver/reviewer receipts are required"
    )
    _require_root()
    if variant not in VARIANT_MODELS or SAFE_RUN_ID.fullmatch(run_id) is None:
        _fail("finalize needs an approved variant and run_id")
    if scope_kind not in {"full", "pilot"}:
        _fail("finalize scope kind must be full or pilot")
    solver = _identity(solver_user)
    verifier = _identity(verifier_user)
    reviewer = _identity(reviewer_user)
    if len({solver.uid, verifier.uid, reviewer.uid}) != 3:
        _fail("solver, verifier, and reviewer identities must be distinct")
    project = _plain_directory(workspace, label="solver workspace")
    runtime = _plain_directory(runtime_root, label="answer-blind runtime")
    dependency = _plain_directory(dependency_root, label="Lean dependency tree")
    sibling = _plain_directory(sibling_workspace, label="sibling solver workspace")
    controller = _controller_dir(controller_receipts)
    transcript_requested = Path(model_broker_transcript).absolute()
    expected_transcript = controller / f"{variant}-model-broker-transcript.json"
    if transcript_requested != expected_transcript:
        _fail("model broker transcript path must be the controller's fixed path")
    if transcript_requested.exists() or transcript_requested.is_symlink():
        _fail("model broker transcript must not exist before independent Review")
    quarantine = Path(quarantine_workspace).absolute()
    if quarantine.exists() or quarantine.is_symlink():
        _fail("quarantine workspace must be a new path")
    if quarantine.parent.is_symlink() or not quarantine.parent.is_dir():
        _fail("quarantine parent must be an existing plain directory")
    parent_metadata = project.parent.stat()
    quarantine_parent_metadata = quarantine.parent.stat()
    if (
        parent_metadata.st_uid != 0 or parent_metadata.st_mode & 0o022
        or quarantine_parent_metadata.st_uid != 0
        or quarantine_parent_metadata.st_mode & 0o022
    ):
        _fail("snapshot/quarantine parents must be root-owned and non-writable by solver")
    _assert_pairwise_disjoint({
        "workspace": project, "runtime": runtime, "dependency": dependency,
        "controller": controller, "sibling": sibling, "quarantine": quarantine,
    })
    if _real_uid_pids(solver.uid):
        _fail("cannot finalize while the dedicated solver UID is active")
    if _real_uid_pids(verifier.uid):
        _fail("cannot finalize while the dedicated verifier UID is active")
    if _real_uid_pids(reviewer.uid):
        _fail("cannot finalize while the dedicated reviewer UID is active")
    _assert_controller_tree(runtime, label="answer-blind runtime")
    _assert_controller_tree(dependency, label="Lean dependency tree")
    family, model = _validate_variant_config(project, variant=variant)
    dependency_files = _inventory_tree(dependency)
    dependency_digest = _hash_index(dependency_files)
    runtime_files = _inventory_tree(runtime, exclude_roots=(dependency,))
    runtime_digest = _hash_index(runtime_files)

    authorization_path = _plain_file(
        _launch_authorization_path(controller, variant=variant),
        label="Landlock launch authorization",
    )
    authorization = _load_json(authorization_path, label="Landlock launch authorization")
    authorization_sha = _sha256_file(authorization_path)
    if (
        authorization.get("variant") != variant
        or authorization.get("run_id") != run_id
        or authorization.get("workspace") != str(project)
        or authorization.get("runtime_root") != str(runtime)
        or authorization.get("dependency_root") != str(dependency)
    ):
        _fail("Landlock launch authorization identity/root drift")
    current_system_paths, current_system_files = _system_readonly_inventory(runtime)
    if authorization.get("system_inventory") != {
        "files": current_system_files,
        "files_sha256": _hash_index(current_system_files),
    }:
        _fail("Landlock launch authorization system inventory drift")
    expected_system_paths = [
        *(str(path) for path in current_system_paths),
        *(str(path) for path in _existing_paths(Path(raw) for raw in SYSTEM_DEVICE_FILES)),
    ]
    if authorization.get("system_read_only_paths") != expected_system_paths:
        _fail("Landlock launch authorization system path drift")

    ready_path = _plain_file(model_broker_receipt, label="model broker ready receipt")
    ready = _load_json(ready_path, label="model broker ready receipt")
    base_key = "ANTHROPIC_BASE_URL" if variant == "kimi-k3" else "ANSWER_BLIND_MODEL_BASE_URL"
    dummy_key = "ANTHROPIC_AUTH_TOKEN" if variant == "kimi-k3" else "ANSWER_BLIND_MODEL_DUMMY_KEY"
    broker_sha = _validate_model_broker_receipt(
        ready_path, variant=variant, run_id=run_id, model=model,
        broker_environment={
            base_key: str(ready.get("listen_url") or ""),
            dummy_key: "answer-blind-public-dummy-token",
        },
        runtime_files=runtime_files,
        request_profile="agent_harness_v1",
    )
    broker_uid = ready.get("broker_uid")
    if (
        not isinstance(broker_uid, int)
        or broker_uid in {solver.uid, verifier.uid, reviewer.uid}
    ):
        _fail("model broker must use a fourth dedicated UID")
    _probe_model_broker(ready_path, expected_sha256=broker_sha)

    aggregate_path = _plain_file(
        controller / f"{variant}-invocations.json",
        label="solver invocation aggregate",
    )
    aggregate = _read_aggregate(aggregate_path, variant=variant, run_id=run_id)
    if aggregate is None:
        _fail("cannot finalize without a solver invocation aggregate")
    receipt_specs = _validate_prior_receipt_chain(
        aggregate=aggregate, controller=controller, variant=variant, family=family,
        model=model, run_id=run_id, identity=solver,
        dependency_digest=dependency_digest, runtime_digest=runtime_digest,
        authorization_sha=authorization_sha, broker_receipt_sha=broker_sha,
    )
    for field in (
        "all_exit_zero", "all_protected_unchanged", "all_stopped",
        "all_uid_quiescent",
    ):
        if aggregate.get(field) is not True:
            _fail(f"solver invocation aggregate does not pass {field}")
    latest = _load_json(Path(receipt_specs[-1]["path"]), label="latest solver receipt")
    if latest.get("protected_after") != _protected_receipt(
        project, solver_gid=solver.gid
    ):
        _fail("workspace protected inventory drifted after the last solver invocation")

    bundle, scope = _bundle_scope(project, scope_ids)
    if scope_kind == "full" and scope != bundle["ids"]:
        _fail("full finalize scope must equal all blind bundle IDs")
    candidate_relative = _safe_relative(candidate_dir, label="candidate directory")
    verifier_paths = _default_verifier_paths(controller, variant=variant)
    if authorization.get("verifier_external_read_write_paths") != [
        str(path.resolve()) for path in verifier_paths
    ]:
        _fail("verifier private paths differ from pre-run launch authorization")
    for path in verifier_paths:
        _plain_directory(path, label="preauthorized verifier private directory")
        metadata = path.stat()
        if metadata.st_uid != verifier.uid or stat.S_IMODE(metadata.st_mode) != 0o700:
            _fail("preauthorized verifier directory ownership/mode drift")
        if any(path.iterdir()):
            _fail("preauthorized verifier directory is not fresh")
    reviewer_paths = _default_reviewer_paths(controller, variant=variant)
    if authorization.get("reviewer_external_read_write_paths") != [
        str(path.resolve()) for path in reviewer_paths
    ]:
        _fail("reviewer private paths differ from pre-run launch authorization")
    for path in reviewer_paths:
        _plain_directory(path, label="preauthorized reviewer private directory")
        metadata = path.stat()
        if metadata.st_uid != reviewer.uid or stat.S_IMODE(metadata.st_mode) != 0o700:
            _fail("preauthorized reviewer directory ownership/mode drift")
        if any(path.iterdir()):
            _fail("preauthorized reviewer directory is not fresh")
    ready_port = urlparse(str(ready.get("listen_url") or "")).port
    if authorization.get("allowed_model_broker_tcp_port") != ready_port:
        _fail("launch authorization broker TCP port drift")

    marker = controller / f"{variant}-finalized.json"
    if marker.exists() or marker.is_symlink():
        _fail("run already entered irreversible finalize")
    _atomic_new_controller_file(
        marker,
        _pretty_json_bytes({
            "schema_version": SCHEMA_VERSION, "protocol": PROTOCOL,
            "phase": "finalize_in_progress", "variant": variant,
            "run_id": run_id, "workspace": str(project),
            "quarantine_workspace": str(quarantine),
        }),
        mode=0o400,
    )

    # From this point onward the marker prevents any solver requeue.  Preserve
    # the full old tree in a root-only quarantine and recreate the same
    # authorized path using a source-only copy.
    _make_root_readonly(project)
    os.rename(project, quarantine)
    _copy_clean_snapshot(
        source=quarantine, destination=project, dependency=dependency,
        scope_ids=scope,
    )
    _assert_controller_tree(project, label="clean solver snapshot")
    snapshot_files = _snapshot_inventory(project, dependency=dependency)
    snapshot_digest = _hash_index(snapshot_files)
    if any(path.suffix in {".olean", ".ilean"} for path in project.rglob("*")):
        _fail("clean snapshot unexpectedly retained compiled Lean state")

    review_input = controller.parent / f".{controller.name}-{variant}-review-input"
    _copy_review_input(project=project, destination=review_input, scope_ids=scope)
    reviewer_home, reviewer_tmp, reviewer_output = reviewer_paths
    review_semantic = reviewer_output / "independent-review-result.json"
    review_wrapper_path = controller / f"{variant}-independent-review-invocation.json"
    review_error: BaseException | None = None
    review_wrapper: dict[str, Any] | None = None
    try:
        review_wrapper = run_independent_reviewer(
            project=project, review_input=review_input, output=review_semantic,
            controller_receipt=review_wrapper_path, reviewer_user=reviewer_user,
            runtime=runtime, dependency=dependency, home=reviewer_home,
            temporary=reviewer_tmp, dependency_digest=dependency_digest,
            runtime_digest=runtime_digest, snapshot_digest=snapshot_digest,
            authorization_sha=authorization_sha, broker_ready_path=ready_path,
            broker_ready_sha=broker_sha, variant=variant, run_id=run_id,
            family=family, model=model, scope_ids=scope,
            candidate_dir=candidate_relative, timeout_s=timeout_s,
        )
        _probe_model_broker(ready_path, expected_sha256=broker_sha)
    except BaseException as exc:
        review_error = exc

    transcript_path = transcript_requested
    broker_stop_log = controller / f"{variant}-model-broker-stop.log"
    broker_runner = _plain_file(
        runtime / "bin/answer-blind-model-broker",
        label="trusted model broker controller", executable=True,
    )
    with broker_stop_log.open("xb") as log:
        stopped = subprocess.run(
            [
                str(broker_runner), "stop", "--controller-dir", str(controller),
                "--variant", variant, "--timeout-s", "60",
            ],
            cwd=controller,
            env={
                "HOME": str(controller), "TMPDIR": str(controller),
                "PATH": f"{runtime}/bin:{runtime}/venv/bin",
                "PYTHONSAFEPATH": "1", "PYTHONNOUSERSITE": "1",
                "PYTHONDONTWRITEBYTECODE": "1", "LANG": "C.UTF-8",
                "LC_ALL": "C.UTF-8",
            },
            stdin=subprocess.DEVNULL, stdout=log, stderr=subprocess.STDOUT,
            timeout=90, check=False,
        )
        log.flush()
        os.fsync(log.fileno())
    os.chown(broker_stop_log, 0, 0)
    os.chmod(broker_stop_log, 0o400)
    if stopped.returncode != 0:
        _fail(f"model broker failed to stop; inspect {broker_stop_log}")
    transcript_path = _plain_file(transcript_path, label="model broker transcript")
    transcript_sha = _validate_model_broker_transcript(
        transcript_path, variant=variant, run_id=run_id, ready_sha256=broker_sha,
    )
    if _real_uid_pids(broker_uid):
        _fail("model broker dedicated UID is not quiescent after stop")
    if review_error is not None:
        raise review_error
    if review_wrapper is None:
        _fail("independent reviewer produced no wrapper receipt")

    verifier_home, verifier_tmp, verifier_output = verifier_paths
    semantic_receipt = verifier_output / "lean-verifier-result.json"
    wrapper_receipt = controller / f"{variant}-lean-verifier-invocation.json"
    verifier_wrapper = run_verifier(
        project=project, candidate_dir=candidate_relative,
        output=semantic_receipt, controller_receipt=wrapper_receipt,
        verifier_user=verifier_user, runtime_root=runtime,
        dependency_root=dependency, private_home=verifier_home,
        private_tmp=verifier_tmp,
        expected_dependency_inventory_sha256=dependency_digest,
        expected_runtime_inventory_sha256=runtime_digest,
        expected_snapshot_inventory_sha256=snapshot_digest,
        expected_launch_authorization_sha256=authorization_sha,
        variant=variant, run_id=run_id, scope_ids=scope, timeout_s=timeout_s,
    )
    if verifier_wrapper.get("exit_code") != 0:
        _fail("Lean verifier wrapper did not pass")
    if _hash_index(_snapshot_inventory(project, dependency=dependency)) != snapshot_digest:
        _fail("clean solver snapshot changed during Lean verification")

    generated = {
        relative: _sha256_file(project.joinpath(*PurePosixPath(relative).parts))
        for relative in GENERATED_PROTECTED_FILES
    }
    seal = {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        "phase": "freeze_authorization",
        "solver_stopped": True,
        "seed_manifest_sha256": _sha256_file(project / "isolation_manifest.json"),
        "blind_bundle": bundle,
        "freeze_scope": {"kind": scope_kind, "ids": scope},
        "generated_files": generated,
        "dependency_inventory": {
            "root": str(dependency), "files": dependency_files,
            "files_sha256": dependency_digest,
        },
        "runtime_inventory": {
            "root": str(runtime), "files": runtime_files,
            "files_sha256": runtime_digest,
        },
        "snapshot_inventory": {
            "files": snapshot_files, "files_sha256": snapshot_digest,
        },
        "launch_authorization": {
            "path": str(authorization_path), "sha256": authorization_sha,
        },
        "model_broker": {
            "ready_receipt": {"path": str(ready_path), "sha256": broker_sha},
            "transcript": {"path": str(transcript_path), "sha256": transcript_sha},
        },
        "solver": {"model_family": family, "model_id": model, "run_id": run_id},
        "isolation": {
            "filesystem_answer_blind": True, "network_answer_blind": False,
        },
        "solver_invocation_receipt": {
            "path": str(aggregate_path), "sha256": _sha256_file(aggregate_path),
        },
        "verifier_receipt": {
            "path": str(wrapper_receipt), "sha256": _sha256_file(wrapper_receipt),
        },
        "independent_review_receipt": {
            "path": str(review_wrapper_path),
            "sha256": _sha256_file(review_wrapper_path),
        },
    }
    if set(seal) != CONTROLLER_SEAL_FIELDS:
        _fail("internal controller freeze-authorization schema drift")
    seal_path = controller / f"{variant}-freeze-authorization.json"
    seal_payload = _pretty_json_bytes(seal)
    seal_sha = _sha256_bytes(seal_payload)
    _atomic_new_controller_file(seal_path, seal_payload, mode=0o400)
    _atomic_new_controller_file(
        Path(str(seal_path) + ".sha256"),
        f"{seal_sha}  {seal_path.name}\n".encode("ascii"), mode=0o400,
    )

    freeze_output = controller / f"{variant}-frozen-manifest.json"
    freeze_log = controller / f"{variant}-freeze.log"
    archon = _plain_file(runtime / "bin/archon", label="trusted Archon", executable=True)
    argv = [
        str(archon), "blind-freeze", "--project", str(project),
        "--candidate-dir", candidate_relative, "--output", str(freeze_output),
        "--controller-seal", str(seal_path),
        "--expected-controller-seal-sha256", seal_sha,
    ]
    with freeze_log.open("xb") as log:
        completed = subprocess.run(
            argv, cwd=project,
            env={
                "HOME": str(controller), "TMPDIR": str(controller),
                "PATH": f"{runtime}/bin:{runtime}/venv/bin",
                "PYTHONSAFEPATH": "1", "PYTHONDONTWRITEBYTECODE": "1",
                "PYTHONNOUSERSITE": "1", "LANG": "C.UTF-8", "LC_ALL": "C.UTF-8",
            },
            stdin=subprocess.DEVNULL, stdout=log, stderr=subprocess.STDOUT,
            timeout=timeout_s, check=False,
        )
        log.flush()
        os.fsync(log.fileno())
    os.chown(freeze_log, 0, 0)
    os.chmod(freeze_log, 0o400)
    if completed.returncode != 0 or not freeze_output.is_file():
        _fail(f"trusted freeze failed closed; inspect {freeze_log}")
    os.chown(freeze_output, 0, 0)
    os.chmod(freeze_output, 0o400)
    final_marker = {
        "schema_version": SCHEMA_VERSION, "protocol": PROTOCOL,
        "phase": "finalized", "variant": variant, "run_id": run_id,
        "workspace": str(project), "quarantine_workspace": str(quarantine),
        "snapshot_inventory_sha256": snapshot_digest,
        "controller_seal": {"path": str(seal_path), "sha256": seal_sha},
        "freeze_manifest": {
            "path": str(freeze_output), "sha256": _sha256_file(freeze_output),
        },
    }
    _replace_controller_json(marker, _pretty_json_bytes(final_marker))
    return final_marker


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    harden = subparsers.add_parser("harden")
    harden.add_argument("--workspace", type=Path, required=True)
    harden.add_argument("--solver-user", required=True)
    harden.add_argument("--dependency-root", type=Path, required=True)
    harden.add_argument("--private-home", type=Path, required=True)
    harden.add_argument("--private-tmp", type=Path, required=True)
    harden.add_argument("--variant", choices=sorted(VARIANT_MODELS), required=True)
    harden.add_argument("--run-id", required=True)

    runtime_harden = subparsers.add_parser("harden-runtime")
    runtime_harden.add_argument("--runtime-root", type=Path, required=True)

    run = subparsers.add_parser("run")
    run.add_argument("--workspace", type=Path, required=True)
    run.add_argument("--variant", choices=sorted(VARIANT_MODELS), required=True)
    run.add_argument("--solver-user", required=True)
    run.add_argument("--verifier-user", required=True)
    run.add_argument("--reviewer-user", required=True)
    run.add_argument("--runtime-root", type=Path, required=True)
    run.add_argument("--dependency-root", type=Path, required=True)
    run.add_argument("--private-home", type=Path, required=True)
    run.add_argument("--private-tmp", type=Path, required=True)
    run.add_argument("--controller-receipts", type=Path, required=True)
    run.add_argument("--run-id", required=True)
    run.add_argument("--timeout-s", type=int, default=21600)
    run.add_argument("--sibling-workspace", type=Path)
    run.add_argument("--credential-env-file", type=Path)
    run.add_argument("--model-broker-receipt", type=Path, required=True)

    probe = subparsers.add_parser("probe")
    probe.add_argument("--executable", type=Path, required=True)
    probe.add_argument("--workspace", type=Path, required=True)
    probe.add_argument("--runtime-root", type=Path, required=True)
    probe.add_argument("--dependency-root", type=Path, required=True)
    probe.add_argument("--private-home", type=Path, required=True)
    probe.add_argument("--private-tmp", type=Path, required=True)
    probe.add_argument("--controller-dir", type=Path, required=True)
    probe.add_argument("--user", required=True)
    probe.add_argument("--log-name", required=True)

    verify = subparsers.add_parser("verify")
    verify.add_argument("--project", type=Path, required=True)
    verify.add_argument("--candidate-dir", default="blind_candidates")
    verify.add_argument("--output", type=Path, required=True)
    verify.add_argument("--controller-receipt", type=Path, required=True)
    verify.add_argument("--verifier-user", required=True)
    verify.add_argument("--runtime-root", type=Path, required=True)
    verify.add_argument("--dependency-root", type=Path, required=True)
    verify.add_argument("--private-home", type=Path, required=True)
    verify.add_argument("--private-tmp", type=Path, required=True)
    verify.add_argument("--expected-dependency-inventory-sha256", required=True)
    verify.add_argument("--expected-runtime-inventory-sha256", required=True)
    verify.add_argument("--expected-snapshot-inventory-sha256", required=True)
    verify.add_argument("--expected-launch-authorization-sha256", required=True)
    verify.add_argument("--variant", choices=sorted(VARIANT_MODELS), required=True)
    verify.add_argument("--run-id", required=True)
    verify.add_argument("--scope-id", action="append", required=True)
    verify.add_argument("--timeout-s", type=int, default=1800)

    finalize = subparsers.add_parser("finalize")
    finalize.add_argument("--workspace", type=Path, required=True)
    finalize.add_argument("--variant", choices=sorted(VARIANT_MODELS), required=True)
    finalize.add_argument("--solver-user", required=True)
    finalize.add_argument("--verifier-user", required=True)
    finalize.add_argument("--reviewer-user", required=True)
    finalize.add_argument("--runtime-root", type=Path, required=True)
    finalize.add_argument("--dependency-root", type=Path, required=True)
    finalize.add_argument("--controller-receipts", type=Path, required=True)
    finalize.add_argument("--run-id", required=True)
    finalize.add_argument("--sibling-workspace", type=Path, required=True)
    finalize.add_argument("--model-broker-receipt", type=Path, required=True)
    finalize.add_argument("--model-broker-transcript", type=Path, required=True)
    finalize.add_argument("--quarantine-workspace", type=Path, required=True)
    finalize.add_argument("--scope-kind", choices=("full", "pilot"), required=True)
    finalize.add_argument("--scope-id", action="append", default=[])
    finalize.add_argument("--candidate-dir", default="blind_candidates")
    finalize.add_argument("--timeout-s", type=int, default=1800)
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    parser = _parser()
    args = parser.parse_args(argv)
    try:
        if args.command == "harden":
            result = harden_solver_workspace(
                workspace=args.workspace,
                identity=_identity(args.solver_user),
                dependency_root=args.dependency_root,
                private_home=args.private_home,
                private_tmp=args.private_tmp,
                variant=args.variant,
                run_id=args.run_id,
            )
        elif args.command == "harden-runtime":
            harden_controller_tree(args.runtime_root)
            result = {"runtime_root": str(args.runtime_root.resolve()), "hardened": True}
        elif args.command == "run":
            result = run_solver_iteration(
                workspace=args.workspace,
                variant=args.variant,
                solver_user=args.solver_user,
                runtime_root=args.runtime_root,
                dependency_root=args.dependency_root,
                private_home=args.private_home,
                private_tmp=args.private_tmp,
                controller_receipts=args.controller_receipts,
                run_id=args.run_id,
                timeout_s=args.timeout_s,
                sibling_workspace=args.sibling_workspace,
                credential_env_file=args.credential_env_file,
                verifier_user=args.verifier_user,
                reviewer_user=args.reviewer_user,
                model_broker_receipt=args.model_broker_receipt,
            )
        elif args.command == "probe":
            outcome = run_landlock_version_probe(
                executable=args.executable,
                workspace=args.workspace,
                runtime_root=args.runtime_root,
                dependency_root=args.dependency_root,
                private_home=args.private_home,
                private_tmp=args.private_tmp,
                controller_dir=args.controller_dir,
                user=args.user,
                log_name=args.log_name,
            )
            result = {
                "exit_code": outcome.exit_code,
                "solver_stopped": outcome.solver_stopped,
                "descendants_stopped": outcome.descendants_stopped,
                "isolation_probes": outcome.probes,
            }
        elif args.command == "verify":
            result = run_verifier(
                project=args.project,
                candidate_dir=args.candidate_dir,
                output=args.output,
                controller_receipt=args.controller_receipt,
                verifier_user=args.verifier_user,
                runtime_root=args.runtime_root,
                dependency_root=args.dependency_root,
                private_home=args.private_home,
                private_tmp=args.private_tmp,
                expected_dependency_inventory_sha256=args.expected_dependency_inventory_sha256,
                expected_runtime_inventory_sha256=args.expected_runtime_inventory_sha256,
                expected_snapshot_inventory_sha256=args.expected_snapshot_inventory_sha256,
                expected_launch_authorization_sha256=args.expected_launch_authorization_sha256,
                variant=args.variant,
                run_id=args.run_id,
                scope_ids=args.scope_id,
                timeout_s=args.timeout_s,
            )
        else:
            result = finalize_solver_run(
                workspace=args.workspace,
                variant=args.variant,
                solver_user=args.solver_user,
                verifier_user=args.verifier_user,
                reviewer_user=args.reviewer_user,
                runtime_root=args.runtime_root,
                dependency_root=args.dependency_root,
                controller_receipts=args.controller_receipts,
                run_id=args.run_id,
                sibling_workspace=args.sibling_workspace,
                model_broker_receipt=args.model_broker_receipt,
                model_broker_transcript=args.model_broker_transcript,
                quarantine_workspace=args.quarantine_workspace,
                scope_kind=args.scope_kind,
                scope_ids=args.scope_id,
                candidate_dir=args.candidate_dir,
                timeout_s=args.timeout_s,
            )
    except ControllerError as exc:
        parser.error(str(exc))
    print(json.dumps(result, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
