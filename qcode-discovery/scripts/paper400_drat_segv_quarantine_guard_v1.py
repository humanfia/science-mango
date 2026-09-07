#!/usr/bin/env python3
"""Fail-closed shared-lock guard for one deterministic DRAT-crash root.

This program is deliberately a *quarantine*, not a proof checker.  A sealed
manifest identifies one stopped leaf, its existing hierarchy lock, proof,
cube, checker and the terminal records that were absent when the incident was
reviewed.  The guard acquires ``LOCK_SH|LOCK_NB`` and sends ``READY=1`` only
after replaying every bound pathname and identity.  It then repeats that
replay forever.  It never creates, writes, renames or removes a file.

One process guards one root.  Therefore a systemd unit that finds an active
exclusive checker exits with EX_TEMPFAIL and may be retried independently;
no active checker is interrupted and no unrelated root is held back.
"""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
import re
import socket
import stat
import sys
import time
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Any


GATE = "paper400-drat-segv-quarantine-guard-v1"
SCHEMA = "paper400-drat-segv-quarantine-manifest-v1"
EX_TEMPFAIL = 75
MAX_MANIFEST_BYTES = 4 << 20
BAD_CHECKER_SHA256 = (
    "8d25091073e9295028dd4aec85acca4d9b3381d2cfcc145a5b0e14ae909ce394"
)
REQUIRED_ABSENT = frozenset({
    "state/20-proof-harvest.claim",
    "state/21-drat.json",
    "state/22-lrat.json",
    "certificate.json",
    "validation.json",
    "COMMIT.json",
})
_ENTRY_ID = re.compile(r"[a-z0-9][a-z0-9-]{0,63}\Z")
_HEX = re.compile(r"[0-9a-f]{64}\Z")


class QuarantineGuardError(RuntimeError):
    """A manifest, source, pathname or inode violated the guard contract."""


class QuarantineBusyError(QuarantineGuardError):
    """The root is legitimately held exclusively and must be retried later."""


@dataclass(frozen=True)
class Identity:
    device: int
    inode: int
    mode: int
    uid: int
    links: int | None = None
    size: int | None = None
    mtime_ns: int | None = None
    ctime_ns: int | None = None


@dataclass
class HeldPath:
    path: Path
    chain: list[int]
    descriptor: int
    expected: Identity
    directory: bool


@dataclass
class HeldQuarantine:
    entry_id: str
    manifest: HeldPath
    root: HeldPath
    lock: HeldPath
    proof: HeldPath
    cube: HeldPath
    checker: HeldPath
    absent_relative_paths: tuple[str, ...]


_FAULT_HOOK: Callable[[str, Path], None] = lambda _stage, _path: None


def _canonical(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
        allow_nan=False,
    ).encode("ascii")


def seal_manifest(value: Mapping[str, Any]) -> dict[str, Any]:
    """Return a canonical record seal; primarily useful to renderers/tests."""

    result = dict(value)
    if "record_sha256" in result:
        raise QuarantineGuardError("manifest is already sealed")
    result["record_sha256"] = hashlib.sha256(_canonical(result)).hexdigest()
    return result


def manifest_payload(value: Mapping[str, Any]) -> bytes:
    return _canonical(value) + b"\n"


def _absolute(path: Path) -> Path:
    value = Path(path)
    if (
        not value.is_absolute() or str(value) != os.path.abspath(str(value))
        or not value.name or value.name in {".", ".."}
    ):
        raise QuarantineGuardError("bound path is not absolute and normalized")
    return value


def _relative(value: Any) -> str:
    if type(value) is not str:
        raise QuarantineGuardError("relative path is not a string")
    path = Path(value)
    if (
        path.is_absolute() or not path.parts
        or any(part in {"", ".", ".."} for part in path.parts)
        or str(path) != value
    ):
        raise QuarantineGuardError("relative path is unsafe")
    return value


def _natural(value: Any, name: str) -> int:
    if type(value) is not int or value < 0:
        raise QuarantineGuardError(f"{name} is not a natural number")
    return value


def _identity(value: Any, *, full: bool) -> Identity:
    if type(value) is not dict:
        raise QuarantineGuardError("identity is not an object")
    required = {"device", "inode", "mode", "uid"}
    optional = {"links", "size", "mtime_ns", "ctime_ns"}
    if set(value) != required | (optional if full else set()):
        raise QuarantineGuardError("identity fields do not match the schema")
    result = Identity(
        device=_natural(value["device"], "device"),
        inode=_natural(value["inode"], "inode"),
        mode=_natural(value["mode"], "mode"),
        uid=_natural(value["uid"], "uid"),
        links=_natural(value["links"], "links") if full else None,
        size=_natural(value["size"], "size") if full else None,
        mtime_ns=_natural(value["mtime_ns"], "mtime_ns") if full else None,
        ctime_ns=_natural(value["ctime_ns"], "ctime_ns") if full else None,
    )
    if result.mode > 0o7777:
        raise QuarantineGuardError("identity mode is invalid")
    return result


def identity_record(info: os.stat_result, *, full: bool) -> dict[str, int]:
    result = {
        "device": int(info.st_dev), "inode": int(info.st_ino),
        "mode": stat.S_IMODE(info.st_mode), "uid": int(info.st_uid),
    }
    if full:
        result.update({
            "links": int(info.st_nlink), "size": int(info.st_size),
            "mtime_ns": int(info.st_mtime_ns), "ctime_ns": int(info.st_ctime_ns),
        })
    return result


def _matches(info: os.stat_result, expected: Identity, *, directory: bool) -> bool:
    if directory != stat.S_ISDIR(info.st_mode):
        return False
    if not directory and not stat.S_ISREG(info.st_mode):
        return False
    observed: tuple[int | None, ...] = (
        info.st_dev, info.st_ino, stat.S_IMODE(info.st_mode), info.st_uid,
        info.st_nlink if expected.links is not None else None,
        info.st_size if expected.size is not None else None,
        info.st_mtime_ns if expected.mtime_ns is not None else None,
        info.st_ctime_ns if expected.ctime_ns is not None else None,
    )
    wanted = (
        expected.device, expected.inode, expected.mode, expected.uid,
        expected.links, expected.size, expected.mtime_ns, expected.ctime_ns,
    )
    return observed == wanted


def _open_chain(path: Path) -> list[int]:
    target = _absolute(path / "sentinel").parent
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW
    chain = [os.open("/", flags)]
    try:
        for component in target.parts[1:]:
            child = os.open(component, flags, dir_fd=chain[-1])
            info = os.fstat(child)
            if not stat.S_ISDIR(info.st_mode) or info.st_uid not in {
                0, os.geteuid(),
            }:
                os.close(child)
                raise QuarantineGuardError("bound ancestor metadata is unsafe")
            chain.append(child)
        return chain
    except BaseException:
        for descriptor in reversed(chain):
            os.close(descriptor)
        raise


def _replay_chain(path: Path, chain: Sequence[int]) -> None:
    parts = path.parts[1:]
    if len(chain) != len(parts) + 1:
        raise QuarantineGuardError("bound ancestor chain length changed")
    for index, component in enumerate(parts, start=1):
        edge = os.stat(component, dir_fd=chain[index - 1], follow_symlinks=False)
        held = os.fstat(chain[index])
        if (
            not stat.S_ISDIR(edge.st_mode)
            or (edge.st_dev, edge.st_ino) != (held.st_dev, held.st_ino)
        ):
            raise QuarantineGuardError("bound ancestor edge changed")


def _open_absolute(path: Path, expected: Identity, *, directory: bool) -> HeldPath:
    target = _absolute(path)
    chain = _open_chain(target.parent)
    descriptor = -1
    flags = os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW
    if directory:
        flags |= os.O_DIRECTORY
    try:
        descriptor = os.open(target.name, flags, dir_fd=chain[-1])
        info = os.fstat(descriptor)
        if not _matches(info, expected, directory=directory):
            raise QuarantineGuardError(f"bound identity changed: {target}")
        result = HeldPath(target, chain, descriptor, expected, directory)
        _replay_path(result)
        return result
    except BaseException:
        if descriptor >= 0:
            os.close(descriptor)
        for item in reversed(chain):
            os.close(item)
        raise


def _open_relative(root: HeldPath, relative: str, expected: Identity) -> HeldPath:
    value = _relative(relative)
    parts = Path(value).parts
    chain = [os.dup(root.descriptor)]
    descriptor = -1
    try:
        for component in parts[:-1]:
            child = os.open(
                component,
                os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW,
                dir_fd=chain[-1],
            )
            info = os.fstat(child)
            if not stat.S_ISDIR(info.st_mode) or info.st_uid != os.geteuid():
                os.close(child)
                raise QuarantineGuardError("root-relative ancestor is unsafe")
            chain.append(child)
        descriptor = os.open(
            parts[-1], os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW,
            dir_fd=chain[-1],
        )
        info = os.fstat(descriptor)
        if not _matches(info, expected, directory=False):
            raise QuarantineGuardError(f"root-relative identity changed: {value}")
        held = HeldPath(root.path / value, chain, descriptor, expected, False)
        _replay_relative(root, held, value)
        return held
    except BaseException:
        if descriptor >= 0:
            os.close(descriptor)
        for item in reversed(chain):
            os.close(item)
        raise


def _replay_path(held: HeldPath) -> None:
    _replay_chain(held.path.parent, held.chain)
    edge = os.stat(held.path.name, dir_fd=held.chain[-1], follow_symlinks=False)
    current = os.fstat(held.descriptor)
    if (
        (edge.st_dev, edge.st_ino) != (current.st_dev, current.st_ino)
        or not _matches(current, held.expected, directory=held.directory)
    ):
        raise QuarantineGuardError(f"bound pathname changed: {held.path}")


def _replay_relative(root: HeldPath, held: HeldPath, relative: str) -> None:
    _replay_path(root)
    parts = Path(relative).parts
    if len(held.chain) != len(parts):
        raise QuarantineGuardError("root-relative chain length changed")
    previous = root.descriptor
    for index, component in enumerate(parts[:-1]):
        edge = os.stat(component, dir_fd=previous, follow_symlinks=False)
        current = os.fstat(held.chain[index + 1])
        if (
            not stat.S_ISDIR(edge.st_mode)
            or (edge.st_dev, edge.st_ino) != (current.st_dev, current.st_ino)
        ):
            raise QuarantineGuardError("root-relative ancestor edge changed")
        previous = held.chain[index + 1]
    edge = os.stat(parts[-1], dir_fd=held.chain[-1], follow_symlinks=False)
    current = os.fstat(held.descriptor)
    if (
        (edge.st_dev, edge.st_ino) != (current.st_dev, current.st_ino)
        or not _matches(current, held.expected, directory=False)
    ):
        raise QuarantineGuardError("root-relative bound pathname changed")


def _digest_descriptor(descriptor: int, expected_size: int) -> str:
    position = os.lseek(descriptor, 0, os.SEEK_CUR)
    try:
        os.lseek(descriptor, 0, os.SEEK_SET)
        digest = hashlib.sha256()
        remaining = expected_size
        while remaining:
            chunk = os.read(descriptor, min(1 << 20, remaining))
            if not chunk:
                raise QuarantineGuardError("bound file was truncated during hash")
            digest.update(chunk)
            remaining -= len(chunk)
        if os.read(descriptor, 1):
            raise QuarantineGuardError("bound file grew during hash")
        return digest.hexdigest()
    finally:
        os.lseek(descriptor, position, os.SEEK_SET)


def _close_path(held: HeldPath | None) -> None:
    if held is None:
        return
    try:
        os.close(held.descriptor)
    except OSError:
        pass
    for item in reversed(held.chain):
        try:
            os.close(item)
        except OSError:
            pass


def close(held: HeldQuarantine | None) -> None:
    if held is None:
        return
    try:
        fcntl.flock(held.lock.descriptor, fcntl.LOCK_UN)
    except OSError:
        pass
    for item in (
        held.checker, held.cube, held.proof, held.lock, held.root, held.manifest,
    ):
        _close_path(item)


def _load_manifest(path: Path, expected_sha256: str) -> tuple[HeldPath, dict[str, Any]]:
    if not _HEX.fullmatch(expected_sha256):
        raise QuarantineGuardError("manifest SHA-256 is malformed")
    target = _absolute(path)
    info = os.stat(target, follow_symlinks=False)
    if (
        not stat.S_ISREG(info.st_mode) or info.st_uid != os.geteuid()
        or info.st_nlink != 1 or not 1 <= info.st_size <= MAX_MANIFEST_BYTES
    ):
        raise QuarantineGuardError("manifest metadata is unsafe")
    held = _open_absolute(target, _identity(identity_record(info, full=True), full=True), directory=False)
    try:
        payload_sha = _digest_descriptor(held.descriptor, info.st_size)
        if payload_sha != expected_sha256:
            raise QuarantineGuardError("manifest file SHA-256 changed")
        os.lseek(held.descriptor, 0, os.SEEK_SET)
        payload = os.read(held.descriptor, info.st_size)
        try:
            value = json.loads(payload)
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise QuarantineGuardError("manifest is not canonical JSON") from exc
        if type(value) is not dict or manifest_payload(value) != payload:
            raise QuarantineGuardError("manifest bytes are not canonical")
        record_sha = value.get("record_sha256")
        unsigned = dict(value)
        unsigned.pop("record_sha256", None)
        if (
            not isinstance(record_sha, str) or not _HEX.fullmatch(record_sha)
            or hashlib.sha256(_canonical(unsigned)).hexdigest() != record_sha
        ):
            raise QuarantineGuardError("manifest record seal is invalid")
        return held, value
    except BaseException:
        _close_path(held)
        raise


def _entry(manifest: Mapping[str, Any], entry_id: str) -> Mapping[str, Any]:
    if manifest.get("schema_version") != 1 or manifest.get("kind") != SCHEMA:
        raise QuarantineGuardError("manifest schema is not admitted")
    if manifest.get("bad_checker_sha256") != BAD_CHECKER_SHA256:
        raise QuarantineGuardError("manifest does not bind the known-bad checker")
    if not _ENTRY_ID.fullmatch(entry_id):
        raise QuarantineGuardError("entry id is malformed")
    entries = manifest.get("entries")
    if type(entries) is not list or not entries:
        raise QuarantineGuardError("manifest entries are absent")
    matches = [item for item in entries if type(item) is dict and item.get("id") == entry_id]
    if len(matches) != 1 or len({item.get("id") for item in entries if type(item) is dict}) != len(entries):
        raise QuarantineGuardError("manifest entry ids are absent or ambiguous")
    result = matches[0]
    incident = result.get("incident")
    if (
        result.get("quarantine_enabled") is not True
        or type(incident) is not dict
        or _natural(incident.get("deterministic_attempts"), "attempt count") < 3
        or incident.get("signal") != 11
        or incident.get("all_same_proof_cube_checker") is not True
        or result.get("alternative_certification") != "none"
    ):
        raise QuarantineGuardError("entry is not an admitted deterministic crash quarantine")
    absent = result.get("required_absent_relative_paths")
    if (
        type(absent) is not list or any(type(item) is not str for item in absent)
        or not REQUIRED_ABSENT.issubset(absent)
        or len(set(absent)) != len(absent)
    ):
        raise QuarantineGuardError("entry terminal-absence set is incomplete")
    return result


def _file_spec(value: Any, *, role: str) -> tuple[str, Identity, str]:
    if type(value) is not dict:
        raise QuarantineGuardError(f"{role} specification is absent")
    relative = _relative(value.get("relative_path"))
    expected = _identity(value.get("identity"), full=True)
    digest = value.get("sha256")
    if type(digest) is not str or not _HEX.fullmatch(digest):
        raise QuarantineGuardError(f"{role} SHA-256 is malformed")
    return relative, expected, digest


def _assert_absent(root: HeldPath, relative_paths: Sequence[str]) -> None:
    for raw in relative_paths:
        relative = _relative(raw)
        parts = Path(relative).parts
        directories = [os.dup(root.descriptor)]
        try:
            for component in parts[:-1]:
                try:
                    child = os.open(
                        component,
                        os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC
                        | os.O_NOFOLLOW,
                        dir_fd=directories[-1],
                    )
                except OSError as exc:
                    raise QuarantineGuardError(
                        "terminal-absence ancestor is unavailable or unsafe"
                    ) from exc
                info = os.fstat(child)
                if not stat.S_ISDIR(info.st_mode) or info.st_uid != os.geteuid():
                    os.close(child)
                    raise QuarantineGuardError(
                        "terminal-absence ancestor metadata is unsafe"
                    )
                directories.append(child)
            try:
                os.stat(
                    parts[-1], dir_fd=directories[-1], follow_symlinks=False,
                )
            except FileNotFoundError:
                # Prove that every traversed edge still names the descriptor
                # under which absence was observed.  O_NOFOLLOW above prevents
                # a substituted state-directory symlink from hiding a terminal.
                previous = root.descriptor
                for index, component in enumerate(parts[:-1], start=1):
                    edge = os.stat(
                        component, dir_fd=previous, follow_symlinks=False,
                    )
                    held = os.fstat(directories[index])
                    if (
                        not stat.S_ISDIR(edge.st_mode)
                        or (edge.st_dev, edge.st_ino)
                        != (held.st_dev, held.st_ino)
                    ):
                        raise QuarantineGuardError(
                            "terminal-absence ancestor edge changed"
                        )
                    previous = directories[index]
                continue
            raise QuarantineGuardError(
                f"terminal/quarantine-exit artifact exists: {relative}"
            )
        finally:
            for descriptor in reversed(directories):
                os.close(descriptor)


def acquire(manifest_path: Path, manifest_sha256: str, entry_id: str) -> HeldQuarantine:
    manifest_held: HeldPath | None = None
    root: HeldPath | None = None
    lock: HeldPath | None = None
    proof: HeldPath | None = None
    cube: HeldPath | None = None
    checker: HeldPath | None = None
    result: HeldQuarantine | None = None
    try:
        manifest_held, manifest = _load_manifest(manifest_path, manifest_sha256)
        value = _entry(manifest, entry_id)
        root = _open_absolute(
            _absolute(Path(value.get("root"))),
            _identity(value.get("root_identity"), full=False),
            directory=True,
        )
        lock_rel, lock_identity, lock_sha = _file_spec(value.get("lock"), role="lock")
        if (
            lock_rel != ".hierarchical-resume.lock" or lock_identity.size != 0
            or lock_sha != hashlib.sha256(b"").hexdigest()
        ):
            raise QuarantineGuardError("entry does not bind the hierarchy lock sentinel")
        lock = _open_relative(root, lock_rel, lock_identity)
        try:
            fcntl.flock(lock.descriptor, fcntl.LOCK_SH | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise QuarantineBusyError("hierarchy lock is exclusively busy") from exc
        _FAULT_HOOK("after_shared_lock", lock.path)
        proof_rel, proof_identity, _proof_sha = _file_spec(value.get("proof"), role="proof")
        if (
            proof_rel != "runtime/dmtcp/proof.drat"
            or value["proof"].get("content_hash_replay") != "journal-bound-stat-only"
        ):
            raise QuarantineGuardError("large-proof hash replay policy is not explicit")
        proof = _open_relative(root, proof_rel, proof_identity)
        cube_rel, cube_identity, cube_sha = _file_spec(value.get("cube"), role="cube")
        if cube_rel != "static/cube.cnf":
            raise QuarantineGuardError("entry does not bind the static cube pathname")
        cube = _open_relative(root, cube_rel, cube_identity)
        if _digest_descriptor(cube.descriptor, cube_identity.size or 0) != cube_sha:
            raise QuarantineGuardError("cube SHA-256 changed")
        checker_value = value.get("checker")
        if type(checker_value) is not dict:
            raise QuarantineGuardError("checker specification is absent")
        checker_sha = checker_value.get("sha256")
        if checker_sha != BAD_CHECKER_SHA256:
            raise QuarantineGuardError("entry checker differs from known-bad checker")
        checker = _open_absolute(
            _absolute(Path(checker_value.get("path"))),
            _identity(checker_value.get("identity"), full=True),
            directory=False,
        )
        if _digest_descriptor(checker.descriptor, checker.expected.size or 0) != checker_sha:
            raise QuarantineGuardError("checker SHA-256 changed")
        absent = tuple(value["required_absent_relative_paths"])
        _assert_absent(root, absent)
        result = HeldQuarantine(
            entry_id, manifest_held, root, lock, proof, cube, checker, absent,
        )
        replay(result)
        return result
    except BaseException:
        if result is not None:
            close(result)
        else:
            if lock is not None:
                try:
                    fcntl.flock(lock.descriptor, fcntl.LOCK_UN)
                except OSError:
                    pass
            for item in (checker, cube, proof, lock, root, manifest_held):
                _close_path(item)
        raise


def replay(held: HeldQuarantine) -> None:
    _replay_path(held.manifest)
    _replay_path(held.root)
    _replay_relative(held.root, held.lock, ".hierarchical-resume.lock")
    proof_rel = str(held.proof.path.relative_to(held.root.path))
    cube_rel = str(held.cube.path.relative_to(held.root.path))
    _replay_relative(held.root, held.proof, proof_rel)
    _replay_relative(held.root, held.cube, cube_rel)
    _replay_path(held.checker)
    _assert_absent(held.root, held.absent_relative_paths)


def _notify_ready(held: HeldQuarantine) -> None:
    address = os.environ.get("NOTIFY_SOCKET")
    if not address:
        raise QuarantineGuardError("systemd notify socket is absent")
    if address.startswith("@"):
        address = "\0" + address[1:]
    channel = socket.socket(socket.AF_UNIX, socket.SOCK_DGRAM | socket.SOCK_CLOEXEC)
    try:
        channel.connect(address)
        channel.sendall(
            f"READY=1\nSTATUS=quarantined {held.entry_id}; periodic identity replay active\n".encode("ascii")
        )
    except OSError as exc:
        raise QuarantineGuardError("cannot notify systemd after identity replay") from exc
    finally:
        channel.close()


def hold(
    manifest_path: Path, manifest_sha256: str, entry_id: str, *,
    replay_seconds: float = 1.0,
) -> None:
    if type(replay_seconds) not in {int, float} or not 0.1 <= float(replay_seconds) <= 60.0:
        raise QuarantineGuardError("identity replay interval is unsafe")
    held = acquire(manifest_path, manifest_sha256, entry_id)
    try:
        # acquire() already completed one full replay.  This second replay is
        # intentionally adjacent to READY so no partially checked guard is active.
        replay(held)
        _notify_ready(held)
        while True:
            time.sleep(float(replay_seconds))
            replay(held)
    finally:
        close(held)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--manifest-sha256", required=True)
    parser.add_argument("--entry-id", required=True)
    parser.add_argument("--replay-seconds", type=float, default=1.0)
    parser.add_argument("--version", action="version", version=GATE)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    hold(
        args.manifest, args.manifest_sha256, args.entry_id,
        replay_seconds=args.replay_seconds,
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except QuarantineBusyError as exc:
        print(f"BUSY: {exc}", file=sys.stderr)
        raise SystemExit(EX_TEMPFAIL)
    except (QuarantineGuardError, OSError, ValueError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
