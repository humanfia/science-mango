#!/usr/bin/env python3
"""Render independent, source-bound DRAT SIGSEGV quarantine units.

The renderer has no systemd control code: it cannot install, enable, start,
stop or reload a unit.  It consumes one already sealed incident manifest and
writes review candidates into an explicit, existing private directory.  Each
enabled manifest entry becomes a separate ``Type=notify`` service, so a root
whose exclusive checker is still active retries later without blocking guards
for idle roots.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import sys
from typing import Any


PROJECT = Path(__file__).resolve().parent.parent
GUARD = PROJECT / "scripts/paper400_drat_segv_quarantine_guard_v1.py"
SCHEMA = "paper400-drat-segv-quarantine-manifest-v1"
TARGET_NAME = "paper400-drat-segv-quarantine-v1.target"
MAX_SOURCE_BYTES = 16 << 20
MAX_MANIFEST_BYTES = 4 << 20
_ENTRY_ID = re.compile(r"[a-z0-9][a-z0-9-]{0,63}\Z")
_SAFE_PATH = re.compile(r"/[A-Za-z0-9._/-]+\Z")
_HEX = re.compile(r"[0-9a-f]{64}\Z")


class QuarantineRenderError(RuntimeError):
    """A source, manifest or candidate violated the render contract."""


_LOADER = b'''import hashlib,os,stat,sys
p,h=sys.argv[1:3]
if not p.startswith("/") or os.path.abspath(p)!=p:
 raise SystemExit(125)
D=os.O_RDONLY|os.O_DIRECTORY|os.O_CLOEXEC|os.O_NOFOLLOW
chain=[os.open("/",D)];fd=-1
try:
 parts=[x for x in p.split("/") if x]
 for part in parts[:-1]:
  child=os.open(part,D,dir_fd=chain[-1]);info=os.fstat(child)
  if not stat.S_ISDIR(info.st_mode) or info.st_uid not in (0,os.geteuid()):
   os.close(child);raise SystemExit(125)
  chain.append(child)
 fd=os.open(parts[-1],os.O_RDONLY|os.O_CLOEXEC|os.O_NOFOLLOW,dir_fd=chain[-1])
 before=os.fstat(fd)
 if not stat.S_ISREG(before.st_mode) or before.st_uid!=os.geteuid() or before.st_nlink!=1 or not 1<=before.st_size<=16777216:
  raise SystemExit(125)
 data=b""
 while len(data)<before.st_size:
  chunk=os.read(fd,min(1048576,before.st_size-len(data)))
  if not chunk: raise SystemExit(125)
  data+=chunk
 after=os.fstat(fd)
 for index,part in enumerate(parts[:-1]):
  edge=os.stat(part,dir_fd=chain[index],follow_symlinks=False);held=os.fstat(chain[index+1])
  if not stat.S_ISDIR(edge.st_mode) or (edge.st_dev,edge.st_ino)!=(held.st_dev,held.st_ino): raise SystemExit(125)
 edge=os.stat(parts[-1],dir_fd=chain[-1],follow_symlinks=False)
 if os.read(fd,1) or hashlib.sha256(data).hexdigest()!=h or (before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns,before.st_ctime_ns)!=(after.st_dev,after.st_ino,after.st_size,after.st_mtime_ns,after.st_ctime_ns) or (edge.st_dev,edge.st_ino)!=(before.st_dev,before.st_ino):
  raise SystemExit(125)
 sys.argv=[p]+sys.argv[3:]
 scope={"__name__":"__main__","__file__":p,"__package__":None,"__cached__":None,"__builtins__":__builtins__}
 exec(compile(data,p,"exec"),scope,scope)
finally:
 if fd>=0: os.close(fd)
 for item in reversed(chain): os.close(item)
'''


def _canonical(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
        allow_nan=False,
    ).encode("ascii")


def _identity(info: os.stat_result) -> tuple[int, ...]:
    return (
        info.st_dev, info.st_ino, info.st_mode, info.st_uid, info.st_nlink,
        info.st_size, info.st_mtime_ns, info.st_ctime_ns,
    )


def _read_stable(path: Path, *, limit: int, executable: bool | None) -> tuple[bytes, os.stat_result]:
    if not path.is_absolute() or str(path) != os.path.abspath(str(path)):
        raise QuarantineRenderError("bound input path is not absolute/normalized")
    descriptor = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        before = os.fstat(descriptor)
        if (
            not stat.S_ISREG(before.st_mode) or before.st_uid != os.geteuid()
            or before.st_nlink != 1 or not 1 <= before.st_size <= limit
            or (
                executable is not None
                and bool(stat.S_IMODE(before.st_mode) & 0o111) is not executable
            )
        ):
            raise QuarantineRenderError(f"bound input metadata is unsafe: {path}")
        chunks: list[bytes] = []
        remaining = before.st_size
        while remaining:
            chunk = os.read(descriptor, min(1 << 20, remaining))
            if not chunk:
                raise QuarantineRenderError(f"bound input was truncated: {path}")
            chunks.append(chunk)
            remaining -= len(chunk)
        if os.read(descriptor, 1):
            raise QuarantineRenderError(f"bound input grew: {path}")
        after = os.fstat(descriptor)
        edge = os.stat(path, follow_symlinks=False)
        if _identity(before) != _identity(after) or _identity(before) != _identity(edge):
            raise QuarantineRenderError(f"bound input pathname changed: {path}")
        return b"".join(chunks), before
    finally:
        os.close(descriptor)


def load_manifest(path: Path) -> tuple[dict[str, Any], bytes, str]:
    payload, _info = _read_stable(path, limit=MAX_MANIFEST_BYTES, executable=False)
    try:
        value = json.loads(payload)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise QuarantineRenderError("manifest is not JSON") from exc
    if type(value) is not dict or _canonical(value) + b"\n" != payload:
        raise QuarantineRenderError("manifest is not canonical")
    record_sha = value.get("record_sha256")
    unsigned = dict(value)
    unsigned.pop("record_sha256", None)
    if (
        value.get("schema_version") != 1 or value.get("kind") != SCHEMA
        or not isinstance(record_sha, str) or not _HEX.fullmatch(record_sha)
        or hashlib.sha256(_canonical(unsigned)).hexdigest() != record_sha
    ):
        raise QuarantineRenderError("manifest seal/schema is invalid")
    entries = value.get("entries")
    if type(entries) is not list or not entries:
        raise QuarantineRenderError("manifest has no entries")
    ids: list[str] = []
    for entry in entries:
        if type(entry) is not dict or not isinstance(entry.get("id"), str):
            raise QuarantineRenderError("manifest entry is malformed")
        entry_id = entry["id"]
        if not _ENTRY_ID.fullmatch(entry_id):
            raise QuarantineRenderError("manifest entry id is unsafe")
        if entry.get("quarantine_enabled") is not True:
            raise QuarantineRenderError(
                f"entry {entry_id} is not explicitly enabled for quarantine"
            )
        if entry.get("alternative_certification") != "none":
            raise QuarantineRenderError(
                f"entry {entry_id} has an alternate certification path"
            )
        ids.append(entry_id)
    if len(set(ids)) != len(ids):
        raise QuarantineRenderError("manifest entry ids are duplicated")
    return value, payload, hashlib.sha256(payload).hexdigest()


def unit_name(entry_id: str) -> str:
    if not _ENTRY_ID.fullmatch(entry_id):
        raise QuarantineRenderError("unit entry id is unsafe")
    return f"paper400-drat-segv-quarantine-{entry_id}-v1.service"


def anchor_name(entry_id: str) -> str:
    if not _ENTRY_ID.fullmatch(entry_id):
        raise QuarantineRenderError("anchor entry id is unsafe")
    return f"paper400-drat-segv-quarantine-{entry_id}-v1.target"


def _quote(value: str) -> str:
    if "\n" in value or "\r" in value or "\x00" in value:
        raise QuarantineRenderError("systemd argument contains control bytes")
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"').replace("%", "%%") + '"'


def unit_payload(
    entry_id: str, manifest_path: Path, manifest_sha256: str,
    guard_sha256: str,
) -> bytes:
    if not _SAFE_PATH.fullmatch(str(manifest_path)) or not _SAFE_PATH.fullmatch(str(GUARD)):
        raise QuarantineRenderError("unit path contains unsafe characters")
    if not _HEX.fullmatch(manifest_sha256) or not _HEX.fullmatch(guard_sha256):
        raise QuarantineRenderError("unit digest is malformed")
    loader = base64.b64encode(_LOADER).decode("ascii")
    command = " ".join([
        "/usr/bin/env", "-i",
        "HOME=/home/jing", "LANG=C.UTF-8", "LC_ALL=C.UTF-8",
        "LOGNAME=jing", "PATH=/usr/bin:/bin", "PYTHONDONTWRITEBYTECODE=1",
        "PYTHONNOUSERSITE=1", "PYTHONPYCACHEPREFIX=/dev/null",
        "PYTHONSAFEPATH=1", "USER=jing", "XDG_RUNTIME_DIR=/run/user/1001",
        "NOTIFY_SOCKET=${NOTIFY_SOCKET}",
        "/usr/bin/python3", "-I", "-S", "-B", "-c",
        _quote(f"import base64;exec(compile(base64.b64decode('{loader}'),'<paper400-drat-segv-quarantine-source-loader-v1>','exec'))"),
        _quote(str(GUARD)), guard_sha256,
        "--manifest", _quote(str(manifest_path)),
        "--manifest-sha256", manifest_sha256,
        "--entry-id", entry_id,
        "--replay-seconds", "1",
    ])
    anchor = anchor_name(entry_id)
    return f"""[Unit]
Description=Paper400 deterministic DRAT SIGSEGV quarantine ({entry_id})
Documentation=file://{manifest_path}
StartLimitIntervalSec=0
PartOf={anchor}
RefuseManualStart=yes
RefuseManualStop=yes

[Service]
Type=notify
NotifyAccess=main
ExecStart={command}
Restart=always
RestartSec=5s
TimeoutStartSec=30s
KillMode=process
UMask=0077
NoNewPrivileges=yes
PrivateDevices=yes
PrivateTmp=yes
PrivateNetwork=yes
ProtectSystem=strict
ProtectHome=read-only
ProtectControlGroups=yes
ProtectKernelModules=yes
ProtectKernelTunables=yes
ProtectKernelLogs=yes
ProtectClock=yes
ProtectHostname=yes
CapabilityBoundingSet=
AmbientCapabilities=
RestrictAddressFamilies=AF_UNIX
RestrictNamespaces=yes
RestrictRealtime=yes
RestrictSUIDSGID=yes
LockPersonality=yes
MemoryDenyWriteExecute=yes
SystemCallArchitectures=native

[Install]
WantedBy={anchor}
""".encode("utf-8")


def anchor_payload(entry_id: str) -> bytes:
    service = unit_name(entry_id)
    return f"""[Unit]
Description=Paper400 DRAT SIGSEGV quarantine anchor ({entry_id})
Wants={service}
Upholds={service}
StopWhenUnneeded=no
RefuseManualStop=yes
""".encode("utf-8")


def target_payload(anchors: list[str]) -> bytes:
    units = " ".join(anchors)
    return f"""[Unit]
Description=Paper400 deterministic DRAT SIGSEGV quarantine guards v1
Wants={units}
StopWhenUnneeded=no
RefuseManualStop=yes

[Install]
WantedBy=default.target
""".encode("utf-8")


def candidates(manifest_path: Path) -> dict[str, bytes]:
    value, _manifest_payload, manifest_sha = load_manifest(manifest_path)
    guard_payload, _guard_info = _read_stable(
        GUARD, limit=MAX_SOURCE_BYTES, executable=False,
    )
    guard_sha = hashlib.sha256(guard_payload).hexdigest()
    names = [unit_name(entry["id"]) for entry in value["entries"]]
    anchors = [anchor_name(entry["id"]) for entry in value["entries"]]
    result = {
        name: unit_payload(entry["id"], manifest_path, manifest_sha, guard_sha)
        for name, entry in zip(names, value["entries"], strict=True)
    }
    result.update({
        name: anchor_payload(entry["id"])
        for name, entry in zip(anchors, value["entries"], strict=True)
    })
    result[TARGET_NAME] = target_payload(anchors)
    return result


def _private_output(path: Path) -> None:
    if not path.is_absolute() or str(path) != os.path.abspath(str(path)):
        raise QuarantineRenderError("output directory is not absolute/normalized")
    info = os.stat(path, follow_symlinks=False)
    if (
        not stat.S_ISDIR(info.st_mode) or info.st_uid != os.geteuid()
        or stat.S_IMODE(info.st_mode) != 0o700
    ):
        raise QuarantineRenderError("output directory is not private and owned")


def write_candidates(manifest_path: Path, output_directory: Path) -> list[Path]:
    _private_output(output_directory)
    payloads = candidates(manifest_path)
    if any((output_directory / name).exists() for name in payloads):
        raise QuarantineRenderError("one candidate output already exists")
    written: list[Path] = []
    try:
        for name, payload in payloads.items():
            path = output_directory / name
            descriptor = os.open(
                path,
                os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW,
                0o600,
            )
            try:
                view = memoryview(payload)
                while view:
                    count = os.write(descriptor, view)
                    view = view[count:]
                os.fsync(descriptor)
            finally:
                os.close(descriptor)
            written.append(path)
        directory_fd = os.open(output_directory, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
        return written
    except BaseException:
        for path in reversed(written):
            try:
                path.unlink()
            except FileNotFoundError:
                pass
        raise


def check_candidates(manifest_path: Path, output_directory: Path) -> None:
    _private_output(output_directory)
    expected = candidates(manifest_path)
    for name, payload in expected.items():
        observed, _info = _read_stable(
            output_directory / name, limit=16 << 20, executable=False,
        )
        if observed != payload:
            raise QuarantineRenderError(f"candidate bytes changed: {name}")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--write", action="store_true")
    action.add_argument("--check", action="store_true")
    action.add_argument("--verify", action="store_true")
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output-directory", type=Path)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.verify:
        if args.output_directory is not None:
            raise QuarantineRenderError("manifest verification accepts no output")
        candidates(args.manifest)
    else:
        if args.output_directory is None:
            raise QuarantineRenderError("candidate action requires output directory")
        if args.write:
            write_candidates(args.manifest, args.output_directory)
        else:
            check_candidates(args.manifest, args.output_directory)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (QuarantineRenderError, OSError, ValueError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
