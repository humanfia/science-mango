#!/usr/bin/env python3
"""Render, but never install or start, the source-bound c0084 guard unit.

The admission binds the reviewed 57-attempt quarantine manifest, the exact
58th and 59th SIGSEGV journal result chains, the legacy 00/10/11/start.commit
chain, the absent legacy PIDs, and the absence of terminal/prune artifacts.
The service retries exit 75 while a legacy harvest owns the hierarchy lock;
it never signals that harvest or the independent saturator.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
import stat
import sys
from pathlib import Path
from typing import Any, Mapping


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from scripts import paper400_c0084_inactive_checker_crash_guard_v1 as guard
from scripts import paper400_drat_segv_quarantine_guard_v1 as quarantine
from scripts import render_paper400_drat_segv_quarantine_v1 as base_renderer


ADMISSION_PATH = (
    PROJECT / "deploy/paper400/systemd/"
    "paper400-c0084-inactive-checker-crash-admission-v1.json"
)
UNIT_NAME = "paper400-c0084-inactive-checker-crash-guard-v1.service"
UNIT_PATH = PROJECT / "deploy/paper400/systemd" / UNIT_NAME
MAX_SOURCE_BYTES = 16 << 20


class C0084GuardRenderError(RuntimeError):
    """A production input or rendered byte changed from the reviewed scope."""


def _canonical(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
        allow_nan=False,
    ).encode("ascii")


def _identity(info: os.stat_result) -> tuple[int, ...]:
    return (
        int(info.st_dev), int(info.st_ino), int(info.st_mode),
        int(info.st_uid), int(info.st_nlink), int(info.st_size),
        int(info.st_mtime_ns), int(info.st_ctime_ns),
    )


def _stable_bytes(
    path: Path, *, limit: int, executable: bool,
) -> tuple[bytes, os.stat_result]:
    target = Path(path)
    if not target.is_absolute() or str(target) != os.path.abspath(str(target)):
        raise C0084GuardRenderError("renderer input is not absolute/normalized")
    descriptor = os.open(
        target, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW,
    )
    try:
        before = os.fstat(descriptor)
        if (
            not stat.S_ISREG(before.st_mode)
            or before.st_uid != os.geteuid()
            or before.st_nlink != 1
            or not 1 <= before.st_size <= limit
            or bool(stat.S_IMODE(before.st_mode) & 0o111) is not executable
        ):
            raise C0084GuardRenderError(
                f"renderer input metadata is unsafe: {target}"
            )
        chunks: list[bytes] = []
        remaining = before.st_size
        while remaining:
            chunk = os.read(descriptor, min(1 << 20, remaining))
            if not chunk:
                raise C0084GuardRenderError("renderer input was truncated")
            chunks.append(chunk)
            remaining -= len(chunk)
        if os.read(descriptor, 1):
            raise C0084GuardRenderError("renderer input grew")
        after = os.fstat(descriptor)
        edge = os.stat(target, follow_symlinks=False)
        if _identity(before) != _identity(after) or _identity(before) != _identity(edge):
            raise C0084GuardRenderError("renderer input pathname changed")
        return b"".join(chunks), before
    finally:
        os.close(descriptor)


def _read_record(
    relative: str, *, self_hash_field: str,
) -> tuple[dict[str, Any], dict[str, Any]]:
    path = guard.EXPECTED_ROOT / relative
    data, info = _stable_bytes(
        path, limit=guard.MAX_SMALL_RECORD_BYTES, executable=False,
    )
    try:
        value = json.loads(data)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise C0084GuardRenderError("legacy bound record is not JSON") from exc
    if (
        type(value) is not dict
        or data not in {_canonical(value), _canonical(value) + b"\n"}
        or not guard._valid_seal(value, self_hash_field)
    ):
        raise C0084GuardRenderError(
            f"legacy bound record is not canonical/sealed: {relative}"
        )
    return value, {
        "relative_path": relative,
        "identity": quarantine.identity_record(info, full=True),
        "file_sha256": hashlib.sha256(data).hexdigest(),
        "self_hash_field": self_hash_field,
        "self_hash": value[self_hash_field],
    }


def _require_absent(relative: str) -> None:
    path = guard.EXPECTED_ROOT / relative
    try:
        os.stat(path, follow_symlinks=False)
    except FileNotFoundError:
        return
    except OSError as exc:
        raise C0084GuardRenderError(
            f"cannot establish terminal absence: {relative}"
        ) from exc
    raise C0084GuardRenderError(
        f"terminal/prune artifact already exists: {relative}"
    )


def _quarantine_material() -> tuple[dict[str, Any], dict[str, Any]]:
    data, _info = _stable_bytes(
        guard.EXPECTED_QUARANTINE_MANIFEST,
        limit=quarantine.MAX_MANIFEST_BYTES,
        executable=False,
    )
    if hashlib.sha256(data).hexdigest() != guard.EXPECTED_QUARANTINE_FILE_SHA256:
        raise C0084GuardRenderError("fixed quarantine manifest file hash changed")
    try:
        manifest = json.loads(data)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise C0084GuardRenderError("fixed quarantine manifest is not JSON") from exc
    if (
        type(manifest) is not dict
        or data != quarantine.manifest_payload(manifest)
        or manifest.get("record_sha256")
        != guard.EXPECTED_QUARANTINE_RECORD_SHA256
    ):
        raise C0084GuardRenderError("fixed quarantine manifest seal changed")
    try:
        entry = quarantine._entry(manifest, guard.EXPECTED_ENTRY_ID)
    except quarantine.QuarantineGuardError as exc:
        raise C0084GuardRenderError(str(exc)) from exc
    return manifest, dict(entry)


def admission_value() -> dict[str, Any]:
    manifest, entry = _quarantine_material()
    records: dict[str, dict[str, Any]] = {}
    values: dict[str, dict[str, Any]] = {}
    for role, relative in guard.REQUIRED_RECORD_PATHS.items():
        field = "self_sha256" if role == "controller_start" else "record_sha256"
        values[role], records[role] = _read_record(
            relative, self_hash_field=field,
        )
    stale_pids = guard._validate_record_chain(values)
    for pid in stale_pids:
        guard._pid_absent(pid)
    for relative in guard.REQUIRED_ABSENT:
        _require_absent(relative)

    proof_sha = entry.get("proof", {}).get("sha256")
    cube_sha = entry.get("cube", {}).get("sha256")
    checker_sha = entry.get("checker", {}).get("sha256")
    attempts = [
        {
            **dict(attempt),
            "proof_sha256": proof_sha,
            "cube_sha256": cube_sha,
            "checker_sha256": checker_sha,
            "exit_code": -11,
            "signal": 11,
            "drat_verified": False,
            "terminal_claim_created": False,
            "verification_retry_allowed": True,
        }
        for attempt in guard.EXPECTED_SUPPLEMENTAL_JOURNAL_ATTEMPTS
    ]
    admission = guard.seal({
        "schema_version": guard.SCHEMA_VERSION,
        "kind": guard.ADMISSION_KIND,
        "gate": guard.GATE,
        "root": str(guard.EXPECTED_ROOT),
        "global_child_id": "c0084",
        "global_child_index": guard.EXPECTED_CHILD_INDEX,
        "quarantine_binding": {
            "manifest_path": str(guard.EXPECTED_QUARANTINE_MANIFEST),
            "manifest_file_sha256": guard.EXPECTED_QUARANTINE_FILE_SHA256,
            "manifest_record_sha256": guard.EXPECTED_QUARANTINE_RECORD_SHA256,
            "entry_id": guard.EXPECTED_ENTRY_ID,
            "base_attempts": guard.EXPECTED_BASE_SIGSEGV_ATTEMPTS,
        },
        "records": records,
        "stale_processes": [
            {
                "role": "stage_claim", "pid": stale_pids[0],
                "expected_absent": True, "proc_start_ticks": None,
            },
            {
                "role": "solver", "pid": stale_pids[1],
                "expected_absent": True,
                "proc_start_ticks": values["controller_start"][
                    "proc_start_ticks"
                ],
            },
        ],
        "incident": {
            "base_attempts": guard.EXPECTED_BASE_SIGSEGV_ATTEMPTS,
            "supplemental_attempts": attempts,
            "total_attempts": (
                guard.EXPECTED_BASE_SIGSEGV_ATTEMPTS + len(attempts)
            ),
            "same_proof_cube_checker": True,
            "required_signal": 11,
            "proof_sha256": proof_sha,
            "cube_sha256": cube_sha,
            "checker_sha256": checker_sha,
            "proof_content_hash_replay": "journal-bound-stat-only",
        },
        "claim_scope": {
            "hardness_only": True,
            "solver_terminal_claim": False,
            "unsat_claim": False,
            "old_proof_certified": False,
            "recursive_children_require_fresh_proof": True,
            "terminal_publication_authorized": False,
            "root_guard_blocks_only_exclusive_legacy_actions": True,
            "saturator_stop_required": False,
        },
        "source_binding": guard.source_binding(),
    })
    guard._admission_schema(admission)
    guard._validate_incident(admission["incident"], manifest, entry)
    return admission


def admission_payload() -> bytes:
    return guard.payload(admission_value())


def _quote(value: str) -> str:
    if any(character in value for character in ("\n", "\r", "\x00")):
        raise C0084GuardRenderError("systemd argument contains control bytes")
    return (
        '"' + value.replace("\\", "\\\\").replace('"', '\\"')
        .replace("%", "%%") + '"'
    )


def unit_payload(admission: bytes) -> bytes:
    source, _info = _stable_bytes(
        Path(guard.__file__).resolve(strict=True),
        limit=MAX_SOURCE_BYTES,
        executable=False,
    )
    source_sha = hashlib.sha256(source).hexdigest()
    admission_sha = hashlib.sha256(admission).hexdigest()
    loader = base64.b64encode(base_renderer._LOADER).decode("ascii")
    loader_command = (
        "import base64;exec(compile(base64.b64decode("
        f"'{loader}'),'<paper400-c0084-guard-source-loader-v1>','exec'))"
    )
    command = " ".join([
        "/usr/bin/env", "-i",
        "HOME=/home/jing", "LANG=C.UTF-8", "LC_ALL=C.UTF-8",
        "LOGNAME=jing", "PATH=/usr/bin:/bin", "PYTHONDONTWRITEBYTECODE=1",
        "PYTHONNOUSERSITE=1", "PYTHONPYCACHEPREFIX=/dev/null",
        "PYTHONSAFEPATH=1", "USER=jing", "XDG_RUNTIME_DIR=/run/user/1001",
        "NOTIFY_SOCKET=${NOTIFY_SOCKET}",
        "/usr/bin/python3", "-I", "-S", "-B", "-c",
        _quote(loader_command),
        _quote(str(Path(guard.__file__).resolve(strict=True))), source_sha,
        "--admission", _quote(str(ADMISSION_PATH)),
        "--admission-sha256", admission_sha,
        "--replay-seconds", "1",
    ])
    return f"""[Unit]
Description=Paper400 c0084 inactive checker-crash shared root guard v1
Documentation=file://{ADMISSION_PATH}
StartLimitIntervalSec=0
RefuseManualStart=no
RefuseManualStop=yes

[Service]
Type=notify
NotifyAccess=main
ExecStart={command}
Restart=on-failure
RestartSec=5s
TimeoutStartSec=30s
TimeoutStopSec=10s
KillMode=process
UMask=0077
NoNewPrivileges=yes
PrivateTmp=yes
PrivateNetwork=yes
ProtectSystem=strict
ProtectHome=read-only
ProtectControlGroups=yes
ProtectHostname=yes
RestrictAddressFamilies=AF_UNIX
RestrictNamespaces=yes
RestrictRealtime=yes
RestrictSUIDSGID=yes
LockPersonality=yes
MemoryDenyWriteExecute=yes
SystemCallArchitectures=native

[Install]
WantedBy=default.target
""".encode("utf-8")


def rendered() -> dict[Path, bytes]:
    admission = admission_payload()
    return {
        ADMISSION_PATH: admission,
        UNIT_PATH: unit_payload(admission),
    }


def _replace(path: Path, payload: bytes) -> None:
    if not path.parent.is_dir() or path.parent.is_symlink():
        raise C0084GuardRenderError("candidate parent directory is unsafe")
    temporary = path.with_name(f".{path.name}.tmp-{os.getpid()}")
    descriptor = -1
    try:
        descriptor = os.open(
            temporary,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
            | os.O_NOFOLLOW,
            0o600,
        )
        view = memoryview(payload)
        while view:
            count = os.write(descriptor, view)
            view = view[count:]
        os.fsync(descriptor)
        os.close(descriptor)
        descriptor = -1
        os.replace(temporary, path)
        directory = os.open(
            path.parent,
            os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW,
        )
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        if descriptor >= 0:
            os.close(descriptor)
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def render(*, check: bool) -> bool:
    expected = rendered()
    if check:
        return all(
            path.is_file() and not path.is_symlink()
            and path.read_bytes() == payload
            for path, payload in expected.items()
        )
    for path, payload in expected.items():
        _replace(path, payload)
    return True


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    return 0 if render(check=args.check) else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        C0084GuardRenderError, guard.C0084RecoveryGuardError,
        quarantine.QuarantineGuardError, OSError, ValueError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
