#!/usr/bin/env python3
"""Run the final answer-blind Lean verifier under a dedicated non-root UID.

The trusted root controller owns this launcher and every receipt it publishes.
The Lean process receives no model credential and reads only the traversable,
root-owned verifier snapshot plus the sealed Lean/runtime dependency trees.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import pwd
import resource
import signal
import stat
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Any, NoReturn, Sequence

from archon.commands import blind_evaluation as blind


class VerifierControllerError(RuntimeError):
    pass


def _fail(message: str) -> NoReturn:
    raise VerifierControllerError(message)


def _json_bytes(value: Any) -> bytes:
    return (
        json.dumps(
            value, ensure_ascii=False, sort_keys=True,
            separators=(",", ":"), allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def _sha(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _root_dir(path: Path, *, label: str, traversable: bool = False) -> Path:
    if path.is_symlink() or not path.is_dir():
        _fail(f"{label} must be a plain directory")
    result = path.resolve(strict=True)
    metadata = result.stat(follow_symlinks=False)
    if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) & 0o022:
        _fail(f"{label} must be root-owned and not group/other writable")
    if traversable and stat.S_IMODE(metadata.st_mode) & 0o001 == 0:
        _fail(f"{label} must be world-traversable for the verifier UID")
    if traversable:
        for directory, names, files in os.walk(result, followlinks=False):
            base = Path(directory)
            if stat.S_IMODE(base.stat(follow_symlinks=False).st_mode) & 0o001 == 0:
                _fail(f"{label} contains a non-traversable directory: {base}")
            for name in files:
                child = base / name
                if not child.is_symlink() and (
                    stat.S_IMODE(child.stat(follow_symlinks=False).st_mode) & 0o004
                    == 0
                ):
                    _fail(f"{label} contains a non-readable file: {child}")
    return result


def _root_file(path: Path, *, label: str, executable: bool = False) -> Path:
    if path.is_symlink() or not path.is_file():
        _fail(f"{label} must be a plain file")
    result = path.resolve(strict=True)
    metadata = result.stat(follow_symlinks=False)
    if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) & 0o022:
        _fail(f"{label} must be root-owned and not group/other writable")
    if executable and not os.access(result, os.X_OK):
        _fail(f"{label} is not executable")
    return result


def _write_new(path: Path, payload: bytes, *, mode: int = 0o400) -> None:
    if path.exists() or path.is_symlink() or path.parent.is_symlink():
        _fail(f"controller output must be new: {path}")
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, mode)
    try:
        view = memoryview(payload)
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                _fail(f"short controller write: {path}")
            view = view[written:]
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    os.chown(path, 0, 0)
    os.chmod(path, mode)


def _uid_pids(uid: int) -> list[int]:
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


def _cleanup_uid(
    *, uid: int, rlimit_nproc: int = 64, quiet_period_ms: int = 500,
) -> dict[str, Any]:
    deadline = time.monotonic() + 10.0
    quiet_since: float | None = None
    kill_rounds = 0
    prlimit_ok = True
    pidfd_used = False
    while time.monotonic() < deadline:
        pids = _uid_pids(uid)
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
            try:
                pidfd = os.pidfd_open(pid, 0)
            except ProcessLookupError:
                continue
            try:
                signal.pidfd_send_signal(pidfd, signal.SIGKILL)
                pidfd_used = True
            except ProcessLookupError:
                pass
            finally:
                os.close(pidfd)
        time.sleep(0.025)
    after = _uid_pids(uid)
    return {
        "mechanism": "dedicated_uid_prlimit_pidfd_v1",
        "uid": uid,
        "rlimit_nproc": rlimit_nproc,
        "quiescent_before": True,
        "before_pids": [],
        "prlimit_zero_applied": prlimit_ok,
        "pidfd_kill_used": pidfd_used,
        "kill_rounds": kill_rounds,
        "quiet_period_ms": quiet_period_ms,
        "after_pids": after,
        "quiescent_after": not after,
    }


def run_verifier(
    *, snapshot_root: Path, controller_dir: Path, runtime_root: Path,
    dependency_root: Path, archon_executable: Path, lake_executable: Path,
    verifier_user: str, scratch_root: Path, output: Path,
    scope_ids: Sequence[str], timeout_s: int = 3600,
) -> dict[str, Any]:
    if os.geteuid() != 0:
        _fail("final verifier controller must run as root")
    if not scope_ids or list(scope_ids) != sorted(set(scope_ids)):
        _fail("verifier scope IDs must be a non-empty sorted unique list")
    if timeout_s < 1:
        _fail("verifier timeout must be positive")
    snapshot = _root_dir(snapshot_root, label="verifier snapshot", traversable=True)
    controller = _root_dir(controller_dir, label="verifier controller directory")
    runtime = _root_dir(runtime_root, label="answer-blind runtime", traversable=True)
    dependency = _root_dir(
        dependency_root, label="Lean dependency root", traversable=True,
    )
    scratch = _root_dir(scratch_root, label="verifier scratch root", traversable=True)
    for writable in (controller, scratch):
        for protected in (snapshot, runtime, dependency):
            if writable == protected or writable.is_relative_to(protected) or (
                protected.is_relative_to(writable)
            ):
                _fail("verifier writable and sealed roots must be disjoint")
    archon = _root_file(
        archon_executable, label="trusted Archon executable", executable=True,
    )
    lake = _root_file(
        lake_executable, label="trusted Lake executable", executable=True,
    )
    output_path = output.resolve()
    if output_path.parent != controller:
        _fail("verifier invocation output must be directly under controller-dir")

    identity = pwd.getpwnam(verifier_user)
    if identity.pw_uid == 0 or identity.pw_gid == 0:
        _fail("final verifier must use a non-root UID and GID")
    if _uid_pids(identity.pw_uid):
        _fail("dedicated verifier UID is not quiescent before invocation")

    dependency_files = blind._regular_file_inventory(
        dependency, label="verifier dependency inventory",
    )
    runtime_files = blind._regular_file_inventory(
        runtime, label="verifier runtime inventory", exclude_roots=(dependency,),
    )
    try:
        archon_relative = archon.relative_to(runtime).as_posix()
    except ValueError:
        _fail("trusted Archon executable must be inside the sealed runtime")
    if runtime_files.get(archon_relative) != _sha(archon.read_bytes()):
        _fail("trusted Archon executable is absent from the runtime inventory")
    snapshot_files = blind._project_snapshot_inventory(
        snapshot, dependency_root=dependency,
    )
    dependency_sha = blind._hash_index(dependency_files)
    runtime_sha = blind._hash_index(runtime_files)
    snapshot_sha = blind._hash_index(snapshot_files)
    try:
        archon_relative = archon.relative_to(runtime).as_posix()
        lake_relative = lake.relative_to(runtime).as_posix()
    except ValueError:
        _fail("verifier executables must be inside the sealed runtime root")
    for executable, relative, label in (
        (archon, archon_relative, "Archon"), (lake, lake_relative, "Lake"),
    ):
        if runtime_files.get(relative) != _sha(executable.read_bytes()):
            _fail(f"trusted {label} executable is absent from runtime inventory")

    private = Path(tempfile.mkdtemp(prefix="final-lean-", dir=scratch))
    os.chown(private, identity.pw_uid, identity.pw_gid)
    os.chmod(private, 0o700)
    raw_receipt = private / "lean-verifier-result.json"
    log_path = controller / f"{output_path.stem}.stdout.log"
    result_path = controller / f"{output_path.stem}.result.json"
    if any(path.exists() or path.is_symlink() for path in (log_path, result_path, output_path)):
        _fail("verifier controller outputs must all be new")
    argv = [
        str(archon), "blind-verify-lean",
        "--project", str(snapshot),
        "--candidate-dir", "blind_candidates",
        "--output", str(raw_receipt),
        "--runtime-executable", str(lake),
        "--runtime-root", str(runtime),
        "--dependency-root", str(dependency),
        "--expected-dependency-inventory-sha256", dependency_sha,
        "--expected-runtime-inventory-sha256", runtime_sha,
        "--expected-snapshot-inventory-sha256", snapshot_sha,
        "--timeout-s", str(timeout_s),
    ]
    for record_id in scope_ids:
        argv.extend(("--scope-id", record_id))

    def drop() -> None:
        os.setgroups([])
        resource.setrlimit(resource.RLIMIT_NPROC, (64, 64))
        os.setgid(identity.pw_gid)
        os.setuid(identity.pw_uid)
        os.umask(0o077)

    environment = {
        "HOME": str(private), "TMPDIR": str(private),
        "TMP": str(private), "TEMP": str(private),
        "PATH": f"{runtime / 'bin'}:{lake.parent}",
        "LANG": "C.UTF-8", "LC_ALL": "C.UTF-8", "TZ": "UTC",
        "PYTHONSAFEPATH": "1", "PYTHONNOUSERSITE": "1",
        "PYTHONDONTWRITEBYTECODE": "1",
    }
    descriptor = os.open(log_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    timed_out = False
    try:
        with os.fdopen(descriptor, "wb") as log:
            process = subprocess.Popen(
                argv, cwd=snapshot, env=environment, stdin=subprocess.DEVNULL,
                stdout=log, stderr=subprocess.STDOUT, start_new_session=True,
                preexec_fn=drop,
            )
            try:
                exit_code = process.wait(timeout=timeout_s + 60)
            except subprocess.TimeoutExpired:
                timed_out = True
                exit_code = -signal.SIGKILL
            quiescence = _cleanup_uid(uid=identity.pw_uid)
            try:
                process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                pass
            log.flush()
            os.fsync(log.fileno())
    finally:
        os.chown(log_path, 0, 0)
        os.chmod(log_path, 0o400)

    if timed_out or exit_code != 0:
        _fail(f"final Lean verifier exited unsuccessfully: {exit_code}")
    if not quiescence["prlimit_zero_applied"] or not quiescence["quiescent_after"]:
        _fail("final Lean verifier UID could not be proven quiescent")
    if not raw_receipt.is_file() or raw_receipt.is_symlink():
        _fail("final Lean verifier did not produce its semantic receipt")
    raw_payload = raw_receipt.read_bytes()
    try:
        raw_value = json.loads(raw_payload.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        _fail(f"final Lean verifier receipt is invalid JSON: {exc}")
    if not isinstance(raw_value, dict) or raw_value.get("verifier_uid") != identity.pw_uid:
        _fail("final Lean verifier receipt has stale UID provenance")
    blind._validate_verifier_receipt(raw_value, seal={
        "dependency_inventory": {"files_sha256": dependency_sha},
        "runtime_inventory": {
            "root": str(runtime), "files": runtime_files,
            "files_sha256": runtime_sha,
        },
        "snapshot_inventory": {"files_sha256": snapshot_sha},
        "freeze_scope": {"ids": list(scope_ids)},
    })
    if (
        blind._hash_index(blind._regular_file_inventory(
            dependency, label="post-verifier dependency inventory",
        )) != dependency_sha
        or blind._hash_index(blind._regular_file_inventory(
            runtime, label="post-verifier runtime inventory",
            exclude_roots=(dependency,),
        )) != runtime_sha
        or blind._hash_index(blind._project_snapshot_inventory(
            snapshot, dependency_root=dependency,
        )) != snapshot_sha
    ):
        _fail("sealed verifier inputs changed during verification")
    _write_new(result_path, raw_payload)
    try:
        raw_receipt.unlink()
        private.rmdir()
    except OSError:
        # A clean verifier should leave only its receipt.  Refuse to attest if
        # its private directory contains any unexpected state.
        _fail("final Lean verifier left unexpected private state")

    log_payload = log_path.read_bytes()
    wrapper = {
        "schema_version": 1,
        "protocol": blind.PROTOCOL,
        "phase": "lean_verifier_invocation",
        "verifier_uid": identity.pw_uid,
        "command_argv": argv,
        "exit_code": exit_code,
        "solver_stopped": True,
        "descendants_stopped": True,
        "network_answer_blind": False,
        "dependency_inventory_sha256": dependency_sha,
        "runtime_inventory_sha256": runtime_sha,
        "snapshot_inventory_sha256": snapshot_sha,
        "snapshot_root": str(snapshot),
        "dedicated_uid_quiescence": quiescence,
        "verifier_receipt": {
            "path": str(result_path), "sha256": _sha(raw_payload),
        },
        "stdout_log": {
            "path": str(log_path), "sha256": _sha(log_payload),
            "size": len(log_payload),
        },
    }
    _write_new(output_path, _json_bytes(wrapper))
    return wrapper


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snapshot-root", type=Path, required=True)
    parser.add_argument("--controller-dir", type=Path, required=True)
    parser.add_argument("--runtime-root", type=Path, required=True)
    parser.add_argument("--dependency-root", type=Path, required=True)
    parser.add_argument("--archon-executable", type=Path, required=True)
    parser.add_argument("--lake-executable", type=Path, required=True)
    parser.add_argument("--verifier-user", required=True)
    parser.add_argument("--scratch-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--scope-id", action="append", required=True)
    parser.add_argument("--timeout-s", type=int, default=3600)
    return parser


def main() -> int:
    args = _parser().parse_args()
    try:
        run_verifier(
            snapshot_root=args.snapshot_root,
            controller_dir=args.controller_dir,
            runtime_root=args.runtime_root,
            dependency_root=args.dependency_root,
            archon_executable=args.archon_executable,
            lake_executable=args.lake_executable,
            verifier_user=args.verifier_user,
            scratch_root=args.scratch_root,
            output=args.output,
            scope_ids=sorted(args.scope_id),
            timeout_s=args.timeout_s,
        )
    except VerifierControllerError as exc:
        raise SystemExit(f"error: {exc}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
