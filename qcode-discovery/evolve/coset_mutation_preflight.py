"""Hard-wall, data-only preflight for evolved coset policies.

The evolved payload is strict JSON.  It is never imported, compiled, or
executed as Python.  A short-lived, isolated-session child parses the policy
and renders catalog-bound candidates; the long-lived OpenEvolve evaluator
accepts only a bounded canonical-JSON response and independently revalidates
the resulting plain data.
"""

from __future__ import annotations

import argparse
import ctypes
import hashlib
import json
import math
import os
import selectors
import signal
import stat
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence


PREFLIGHT_PROTOCOL = "qcode-coset-mutation-preflight-v1"
PREFLIGHT_SCHEMA_VERSION = 1
DEFAULT_HARD_TIMEOUT_S = 30.0
DEFAULT_MEMORY_LIMIT_BYTES = 512 * 1024 * 1024
MAX_POLICY_SOURCE_BYTES = 262_144
MAX_PROTOCOL_BYTES = 2 * 1024 * 1024
MAX_DIAGNOSTIC_BYTES = 64 * 1024
TERMINATION_GRACE_S = 0.25

_SHA256_HEX = frozenset("0123456789abcdef")


@dataclass(frozen=True, slots=True)
class CosetMutationPreflightResult:
    """A validated policy and its catalog-bound candidate definitions."""

    program_sha256: str
    program_bytes: int
    policy_sha256: str
    candidates: tuple[dict[str, Any], ...]
    elapsed_s: float


class InvalidCosetMutation(ValueError):
    """The evolved bytes are not a valid coset policy."""

    def __init__(
        self,
        reason_code: str,
        *,
        program_sha256: str | None,
        program_bytes: int | None,
        detail_sha256: str,
        error_type: str = "CosetPolicyError",
    ) -> None:
        super().__init__(reason_code)
        self.reason_code = reason_code
        self.program_sha256 = program_sha256
        self.program_bytes = program_bytes
        self.detail_sha256 = detail_sha256
        self.error_type = error_type


class CosetMutationRuntimeError(RuntimeError):
    """The trusted preflight runtime failed or violated its protocol."""

    def __init__(self, reason_code: str, *, detail_sha256: str | None = None) -> None:
        super().__init__(reason_code)
        self.reason_code = reason_code
        self.detail_sha256 = detail_sha256


@dataclass(frozen=True, slots=True)
class _SourceSnapshot:
    payload: bytes
    sha256: str
    size: int


@dataclass(frozen=True, slots=True)
class _ProcessIdentity:
    pid: int
    pgid: int
    session_id: int
    uid: int
    starttime: int


def _detail_sha256(value: str | bytes) -> str:
    encoded = value if isinstance(value, bytes) else value.encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _valid_sha256(value: Any) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 64
        and set(value) <= _SHA256_HEX
    )


def _canonical_json_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def _snapshot_regular_file(path: str | Path) -> _SourceSnapshot:
    """Read one bounded inode snapshot without following a final symlink."""

    lexical = Path(os.path.abspath(os.fspath(path)))
    flags = os.O_RDONLY | os.O_CLOEXEC | os.O_NONBLOCK
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(lexical, flags)
    except OSError as exc:
        raise CosetMutationRuntimeError(
            "source_open_failed", detail_sha256=_detail_sha256(type(exc).__name__)
        ) from exc
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise CosetMutationRuntimeError("source_not_regular")
        if before.st_size > MAX_POLICY_SOURCE_BYTES:
            raise InvalidCosetMutation(
                "source_too_large",
                program_sha256=None,
                program_bytes=int(before.st_size),
                detail_sha256=_detail_sha256("source_too_large"),
            )
        chunks: list[bytes] = []
        observed = 0
        while observed <= MAX_POLICY_SOURCE_BYTES:
            chunk = os.read(
                descriptor,
                min(65536, MAX_POLICY_SOURCE_BYTES + 1 - observed),
            )
            if not chunk:
                break
            chunks.append(chunk)
            observed += len(chunk)
        payload = b"".join(chunks)
        after = os.fstat(descriptor)
        stable_fields = ("st_dev", "st_ino", "st_size", "st_mtime_ns")
        if any(getattr(before, name) != getattr(after, name) for name in stable_fields):
            raise CosetMutationRuntimeError("source_changed_during_snapshot")
        if len(payload) > MAX_POLICY_SOURCE_BYTES:
            raise InvalidCosetMutation(
                "source_too_large",
                program_sha256=None,
                program_bytes=len(payload),
                detail_sha256=_detail_sha256("source_too_large"),
            )
        if len(payload) != after.st_size:
            raise CosetMutationRuntimeError("source_snapshot_incomplete")
    except OSError as exc:
        raise CosetMutationRuntimeError(
            "source_read_failed", detail_sha256=_detail_sha256(type(exc).__name__)
        ) from exc
    finally:
        os.close(descriptor)
    return _SourceSnapshot(
        payload=payload,
        sha256=hashlib.sha256(payload).hexdigest(),
        size=len(payload),
    )


def _read_process_identity(pid: int) -> tuple[str, _ProcessIdentity]:
    try:
        raw = Path(f"/proc/{pid}/stat").read_text()
        status = os.stat(f"/proc/{pid}", follow_symlinks=False)
    except (OSError, UnicodeError) as exc:
        raise CosetMutationRuntimeError("process_identity_unavailable") from exc
    closing = raw.rfind(")")
    if closing < 1:
        raise CosetMutationRuntimeError("process_identity_invalid")
    fields = raw[closing + 2 :].split()
    try:
        state = fields[0]
        pgid = int(fields[2])
        session_id = int(fields[3])
        starttime = int(fields[19])
    except (IndexError, ValueError) as exc:
        raise CosetMutationRuntimeError("process_identity_invalid") from exc
    return state, _ProcessIdentity(
        pid=pid,
        pgid=pgid,
        session_id=session_id,
        uid=int(status.st_uid),
        starttime=starttime,
    )


def _validate_private_identity(identity: _ProcessIdentity, expected_pid: int) -> None:
    if (
        identity.pid != expected_pid
        or identity.pid <= 1
        or identity.pgid != identity.pid
        or identity.session_id != identity.pid
        or identity.uid != os.getuid()
        or identity.starttime <= 0
        or identity.pgid == os.getpgrp()
        or identity.session_id == os.getsid(0)
    ):
        raise CosetMutationRuntimeError("process_group_not_private")


def _identity_is_pinned(identity: _ProcessIdentity) -> bool:
    try:
        _state, observed = _read_process_identity(identity.pid)
    except CosetMutationRuntimeError:
        return False
    return observed == identity


def _live_group_members(identity: _ProcessIdentity) -> list[int]:
    members: list[int] = []
    try:
        entries = list(Path("/proc").iterdir())
    except OSError as exc:
        raise CosetMutationRuntimeError("process_group_scan_failed") from exc
    for entry in entries:
        if not entry.name.isdigit():
            continue
        try:
            state, observed = _read_process_identity(int(entry.name))
        except CosetMutationRuntimeError:
            continue
        if (
            observed.pgid == identity.pgid
            and observed.session_id == identity.session_id
        ):
            if observed.uid != identity.uid or observed.starttime < identity.starttime:
                raise CosetMutationRuntimeError("process_group_identity_unsafe")
            if state != "Z":
                members.append(observed.pid)
    return members


def _signal_group(identity: _ProcessIdentity, signal_number: int) -> None:
    if not _identity_is_pinned(identity):
        raise CosetMutationRuntimeError("process_group_identity_unpinned")
    try:
        os.killpg(identity.pgid, signal_number)
    except ProcessLookupError:
        return
    except OSError as exc:
        raise CosetMutationRuntimeError("process_group_signal_failed") from exc


def _terminate_group(
    process: subprocess.Popen[bytes],
    identity: _ProcessIdentity,
) -> None:
    """Kill every live member while the unreaped leader pins PID/PGID/SID."""

    if process.returncode is not None:
        if _live_group_members(identity):
            raise CosetMutationRuntimeError("process_group_reaped_before_cleanup")
        return
    members = _live_group_members(identity)
    if members:
        _signal_group(identity, signal.SIGTERM)
        deadline = time.monotonic() + TERMINATION_GRACE_S
        while _live_group_members(identity) and time.monotonic() < deadline:
            time.sleep(0.01)
        if _live_group_members(identity):
            _signal_group(identity, signal.SIGKILL)
            deadline = time.monotonic() + 5.0
            while _live_group_members(identity) and time.monotonic() < deadline:
                time.sleep(0.01)
    try:
        process.wait(timeout=5.0)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise CosetMutationRuntimeError("process_reap_failed") from exc
    if _live_group_members(identity):
        raise CosetMutationRuntimeError("process_group_survived_kill")


def _wait_for_leader_zombie(identity: _ProcessIdentity, deadline: float) -> bool:
    while time.monotonic() < deadline:
        try:
            state, observed = _read_process_identity(identity.pid)
        except CosetMutationRuntimeError:
            return False
        if observed != identity:
            return False
        if state == "Z":
            return True
        time.sleep(0.01)
    return False


def _child_environment() -> dict[str, str]:
    return {
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
        "OMP_NUM_THREADS": "1",
        "OPENBLAS_NUM_THREADS": "1",
        "MKL_NUM_THREADS": "1",
        "NUMEXPR_NUM_THREADS": "1",
    }


def _child_command(
    python_executable: str,
    *,
    hard_timeout_s: float,
    memory_limit_bytes: int,
) -> list[str]:
    executable = Path(python_executable)
    script = Path(__file__).resolve(strict=True)
    return [
        str(executable),
        "-I",
        str(script),
        "--child",
        "--memory-limit-bytes",
        str(memory_limit_bytes),
        "--cpu-limit-seconds",
        str(max(1, math.ceil(hard_timeout_s))),
    ]


def _exchange(
    process: subprocess.Popen[bytes],
    identity: _ProcessIdentity,
    payload: bytes,
    *,
    timeout: float,
) -> tuple[bytes, bytes, int]:
    if process.stdin is None or process.stdout is None or process.stderr is None:
        raise CosetMutationRuntimeError("child_pipes_unavailable")
    streams = {
        process.stdout.fileno(): ("stdout", selectors.EVENT_READ),
        process.stderr.fileno(): ("stderr", selectors.EVENT_READ),
        process.stdin.fileno(): ("stdin", selectors.EVENT_WRITE),
    }
    buffers = {"stdout": bytearray(), "stderr": bytearray()}
    limits = {"stdout": MAX_PROTOCOL_BYTES, "stderr": MAX_DIAGNOSTIC_BYTES}
    selector = selectors.DefaultSelector()
    for descriptor, (channel, event) in streams.items():
        os.set_blocking(descriptor, False)
        selector.register(descriptor, event, channel)
    input_offset = 0
    deadline = time.monotonic() + timeout
    try:
        while selector.get_map():
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                _terminate_group(process, identity)
                raise CosetMutationRuntimeError("hard_timeout")
            events = selector.select(min(remaining, 0.1))
            for key, mask in events:
                descriptor = int(key.fd)
                channel = str(key.data)
                if channel == "stdin" and mask & selectors.EVENT_WRITE:
                    try:
                        written = os.write(descriptor, payload[input_offset:])
                    except (BrokenPipeError, ConnectionResetError):
                        written = 0
                    if written > 0:
                        input_offset += written
                    if written == 0 or input_offset == len(payload):
                        selector.unregister(descriptor)
                        process.stdin.close()
                    continue
                if mask & selectors.EVENT_READ:
                    limit = limits[channel]
                    try:
                        chunk = os.read(
                            descriptor,
                            min(65536, limit + 1 - len(buffers[channel])),
                        )
                    except BlockingIOError:
                        continue
                    if not chunk:
                        selector.unregister(descriptor)
                        continue
                    buffers[channel].extend(chunk)
                    if len(buffers[channel]) > limit:
                        _terminate_group(process, identity)
                        raise CosetMutationRuntimeError(f"{channel}_limit_exceeded")
        if not _wait_for_leader_zombie(identity, deadline):
            _terminate_group(process, identity)
            raise CosetMutationRuntimeError("hard_timeout")
        if _live_group_members(identity):
            _terminate_group(process, identity)
            raise CosetMutationRuntimeError("unexpected_child_process")
        try:
            returncode = process.wait(
                timeout=max(0.001, deadline - time.monotonic())
            )
        except subprocess.TimeoutExpired as exc:
            raise CosetMutationRuntimeError("process_reap_failed") from exc
        return bytes(buffers["stdout"]), bytes(buffers["stderr"]), returncode
    finally:
        selector.close()


def _strict_json_object(payload: bytes) -> dict[str, Any]:
    def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate key: {key}")
            result[key] = value
        return result

    def reject_constant(value: str) -> None:
        raise ValueError(f"non-finite constant: {value}")

    try:
        if not payload.endswith(b"\n") or b"\n" in payload[:-1]:
            raise ValueError("protocol must be exactly one JSON line")
        value = json.loads(
            payload[:-1].decode("utf-8", errors="strict"),
            object_pairs_hook=reject_duplicates,
            parse_constant=reject_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        raise CosetMutationRuntimeError(
            "protocol_invalid", detail_sha256=_detail_sha256(type(exc).__name__)
        ) from exc
    if type(value) is not dict or payload != _canonical_json_bytes(value) + b"\n":
        raise CosetMutationRuntimeError("protocol_not_canonical")
    return value


def _validated_response(
    response: dict[str, Any],
    snapshot: _SourceSnapshot,
) -> CosetMutationPreflightResult:
    common = {"protocol", "schema_version", "status", "program_sha256", "program_bytes"}
    if (
        response.get("protocol") != PREFLIGHT_PROTOCOL
        or response.get("schema_version") != PREFLIGHT_SCHEMA_VERSION
        or response.get("program_sha256") != snapshot.sha256
        or response.get("program_bytes") != snapshot.size
    ):
        raise CosetMutationRuntimeError("protocol_binding_mismatch")
    status_value = response.get("status")
    if status_value == "invalid_mutation":
        expected = common | {"reason_code", "error_type", "detail_sha256"}
        if (
            set(response) != expected
            or response.get("reason_code") != "dsl_invalid"
            or response.get("error_type") != "CosetPolicyError"
            or not _valid_sha256(response.get("detail_sha256"))
        ):
            raise CosetMutationRuntimeError("invalid_mutation_envelope_malformed")
        raise InvalidCosetMutation(
            "dsl_invalid",
            program_sha256=snapshot.sha256,
            program_bytes=snapshot.size,
            detail_sha256=response["detail_sha256"],
        )
    expected = common | {
        "policy_sha256",
        "policy",
        "candidate_count",
        "candidates",
    }
    if status_value != "valid" or set(response) != expected:
        raise CosetMutationRuntimeError("valid_envelope_malformed")
    policy_document = response.get("policy")
    policy_sha256 = response.get("policy_sha256")
    if (
        type(policy_document) is not dict
        or not _valid_sha256(policy_sha256)
        or hashlib.sha256(_canonical_json_bytes(policy_document)).hexdigest()
        != policy_sha256
    ):
        raise CosetMutationRuntimeError("policy_digest_mismatch")

    try:
        from evolve import coset_policy_dsl as dsl
        from evolve import coset_search_contract as contract
    except Exception as exc:
        raise CosetMutationRuntimeError(
            "parent_contract_import_failed",
            detail_sha256=_detail_sha256(type(exc).__name__),
        ) from exc
    if dsl.MAX_POLICY_BYTES != MAX_POLICY_SOURCE_BYTES:
        raise CosetMutationRuntimeError("policy_source_cap_mismatch")
    candidates = response.get("candidates")
    count = response.get("candidate_count")
    if (
        type(candidates) is not list
        or type(count) is not int
        or count != len(candidates)
        or count != contract.MAX_GENERATED_CANDIDATES
    ):
        raise CosetMutationRuntimeError("candidate_count_invalid")
    normalized: list[dict[str, Any]] = []
    digests: set[str] = set()
    try:
        for candidate in candidates:
            if type(candidate) is not dict:
                raise ValueError("candidate is not a plain object")
            item = contract.normalize_candidate(candidate)
            if item != candidate:
                raise ValueError("candidate is not canonical")
            digest = contract.candidate_digest(item)
            if digest in digests:
                raise ValueError("duplicate candidate")
            digests.add(digest)
            normalized.append(item)
    except (TypeError, ValueError) as exc:
        raise CosetMutationRuntimeError(
            "candidate_revalidation_failed",
            detail_sha256=_detail_sha256(type(exc).__name__),
        ) from exc
    try:
        views = contract.action_search_views()
        expected_quotas = contract.quota_by_normality(
            views,
            contract.MAX_GENERATED_CANDIDATES,
        )
        observed_quotas = {view.action_id: 0 for view in views}
        for item in normalized:
            observed_quotas[item["action_id"]] += 1
    except (KeyError, TypeError, ValueError) as exc:
        raise CosetMutationRuntimeError(
            "candidate_revalidation_failed",
            detail_sha256=_detail_sha256(type(exc).__name__),
        ) from exc
    if observed_quotas != expected_quotas:
        raise CosetMutationRuntimeError("candidate_quota_invalid")
    return CosetMutationPreflightResult(
        program_sha256=snapshot.sha256,
        program_bytes=snapshot.size,
        policy_sha256=policy_sha256,
        candidates=tuple(normalized),
        elapsed_s=0.0,
    )


def _validated_python_executable(value: str | None) -> str:
    raw = sys.executable if value is None else value
    path = Path(raw)
    if not path.is_absolute():
        raise CosetMutationRuntimeError("python_executable_not_absolute")
    try:
        resolved = path.resolve(strict=True)
        status = resolved.stat()
    except OSError as exc:
        raise CosetMutationRuntimeError("python_executable_unavailable") from exc
    if not stat.S_ISREG(status.st_mode) or not os.access(resolved, os.X_OK):
        raise CosetMutationRuntimeError("python_executable_invalid")
    # Preserve the absolute lexical invocation so a venv's ``pyvenv.cfg`` and
    # site-packages remain active.  The target was resolved only for validation.
    return str(path)


def preflight_coset_policy(
    program_path: str | Path,
    *,
    python_executable: str | None = None,
    hard_timeout_s: float = DEFAULT_HARD_TIMEOUT_S,
    memory_limit_bytes: int = DEFAULT_MEMORY_LIMIT_BYTES,
) -> CosetMutationPreflightResult:
    """Parse and render one evolved JSON policy behind a hard process wall."""

    if (
        isinstance(hard_timeout_s, bool)
        or not isinstance(hard_timeout_s, (int, float))
        or not math.isfinite(float(hard_timeout_s))
        or hard_timeout_s <= 0
    ):
        raise CosetMutationRuntimeError("hard_timeout_invalid")
    if (
        isinstance(memory_limit_bytes, bool)
        or not isinstance(memory_limit_bytes, int)
        or memory_limit_bytes < 64 * 1024 * 1024
    ):
        raise CosetMutationRuntimeError("memory_limit_invalid")
    started = time.monotonic()
    snapshot = _snapshot_regular_file(program_path)
    executable = _validated_python_executable(python_executable)
    command = _child_command(
        executable,
        hard_timeout_s=float(hard_timeout_s),
        memory_limit_bytes=memory_limit_bytes,
    )
    process: subprocess.Popen[bytes] | None = None
    identity: _ProcessIdentity | None = None
    try:
        with tempfile.TemporaryDirectory(prefix="qcode-coset-preflight-") as cwd:
            process = subprocess.Popen(
                command,
                cwd=cwd,
                env=_child_environment(),
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                close_fds=True,
                start_new_session=True,
            )
            _state, observed_identity = _read_process_identity(process.pid)
            _validate_private_identity(observed_identity, process.pid)
            # Publish the identity to cleanup only after every safety check.
            identity = observed_identity
            stdout, stderr, returncode = _exchange(
                process,
                identity,
                snapshot.payload,
                timeout=float(hard_timeout_s),
            )
    except OSError as exc:
        raise CosetMutationRuntimeError(
            "child_start_failed", detail_sha256=_detail_sha256(type(exc).__name__)
        ) from exc
    finally:
        if process is not None and process.returncode is None:
            if identity is not None:
                _terminate_group(process, identity)
            else:
                # Group signalling is unsafe until PID/PGID/SID are pinned.
                # Killing and reaping the directly-created trusted leader is
                # still necessary so a failed identity check cannot leak it.
                try:
                    process.kill()
                except ProcessLookupError:
                    pass
                except OSError as exc:
                    raise CosetMutationRuntimeError(
                        "unverified_process_kill_failed"
                    ) from exc
                try:
                    process.wait(timeout=5.0)
                except (OSError, subprocess.TimeoutExpired) as exc:
                    raise CosetMutationRuntimeError(
                        "unverified_process_reap_failed"
                    ) from exc
        if process is not None:
            for stream in (process.stdin, process.stdout, process.stderr):
                if stream is not None and not stream.closed:
                    stream.close()
    if returncode != 0:
        raise CosetMutationRuntimeError(
            "child_nonzero_exit",
            detail_sha256=_detail_sha256(
                str(returncode).encode("ascii") + b"\0" + stderr
            ),
        )
    if stderr:
        raise CosetMutationRuntimeError(
            "child_stderr_nonempty", detail_sha256=_detail_sha256(stderr)
        )
    response = _strict_json_object(stdout)
    result = _validated_response(response, snapshot)
    return CosetMutationPreflightResult(
        program_sha256=result.program_sha256,
        program_bytes=result.program_bytes,
        policy_sha256=result.policy_sha256,
        candidates=result.candidates,
        elapsed_s=time.monotonic() - started,
    )


def _install_child_limits(memory_limit_bytes: int, cpu_limit_seconds: int) -> None:
    import resource

    parent_pid = os.getppid()
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(1, signal.SIGKILL, 0, 0, 0) != 0:  # PR_SET_PDEATHSIG
        error_number = ctypes.get_errno()
        raise OSError(error_number, "prctl(PR_SET_PDEATHSIG) failed")
    if os.getppid() != parent_pid:
        os.kill(os.getpid(), signal.SIGKILL)
    limits = (
        (resource.RLIMIT_AS, memory_limit_bytes),
        (resource.RLIMIT_CPU, cpu_limit_seconds),
        (resource.RLIMIT_CORE, 0),
        (resource.RLIMIT_FSIZE, 0),
        (resource.RLIMIT_NOFILE, 32),
    )
    for kind, value in limits:
        resource.setrlimit(kind, (value, value))


def _child_response(source: bytes) -> dict[str, Any]:
    project_root = str(Path(__file__).resolve(strict=True).parent.parent)
    if project_root not in sys.path:
        sys.path.insert(0, project_root)
    # ``-I`` ignores PYTHONDONTWRITEBYTECODE.  Set the interpreter flag before
    # trusted project imports so RLIMIT_FSIZE=0 cannot turn a harmless pyc
    # cache miss into SIGXFSZ.
    sys.dont_write_bytecode = True
    from evolve.coset_policy_dsl import (
        MAX_POLICY_BYTES,
        CosetPolicyError,
        parse_policy,
        policy_digest,
        policy_document,
        render_candidates,
    )

    program_sha256 = hashlib.sha256(source).hexdigest()
    common = {
        "protocol": PREFLIGHT_PROTOCOL,
        "schema_version": PREFLIGHT_SCHEMA_VERSION,
        "program_sha256": program_sha256,
        "program_bytes": len(source),
    }
    try:
        if len(source) > MAX_POLICY_BYTES:
            raise CosetPolicyError("coset policy payload exceeds the source cap")
        policy = parse_policy(source)
        candidates = render_candidates(policy)
    except CosetPolicyError as exc:
        return {
            **common,
            "status": "invalid_mutation",
            "reason_code": "dsl_invalid",
            "error_type": "CosetPolicyError",
            "detail_sha256": _detail_sha256(
                type(exc).__name__ + "\0" + str(exc)
            ),
        }
    document = policy_document(policy)
    digest = policy_digest(policy)
    if hashlib.sha256(_canonical_json_bytes(document)).hexdigest() != digest:
        raise RuntimeError("trusted policy digest implementation disagrees")
    return {
        **common,
        "status": "valid",
        "policy_sha256": digest,
        "policy": document,
        "candidate_count": len(candidates),
        "candidates": candidates,
    }


def _read_child_stdin() -> bytes:
    payload = sys.stdin.buffer.read(MAX_POLICY_SOURCE_BYTES + 1)
    if len(payload) > MAX_POLICY_SOURCE_BYTES:
        # The parent never sends this.  Raising outside the mutation-error
        # boundary makes a broken parent/transport fail closed.
        raise RuntimeError("parent exceeded the mutation source cap")
    return payload


def _main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument("--child", action="store_true")
    parser.add_argument("--memory-limit-bytes", type=int)
    parser.add_argument("--cpu-limit-seconds", type=int)
    arguments = parser.parse_args(argv)
    if (
        not arguments.child
        or arguments.memory_limit_bytes is None
        or arguments.cpu_limit_seconds is None
    ):
        return 2
    _install_child_limits(
        arguments.memory_limit_bytes,
        arguments.cpu_limit_seconds,
    )
    response = _child_response(_read_child_stdin())
    encoded = _canonical_json_bytes(response) + b"\n"
    if len(encoded) > MAX_PROTOCOL_BYTES:
        raise RuntimeError("trusted preflight response exceeds protocol cap")
    sys.stdout.buffer.write(encoded)
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    raise SystemExit(_main())


__all__ = [
    "CosetMutationPreflightResult",
    "CosetMutationRuntimeError",
    "DEFAULT_HARD_TIMEOUT_S",
    "DEFAULT_MEMORY_LIMIT_BYTES",
    "InvalidCosetMutation",
    "MAX_POLICY_SOURCE_BYTES",
    "PREFLIGHT_PROTOCOL",
    "PREFLIGHT_SCHEMA_VERSION",
    "preflight_coset_policy",
]
