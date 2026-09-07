#!/usr/bin/env python3
"""Run the IPhO 2026 answer-blind Archon loop under the sealed jail.

This is root-side controller code.  It never loads an official answer or a
provider credential.  The solver receives only a fixed public dummy token for
an already-running loopback broker and a read-only projection of the local
LeanExplore cache.
"""

from __future__ import annotations

import argparse
import errno
import hashlib
import http.client
import importlib.util
import json
import os
import re
import shutil
import signal
import stat
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable, Mapping
from urllib.parse import urlparse


SEALED_RUNTIME = Path("/opt/icho-answer-blind-runtime-10b04c62-rebuilt1-idle1800")
SEALED_HELPER = Path("libexec/run_answer_blind_iteration.py")
CLAUDE_BINARY = Path(
    "/root/icho-answer-blind-overlay-49360f26-univ-kimi-k3/bin/claude"
)
CLAUDE_BINARY_SHA256 = (
    "4e9bec1177ce9690e8bd988b710ac24105e70da428dd094c5adcbbe786a55555"
)
CLAUDE_LS_BINARY = Path(
    "/root/icho-answer-blind-overlay-49360f26-univ-kimi-k3/bin/ls"
)
CLAUDE_LS_BINARY_SHA256 = (
    "53a9c0557a948069d56f964cf21c7c0854bb2677d9985080369ed1e172161625"
)
CLAUDE_CODE_RUNTIME_READONLY_PATHS = tuple(
    Path(item)
    for item in (
        "/proc",
        "/sys/fs/cgroup/cpu.max",
        "/sys/fs/cgroup/memory.max",
        "/sys/fs/cgroup/memory.high",
        "/sys/devices/system/cpu/online",
        "/sys/kernel/mm/transparent_hugepage/enabled",
    )
)
SECCOMP_RECEIVE_DEADLINE_S = 1.0
ARCHON_FORK_BOOTSTRAP = (
    "import multiprocessing as mp, runpy; "
    "mp.set_start_method('fork'); "
    "runpy.run_module('archon.cli', run_name='__main__')"
)
MODEL = "anthropic-kimi-k3"
VARIANT = "kimi-k3"
TOKIO_WORKER_THREADS = "1"
TARGET_DIR = "IPhO2026Problems"
LEGACY_TARGET_DIR = "IChO2026Problems"
LEAN_EXPLORE_VERSION = "20260714_172516"
LEAN_EXPLORE_EMBEDDING_MODEL = "Qwen/Qwen3-Embedding-0.6B"
LEAN_EXPLORE_EMBEDDING_CACHE_REPO = (
    "models--Qwen--Qwen3-Embedding-0.6B"
)
LEAN_EXPLORE_EMBEDDING_REVISION = "97b0c614be4d77ee51c0cef4e5f07c00f9eb65b3"
LEAN_EXPLORE_EMBEDDING_BLOBS = {
    "00a82ea60dfb1d8aed899c16e2b4f12673cd2f79": "c34d9b7e5a267ad3fdd13227a253686bc90844ff4744a2a6a86c7c905e3d06f3",
    "0437e45c94563b09e13cb7a64478fc406947a93cb34a7e05870fc8dcd48e23fd": "0437e45c94563b09e13cb7a64478fc406947a93cb34a7e05870fc8dcd48e23fd",
    "31349551d90c7606f325fe0f11bbb8bd5fa0d7c7": "8831e4f1a044471340f7c0a83d7bd71306a5b867e95fd870f74d0c5308a904d5",
    "4783fe10ac3adce15ac8f358ef5462739852c569": "ca10d7e9fb3ed18575dd1e277a2579c16d108e32f27439684afa0e10b1440910",
    "7345216a0785dc7086e8c245b2a9d3896ce2b756": "253153d0738ceb4c668d2eff957714dd2bea0b56de772a9fdccd96cbf517e6a0",
    "76aef3ade63553ebb698fe3c2a3264040ed093f8": "10667c72ddb772627bf1780cb7f86af8e2ae0032b8c243c731172064105c6961",
    "952a9b81c0bfd99800fabf352f69c7ccd46c5e43": "84e40c8e006c9b1d6c122e02cba9b02458120b5fb0c87b746c41e0207cf642cf",
    "b6291baabbc39f9792d6759883a47d7d5bd0fbcf": "37bf193fa101f19101bfad9c31d3eb0f786e247b7b1e5cb7f007d730eed1ddbd",
    "cef2749ee93607b8f9a58ec72f4f6bfaf874e71d": "b5bf1f51fc45be473a54718cef92448d90a1be001bf9b9a44b8c7f10a19feaa9",
    "def76fb086971c7867b829c23a26261e38d9d74e02139253b38aeb9df8b4b50a": "def76fb086971c7867b829c23a26261e38d9d74e02139253b38aeb9df8b4b50a",
}
LEAN_EXPLORE_EMBEDDING_SNAPSHOT_BLOBS = {
    "1_Pooling/config.json": "b6291baabbc39f9792d6759883a47d7d5bd0fbcf",
    "README.md": "00a82ea60dfb1d8aed899c16e2b4f12673cd2f79",
    "config.json": "cef2749ee93607b8f9a58ec72f4f6bfaf874e71d",
    "config_sentence_transformers.json": "76aef3ade63553ebb698fe3c2a3264040ed093f8",
    "merges.txt": "31349551d90c7606f325fe0f11bbb8bd5fa0d7c7",
    "model.safetensors": "0437e45c94563b09e13cb7a64478fc406947a93cb34a7e05870fc8dcd48e23fd",
    "modules.json": "952a9b81c0bfd99800fabf352f69c7ccd46c5e43",
    "tokenizer.json": "def76fb086971c7867b829c23a26261e38d9d74e02139253b38aeb9df8b4b50a",
    "tokenizer_config.json": "7345216a0785dc7086e8c245b2a9d3896ce2b756",
    "vocab.json": "4783fe10ac3adce15ac8f358ef5462739852c569",
}
LEAN_EXPLORE_EMBEDDING_MISSING_MARKERS = {
    "2_Normalize/config.json",
    "adapter_config.json",
    "added_tokens.json",
    "chat_template.jinja",
    "preprocessor_config.json",
    "processor_config.json",
    "sentence_albert_config.json",
    "sentence_bert_config.json",
    "sentence_camembert_config.json",
    "sentence_distilbert_config.json",
    "sentence_roberta_config.json",
    "sentence_xlm-roberta_config.json",
    "sentence_xlnet_config.json",
    "special_tokens_map.json",
    "video_preprocessor_config.json",
}
DUMMY_TOKEN = "answer-blind-public-dummy-token"
BROKER_REQUEST_PROFILE = "agent_harness_v1"
PROTOCOL = "ipho-2026-answer-blind-confined-loop-v1"
SAFE_RUN_ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,127}$")


class LaunchError(RuntimeError):
    """A controller-side answer-blind invariant was not satisfied."""


class _SeccompReceiveDeadline(RuntimeError):
    """Internal signal used to interrupt a stale USER_NOTIF receive."""


def _plain_directory(raw: Path | str, *, label: str) -> Path:
    path = Path(raw)
    if path.is_symlink():
        raise LaunchError(f"{label} must not be a symbolic link: {path}")
    try:
        resolved = path.resolve(strict=True)
    except OSError as exc:
        raise LaunchError(f"{label} does not exist: {path}") from exc
    if not resolved.is_dir():
        raise LaunchError(f"{label} is not a directory: {path}")
    return resolved


def _plain_file(raw: Path | str, *, label: str) -> Path:
    path = Path(raw)
    if path.is_symlink():
        raise LaunchError(f"{label} must not be a symbolic link: {path}")
    try:
        resolved = path.resolve(strict=True)
    except OSError as exc:
        raise LaunchError(f"{label} does not exist: {path}") from exc
    if not resolved.is_file():
        raise LaunchError(f"{label} is not a regular file: {path}")
    return resolved


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _validate_claude_runtime(
    binary: Path = CLAUDE_BINARY,
    *,
    expected_sha256: str = CLAUDE_BINARY_SHA256,
    ls_binary: Path = CLAUDE_LS_BINARY,
    ls_expected_sha256: str = CLAUDE_LS_BINARY_SHA256,
) -> tuple[Path, tuple[Path, ...]]:
    claude = _plain_file(binary, label="Claude Code binary")
    metadata = claude.stat(follow_symlinks=False)
    if (
        metadata.st_uid != 0
        or stat.S_IMODE(metadata.st_mode) != 0o555
        or not os.access(claude, os.X_OK)
    ):
        raise LaunchError("Claude Code binary must be root-owned mode 0555")
    if _sha256_file(claude) != expected_sha256:
        raise LaunchError("Claude Code binary SHA-256 drift")

    runtime_ls = _plain_file(ls_binary, label="Claude Code ls helper")
    ls_metadata = runtime_ls.stat(follow_symlinks=False)
    if (
        ls_metadata.st_uid != 0
        or stat.S_IMODE(ls_metadata.st_mode) & 0o022
        or not os.access(runtime_ls, os.X_OK)
    ):
        raise LaunchError("Claude Code ls helper must be root-owned and not writable")
    if _sha256_file(runtime_ls) != ls_expected_sha256:
        raise LaunchError("Claude Code ls helper SHA-256 drift")

    runtime_paths: list[Path] = [runtime_ls]
    for raw in CLAUDE_CODE_RUNTIME_READONLY_PATHS:
        if raw.is_symlink():
            raise LaunchError(f"Claude runtime metadata path is a symlink: {raw}")
        try:
            path = raw.resolve(strict=True)
        except OSError as exc:
            raise LaunchError(f"Claude runtime metadata path is missing: {raw}") from exc
        if not (path.is_file() or path.is_dir()):
            raise LaunchError(f"Claude runtime metadata path is unsafe: {path}")
        entry = path.stat(follow_symlinks=False)
        if entry.st_uid != 0 or stat.S_IMODE(entry.st_mode) & 0o022:
            raise LaunchError(f"Claude runtime metadata path is writable: {path}")
        runtime_paths.append(path)
    return claude, tuple(runtime_paths)


def _install_seccomp_receive_deadline(sealed: Any) -> None:
    """Bound the kernel USER_NOTIF exit race without changing network policy."""

    if getattr(sealed, "_ipho_seccomp_receive_deadline_installed", False):
        return
    original_ioctl = sealed._seccomp_ioctl
    receive_request = sealed.SECCOMP_IOCTL_NOTIF_RECV

    def guarded_ioctl(fd: int, request: int, argument: Any) -> int:
        if request != receive_request:
            return original_ioctl(fd, request, argument)
        if any(signal.getitimer(signal.ITIMER_REAL)):
            raise LaunchError("controller already has an active real-time timer")
        previous_handler = signal.getsignal(signal.SIGALRM)

        def expire(_signum: int, _frame: Any) -> None:
            raise _SeccompReceiveDeadline

        signal.signal(signal.SIGALRM, expire)
        signal.setitimer(signal.ITIMER_REAL, SECCOMP_RECEIVE_DEADLINE_S)
        try:
            try:
                return original_ioctl(fd, request, argument)
            except _SeccompReceiveDeadline as exc:
                raise OSError(
                    errno.EINTR, "stale seccomp USER_NOTIF receive interrupted"
                ) from exc
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0.0)
            signal.signal(signal.SIGALRM, previous_handler)

    sealed._seccomp_ioctl = guarded_ioctl
    sealed._ipho_seccomp_receive_deadline_installed = True


def _allow_seccomp_socketpair(sealed: Any) -> None:
    """Allow anonymous local IPC used by Claude Code subprocess tools."""

    if getattr(sealed, "_ipho_socketpair_allowed", False):
        return
    original_program = sealed._seccomp_filter_program
    errno_result = 0x00050000 | errno.EPERM

    def patched_program() -> tuple[Any, Any]:
        original_array, _original = original_program()
        instructions: list[Any] = []
        removed = 0
        index = 0
        while index < len(original_array):
            current = original_array[index]
            if (
                int(current.code) == 0x15
                and int(current.jt) == 0
                and int(current.jf) == 1
                and int(current.k) == 53
            ):
                if index + 1 >= len(original_array):
                    raise LaunchError("truncated socketpair seccomp rule")
                following = original_array[index + 1]
                if int(following.code) != 0x06 or int(following.k) != errno_result:
                    raise LaunchError("unexpected socketpair seccomp rule")
                removed += 1
                index += 2
                continue
            instructions.append(
                sealed._SockFilter(
                    int(current.code),
                    int(current.jt),
                    int(current.jf),
                    int(current.k),
                )
            )
            index += 1
        if removed != 1:
            raise LaunchError("socketpair seccomp rule count drifted")
        array = (sealed._SockFilter * len(instructions))(*instructions)
        return array, sealed._SockFprog(len(instructions), array)

    sealed._seccomp_filter_program = patched_program
    sealed._ipho_socketpair_allowed = True


def _allow_seccomp_native_sockets(sealed: Any) -> None:
    """Let Claude subprocess IPC use native sockets under the Landlock policy."""

    if getattr(sealed, "_ipho_native_sockets_allowed", False):
        return
    original_program = sealed._seccomp_filter_program
    errno_result = 0x00050000 | errno.EPERM
    user_notif = int(sealed.SECCOMP_RET_USER_NOTIF)

    def patched_program() -> tuple[Any, Any]:
        original_array, _original = original_program()
        instructions: list[Any] = []
        removed = 0
        listener_anchor_replaced = 0
        index = 0
        while index < len(original_array):
            current = original_array[index]
            if (
                int(current.code) == 0x15
                and int(current.jt) == 0
                and int(current.jf) == 1
                and int(current.k) in {41, 42}
            ):
                if index + 1 >= len(original_array):
                    raise LaunchError("truncated socket/connect seccomp rule")
                following = original_array[index + 1]
                if int(following.code) != 0x06 or int(following.k) != user_notif:
                    raise LaunchError("unexpected socket/connect seccomp rule")
                removed += 1
                index += 2
                continue
            if (
                int(current.code) == 0x15
                and int(current.jt) == 0
                and int(current.jf) == 1
                and int(current.k) == 438
            ):
                if index + 1 >= len(original_array):
                    raise LaunchError("truncated pidfd_getfd seccomp rule")
                following = original_array[index + 1]
                if int(following.code) != 0x06 or int(following.k) != errno_result:
                    raise LaunchError("unexpected pidfd_getfd seccomp rule")
                instructions.extend(
                    (
                        sealed._SockFilter(0x15, 0, 1, 438),
                        sealed._SockFilter(0x06, 0, 0, user_notif),
                    )
                )
                listener_anchor_replaced += 1
                index += 2
                continue
            instructions.append(
                sealed._SockFilter(
                    int(current.code),
                    int(current.jt),
                    int(current.jf),
                    int(current.k),
                )
            )
            index += 1
        if removed != 2:
            raise LaunchError("socket/connect seccomp rule count drifted")
        if listener_anchor_replaced != 1:
            raise LaunchError("pidfd_getfd seccomp rule count drifted")
        array = (sealed._SockFilter * len(instructions))(*instructions)
        return array, sealed._SockFprog(len(instructions), array)

    sealed._seccomp_filter_program = patched_program
    sealed._ipho_native_sockets_allowed = True


def _load_json(path: Path, *, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise LaunchError(f"invalid {label}: {path}") from exc
    if not isinstance(value, dict):
        raise LaunchError(f"{label} must contain one JSON object")
    return value


def _inside(path: Path, parent: Path) -> bool:
    return path == parent or path.is_relative_to(parent)


def _require_disjoint(paths: Mapping[str, Path]) -> None:
    entries = list(paths.items())
    for index, (left_label, left) in enumerate(entries):
        for right_label, right in entries[index + 1 :]:
            if _inside(left, right) or _inside(right, left):
                raise LaunchError(
                    f"{left_label} overlaps {right_label}: {left} / {right}"
                )


def _lean_explore_hf_environment(path: Path) -> dict[str, str]:
    return {
        "HF_HOME": str(path),
        "HF_HUB_OFFLINE": "1",
        "TRANSFORMERS_OFFLINE": "1",
    }


def _validate_controller_dir(path: Path) -> None:
    metadata = path.stat(follow_symlinks=False)
    if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) != 0o700:
        raise LaunchError("controller directory must be root-owned mode 0700")


def _validate_controller_file(path: Path, *, label: str, mode: int) -> None:
    metadata = path.stat(follow_symlinks=False)
    if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) != mode:
        raise LaunchError(f"{label} must be root-owned mode {mode:04o}")


def _load_sealed_helper(runtime_root: Path):
    if runtime_root != SEALED_RUNTIME.resolve(strict=True):
        raise LaunchError(f"runtime root must be the pinned sealed tree: {SEALED_RUNTIME}")
    helper = _plain_file(runtime_root / SEALED_HELPER, label="sealed jail helper")
    archon = _plain_file(runtime_root / "bin/archon", label="sealed Archon")
    for path, label in ((helper, "sealed jail helper"), (archon, "sealed Archon")):
        metadata = path.stat(follow_symlinks=False)
        if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) & 0o022:
            raise LaunchError(f"{label} is not root-owned read-only: {path}")
    if not os.access(archon, os.X_OK):
        raise LaunchError("sealed Archon is not executable")
    spec = importlib.util.spec_from_file_location("_ipho_sealed_iteration", helper)
    if spec is None or spec.loader is None:
        raise LaunchError("cannot construct sealed helper import")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def _parameterize_ipho_targets(sealed: Any) -> None:
    """Change only the sealed helper's mutable IChO target paths."""

    directories = tuple(sealed.MUTABLE_WORKSPACE_DIRS)
    files = tuple(sealed.MUTABLE_WORKSPACE_FILES)
    if LEGACY_TARGET_DIR not in directories:
        raise LaunchError("sealed mutable target directory contract drifted")
    if f"{LEGACY_TARGET_DIR}/All.lean" not in files:
        raise LaunchError("sealed mutable target umbrella contract drifted")
    sealed.MUTABLE_WORKSPACE_DIRS = tuple(
        TARGET_DIR if item == LEGACY_TARGET_DIR else item for item in directories
    )
    sealed.MUTABLE_WORKSPACE_FILES = tuple(
        item.replace(f"{LEGACY_TARGET_DIR}/", f"{TARGET_DIR}/", 1)
        if item.startswith(f"{LEGACY_TARGET_DIR}/")
        else item
        for item in files
    )
    required = {"blueprint", ".lake/build", ".lake/config", ".archon/logs"}
    if not required.issubset(set(sealed.MUTABLE_WORKSPACE_DIRS)):
        raise LaunchError("sealed mutable blueprint/Lake/Archon contract drifted")


def _ensure_legacy_umbrella_anchor(workspace: Path) -> str:
    """Satisfy sealed IChO path anchors with exact IPhO-only content."""

    source = _plain_file(workspace / f"{TARGET_DIR}.lean", label="IPhO umbrella")
    legacy = workspace / f"{LEGACY_TARGET_DIR}.lean"
    if legacy.exists() or legacy.is_symlink():
        legacy_file = _plain_file(legacy, label="sealed umbrella compatibility anchor")
        if _sha256_file(legacy_file) != _sha256_file(source):
            raise LaunchError("sealed umbrella compatibility anchor differs from IPhO")
        method = "existing-identical"
    else:
        try:
            os.link(source, legacy, follow_symlinks=False)
            method = "hardlink"
        except OSError as exc:
            if exc.errno not in {errno.EXDEV, errno.EPERM, errno.EACCES}:
                raise
            shutil.copyfile(source, legacy, follow_symlinks=False)
            os.chown(legacy, 0, 0, follow_symlinks=False)
            os.chmod(legacy, 0o644, follow_symlinks=False)
            method = "copy"
    if _sha256_file(legacy) != _sha256_file(source):
        raise LaunchError("failed to create an exact umbrella compatibility anchor")

    legacy_directory = workspace / LEGACY_TARGET_DIR
    if legacy_directory.exists() or legacy_directory.is_symlink():
        if legacy_directory.is_symlink() or not legacy_directory.is_dir():
            raise LaunchError("sealed legacy target compatibility directory is unsafe")
    else:
        legacy_directory.mkdir(mode=0o755)
    os.chown(legacy_directory, 0, 0)
    os.chmod(legacy_directory, 0o755)

    legacy_all = legacy_directory / "All.lean"
    expected = (
        f"import {TARGET_DIR}\n\n"
        "/-! Sealed-helper compatibility anchor. -/\n"
    ).encode("utf-8")
    if legacy_all.exists() or legacy_all.is_symlink():
        legacy_all_file = _plain_file(
            legacy_all, label="sealed legacy target compatibility anchor"
        )
        if legacy_all_file.read_bytes() != expected:
            raise LaunchError("sealed legacy target compatibility anchor differs")
    else:
        descriptor = os.open(
            legacy_all, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644
        )
        try:
            os.write(descriptor, expected)
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
    os.chown(legacy_all, 0, 0)
    os.chmod(legacy_all, 0o644)
    return method + "+legacy-target-all"

def _validate_broker_binding(
    receipt: Mapping[str, Any],
    credentials: Mapping[str, str],
    *,
    run_id: str,
) -> int:
    base_url = credentials.get("ANTHROPIC_BASE_URL", "")
    parsed = urlparse(base_url)
    if (
        parsed.scheme not in {"http", "https"}
        or parsed.hostname != "127.0.0.1"
        or parsed.port is None
        or parsed.username
        or parsed.password
    ):
        raise LaunchError("solver broker URL must use explicit IPv4 loopback and port")
    dummy_keys = [
        key
        for key in ("ANTHROPIC_AUTH_TOKEN", "ANTHROPIC_API_KEY")
        if credentials.get(key)
    ]
    if len(dummy_keys) != 1 or credentials[dummy_keys[0]] != DUMMY_TOKEN:
        raise LaunchError("solver environment must contain only the fixed dummy token")
    if (
        receipt.get("phase") != "model_broker_ready"
        or receipt.get("run_id") != run_id
        or receipt.get("allowed_model") != MODEL
        or receipt.get("listen_url") != base_url
        or receipt.get("request_profile") != BROKER_REQUEST_PROFILE
    ):
        raise LaunchError("broker-ready receipt does not bind this run/model/URL")
    if receipt.get("public_dummy_key_sha256") != hashlib.sha256(
        DUMMY_TOKEN.encode("utf-8")
    ).hexdigest():
        raise LaunchError("broker-ready receipt does not bind the public dummy token")
    return parsed.port


def _probe_model_broker(receipt_path: Path, *, expected_sha256: str) -> None:
    """Verify the exact request-profile-aware loopback broker health identity."""

    if _sha256_file(receipt_path) != expected_sha256:
        raise LaunchError("model broker ready receipt drifted before health check")
    receipt = _load_json(receipt_path, label="model broker receipt")
    parsed = urlparse(str(receipt.get("listen_url") or ""))
    if (
        parsed.scheme != "http"
        or parsed.hostname != "127.0.0.1"
        or parsed.port is None
    ):
        raise LaunchError("model broker receipt has no exact IPv4 loopback port")
    connection = http.client.HTTPConnection(parsed.hostname, parsed.port, timeout=2)
    try:
        connection.request(
            "GET",
            "/__answer_blind_health",
            headers={"Authorization": f"Bearer {DUMMY_TOKEN}"},
        )
        response = connection.getresponse()
        payload = response.read(64 * 1024)
        if response.status != 200:
            raise LaunchError(
                f"model broker health endpoint returned HTTP {response.status}"
            )
        health = json.loads(payload)
    except (OSError, http.client.HTTPException, json.JSONDecodeError) as exc:
        raise LaunchError("hash-bound model broker health check failed") from exc
    finally:
        connection.close()
    expected_health = {
        "schema_version": receipt.get("schema_version"),
        "protocol": receipt.get("protocol"),
        "phase": "model_broker_health",
        "variant": receipt.get("variant"),
        "run_id": receipt.get("run_id"),
        "allowed_model": receipt.get("allowed_model"),
        "broker_binary_sha256": receipt.get("broker_binary_sha256"),
        "request_profile": BROKER_REQUEST_PROFILE,
    }
    if health != expected_health:
        raise LaunchError("model broker health identity differs from its ready receipt")
    if _sha256_file(receipt_path) != expected_sha256:
        raise LaunchError("model broker ready receipt drifted during health check")


def _validate_readonly_tree(
    path: Path, *, label: str, require_other_readable: bool = False
) -> dict[str, int]:
    files = 0
    directories = 0
    bytes_total = 0
    pending = [path]
    while pending:
        current = pending.pop()
        metadata = current.lstat()
        mode = stat.S_IMODE(metadata.st_mode)
        if not (
            stat.S_ISDIR(metadata.st_mode) or stat.S_ISREG(metadata.st_mode)
        ):
            raise LaunchError(f"{label} contains an unsupported entry: {current}")
        if metadata.st_uid != 0 or mode & 0o022:
            raise LaunchError(f"{label} entry is not root-owned read-only: {current}")
        if stat.S_ISDIR(metadata.st_mode):
            if require_other_readable and mode & 0o005 != 0o005:
                raise LaunchError(f"{label} directory is not solver-readable: {current}")
            directories += 1
            with os.scandir(current) as entries:
                pending.extend(Path(entry.path) for entry in entries)
        elif stat.S_ISREG(metadata.st_mode):
            if require_other_readable and not mode & stat.S_IROTH:
                raise LaunchError(f"{label} file is not solver-readable: {current}")
            files += 1
            bytes_total += metadata.st_size
    return {"files": files, "directories": directories, "bytes": bytes_total}


def _relative_tree(path: Path) -> tuple[set[str], dict[str, Path]]:
    directories: set[str] = set()
    files: dict[str, Path] = {}
    for root, names, filenames in os.walk(path, topdown=True, followlinks=False):
        base = Path(root)
        for name in names:
            child = base / name
            directories.add(child.relative_to(path).as_posix())
        for name in filenames:
            child = base / name
            files[child.relative_to(path).as_posix()] = child
    return directories, files


def _parent_directories(paths: Iterable[str]) -> set[str]:
    result: set[str] = set()
    for raw in paths:
        parent = Path(raw).parent
        while parent != Path("."):
            result.add(parent.as_posix())
            parent = parent.parent
    return result


def _validate_lean_explore_hf_cache(
    path: Path,
    *,
    expected_revision: str = LEAN_EXPLORE_EMBEDDING_REVISION,
    expected_blobs: Mapping[str, str] = LEAN_EXPLORE_EMBEDDING_BLOBS,
    expected_snapshot_blobs: Mapping[
        str, str
    ] = LEAN_EXPLORE_EMBEDDING_SNAPSHOT_BLOBS,
    expected_missing_markers: set[
        str
    ] = LEAN_EXPLORE_EMBEDDING_MISSING_MARKERS,
) -> dict[str, Any]:
    """Validate the exact materialized offline embedding-model cache."""

    label = "LeanExplore Hugging Face cache"
    inventory = _validate_readonly_tree(
        path, label=label, require_other_readable=True
    )
    hub = path / "hub"
    model = hub / LEAN_EXPLORE_EMBEDDING_CACHE_REPO
    if {child.name for child in path.iterdir()} != {"hub"}:
        raise LaunchError(f"{label} root must contain only hub")
    if hub.is_symlink() or not hub.is_dir():
        raise LaunchError(f"{label} hub entry is not a plain directory")
    if {child.name for child in hub.iterdir()} != {
        LEAN_EXPLORE_EMBEDDING_CACHE_REPO
    }:
        raise LaunchError(
            f"{label} must contain only {LEAN_EXPLORE_EMBEDDING_MODEL}"
        )
    if model.is_symlink() or not model.is_dir():
        raise LaunchError(f"{label} model entry is not a plain directory")

    model_entries = {child.name for child in model.iterdir()}
    expected_model_entries = {"blobs", "refs", "snapshots"}
    if expected_missing_markers:
        expected_model_entries.add(".no_exist")
    if model_entries != expected_model_entries:
        raise LaunchError(f"{label} model tree has an unexpected top-level manifest")

    refs = model / "refs"
    snapshots = model / "snapshots"
    main_ref = _plain_file(refs / "main", label=f"{label} main ref")
    try:
        raw_revision = main_ref.read_bytes()
    except OSError as exc:
        raise LaunchError(f"{label} main ref is invalid") from exc
    if raw_revision != expected_revision.encode("ascii"):
        raise LaunchError(f"{label} main ref is not the pinned revision")
    revision = expected_revision
    if {child.name for child in refs.iterdir()} != {"main"}:
        raise LaunchError(f"{label} must contain only the main ref")
    if {child.name for child in snapshots.iterdir()} != {revision}:
        raise LaunchError(f"{label} must contain exactly its pinned snapshot")

    blobs = _plain_directory(model / "blobs", label=f"{label} blobs")
    blob_directories, blob_files = _relative_tree(blobs)
    if blob_directories or set(blob_files) != set(expected_blobs):
        raise LaunchError(f"{label} blob manifest differs from the pinned model")
    for name, expected_sha256 in expected_blobs.items():
        if _sha256_file(blob_files[name]) != expected_sha256:
            raise LaunchError(f"{label} blob digest differs: {name}")

    snapshot = _plain_directory(
        snapshots / revision, label=f"{label} pinned snapshot"
    )
    snapshot_directories, snapshot_files = _relative_tree(snapshot)
    if (
        snapshot_directories != _parent_directories(expected_snapshot_blobs)
        or set(snapshot_files) != set(expected_snapshot_blobs)
    ):
        raise LaunchError(f"{label} snapshot manifest differs from the pinned model")
    for relative, blob_name in expected_snapshot_blobs.items():
        if blob_name not in blob_files or not os.path.samefile(
            snapshot_files[relative], blob_files[blob_name]
        ):
            raise LaunchError(f"{label} snapshot is not materialized as pinned hardlinks")

    if expected_missing_markers:
        no_exist_revision = _plain_directory(
            model / ".no_exist" / revision,
            label=f"{label} missing-file markers",
        )
        marker_directories, marker_files = _relative_tree(no_exist_revision)
        if (
            marker_directories != _parent_directories(expected_missing_markers)
            or set(marker_files) != expected_missing_markers
            or any(path.stat().st_size for path in marker_files.values())
        ):
            raise LaunchError(f"{label} missing-file marker manifest differs")
        if {child.name for child in (model / ".no_exist").iterdir()} != {
            revision
        }:
            raise LaunchError(f"{label} contains markers for an extra revision")
    return {
        "path": str(path),
        "model": LEAN_EXPLORE_EMBEDDING_MODEL,
        "revision": revision,
        "layout": "exact-materialized-huggingface-hub-cache-v1",
        "manifest_verified": True,
        **inventory,
    }


def _sealed_site_packages(runtime_root: Path) -> Path:
    candidates = sorted((runtime_root / "venv/lib").glob("python*/site-packages"))
    candidates = [path.resolve() for path in candidates if (path / "archon").is_dir()]
    if len(candidates) != 1:
        raise LaunchError("sealed Archon site-packages path is ambiguous")
    return candidates[0]


def _confirm_archon_origin(
    *, runtime_root: Path, sealed_site: Path, supplemental_site: Path
) -> str:
    python_path = os.pathsep.join((str(sealed_site), str(supplemental_site)))
    environment = {
        "PATH": f"{runtime_root}/bin:{runtime_root}/venv/bin",
        "PYTHONPATH": python_path,
        "PYTHONDONTWRITEBYTECODE": "1",
        "PYTHONNOUSERSITE": "1",
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
    }
    command = (
        "import pathlib,archon; "
        "print(pathlib.Path(archon.__file__).resolve(), end='')"
    )
    completed = subprocess.run(
        [str(runtime_root / "venv/bin/python"), "-c", command],
        env=environment,
        check=False,
        capture_output=True,
        text=True,
        timeout=30,
    )
    if completed.returncode != 0:
        raise LaunchError("cannot verify sealed Archon import provenance")
    origin = Path(completed.stdout.strip()).resolve()
    if not _inside(origin, sealed_site / "archon"):
        raise LaunchError(f"supplemental PYTHONPATH shadows sealed Archon: {origin}")
    return python_path


def _project_lean_explore_cache(source: Path, home: Path) -> dict[str, Any]:
    inventory = _validate_readonly_tree(source, label="LeanExplore cache")
    destination = home / ".lean_explore"
    if destination.exists() or destination.is_symlink():
        raise LaunchError("private solver home already contains .lean_explore")
    destination.mkdir(mode=0o755)
    os.chown(destination, 0, 0)
    hardlinks = 0
    copies = 0
    directories: list[Path] = [destination]
    for root, names, files in os.walk(source, topdown=True, followlinks=False):
        source_root = Path(root)
        relative = source_root.relative_to(source)
        target_root = destination / relative
        for name in names:
            source_dir = source_root / name
            if source_dir.is_symlink() or not source_dir.is_dir():
                raise LaunchError(f"unsafe LeanExplore cache directory: {source_dir}")
            target_dir = target_root / name
            target_dir.mkdir(mode=0o755)
            os.chown(target_dir, 0, 0)
            directories.append(target_dir)
        for name in files:
            source_file = source_root / name
            metadata = source_file.lstat()
            if not stat.S_ISREG(metadata.st_mode):
                raise LaunchError(f"unsafe LeanExplore cache file: {source_file}")
            target_file = target_root / name
            can_link = bool(stat.S_IMODE(metadata.st_mode) & stat.S_IROTH)
            if can_link:
                try:
                    os.link(source_file, target_file, follow_symlinks=False)
                    hardlinks += 1
                    continue
                except OSError as exc:
                    if exc.errno not in {errno.EXDEV, errno.EPERM, errno.EACCES}:
                        raise
            shutil.copyfile(source_file, target_file, follow_symlinks=False)
            os.chown(target_file, 0, 0, follow_symlinks=False)
            os.chmod(target_file, 0o444, follow_symlinks=False)
            copies += 1
    for directory in sorted(directories, key=lambda item: len(item.parts), reverse=True):
        os.chmod(directory, 0o555, follow_symlinks=False)
    return {
        "source": str(source),
        "destination": str(destination),
        **inventory,
        "hardlinked_files": hardlinks,
        "copied_files": copies,
        "read_only_projection": True,
    }


def _extend_readonly_policy(
    sealed: Any, policy: Any, path: Path, *, label: str = "read-only extension"
) -> Any:
    for writable in policy.read_write_paths:
        if _inside(path, writable) or _inside(writable, path):
            raise LaunchError(f"{label} overlaps writable authority")
    for existing in policy.read_only_paths:
        if path != existing and (
            _inside(path, existing) or _inside(existing, path)
        ):
            raise LaunchError(f"{label} overlaps existing read-only authority")
    for probe in policy.probe_paths:
        if _inside(probe, path):
            raise LaunchError(f"{label} would cover a required denial probe")
    readonly = tuple(dict.fromkeys((*policy.read_only_paths, path)))
    if Path("/root") in readonly:
        raise LaunchError("Landlock policy must not admit the /root parent")
    return sealed.LandlockPolicy(
        abi=policy.abi,
        read_only_paths=readonly,
        read_write_paths=policy.read_write_paths,
        probe_paths=policy.probe_paths,
        allowed_connect_tcp_ports=policy.allowed_connect_tcp_ports,
    )


def _extend_claude_runtime_policy(
    sealed: Any,
    policy: Any,
    *,
    claude: Path,
    runtime_paths: tuple[Path, ...],
) -> Any:
    """Admit only the pinned executable and Bun metadata paths.

    /proc/1/environ remains a live negative open/read probe. Landlock must
    expose procfs so a forked Bun process can resolve /proc/self, while the
    dedicated solver UID still makes that particular probe fail closed.
    """

    readonly = list(policy.read_only_paths)

    def is_proc_environ_probe(path: Path) -> bool:
        return (
            len(path.parts) == 4
            and path.parts[:2] == ("/", "proc")
            and path.parts[2].isdigit()
            and path.parts[3] == "environ"
        )

    for path in (claude, *runtime_paths):
        for writable in policy.read_write_paths:
            if _inside(path, writable) or _inside(writable, path):
                raise LaunchError("Claude runtime authority overlaps writable authority")
        covered = False
        for existing in readonly:
            if path == existing or _inside(path, existing):
                covered = True
                break
            if _inside(existing, path):
                raise LaunchError("Claude runtime authority widens an existing rule")
        for probe in policy.probe_paths:
            if _inside(probe, path) and not (
                path == Path("/proc") and is_proc_environ_probe(probe)
            ):
                raise LaunchError("Claude runtime authority covers a denial probe")
        if not covered:
            readonly.append(path)
    if Path("/root") in readonly:
        raise LaunchError("Claude runtime policy must not admit the /root parent")
    return sealed.LandlockPolicy(
        abi=policy.abi,
        read_only_paths=tuple(readonly),
        read_write_paths=policy.read_write_paths,
        probe_paths=policy.probe_paths,
        allowed_connect_tcp_ports=policy.allowed_connect_tcp_ports,
    )


def _promote_dev_null_writable(sealed: Any, policy: Any) -> Any:
    """Give subprocesses read/write access to the exact null character device."""

    device = Path("/dev/null").resolve(strict=True)
    metadata = device.stat(follow_symlinks=False)
    if (
        device.is_symlink()
        or not stat.S_ISCHR(metadata.st_mode)
        or metadata.st_uid != 0
        or stat.S_IMODE(metadata.st_mode) != 0o666
        or (os.major(metadata.st_rdev), os.minor(metadata.st_rdev)) != (1, 3)
    ):
        raise LaunchError("/dev/null is not the exact root-owned null device")
    if device not in policy.read_only_paths:
        raise LaunchError("sealed policy no longer lists /dev/null read-only")
    readonly = tuple(path for path in policy.read_only_paths if path != device)
    for path in (*readonly, *policy.read_write_paths, *policy.probe_paths):
        if path != device and (_inside(device, path) or _inside(path, device)):
            raise LaunchError("/dev/null authority overlaps another policy path")
    return sealed.LandlockPolicy(
        abi=policy.abi,
        read_only_paths=readonly,
        read_write_paths=(*policy.read_write_paths, device),
        probe_paths=policy.probe_paths,
        allowed_connect_tcp_ports=policy.allowed_connect_tcp_ports,
    )


def _promote_dev_shm_writable(sealed: Any, policy: Any) -> Any:
    """Allow the exact shared-memory directory required by ProcessPoolExecutor."""

    shared = Path("/dev/shm").resolve(strict=True)
    metadata = shared.stat(follow_symlinks=False)
    if (
        shared.is_symlink()
        or not stat.S_ISDIR(metadata.st_mode)
        or metadata.st_uid != 0
        or stat.S_IMODE(metadata.st_mode) != 0o1777
    ):
        raise LaunchError("/dev/shm is not the exact root-owned sticky directory")
    if shared not in policy.probe_paths:
        raise LaunchError("sealed policy no longer probes /dev/shm")
    probes = tuple(path for path in policy.probe_paths if path != shared)
    for path in (*policy.read_only_paths, *policy.read_write_paths, *probes):
        if path != shared and (_inside(shared, path) or _inside(path, shared)):
            raise LaunchError("/dev/shm authority overlaps another policy path")
    return sealed.LandlockPolicy(
        abi=policy.abi,
        read_only_paths=policy.read_only_paths,
        read_write_paths=(*policy.read_write_paths, shared),
        probe_paths=probes,
        allowed_connect_tcp_ports=policy.allowed_connect_tcp_ports,
    )


def _archon_argv(
    archon: Path, *, max_iterations: int, max_parallel: int, max_objectives: int
) -> tuple[str, ...]:
    runtime_root = archon.parent.parent
    return (
        str(runtime_root / "venv/bin/python"),
        "-P",
        "-c",
        ARCHON_FORK_BOOTSTRAP,
        "loop",
        ".",
        "--from",
        "prover",
        "--max-iterations",
        str(max_iterations),
        "--max-parallel",
        str(max_parallel),
        "--max-objectives",
        str(max_objectives),
        "--formalization-review-gate",
        "--formalization-review-max-iterations",
        "3",
        "--proof-review-gate",
        "--proof-review-max-iterations",
        str(max_iterations),
        "--review",
        "--no-dashboard",
        "--no-blueprint-web",
        "--model",
        MODEL,
    )


def _write_new_json(path: Path, value: Mapping[str, Any]) -> None:
    payload = (
        json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    ).encode("utf-8")
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o400)
    try:
        os.write(descriptor, payload)
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    os.chown(path, 0, 0)
    os.chmod(path, 0o400)
    directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, required=True)
    parser.add_argument("--dependency-root", type=Path, required=True)
    parser.add_argument("--runtime-root", type=Path, default=SEALED_RUNTIME)
    parser.add_argument("--solver-user", required=True)
    parser.add_argument("--private-home", type=Path, required=True)
    parser.add_argument("--private-tmp", type=Path, required=True)
    parser.add_argument("--controller-dir", type=Path, required=True)
    parser.add_argument("--broker-ready", type=Path, required=True)
    parser.add_argument("--broker-env", type=Path, required=True)
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--lean-explore-cache", type=Path, default=Path("/root/.lean_explore"))
    parser.add_argument("--lean-explore-hf-cache", type=Path, required=True)
    parser.add_argument("--lean-explore-site-packages", type=Path)
    parser.add_argument("--max-iterations", type=int, default=100)
    parser.add_argument("--max-parallel", type=int, default=4)
    parser.add_argument("--max-objectives", type=int, default=28)
    parser.add_argument("--timeout-s", type=int, default=86400)
    return parser


def run(args: argparse.Namespace) -> tuple[dict[str, Any], int]:
    if os.geteuid() != 0:
        raise LaunchError("the confined loop launcher must run as root")
    if SAFE_RUN_ID.fullmatch(args.run_id) is None:
        raise LaunchError("run-id contains unsafe characters")
    if not 1 <= args.max_parallel <= 4:
        raise LaunchError("max-parallel must be between 1 and 4")
    if not 1 <= args.max_objectives <= 28:
        raise LaunchError("max-objectives must be between 1 and 28")
    if not 1 <= args.max_iterations <= 100 or args.timeout_s < 1:
        raise LaunchError("invalid iteration or timeout limit")

    workspace = _plain_directory(args.workspace, label="solver workspace")
    dependency = _plain_directory(args.dependency_root, label="Lean dependency root")
    runtime = _plain_directory(args.runtime_root, label="sealed runtime")
    controller = _plain_directory(args.controller_dir, label="controller directory")
    cache = _plain_directory(args.lean_explore_cache, label="LeanExplore cache")
    hf_cache = _plain_directory(
        args.lean_explore_hf_cache, label="LeanExplore Hugging Face cache"
    )
    hf_cache_inventory = _validate_lean_explore_hf_cache(hf_cache)
    _validate_controller_dir(controller)
    home = Path(args.private_home).absolute()
    temporary = Path(args.private_tmp).absolute()
    for path, label in ((home, "private home"), (temporary, "private tmp")):
        if path.exists() or path.is_symlink():
            raise LaunchError(f"{label} must be fresh and absent")
        _plain_directory(path.parent, label=f"{label} parent")
    _require_disjoint(
        {
            "workspace": workspace,
            "dependency root": dependency,
            "runtime root": runtime,
            "controller directory": controller,
            "private home": home,
            "private tmp": temporary,
            "LeanExplore source cache": cache,
            "LeanExplore Hugging Face cache": hf_cache,
        }
    )
    if (workspace / ".git").exists() or (workspace / ".archon/.env").exists():
        raise LaunchError("solver workspace must contain neither Git history nor .archon/.env")

    sealed = _load_sealed_helper(runtime)
    _install_seccomp_receive_deadline(sealed)
    _allow_seccomp_socketpair(sealed)
    _allow_seccomp_native_sockets(sealed)
    claude, claude_runtime_paths = _validate_claude_runtime()
    _parameterize_ipho_targets(sealed)
    identity = sealed._identity(args.solver_user)
    if identity.uid == 0:
        raise LaunchError("solver must use a dedicated non-root user")

    broker_ready = _plain_file(args.broker_ready, label="broker-ready receipt")
    broker_env = _plain_file(args.broker_env, label="dummy broker environment")
    _validate_controller_file(broker_ready, label="broker-ready receipt", mode=0o400)
    _validate_controller_file(broker_env, label="dummy broker environment", mode=0o600)
    credentials = sealed._load_credentials(broker_env, variant=VARIANT)
    broker_receipt = _load_json(broker_ready, label="broker-ready receipt")
    broker_port = _validate_broker_binding(
        broker_receipt, credentials, run_id=args.run_id
    )
    if broker_receipt.get("broker_uid") in {0, identity.uid}:
        raise LaunchError("broker and solver must use distinct dedicated non-root UIDs")
    broker_sha = _sha256_file(broker_ready)
    _probe_model_broker(broker_ready, expected_sha256=broker_sha)

    supplemental: Path | None = None
    supplemental_inventory: dict[str, int] | None = None
    python_path: str | None = None
    if args.lean_explore_site_packages is not None:
        supplemental = _plain_directory(
            args.lean_explore_site_packages,
            label="LeanExplore supplemental site-packages",
        )
        supplemental_inventory = _validate_readonly_tree(
            supplemental, label="LeanExplore supplemental site-packages"
        )
        sealed_site = _sealed_site_packages(runtime)
        python_path = _confirm_archon_origin(
            runtime_root=runtime,
            sealed_site=sealed_site,
            supplemental_site=supplemental,
        )

    anchor_method = _ensure_legacy_umbrella_anchor(workspace)
    hardening = sealed.harden_solver_workspace(
        workspace=workspace,
        identity=identity,
        dependency_root=dependency,
        private_home=home,
        private_tmp=temporary,
        variant=VARIANT,
        run_id=args.run_id,
    )
    cache_projection = _project_lean_explore_cache(cache, home)

    probe_paths = [
        Path("/root"),
        Path("/tmp"),
        Path("/var/tmp"),
        Path("/dev/shm"),
        Path("/dev/tty"),
        Path("/proc/1/environ"),
        controller,
        cache,
    ]
    if supplemental is not None:
        venv_parent = next(
            (parent.parent for parent in supplemental.parents if parent.name == ".venv"),
            supplemental.parent,
        )
        probe_paths.append(venv_parent)
    policy = sealed.build_landlock_policy(
        workspace=workspace,
        runtime_root=runtime,
        dependency_root=dependency,
        private_home=home,
        private_tmp=temporary,
        controller_dir=controller,
        required_probe_paths=probe_paths,
        allowed_connect_tcp_ports=(broker_port,),
    )
    policy = _promote_dev_null_writable(sealed, policy)
    policy = _promote_dev_shm_writable(sealed, policy)
    if supplemental is not None:
        policy = _extend_readonly_policy(
            sealed,
            policy,
            supplemental,
            label="LeanExplore supplemental site-packages",
        )
    policy = _extend_readonly_policy(
        sealed,
        policy,
        hf_cache,
        label="LeanExplore Hugging Face cache",
    )
    policy = _extend_claude_runtime_policy(
        sealed,
        policy,
        claude=claude,
        runtime_paths=claude_runtime_paths,
    )

    environment = sealed._minimal_environment(
        home=home,
        temporary=temporary,
        runtime_root=runtime,
        credential_values=credentials,
    )
    environment.update(
        {
            "ANSWER_BLIND_MCP_RUNTIME_ROOT": str(runtime),
            "ANSWER_BLIND_MCP_DEPENDENCY_ROOT": str(dependency),
            "ANSWER_BLIND_MCP_WORKSPACE": str(workspace),
            "LEAN_EXPLORE_CACHE_DIR": str(home / ".lean_explore/cache"),
            "LEAN_EXPLORE_VERSION": LEAN_EXPLORE_VERSION,
            "ANTHROPIC_MODEL": MODEL,
            "ANTHROPIC_DEFAULT_OPUS_MODEL": MODEL,
            "ANTHROPIC_DEFAULT_SONNET_MODEL": MODEL,
            "ANTHROPIC_DEFAULT_HAIKU_MODEL": MODEL,
            "ANTHROPIC_DEFAULT_FABLE_MODEL": MODEL,
            "CLAUDE_CODE_SUBAGENT_MODEL": MODEL,
            "CLAUDE_CODE_AUTO_COMPACT_WINDOW": "1048576",
            "CLAUDE_CODE_EFFORT_LEVEL": "max",
            "CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC": "1",
            "TOKIO_WORKER_THREADS": TOKIO_WORKER_THREADS,
            "GIT_CONFIG_COUNT": "1",
            "GIT_CONFIG_KEY_0": "safe.directory",
            "GIT_CONFIG_VALUE_0": str(dependency) + "/*",
            "SHELL": str(runtime / "bin/bash"),
            **_lean_explore_hf_environment(hf_cache),
        }
    )
    environment["PATH"] = str(claude.parent) + os.pathsep + environment["PATH"]
    if python_path is not None:
        environment["PYTHONPATH"] = python_path

    archon = runtime / "bin/archon"
    argv = _archon_argv(
        archon,
        max_iterations=args.max_iterations,
        max_parallel=args.max_parallel,
        max_objectives=args.max_objectives,
    )
    log_path = controller / f"{args.run_id}-ipho-confined-loop.log"
    receipt_path = controller / f"{args.run_id}-ipho-confined-loop.json"
    if receipt_path.exists() or log_path.exists():
        raise LaunchError("controller log/receipt already exists for this run-id")
    outcome = sealed.run_confined_command(
        argv=argv,
        cwd=workspace,
        environment=environment,
        identity=identity,
        policy=policy,
        log_path=log_path,
        timeout_s=args.timeout_s,
    )
    broker_postflight_error: str | None = None
    try:
        _probe_model_broker(broker_ready, expected_sha256=broker_sha)
    except Exception as exc:  # Controller records and fails closed after cleanup.
        broker_postflight_error = f"{type(exc).__name__}: {exc}"

    effective_exit = (
        126
        if outcome.confinement_error or broker_postflight_error
        else outcome.exit_code
    )
    receipt: dict[str, Any] = {
        "schema_version": 1,
        "protocol": PROTOCOL,
        "phase": "loop_complete",
        "run_id": args.run_id,
        "model": MODEL,
        "command_argv": list(argv),
        "workspace": str(workspace),
        "runtime_root": str(runtime),
        "dependency_root": str(dependency),
        "solver_user": identity.user,
        "solver_uid": identity.uid,
        "limits": {
            "max_iterations": args.max_iterations,
            "max_parallel": args.max_parallel,
            "max_objectives": args.max_objectives,
            "formalization_review_attempts": 3,
            "proof_review_attempts": args.max_iterations,
        },
        "isolation": {
            "filesystem_answer_blind": True,
            "official_answers_supplied": False,
            "model_network": "loopback_broker_only",
            "grounding_packages": ["Mathlib", "Physlib"],
        },
        "broker_ready_sha256": broker_sha,
        "broker_postflight_error": broker_postflight_error,
        "claude_code": {
            "path": str(claude),
            "sha256": CLAUDE_BINARY_SHA256,
            "landlock_access": "read-execute only",
            "runtime_readonly_paths": [str(path) for path in claude_runtime_paths],
            "seccomp_receive_deadline_s": SECCOMP_RECEIVE_DEADLINE_S,
        },
        "umbrella_compatibility_anchor": anchor_method,
        "hardening": hardening,
        "lean_explore_cache": cache_projection,
        "lean_explore_hf_cache": {
            **hf_cache_inventory,
            "landlock_access": "read-only",
            "offline_environment": ["HF_HUB_OFFLINE", "TRANSFORMERS_OFFLINE"],
        },
        "lean_explore_supplemental": (
            {
                "path": str(supplemental),
                "inventory": supplemental_inventory,
                "pythonpath_order": "sealed-first-supplemental-last",
                "archon_origin_verified": True,
            }
            if supplemental is not None
            else None
        ),
        "solver_environment_keys": sorted(environment),
        "started_at": outcome.started_at,
        "ended_at": outcome.ended_at,
        "exit_code": effective_exit,
        "raw_exit_code": outcome.exit_code,
        "timed_out": outcome.timed_out,
        "solver_stopped": outcome.solver_stopped,
        "descendants_stopped": outcome.descendants_stopped,
        "confinement_error": outcome.confinement_error,
        "dedicated_uid_quiescence": outcome.dedicated_uid_quiescence,
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
    }
    _write_new_json(receipt_path, receipt)
    return {
        "run_id": args.run_id,
        "model": MODEL,
        "exit_code": effective_exit,
        "log": str(log_path),
        "receipt": str(receipt_path),
    }, (0 if effective_exit == 0 else 1)


def main(argv: Iterable[str] | None = None) -> int:
    parser = _parser()
    args = parser.parse_args(argv)
    try:
        result, exit_code = run(args)
    except (LaunchError, OSError, subprocess.SubprocessError) as exc:
        parser.error(str(exc))
    print(json.dumps(result, ensure_ascii=False, sort_keys=True))
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
