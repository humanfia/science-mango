#!/usr/bin/env python3
"""Second Landlock layer for the answer-blind Lean MCP server.

This program is copied into the sealed runtime.  It deliberately derives the
project and dependency roots from controller-owned workspace objects instead
of accepting path authority from environment variables or command arguments.
The outer solver Landlock layer remains authoritative for the exact system
file allowlist; the broader system-library rules below can only intersect (and
therefore cannot enlarge) that already-active policy.
"""

from __future__ import annotations

import ctypes
import errno
import os
import stat
from pathlib import Path, PurePosixPath


CREATE, ADD, RESTRICT = 444, 445, 446
VERSION, PATH_BENEATH = 1, 1
NO_NEW_PRIVS = 38
RIGHTS = (1 << 15) - 1
READ_FILE = (1 << 0) | (1 << 2)
READ_DIR = READ_FILE | (1 << 3)
FILE_RW = (1 << 1) | (1 << 2) | (1 << 14)
NET_CONNECT_TCP = 1 << 1


class Ruleset(ctypes.Structure):
    _fields_ = [
        ("handled_access_fs", ctypes.c_uint64),
        ("handled_access_net", ctypes.c_uint64),
    ]


class Beneath(ctypes.Structure):
    _fields_ = [("allowed_access", ctypes.c_uint64), ("parent_fd", ctypes.c_int32)]


def _libc() -> ctypes.CDLL:
    return ctypes.CDLL(None, use_errno=True)


def _syscall(number: int, *args: object) -> int:
    result = _libc().syscall(number, *args)
    if result < 0:
        error = ctypes.get_errno()
        raise OSError(error, os.strerror(error))
    return int(result)


def _add(fd: int, path: Path, *, writable: bool) -> None:
    metadata = path.stat()
    directory = stat.S_ISDIR(metadata.st_mode)
    access = RIGHTS if writable and directory else FILE_RW if writable else READ_DIR if directory else READ_FILE
    parent = os.open(path, os.O_PATH | os.O_CLOEXEC)
    try:
        rule = Beneath(access, parent)
        _syscall(ADD, fd, ctypes.byref(rule), PATH_BENEATH, 0)
    finally:
        os.close(parent)


def _project() -> Path:
    current = Path.cwd().resolve(strict=True)
    for candidate in (current, *current.parents):
        manifest = candidate / "isolation_manifest.json"
        config = candidate / ".archon/config.json"
        if manifest.is_file() and config.is_file():
            for protected in (manifest, config):
                metadata = protected.stat(follow_symlinks=False)
                if metadata.st_uid != 0 or metadata.st_mode & 0o022:
                    raise PermissionError(f"untrusted MCP project marker: {protected}")
            return candidate
    raise PermissionError("MCP cwd is outside a controller-owned solver workspace")


def _mutable(project: Path) -> list[Path]:
    relative = (
        "IChO2026Problems", "blind_candidates", "blueprint", ".lake/build",
        ".lake/config", ".archon/logs", ".archon/task_results",
        ".archon/proof-journal", ".archon/iter", ".archon/tmp",
        ".archon/preflight", ".archon/git-dir",
        "IChO2026Problems/All.lean", ".archon/PROGRESS.md",
        ".archon/AUTO_NOTES.md", ".archon/FORMALIZATION_REVIEW_GATE.md",
        ".archon/PROOF_REVIEW_GATE.md", ".archon/formalization-review-gate.json",
        ".archon/proof-review-gate.json", ".archon/STRATEGY.md",
        ".archon/PROJECT_STATUS.md", ".archon/task_done.md",
        ".archon/task_pending.md", ".archon/ARCHON_MEMORY.md",
        ".archon/USER_HINTS.md", ".archon/last_lake_build.log",
        ".archon/sync_leanok-state.json",
    )
    return [project.joinpath(*PurePosixPath(item).parts) for item in relative]


def main() -> int:
    project = _project()
    runtime = Path(__file__).resolve(strict=True).parents[1]
    if os.environ.get("ANSWER_BLIND_MCP_RUNTIME_ROOT") != str(runtime):
        raise PermissionError("MCP runtime binding is absent or stale")
    if os.environ.get("ANSWER_BLIND_MCP_WORKSPACE") != str(project):
        raise PermissionError("MCP workspace binding is absent or stale")
    dependency_link = project / ".lake/packages"
    if not dependency_link.is_symlink():
        raise PermissionError("MCP project lacks sealed dependency link")
    dependency = dependency_link.resolve(strict=True)
    if os.environ.get("ANSWER_BLIND_MCP_DEPENDENCY_ROOT") != str(dependency):
        raise PermissionError("MCP dependency binding is absent or stale")
    if dependency.stat().st_uid != 0 or dependency.stat().st_mode & 0o022:
        raise PermissionError("MCP dependency root is not controller-owned read-only")
    old_home = Path(os.environ.get("HOME", "/root")).resolve()
    mcp_root = project / ".archon/tmp/mcp-private"
    home, temporary = mcp_root / "home", mcp_root / "tmp"
    for path in (mcp_root, home, temporary):
        path.mkdir(mode=0o700, parents=True, exist_ok=True)
        os.chmod(path, 0o700)

    for name in list(os.environ):
        upper = name.upper()
        if any(token in upper for token in ("ANTHROPIC", "OPENAI", "CODEX", "CLAUDE", "HF_TOKEN", "HUGGING_FACE", "API_KEY", "AUTH_TOKEN")):
            os.environ.pop(name, None)
    for name in (
        "ANSWER_BLIND_MCP_RUNTIME_ROOT", "ANSWER_BLIND_MCP_DEPENDENCY_ROOT",
        "ANSWER_BLIND_MCP_WORKSPACE",
    ):
        os.environ.pop(name, None)
    os.environ.update({"HOME": str(home), "TMPDIR": str(temporary), "TMP": str(temporary), "TEMP": str(temporary), "PYTHONSAFEPATH": "1"})

    # MCP/Lean never needs the model broker. Handling CONNECT_TCP with no
    # allowed port rules makes every TCP connection fail closed in this
    # nested layer, even though the parent model process may use one port.
    ruleset = Ruleset(RIGHTS, NET_CONNECT_TCP)
    fd = _syscall(CREATE, ctypes.byref(ruleset), ctypes.sizeof(ruleset), 0)
    try:
        for path in (runtime, dependency, project, Path("/usr/lib"), Path("/usr/lib64"), Path("/lib"), Path("/lib64"), Path("/etc"), Path("/dev")):
            if path.exists():
                _add(fd, path.resolve(), writable=False)
        for path in (*_mutable(project), home, temporary):
            if path.exists():
                _add(fd, path.resolve(), writable=True)
        libc = _libc()
        if libc.prctl(NO_NEW_PRIVS, 1, 0, 0, 0) != 0:
            error = ctypes.get_errno()
            raise OSError(error, os.strerror(error))
        _syscall(RESTRICT, fd, 0)
    finally:
        os.close(fd)

    for forbidden in (old_home, Path("/root"), Path("/tmp"), Path("/var/tmp"), Path("/dev/shm"), Path("/proc/1/environ")):
        try:
            probe = os.open(forbidden, os.O_RDONLY | os.O_CLOEXEC)
        except OSError as exc:
            if exc.errno not in {errno.EACCES, errno.EPERM}:
                raise
        else:
            os.close(probe)
            raise PermissionError(f"nested MCP deny probe succeeded: {forbidden}")

    candidates = list((runtime / "venv/lib").glob("python*/site-packages/archon/.archon-src/tools/lean-lsp-mcp/src"))
    if len(candidates) != 1:
        raise RuntimeError("sealed runtime has ambiguous Lean MCP module roots")
    os.environ["PYTHONPATH"] = str(candidates[0])
    python = runtime / "venv/bin/python"
    os.execve(python, [str(python), "-P", "-m", "lean_lsp_mcp"], dict(os.environ))
    return 127


if __name__ == "__main__":
    raise SystemExit(main())
