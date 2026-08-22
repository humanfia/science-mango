#!/usr/bin/env python3
"""Proof-carrying standalone runner for the paper400 Dic5 base CNF.

This module is intentionally stdlib-only at supervisor import time.  The
scientific final_v13 builder is loaded only by short-lived, isolated helper
processes after an independent final_v13 CLI preflight has exited.  The
standalone solver and the two trusted proof checkers are pinned by physical
SHA-256 and are executed sequentially through sealed memfd copies.

Production state is append-only and fail closed::

    NEW -> STATIC_SEALED -> RAW_UNSAT -> DRAT_VERIFIED
        -> LRAT_VERIFIED -> PROOF_CARRYING_LOWER_20

``RAW_SAT`` and ``UNRESOLVED`` are terminal sinks.  A claim file is created
with O_EXCL before every stateful stage; a crash poisons that root and no
retry or resume is permitted.  JSON commits are canonical, self-hashed, and
published last via fsync plus a no-replace hard link.

The code only proves a distance lower bound.  It never promotes the paper's
unverified upper bound to an exact distance.
"""

from __future__ import annotations

import argparse
import base64
import ctypes
import errno
import fcntl
import hashlib
import json
import math
import os
import resource
import selectors
import signal
import stat
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence


SCHEMA_VERSION = 2
GATE = "paper400-dic5-standalone-proof-carrying-base-v2"
AUTHORITY_PRODUCTION = "PRODUCTION"
AUTHORITY_TEST_ONLY = "TEST_ONLY"

THREAD_ENV = (
    "OMP_NUM_THREADS", "OMP_THREAD_LIMIT", "OPENBLAS_NUM_THREADS",
    "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS",
    "BLIS_NUM_THREADS", "NUMBA_NUM_THREADS", "GOTO_NUM_THREADS",
)
for _thread_name in THREAD_ENV:
    os.environ[_thread_name] = "1"

PROJECT = Path(__file__).resolve().parent.parent
RUNNER_RELATIVE_PATH = (
    "scripts/run_paper400_dic5_w6_standalone_proof_v2.py"
)
OLD_RUNNER_RELATIVE_PATH = (
    "scripts/run_paper400_dic5_w6_optimized_cnf_final_v13.py"
)
OLD_MODULE_RELATIVE_PATH = (
    "evaluation/paper400_dic5_optimized_cnf_final_v13.py"
)
OLD_TEST_RELATIVE_PATH = (
    "tests/test_paper400_dic5_optimized_cnf_final_v13_final2.py"
)

SCIENCE_PYTHON = Path(
    "/root/science-mango-qcode-coset-two-block/qcode-discovery/.venv/bin/python"
)
EXPECTED_PYTHON_REALPATH = Path("/usr/bin/python3.12")
EXPECTED_PYTHON_SHA256 = (
    "1643dacd9feaedc58f3cc581e4d22577dfe25c09b10282936186ccf0f2e61118"
)

SOLVER_PATH = Path(
    "/root/cadical-rel-1.9.5-standalone-audit/build/cadical"
)
SOLVER_AUDIT_PATH = Path(
    "/root/cadical-rel-1.9.5-standalone-audit/build/"
    "standalone-audit-manifest.json"
)
TRUST_POLICY_PATH = Path("/root/qcode-proof-tools/trusted-checker-policy.json")
DRAT_TRIM_PATH = Path("/root/qcode-proof-tools/bin/drat-trim")
LRAT_CHECK_PATH = Path("/root/qcode-proof-tools/bin/lrat-check")

EXPECTED_SOLVER_SHA256 = (
    "f8b70724eb0af0ea3b5c0c305fa6a959822ce680326f04ceee7b44ce970d1171"
)
EXPECTED_SOLVER_BYTES = 1_102_280
EXPECTED_SOLVER_VERSION = "1.9.5"
EXPECTED_SOLVER_COMMIT = "146207318796f094dcded87349a64f0c6927309e"
EXPECTED_SOLVER_AUDIT_SHA256 = (
    "d9297104990410d960a11b10cb9e1facca9ea08cdfd50c1a6f843a522da11eee"
)
EXPECTED_POLICY_FILE_SHA256 = (
    "353163220be9065fa7204ae364fd54699d34718595b38d67a9d2094210121deb"
)
EXPECTED_POLICY_CANONICAL_SHA256 = (
    "4e284ca7f01079210d458d677a8b5e81dd619da408a5e88fcd61bc703775ef4f"
)
EXPECTED_DRAT_TRIM_SHA256 = (
    "a48ebed7b4b6b373d3ddbeb3368dae7622a9e17bab7fe6eb751ab996757f9fbe"
)
EXPECTED_LRAT_CHECK_SHA256 = (
    "5b87b3ee157db3b1c6b0b70e23faa40ab123c8dd6db63d9518d64312da579517"
)
EXPECTED_CHECKER_SOURCE_COMMIT = "2e5e29cb0019d5cfd547d4208dca1b3ec290349f"
EXPECTED_DRAT_TRIM_BYTES = 51_184
EXPECTED_LRAT_CHECK_BYTES = 22_024
ELF_INTERPRETER_LEXICAL = Path("/lib64/ld-linux-x86-64.so.2")
ELF_OBJECT_SPECS = (
    (
        "ld-linux-x86-64.so.2",
        Path("/usr/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2"),
        Path("/lib64/ld-linux-x86-64.so.2"),
        236_616,
        "cd4df4f3c7b83673d61189bf2eaebd33ca4f2853ab9772b8a25e025ef99b1e81",
        (),
    ),
    (
        "libstdc++.so.6",
        Path("/usr/lib/x86_64-linux-gnu/libstdc++.so.6.0.33"),
        Path("/lib/x86_64-linux-gnu/libstdc++.so.6"),
        2_592_224,
        "1fd75fe70354a416d75aef22bcae68c47bd25d20e2d0568c30b1a9838cf62f11",
        ("libm.so.6", "libc.so.6", "ld-linux-x86-64.so.2", "libgcc_s.so.1"),
    ),
    (
        "libm.so.6",
        Path("/usr/lib/x86_64-linux-gnu/libm.so.6"),
        Path("/lib/x86_64-linux-gnu/libm.so.6"),
        952_616,
        "e9c4b28d340e415b8137480ec442662f981e1399386c5931dae0e886e3639e91",
        ("libc.so.6", "ld-linux-x86-64.so.2"),
    ),
    (
        "libgcc_s.so.1",
        Path("/usr/lib/x86_64-linux-gnu/libgcc_s.so.1"),
        Path("/lib/x86_64-linux-gnu/libgcc_s.so.1"),
        183_024,
        "d93224d2b0dab4247598be683adca02f5cf00586f99c187579cd7e92058fb7cb",
        ("libc.so.6", "ld-linux-x86-64.so.2"),
    ),
    (
        "libc.so.6",
        Path("/usr/lib/x86_64-linux-gnu/libc.so.6"),
        Path("/lib/x86_64-linux-gnu/libc.so.6"),
        2_125_328,
        "8db37cf3f2169f59a0f07ef1fea308c35656668c64c8ff294e1860f4121eb161",
        ("ld-linux-x86-64.so.2",),
    ),
)
ELF_PROGRAM_SPECS = {
    "cadical-rel-1.9.5": {
        "path": SOLVER_PATH,
        "sha256": EXPECTED_SOLVER_SHA256,
        "bytes": EXPECTED_SOLVER_BYTES,
        "direct_needed": (
            "libstdc++.so.6", "libm.so.6", "libgcc_s.so.1", "libc.so.6",
        ),
    },
    "drat-trim": {
        "path": DRAT_TRIM_PATH,
        "sha256": EXPECTED_DRAT_TRIM_SHA256,
        "bytes": EXPECTED_DRAT_TRIM_BYTES,
        "direct_needed": ("libc.so.6",),
    },
    "lrat-check": {
        "path": LRAT_CHECK_PATH,
        "sha256": EXPECTED_LRAT_CHECK_SHA256,
        "bytes": EXPECTED_LRAT_CHECK_BYTES,
        "direct_needed": ("libc.so.6",),
    },
}


EXPECTED_OLD_MODULE_SHA256 = (
    "5f55709382a7f6d2087199440d9e53351114e0a32129eaabc584464409ce6ee2"
)
EXPECTED_OLD_RUNNER_SHA256 = (
    "f1f89ff6996d92b38a855660d2d1d70a18793095961c3ebd9f9bae3d64376e2b"
)
EXPECTED_OLD_TEST_SHA256 = (
    "7b0fe015c7fefdafdcf9367d63524ba7a56a0a32498ce125742c367ba910e672"
)
EXPECTED_BASE_CNF_SHA256 = (
    "3ca7bbc31792b27363af4dd56ca79facf1501a1a97d66d64b5684b3597191537"
)
EXPECTED_BASE_DIMACS_SHA256 = (
    "0e4c96f4f002f956d12ff9d3f50d6487d389afcea63d02177fc2a29c4755bd07"
)
EXPECTED_BASE_NUM_VARIABLES = 2_955
EXPECTED_BASE_NUM_CLAUSES = 12_022
EXPECTED_BASE_DIMACS_BYTES = 203_044

SOLVER_TIMEOUT_S = 43_200
CHECKER_TIMEOUT_S = 604_800
PREPARE_TIMEOUT_S = 3_600
TERM_GRACE_S = 30
PR_SET_PDEATHSIG = 1
CHILD_PDEATH_SIGNAL = int(signal.SIGKILL)
FORWARDED_PARENT_SIGNALS = (
    int(signal.SIGHUP), int(signal.SIGINT), int(signal.SIGTERM),
)
_LIBC = ctypes.CDLL(None, use_errno=True)
_PRCTL = _LIBC.prctl
_PRCTL.argtypes = [
    ctypes.c_int, ctypes.c_ulong, ctypes.c_ulong, ctypes.c_ulong, ctypes.c_ulong,
]
_PRCTL.restype = ctypes.c_int
PROOF_MAX_BYTES = 1 << 40
LRAT_MAX_BYTES = 1 << 40
DISK_RESERVE_MARGIN_BYTES = 128 << 30
SOLVER_STDOUT_MAX_BYTES = 16 << 20
SOLVER_STDERR_MAX_BYTES = 16 << 20
CHECKER_LOG_MAX_BYTES = 1 << 20
PREPARE_LOG_MAX_BYTES = 64 << 20
JSON_MAX_BYTES = 128 << 20

RESOURCE_CPU_INTERVALS = 3
RESOURCE_CPU_INTERVAL_S = 2.0
RESOURCE_MAX_BUSY_PERCENT = 60.0
RESOURCE_MIN_RAW_HEADROOM = 8 << 30
RESOURCE_MIN_EFFECTIVE_HEADROOM = 16 << 30
RESOURCE_MAX_EFFECTIVE_FRACTION = 0.75
RESOURCE_MAX_MEMORY_PSI_FULL_AVG10 = 1.0
RESOURCE_MAX_MEMORY_PSI_FULL_AVG60 = 1.0

STATIC_MANIFEST = Path("static/manifest.json")
STATIC_PREFLIGHT = Path("static/old-v13-preflight.json")
STATIC_DIMACS = Path("static/optimized.cnf")
STATIC_COMMIT = Path("state/00-static.commit.json")
SOLVE_CLAIM = Path("state/10-solve.claim")
RAW_COMMIT = Path("state/11-raw.json")
VERIFY_CLAIM = Path("state/20-verify.claim")
DRAT_COMMIT = Path("state/21-drat.json")
LRAT_COMMIT = Path("state/22-lrat.json")
FINALIZE_CLAIM = Path("state/30-finalize.claim")
DRAT_ARTIFACT = Path("artifacts/base.drat")
LRAT_ARTIFACT = Path("artifacts/base.lrat")
CERTIFICATE = Path("certificate.json")
FINAL_COMMIT = Path("COMMIT.json")

STATES = frozenset({
    "NEW", "STATIC_SEALED", "RAW_SAT", "RAW_UNSAT", "UNRESOLVED",
    "DRAT_VERIFIED", "LRAT_VERIFIED", "PROOF_CARRYING_LOWER_20",
})
FINAL_SINK_STATES = frozenset({
    "RAW_SAT", "UNRESOLVED", "PROOF_CARRYING_LOWER_20",
})

_PRODUCTION_CLI_NONCE = object()
_TEST_ONLY_NONCE = object()

_BUILDER_BOOTSTRAP_CODE = (
    "import importlib.abc, importlib.util, os, sys\n"
    "from pathlib import Path\n"
    "runner = Path(sys.argv[1]).resolve(strict=True)\n"
    "mode = sys.argv[2]\n"
    "project = runner.parent.parent\n"
    "class SourceOnlyLoader(importlib.abc.Loader):\n"
    " def __init__(self, path): self.path = Path(path)\n"
    " def create_module(self, spec): return None\n"
    " def exec_module(self, module):\n"
    "  fd = os.open(self.path, os.O_RDONLY | os.O_NOFOLLOW)\n"
    "  try:\n"
    "   before = os.fstat(fd)\n"
    "   if before.st_size < 0 or before.st_size > (16 << 20): "
    "raise RuntimeError('source size invalid')\n"
    "   data = b''\n"
    "   while len(data) < before.st_size:\n"
    "    chunk = os.read(fd, min(1 << 20, before.st_size - len(data)))\n"
    "    if not chunk: break\n"
    "    data += chunk\n"
    "   after = os.fstat(fd)\n"
    "  finally: os.close(fd)\n"
    "  identity = lambda s: (s.st_dev,s.st_ino,s.st_mode,s.st_uid,"
    "s.st_size,s.st_mtime_ns,s.st_ctime_ns)\n"
    "  if identity(before) != identity(after) or len(data) != before.st_size: "
    "raise RuntimeError('source changed while loading')\n"
    "  module.__file__ = str(self.path)\n"
    "  exec(compile(data, str(self.path), 'exec', dont_inherit=True, optimize=0), "
    "module.__dict__)\n"
    "class SourceOnlyFinder(importlib.abc.MetaPathFinder):\n"
    " def find_spec(self, fullname, path=None, target=None):\n"
    "  if not (fullname == 'evaluation' or fullname.startswith('evaluation.') "
    "or fullname == 'scripts' or fullname.startswith('scripts.')): return None\n"
    "  relative = Path(*fullname.split('.'))\n"
    "  package_source = project / relative / '__init__.py'\n"
    "  module_source = project / (str(relative) + '.py')\n"
    "  if package_source.is_file():\n"
    "   return importlib.util.spec_from_file_location(fullname, package_source, "
    "loader=SourceOnlyLoader(package_source), "
    "submodule_search_locations=[str(package_source.parent)])\n"
    "  if module_source.is_file():\n"
    "   return importlib.util.spec_from_file_location(fullname, module_source, "
    "loader=SourceOnlyLoader(module_source))\n"
    "  return None\n"
    "sys.meta_path.insert(0, SourceOnlyFinder())\n"
    "sys.path.insert(0, str(project))\n"
    "import scripts.run_paper400_dic5_w6_optimized_cnf_final_v13 as _old\n"
    "name = '_paper400_standalone_builder'\n"
    "spec = importlib.util.spec_from_file_location(name, runner, "
    "loader=SourceOnlyLoader(runner))\n"
    "if spec is None or spec.loader is None: "
    "raise RuntimeError('builder spec unavailable')\n"
    "module = importlib.util.module_from_spec(spec)\n"
    "sys.modules[name] = module\n"
    "spec.loader.exec_module(module)\n"
    "if module.PROJECT != project: raise RuntimeError('builder project mismatch')\n"
    "if mode == '__prepare_builder':\n"
    " sys.argv = [str(runner), mode]\n"
    " raise SystemExit(module._builder_helper())\n"
    "if mode == '__sat_replay':\n"
    " raise SystemExit(module._sat_replay_helper(int(sys.argv[3])))\n"
    "raise RuntimeError('unknown isolated helper mode')\n"
)



class ProofRunnerError(RuntimeError):
    """A production binding, state, process, or proof invariant failed."""


class _ForwardedParentSignal(BaseException):
    """Propagate an external signal only after the active child tree is reaped."""

    def __init__(self, signum: int) -> None:
        super().__init__(signum)
        self.signum = signum


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def seal(value: Mapping[str, Any], field: str = "record_sha256") -> dict[str, Any]:
    result = dict(value)
    result.pop(field, None)
    result[field] = canonical_sha256(result)
    return result


def json_type_equal(actual: Any, expected: Any) -> bool:
    if type(actual) is not type(expected):
        return False
    if type(actual) is dict:
        return bool(
            set(actual) == set(expected)
            and all(json_type_equal(actual[key], expected[key]) for key in actual)
        )
    if type(actual) is list:
        return bool(
            len(actual) == len(expected)
            and all(json_type_equal(a, b) for a, b in zip(actual, expected, strict=True))
        )
    return bool(actual == expected)


def is_sha256(value: Any) -> bool:
    if type(value) is not str or len(value) != 64:
        return False
    try:
        return bytes.fromhex(value).hex() == value
    except ValueError:
        return False


def selfhash_valid(value: Any, field: str = "record_sha256") -> bool:
    if type(value) is not dict or not is_sha256(value.get(field)):
        return False
    unsigned = dict(value)
    stored = unsigned.pop(field)
    try:
        return stored == canonical_sha256(unsigned)
    except (TypeError, ValueError):
        return False


def _decode_json(payload: bytes, *, canonical: bool) -> dict[str, Any]:
    def pairs(items: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, item in items:
            if type(key) is not str or key in result:
                raise ValueError("duplicate or non-string JSON key")
            result[key] = item
        return result

    def reject_constant(value: str) -> Any:
        raise ValueError(f"non-finite JSON constant: {value}")

    try:
        result = json.loads(
            payload.decode("utf-8"),
            object_pairs_hook=pairs,
            parse_constant=reject_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        raise ProofRunnerError("invalid strict JSON") from exc
    if type(result) is not dict:
        raise ProofRunnerError("JSON root must be an exact object")
    if canonical and payload != canonical_bytes(result) + b"\n":
        raise ProofRunnerError("JSON bytes are not canonical plus one LF")
    return result


def _safe_open_regular(path: Path, *, writable: bool = False) -> int:
    target = Path(path)
    flags = os.O_NOFOLLOW | getattr(os, "O_CLOEXEC", 0)
    flags |= os.O_RDWR if writable else os.O_RDONLY
    descriptor = os.open(target, flags)
    info = os.fstat(descriptor)
    if not stat.S_ISREG(info.st_mode):
        os.close(descriptor)
        raise ProofRunnerError(f"not a regular file: {target}")
    return descriptor


def _read_fd_stable(descriptor: int, *, cap: int) -> bytes:
    before = os.fstat(descriptor)
    if before.st_size < 0 or before.st_size > cap:
        raise ProofRunnerError("file exceeds read cap")
    os.lseek(descriptor, 0, os.SEEK_SET)
    chunks: list[bytes] = []
    total = 0
    while True:
        chunk = os.read(descriptor, min(1 << 20, cap + 1 - total))
        if not chunk:
            break
        chunks.append(chunk)
        total += len(chunk)
        if total > cap:
            raise ProofRunnerError("file grew beyond read cap")
    after = os.fstat(descriptor)
    identity_before = (
        before.st_dev, before.st_ino, before.st_mode, before.st_uid,
        before.st_size, before.st_mtime_ns, before.st_ctime_ns,
    )
    identity_after = (
        after.st_dev, after.st_ino, after.st_mode, after.st_uid,
        after.st_size, after.st_mtime_ns, after.st_ctime_ns,
    )
    if identity_before != identity_after or total != before.st_size:
        raise ProofRunnerError("file changed while reading")
    return b"".join(chunks)

def _hash_fd_stable(descriptor: int, *, cap: int) -> tuple[str, int, os.stat_result]:
    """Hash a stable regular file without retaining its contents in memory."""
    before = os.fstat(descriptor)
    if not stat.S_ISREG(before.st_mode):
        raise ProofRunnerError("hash input is not a regular file")
    if before.st_size < 0 or before.st_size > cap:
        raise ProofRunnerError("file exceeds hash cap")
    digest = hashlib.sha256()
    total = 0
    os.lseek(descriptor, 0, os.SEEK_SET)
    while True:
        chunk = os.read(descriptor, min(1 << 20, cap + 1 - total))
        if not chunk:
            break
        digest.update(chunk)
        total += len(chunk)
        if total > cap:
            raise ProofRunnerError("file grew beyond hash cap")
    after = os.fstat(descriptor)
    before_identity = (
        before.st_dev, before.st_ino, before.st_mode, before.st_uid,
        before.st_nlink, before.st_size, before.st_mtime_ns, before.st_ctime_ns,
    )
    after_identity = (
        after.st_dev, after.st_ino, after.st_mode, after.st_uid,
        after.st_nlink, after.st_size, after.st_mtime_ns, after.st_ctime_ns,
    )
    if before_identity != after_identity or total != before.st_size:
        raise ProofRunnerError("file changed while hashing")
    return digest.hexdigest(), total, after



def _read_file_stable(path: Path, *, cap: int = JSON_MAX_BYTES) -> bytes:
    descriptor = _safe_open_regular(path)
    try:
        return _read_fd_stable(descriptor, cap=cap)
    finally:
        os.close(descriptor)


def file_sha256(path: Path, *, expected_bytes: int | None = None) -> str:
    descriptor = _safe_open_regular(path)
    try:
        digest, total, _ = _hash_fd_stable(
            descriptor,
            cap=(expected_bytes if expected_bytes is not None else PROOF_MAX_BYTES),
        )
    finally:
        os.close(descriptor)
    if expected_bytes is not None and total != expected_bytes:
        raise ProofRunnerError(f"file size mismatch: {path}")
    return digest


def _strict_json(path: Path) -> dict[str, Any]:
    return _decode_json(_read_file_stable(path), canonical=True)


def _physical_record_from_hash(
    path: Path,
    root: Path,
    role: str,
    *,
    digest: str,
    total: int,
    info: os.stat_result,
) -> dict[str, Any]:
    target = Path(path)
    try:
        relative = target.relative_to(root).as_posix()
    except ValueError as exc:
        raise ProofRunnerError("artifact escapes result root") from exc
    lexical = os.stat(target, follow_symlinks=False)
    fd_identity = (
        info.st_dev, info.st_ino, info.st_mode, info.st_uid, info.st_nlink,
        info.st_size, info.st_mtime_ns, info.st_ctime_ns,
    )
    path_identity = (
        lexical.st_dev, lexical.st_ino, lexical.st_mode, lexical.st_uid,
        lexical.st_nlink, lexical.st_size, lexical.st_mtime_ns,
        lexical.st_ctime_ns,
    )
    if not stat.S_ISREG(lexical.st_mode) or path_identity != fd_identity:
        raise ProofRunnerError("artifact path changed while hashing")
    return {
        "role": role,
        "relative_path": relative,
        "file_sha256": digest,
        "bytes": total,
        "mode": stat.S_IMODE(info.st_mode),
        "device": info.st_dev,
        "inode": info.st_ino,
        "links": info.st_nlink,
    }


def _physical_record(path: Path, root: Path, role: str, *, cap: int) -> dict[str, Any]:
    target = Path(path)
    descriptor = _safe_open_regular(target)
    try:
        digest, total, info = _hash_fd_stable(descriptor, cap=cap)
        return _physical_record_from_hash(
            target, root, role, digest=digest, total=total, info=info,
        )
    finally:
        os.close(descriptor)




def _root_identity(root: Path) -> dict[str, Any]:
    target = Path(root)
    lexical = os.stat(target, follow_symlinks=False)
    if not stat.S_ISDIR(lexical.st_mode):
        raise ProofRunnerError("result root is not a directory")
    if stat.S_IMODE(lexical.st_mode) != 0o700:
        raise ProofRunnerError("result root mode is not 0700")
    if lexical.st_uid != os.geteuid():
        raise ProofRunnerError("result root is not owned by effective uid")
    if target.is_symlink() or target.resolve(strict=True) != target:
        raise ProofRunnerError("result root is not a canonical real directory")
    return {
        "absolute_path": str(target),
        "device": lexical.st_dev,
        "inode": lexical.st_ino,
        "mode": stat.S_IMODE(lexical.st_mode),
        "uid": lexical.st_uid,
    }


def _validate_root_argument(root: Path, *, must_exist: bool) -> Path:
    target = Path(root)
    if not target.is_absolute() or str(target) != os.path.abspath(str(target)):
        raise ProofRunnerError("root must be a normalized absolute path")
    if target.name in {"", ".", ".."}:
        raise ProofRunnerError("root has an invalid final component")
    parent = target.parent
    if parent != PROJECT / "results":
        raise ProofRunnerError(
            "root must be one direct child of the pinned PROJECT/results directory"
        )
    parent_lstat = os.stat(parent, follow_symlinks=False)
    if (
        not stat.S_ISDIR(parent_lstat.st_mode)
        or parent.is_symlink()
        or parent.resolve(strict=True) != parent
        or parent_lstat.st_uid != os.geteuid()
    ):
        raise ProofRunnerError("root parent is not a canonical owned directory")
    if must_exist:
        _root_identity(target)
    elif target.exists() or target.is_symlink():
        raise ProofRunnerError("new result root already exists")
    return target


def _mkdir_root(root: Path) -> None:
    target = _validate_root_argument(root, must_exist=False)
    parent_flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | os.O_NOFOLLOW
    parent_fd = os.open(target.parent, parent_flags)
    try:
        os.mkdir(target.name, 0o700, dir_fd=parent_fd)
        os.fsync(parent_fd)
    finally:
        os.close(parent_fd)
    os.chmod(target, 0o700, follow_symlinks=False)
    _root_identity(target)


def _mkdir_new(parent: Path, name: str) -> None:
    if not name or "/" in name or name in {".", ".."}:
        raise ProofRunnerError("unsafe directory component")
    parent_flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | os.O_NOFOLLOW
    parent_fd = os.open(parent, parent_flags)
    try:
        os.mkdir(name, 0o700, dir_fd=parent_fd)
        os.fsync(parent_fd)
    finally:
        os.close(parent_fd)
    child = parent / name
    info = os.stat(child, follow_symlinks=False)
    if not stat.S_ISDIR(info.st_mode) or stat.S_IMODE(info.st_mode) != 0o700:
        raise ProofRunnerError("new stage directory is invalid")


def _write_all(descriptor: int, payload: bytes) -> None:
    view = memoryview(payload)
    while view:
        count = os.write(descriptor, view)
        if count <= 0:
            raise OSError("short write")
        view = view[count:]


def _atomic_publish_bytes(parent: Path, name: str, payload: bytes) -> Path:
    if not name or "/" in name or name in {".", ".."}:
        raise ProofRunnerError("unsafe artifact name")
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | os.O_NOFOLLOW
    directory = os.open(parent, flags)
    temporary = f".{name}.private-{os.getpid()}-{os.urandom(16).hex()}"
    created = False
    try:
        before = os.fstat(directory)
        lexical = os.stat(parent, follow_symlinks=False)
        if (before.st_dev, before.st_ino) != (lexical.st_dev, lexical.st_ino):
            raise ProofRunnerError("artifact parent inode changed")
        file_flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW
        descriptor = os.open(temporary, file_flags, 0o600, dir_fd=directory)
        created = True
        try:
            _write_all(descriptor, payload)
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
        os.link(
            temporary,
            name,
            src_dir_fd=directory,
            dst_dir_fd=directory,
            follow_symlinks=False,
        )
        os.fsync(directory)
        os.unlink(temporary, dir_fd=directory)
        created = False
        os.fsync(directory)
        after = os.fstat(directory)
        lexical_after = os.stat(parent, follow_symlinks=False)
        if (
            (before.st_dev, before.st_ino) != (after.st_dev, after.st_ino)
            or (before.st_dev, before.st_ino)
            != (lexical_after.st_dev, lexical_after.st_ino)
        ):
            raise ProofRunnerError("artifact parent inode changed during commit")
    finally:
        if created:
            try:
                os.unlink(temporary, dir_fd=directory)
                os.fsync(directory)
            except FileNotFoundError:
                pass
        os.close(directory)
    return parent / name


def _atomic_publish_json(parent: Path, name: str, value: Mapping[str, Any]) -> Path:
    return _atomic_publish_bytes(parent, name, canonical_bytes(value) + b"\n")


def _create_claim(root: Path, relative: Path, action: str) -> dict[str, Any]:
    target = root / relative
    payload = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-proof-stage-claim-v2",
        "gate": GATE,
        "action": action,
        "root": str(root),
        "nonce_hex": os.urandom(32).hex(),
        "pid": os.getpid(),
        "terminal": False,
    })
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW
    descriptor = os.open(target, flags, 0o600)
    try:
        _write_all(descriptor, canonical_bytes(payload) + b"\n")
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    directory = os.open(target.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)
    return payload


def _clean_env() -> dict[str, str]:
    result = {
        "PATH": "/usr/bin:/bin",
        "LC_ALL": "C",
        "LANG": "C",
        "TZ": "UTC",
    }
    result.update({name: "1" for name in THREAD_ENV})
    return result


def _hash_record(payload: bytes) -> dict[str, Any]:
    return {"bytes": len(payload), "sha256": hashlib.sha256(payload).hexdigest()}


def _status_lines(payload: bytes) -> list[bytes]:
    try:
        lines = payload.decode("ascii").splitlines()
    except UnicodeDecodeError:
        return []
    return [line.encode("ascii") for line in lines if line.startswith("s ")]


def _semantic_marker_count(payload: bytes, marker: bytes) -> int:
    try:
        lines = payload.decode("ascii").splitlines()
    except UnicodeDecodeError:
        return 0
    return sum(line == marker.decode("ascii") for line in lines)


def _kill_group(pid: int, sig: int) -> bool:
    try:
        os.killpg(pid, sig)
        return True
    except ProcessLookupError:
        return False


def _group_exists(pid: int) -> bool:
    try:
        os.killpg(pid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True


def _child_limits(file_size_cap: int) -> None:
    os.umask(0o077)
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    resource.setrlimit(resource.RLIMIT_FSIZE, (file_size_cap, file_size_cap))


def _child_setup(file_size_cap: int, expected_parent_pid: int) -> None:
    for signum in FORWARDED_PARENT_SIGNALS:
        signal.signal(signum, signal.SIG_DFL)
    _child_limits(file_size_cap)
    ctypes.set_errno(0)
    if _PRCTL(PR_SET_PDEATHSIG, CHILD_PDEATH_SIGNAL, 0, 0, 0) != 0:
        error_number = ctypes.get_errno() or errno.EPERM
        raise OSError(error_number, "PR_SET_PDEATHSIG failed")
    if os.getppid() != expected_parent_pid:
        os.kill(os.getpid(), CHILD_PDEATH_SIGNAL)
        os._exit(127)
    child_pid = os.getpid()
    if os.getpgrp() != child_pid or os.getsid(0) != child_pid:
        raise OSError(errno.EPERM, "child is not its session and process-group leader")


def _child_lifecycle_policy() -> dict[str, Any]:
    return {
        "new_session": True,
        "linux_pr_set_pdeathsig": CHILD_PDEATH_SIGNAL,
        "race_check_expected_parent_pid": True,
        "verify_child_pid_is_pgid_and_sid": True,
        "forwarded_parent_signals": list(FORWARDED_PARENT_SIGNALS),
        "forward_to_child_process_group": True,
        "term_grace_s": TERM_GRACE_S,
        "reap_direct_child_before_return": True,
        "require_empty_process_group": True,
        "reraise_parent_signal_after_reap": True,
    }


def _forward_pending_parent_signal(state: dict[str, Any]) -> None:
    signum = state["interrupt_signal"]
    child_pid = state["child_pid"]
    if (
        type(signum) is not int
        or type(child_pid) is not int
        or state["forwarded"] is True
    ):
        return
    try:
        os.killpg(child_pid, signum)
    except ProcessLookupError:
        return
    except OSError:
        state["forward_error"] = True
        return
    state["forwarded"] = True


def _install_forwarding_handlers(
    state: dict[str, Any],
) -> dict[int, Any]:
    previous: dict[int, Any] = {}

    def handler(signum: int, _frame: Any) -> None:
        if state["interrupt_signal"] is None:
            state["interrupt_signal"] = int(signum)
        if state["interrupt_signal"] == int(signum):
            _forward_pending_parent_signal(state)

    try:
        for signum in FORWARDED_PARENT_SIGNALS:
            previous[signum] = signal.getsignal(signum)
            signal.signal(signum, handler)
    except BaseException:
        for signum, old_handler in reversed(tuple(previous.items())):
            signal.signal(signum, old_handler)
        raise
    return previous


def _restore_forwarding_handlers(previous: Mapping[int, Any]) -> None:
    for signum, old_handler in reversed(tuple(previous.items())):
        signal.signal(signum, old_handler)


def _wait_child_and_group(
    process: subprocess.Popen[bytes], *, timeout_s: int,
) -> tuple[bool, bool]:
    deadline = time.monotonic() + timeout_s
    while True:
        child_reaped = process.poll() is not None
        group_empty = not _group_exists(process.pid)
        if child_reaped and group_empty:
            return True, True
        if time.monotonic() >= deadline:
            return child_reaped, group_empty
        time.sleep(0.05)


def _run_capped_process(
    argv: Sequence[str],
    *,
    timeout_s: int,
    stdout_cap: int,
    stderr_cap: int,
    cwd: Path,
    pass_fds: Sequence[int] = (),
    file_size_cap: int = PROOF_MAX_BYTES,
    watched_fds: Sequence[tuple[int, int]] = (),
) -> tuple[dict[str, Any], bytes, bytes]:
    if (
        type(timeout_s) is not int or timeout_s <= 0
        or type(stdout_cap) is not int or stdout_cap < 0
        or type(stderr_cap) is not int or stderr_cap < 0
        or type(file_size_cap) is not int or file_size_cap < 0
    ):
        raise ProofRunnerError("invalid process limits")
    start_ns = time.monotonic_ns()
    deadline_ns = start_ns + timeout_s * 1_000_000_000
    supervisor_pid = os.getpid()
    stdout = bytearray()
    stderr = bytearray()
    stdout_overflow = False
    stderr_overflow = False
    watched_overflow = False
    timed_out = False
    lingering = False
    launch_error: str | None = None
    process: subprocess.Popen[bytes] | None = None
    selector = selectors.DefaultSelector()
    return_code: int | None = None
    direct_child_reaped = False
    process_group_empty = True
    pdeathsig_setup_confirmed = False
    session_setup_confirmed = False
    stopping = False
    kill_sent = False
    kill_deadline_ns: int | None = None
    unhandled: BaseException | None = None
    signal_state: dict[str, Any] = {
        "interrupt_signal": None,
        "child_pid": None,
        "forwarded": False,
        "forward_error": False,
    }
    previous_handlers = _install_forwarding_handlers(signal_state)
    try:
        if signal_state["interrupt_signal"] is None:
            process = subprocess.Popen(
                list(argv),
                stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                cwd=str(cwd),
                env=_clean_env(),
                close_fds=True,
                pass_fds=tuple(pass_fds),
                start_new_session=True,
                preexec_fn=lambda: _child_setup(file_size_cap, supervisor_pid),
            )
            signal_state["child_pid"] = process.pid
            pdeathsig_setup_confirmed = True
            session_setup_confirmed = True
            _forward_pending_parent_signal(signal_state)
            assert process.stdout is not None and process.stderr is not None
            for stream, label in (
                (process.stdout, "stdout"), (process.stderr, "stderr"),
            ):
                os.set_blocking(stream.fileno(), False)
                selector.register(stream, selectors.EVENT_READ, label)
            while selector.get_map() or process.poll() is None:
                now_ns = time.monotonic_ns()
                interrupt_signal = signal_state["interrupt_signal"]
                if type(interrupt_signal) is int and not stopping:
                    _forward_pending_parent_signal(signal_state)
                    stopping = True
                    kill_deadline_ns = (
                        now_ns + TERM_GRACE_S * 1_000_000_000
                    )
                if not stopping and now_ns >= deadline_ns:
                    timed_out = True
                    stopping = True
                    kill_deadline_ns = (
                        now_ns + TERM_GRACE_S * 1_000_000_000
                    )
                    _kill_group(process.pid, int(signal.SIGTERM))
                for descriptor, cap in watched_fds:
                    try:
                        watched_overflow = (
                            watched_overflow or os.fstat(descriptor).st_size > cap
                        )
                    except OSError:
                        watched_overflow = True
                if watched_overflow and not stopping:
                    stopping = True
                    kill_deadline_ns = (
                        now_ns + TERM_GRACE_S * 1_000_000_000
                    )
                    _kill_group(process.pid, int(signal.SIGTERM))
                if (
                    stopping
                    and kill_deadline_ns is not None
                    and now_ns >= kill_deadline_ns
                ):
                    _kill_group(process.pid, CHILD_PDEATH_SIGNAL)
                    kill_sent = True
                    kill_deadline_ns = None
                events = selector.select(0.1)
                for key, _ in events:
                    try:
                        chunk = os.read(key.fd, 1 << 16)
                    except BlockingIOError:
                        continue
                    if not chunk:
                        selector.unregister(key.fileobj)
                        continue
                    target = stdout if key.data == "stdout" else stderr
                    cap = stdout_cap if key.data == "stdout" else stderr_cap
                    room = max(0, cap - len(target))
                    target.extend(chunk[:room])
                    if len(chunk) > room:
                        if key.data == "stdout":
                            stdout_overflow = True
                        else:
                            stderr_overflow = True
                        if not stopping:
                            stopping = True
                            kill_deadline_ns = (
                                now_ns + TERM_GRACE_S * 1_000_000_000
                            )
                            _kill_group(process.pid, int(signal.SIGTERM))
                if process.poll() is not None and not selector.get_map():
                    break
            return_code = process.wait()
            direct_child_reaped = True
            lingering = _group_exists(process.pid)
    except (OSError, subprocess.SubprocessError) as exc:
        launch_error = f"{type(exc).__name__}: {exc}"
    except BaseException as exc:
        unhandled = exc
    finally:
        try:
            if process is not None:
                if process.poll() is not None:
                    return_code = process.returncode
                    direct_child_reaped = True
                group_present = _group_exists(process.pid)
                lingering = lingering or (direct_child_reaped and group_present)
                if process.poll() is None or group_present:
                    if type(signal_state["interrupt_signal"]) is int:
                        _forward_pending_parent_signal(signal_state)
                    elif not kill_sent:
                        _kill_group(process.pid, int(signal.SIGTERM))
                    if not kill_sent:
                        _wait_child_and_group(process, timeout_s=TERM_GRACE_S)
                    if process.poll() is None or _group_exists(process.pid):
                        _kill_group(process.pid, CHILD_PDEATH_SIGNAL)
                        kill_sent = True
                        _wait_child_and_group(process, timeout_s=TERM_GRACE_S)
                try:
                    return_code = process.wait(timeout=max(1, TERM_GRACE_S))
                    direct_child_reaped = True
                except subprocess.SubprocessError:
                    direct_child_reaped = False
                process_group_empty = not _group_exists(process.pid)
                for stream in (process.stdout, process.stderr):
                    if stream is not None:
                        stream.close()
            selector.close()
        finally:
            _restore_forwarding_handlers(previous_handlers)
    if (
        process is not None
        and (direct_child_reaped is not True or process_group_empty is not True)
    ):
        cleanup_error = ProofRunnerError(
            "child cleanup did not confirm direct reap and empty process group"
        )
        if unhandled is not None:
            cleanup_error.__cause__ = unhandled
        unhandled = cleanup_error
    if type(signal_state["interrupt_signal"]) is int:
        raise _ForwardedParentSignal(signal_state["interrupt_signal"])
    if unhandled is not None:
        raise unhandled
    end_ns = time.monotonic_ns()
    if end_ns > deadline_ns:
        timed_out = True
    signum = -return_code if type(return_code) is int and return_code < 0 else None
    child_pid = signal_state["child_pid"]
    process_record = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "bounded-process-result-v2",
        "argv": list(argv),
        "cwd": str(cwd),
        "environment": _clean_env(),
        "timeout_s": timeout_s,
        "stdout_cap_bytes": stdout_cap,
        "stderr_cap_bytes": stderr_cap,
        "file_size_cap_bytes": file_size_cap,
        "exit_code": return_code,
        "signal": signum,
        "timed_out": timed_out,
        "stdout_overflow": stdout_overflow,
        "stderr_overflow": stderr_overflow,
        "watched_file_overflow": watched_overflow,
        "lingering_process_group": lingering,
        "launch_error": launch_error,
        "elapsed_ns": end_ns - start_ns,
        "child_lifecycle_policy": _child_lifecycle_policy(),
        "supervisor_pid": supervisor_pid,
        "child_pid": child_pid,
        "process_group_id": child_pid,
        "pdeathsig_setup_confirmed": pdeathsig_setup_confirmed,
        "session_setup_confirmed": session_setup_confirmed,
        "forwarded_parent_signal": None,
        "direct_child_reaped": direct_child_reaped,
        "process_group_empty": process_group_empty,
        "stdout": _hash_record(bytes(stdout)),
        "stderr": _hash_record(bytes(stderr)),
    })
    return process_record, bytes(stdout), bytes(stderr)


def _seal_memfd_from_path(
    path: Path, *, expected_sha256: str, expected_bytes: int | None,
    executable: bool,
) -> tuple[int, dict[str, Any]]:
    source_fd = _safe_open_regular(path)
    memfd = os.memfd_create(
        f"qcode-{path.name}",
        getattr(os, "MFD_CLOEXEC", 0) | getattr(os, "MFD_ALLOW_SEALING", 0),
    )
    try:
        before = os.fstat(source_fd)
        digest = hashlib.sha256()
        total = 0
        while True:
            chunk = os.read(source_fd, 1 << 20)
            if not chunk:
                break
            digest.update(chunk)
            _write_all(memfd, chunk)
            total += len(chunk)
        after = os.fstat(source_fd)
        if (
            (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns)
            != (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns)
        ):
            raise ProofRunnerError("memfd source changed while copying")
        actual_sha = digest.hexdigest()
        if actual_sha != expected_sha256:
            raise ProofRunnerError(f"pinned file hash mismatch: {path}")
        if expected_bytes is not None and total != expected_bytes:
            raise ProofRunnerError(f"pinned file size mismatch: {path}")
        os.fchmod(memfd, 0o500 if executable else 0o400)
        seals = (
            fcntl.F_SEAL_WRITE | fcntl.F_SEAL_GROW | fcntl.F_SEAL_SHRINK
            | fcntl.F_SEAL_SEAL
        )
        fcntl.fcntl(memfd, fcntl.F_ADD_SEALS, seals)
        if fcntl.fcntl(memfd, fcntl.F_GET_SEALS) != seals:
            raise ProofRunnerError("memfd seal set mismatch")
        os.lseek(memfd, 0, os.SEEK_SET)
        return memfd, {
            "source_path": str(path),
            "sha256": actual_sha,
            "bytes": total,
            "executable": executable,
            "sealed_memfd": True,
            "seals": ["WRITE", "GROW", "SHRINK", "SEAL"],
        }
    except BaseException:
        os.close(memfd)
        raise
    finally:
        os.close(source_fd)


def _stage_dynamic_runtime() -> dict[str, Any]:
    parent_path = Path("/tmp")
    parent_fd = os.open(
        parent_path, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
    )
    directory_fd = -1
    loader_fd = -1
    directory_name = ""
    staged_names: list[str] = []
    try:
        for _ in range(64):
            candidate = f"qcode-elf-{os.getpid()}-{os.urandom(16).hex()}"
            try:
                os.mkdir(candidate, 0o700, dir_fd=parent_fd)
            except FileExistsError:
                continue
            directory_name = candidate
            break
        if not directory_name:
            raise ProofRunnerError("unable to reserve private ELF directory")
        directory_fd = os.open(
            directory_name,
            os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
            dir_fd=parent_fd,
        )
        directory_info = os.fstat(directory_fd)
        if (
            not stat.S_ISDIR(directory_info.st_mode)
            or stat.S_IMODE(directory_info.st_mode) != 0o700
            or directory_info.st_uid != os.geteuid()
        ):
            raise ProofRunnerError("private ELF directory identity invalid")
        staged_records: list[dict[str, Any]] = []
        for soname, realpath, _alias, expected_bytes, expected_sha256, _needed in ELF_OBJECT_SPECS:
            source_fd = _safe_open_regular(realpath)
            destination_fd = -1
            try:
                before = os.fstat(source_fd)
                destination_fd = os.open(
                    soname,
                    os.O_RDWR | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                    0o400,
                    dir_fd=directory_fd,
                )
                digest = hashlib.sha256()
                total = 0
                while True:
                    chunk = os.read(source_fd, 1 << 20)
                    if not chunk:
                        break
                    digest.update(chunk)
                    _write_all(destination_fd, chunk)
                    total += len(chunk)
                after = os.fstat(source_fd)
                identity = lambda value: (
                    value.st_dev, value.st_ino, value.st_mode, value.st_uid,
                    value.st_nlink, value.st_size, value.st_mtime_ns,
                    value.st_ctime_ns,
                )
                if identity(before) != identity(after):
                    raise ProofRunnerError("ELF source changed while staging")
                actual_sha256 = digest.hexdigest()
                if actual_sha256 != expected_sha256 or total != expected_bytes:
                    raise ProofRunnerError("staged ELF source pin mismatch")
                os.fchmod(destination_fd, 0o400)
                os.fsync(destination_fd)
                staged_info = os.fstat(destination_fd)
                if (
                    not stat.S_ISREG(staged_info.st_mode)
                    or stat.S_IMODE(staged_info.st_mode) != 0o400
                    or staged_info.st_size != expected_bytes
                ):
                    raise ProofRunnerError("staged ELF destination invalid")
                staged_records.append({
                    "soname": soname,
                    "source_realpath": str(realpath),
                    "sha256": actual_sha256,
                    "bytes": total,
                    "device": staged_info.st_dev,
                    "inode": staged_info.st_ino,
                    "mode": stat.S_IMODE(staged_info.st_mode),
                    "uid": staged_info.st_uid,
                })
                staged_names.append(soname)
            finally:
                if destination_fd >= 0:
                    os.close(destination_fd)
                os.close(source_fd)
        os.fsync(directory_fd)
        loader_spec = ELF_OBJECT_SPECS[0]
        loader_fd, loader_memfd = _seal_memfd_from_path(
            loader_spec[1],
            expected_sha256=loader_spec[4],
            expected_bytes=loader_spec[3],
            executable=True,
        )
        source_tcb = _dynamic_elf_tcb_binding()
        record = seal({
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-private-dynamic-elf-runtime-v2",
            "source_tcb_record_sha256": source_tcb["record_sha256"],
            "system_preload_absence": source_tcb["system_preload_absence"],
            "loader_memfd": loader_memfd,
            "directory": {
                "device": directory_info.st_dev,
                "inode": directory_info.st_ino,
                "mode": stat.S_IMODE(directory_info.st_mode),
                "uid": directory_info.st_uid,
            },
            "library_path": f"/proc/self/fd/{directory_fd}",
            "staged_objects": staged_records,
            "loader_options": ["--inhibit-cache", "--library-path", "--argv0"],
            "host_kernel_vdso_trusted_boundary": True,
        })
        return {
            "parent_fd": parent_fd,
            "directory_fd": directory_fd,
            "loader_fd": loader_fd,
            "directory_name": directory_name,
            "staged_names": tuple(staged_names),
            "record": record,
        }
    except BaseException:
        if loader_fd >= 0:
            os.close(loader_fd)
        if directory_fd >= 0:
            for soname in reversed(staged_names):
                try:
                    os.unlink(soname, dir_fd=directory_fd)
                except FileNotFoundError:
                    pass
            try:
                os.fsync(directory_fd)
            except OSError:
                pass
            os.close(directory_fd)
        if directory_name:
            try:
                os.rmdir(directory_name, dir_fd=parent_fd)
                os.fsync(parent_fd)
            except OSError:
                pass
        os.close(parent_fd)
        raise


def _validate_staged_dynamic_runtime(handle: Mapping[str, Any]) -> None:
    directory_fd = handle["directory_fd"]
    record = handle["record"]
    if not json_type_equal(
        record["system_preload_absence"], _system_preload_absence_binding(),
    ):
        raise ProofRunnerError("system loader preload state changed")
    expected = {
        item["soname"]: item for item in record["staged_objects"]
    }
    if set(expected) != set(handle["staged_names"]):
        raise ProofRunnerError("staged ELF name set mismatch")
    directory_info = os.fstat(directory_fd)
    if not json_type_equal(record["directory"], {
        "device": directory_info.st_dev,
        "inode": directory_info.st_ino,
        "mode": stat.S_IMODE(directory_info.st_mode),
        "uid": directory_info.st_uid,
    }):
        raise ProofRunnerError("staged ELF directory changed")
    for soname in handle["staged_names"]:
        descriptor = os.open(
            soname, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=directory_fd,
        )
        try:
            digest, total, info = _hash_fd_stable(
                descriptor, cap=expected[soname]["bytes"],
            )
        finally:
            os.close(descriptor)
        actual = {
            "soname": soname,
            "source_realpath": expected[soname]["source_realpath"],
            "sha256": digest,
            "bytes": total,
            "device": info.st_dev,
            "inode": info.st_ino,
            "mode": stat.S_IMODE(info.st_mode),
            "uid": info.st_uid,
        }
        if not json_type_equal(actual, expected[soname]):
            raise ProofRunnerError("staged ELF object changed")


def _destroy_dynamic_runtime(handle: Mapping[str, Any]) -> None:
    parent_fd = handle["parent_fd"]
    directory_fd = handle["directory_fd"]
    loader_fd = handle["loader_fd"]
    directory_name = handle["directory_name"]
    failure: BaseException | None = None
    try:
        _validate_staged_dynamic_runtime(handle)
    except BaseException as exc:
        failure = exc
    try:
        os.close(loader_fd)
        for soname in reversed(handle["staged_names"]):
            os.unlink(soname, dir_fd=directory_fd)
        os.fsync(directory_fd)
        directory_info = os.fstat(directory_fd)
        lexical = os.stat(
            directory_name, dir_fd=parent_fd, follow_symlinks=False,
        )
        if (
            (directory_info.st_dev, directory_info.st_ino)
            != (lexical.st_dev, lexical.st_ino)
            or not stat.S_ISDIR(lexical.st_mode)
        ):
            raise ProofRunnerError("private ELF directory path changed")
        os.close(directory_fd)
        os.rmdir(directory_name, dir_fd=parent_fd)
        os.fsync(parent_fd)
    except BaseException as exc:
        if failure is None:
            failure = exc
        try:
            os.close(directory_fd)
        except OSError:
            pass
    finally:
        os.close(parent_fd)
    if failure is not None:
        raise ProofRunnerError("private ELF runtime cleanup/validation failed") from failure


def _parse_integer_mapping(path: Path) -> dict[str, int]:
    result: dict[str, int] = {}
    for line in path.read_text(encoding="ascii").splitlines():
        fields = line.split()
        if len(fields) != 2 or fields[0] in result:
            raise ProofRunnerError(f"invalid cgroup integer record: {path}")
        result[fields[0]] = int(fields[1])
    return result


def _parse_pressure(path: Path) -> dict[str, dict[str, float | int]]:
    result: dict[str, dict[str, float | int]] = {}
    for line in path.read_text(encoding="ascii").splitlines():
        fields = line.split()
        if not fields or fields[0] in result:
            raise ProofRunnerError(f"invalid PSI record: {path}")
        values: dict[str, float | int] = {}
        for item in fields[1:]:
            key, separator, raw = item.partition("=")
            if separator != "=" or key in values:
                raise ProofRunnerError(f"invalid PSI value: {path}")
            values[key] = int(raw) if key == "total" else float(raw)
        result[fields[0]] = values
    return result


def _read_cpu_snapshot(cpu: int) -> tuple[int, int]:
    for line in Path("/proc/stat").read_text(encoding="ascii").splitlines():
        fields = line.split()
        if fields and fields[0] == f"cpu{cpu}":
            values = [int(item) for item in fields[1:]]
            idle = values[3] + (values[4] if len(values) > 4 else 0)
            return sum(values), idle
    raise ProofRunnerError(f"CPU {cpu} absent")


def _cgroup_root() -> Path:
    lines = Path("/proc/self/cgroup").read_text(encoding="ascii").splitlines()
    matches = [line.split("::", 1)[1] for line in lines if line.startswith("0::")]
    if len(matches) != 1:
        raise ProofRunnerError("unambiguous cgroup v2 path unavailable")
    relative = matches[0].lstrip("/")
    result = Path("/sys/fs/cgroup") / relative
    if not result.is_dir() or result.is_symlink():
        raise ProofRunnerError("cgroup v2 directory unavailable")
    return result


def _instant_resource(root: Path) -> dict[str, Any]:
    cgroup = _cgroup_root()
    current = int((cgroup / "memory.current").read_text(encoding="ascii").strip())
    maximum_raw = (cgroup / "memory.max").read_text(encoding="ascii").strip()
    maximum = None if maximum_raw == "max" else int(maximum_raw)
    memory_stat = _parse_integer_mapping(cgroup / "memory.stat")
    events = _parse_integer_mapping(cgroup / "memory.events")
    pressure = _parse_pressure(cgroup / "memory.pressure")
    fs = os.statvfs(root)
    available = fs.f_bavail * fs.f_frsize
    return {
        "memory_current": current,
        "memory_max": maximum,
        "memory_stat": memory_stat,
        "memory_events": events,
        "memory_pressure": pressure,
        "filesystem_device": os.stat(root, follow_symlinks=False).st_dev,
        "filesystem_block_size": fs.f_frsize,
        "filesystem_bavail_blocks": fs.f_bavail,
        "filesystem_bavail_bytes": available,
    }


def _resource_gate(root: Path, *, output_cap: int) -> dict[str, Any]:
    affinity = sorted(os.sched_getaffinity(0))
    niceness = os.getpriority(os.PRIO_PROCESS, 0)
    if len(affinity) != 1 or niceness != 19:
        raise ProofRunnerError("production requires one pinned CPU at nice 19")
    cpu = affinity[0]
    snapshots = [_read_cpu_snapshot(cpu)]
    for _ in range(RESOURCE_CPU_INTERVALS):
        time.sleep(RESOURCE_CPU_INTERVAL_S)
        snapshots.append(_read_cpu_snapshot(cpu))
    busy: list[float] = []
    for before, after in zip(snapshots[:-1], snapshots[1:], strict=True):
        total = after[0] - before[0]
        idle = after[1] - before[1]
        busy.append(100.0 * (1.0 - idle / max(1, total)))
    instant = _instant_resource(root)
    memory_stat = instant["memory_stat"]
    file_bytes = int(memory_stat.get("file", 0))
    inactive_file = int(memory_stat.get("inactive_file", 0))
    reclaimable = max(0, min(file_bytes, inactive_file))
    current = instant["memory_current"]
    maximum = instant["memory_max"]
    effective_current = max(0, current - reclaimable)
    if maximum is None:
        raw_headroom = effective_headroom = None
        fraction = 0.0
        memory_capacity_safe = True
    else:
        raw_headroom = maximum - current
        effective_headroom = maximum - effective_current
        fraction = effective_current / maximum if maximum > 0 else math.inf
        memory_capacity_safe = bool(
            raw_headroom >= RESOURCE_MIN_RAW_HEADROOM
            and effective_headroom >= RESOURCE_MIN_EFFECTIVE_HEADROOM
            and maximum > 0
            and fraction <= RESOURCE_MAX_EFFECTIVE_FRACTION
        )
    full = instant["memory_pressure"].get("full", {})
    avg10 = float(full.get("avg10", math.inf))
    avg60 = float(full.get("avg60", math.inf))
    pressure_safe = bool(
        math.isfinite(avg10) and math.isfinite(avg60)
        and avg10 < RESOURCE_MAX_MEMORY_PSI_FULL_AVG10
        and avg60 < RESOURCE_MAX_MEMORY_PSI_FULL_AVG60
    )
    oom_safe = all(
        type(instant["memory_events"].get(name)) is int
        and instant["memory_events"][name] == 0
        for name in ("oom", "oom_kill", "oom_group_kill")
    )
    cpu_safe = bool(
        len(busy) == RESOURCE_CPU_INTERVALS
        and all(math.isfinite(value) and value < RESOURCE_MAX_BUSY_PERCENT for value in busy)
    )
    disk_required = output_cap + DISK_RESERVE_MARGIN_BYTES
    disk_safe = instant["filesystem_bavail_bytes"] >= disk_required
    thread_safe = all(os.environ.get(name) == "1" for name in THREAD_ENV)
    report = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "standalone-resource-gate-v2",
        "cpu": cpu,
        "affinity": affinity,
        "niceness": niceness,
        "busy_percent": busy,
        "cpu_safe": cpu_safe,
        "memory_current": current,
        "memory_max": maximum,
        "file_bytes": file_bytes,
        "inactive_file_bytes": inactive_file,
        "reclaimable_file_bytes": reclaimable,
        "raw_headroom_bytes": raw_headroom,
        "effective_current_bytes": effective_current,
        "effective_headroom_bytes": effective_headroom,
        "effective_current_fraction": fraction,
        "memory_events": instant["memory_events"],
        "memory_pressure": instant["memory_pressure"],
        "memory_capacity_safe": memory_capacity_safe,
        "pressure_safe": pressure_safe,
        "oom_safe": oom_safe,
        "filesystem_device": instant["filesystem_device"],
        "filesystem_block_size": instant["filesystem_block_size"],
        "filesystem_bavail_blocks": instant["filesystem_bavail_blocks"],
        "filesystem_bavail_bytes": instant["filesystem_bavail_bytes"],
        "output_cap_bytes": output_cap,
        "reserve_margin_bytes": DISK_RESERVE_MARGIN_BYTES,
        "disk_required_bytes": disk_required,
        "disk_safe": disk_safe,
        "thread_environment": {name: os.environ.get(name) for name in THREAD_ENV},
        "thread_environment_safe": thread_safe,
        "passed": bool(
            cpu_safe and memory_capacity_safe and pressure_safe and oom_safe
            and disk_safe and thread_safe
        ),
    })
    if report["passed"] is not True:
        raise ProofRunnerError(f"resource gate failed: {report}")
    return report


def _oom_delta(before: Mapping[str, Any], after: Mapping[str, Any]) -> dict[str, int]:
    left = before.get("memory_events", {})
    right = after.get("memory_events", {})
    if type(left) is not dict or type(right) is not dict:
        raise ProofRunnerError("memory event snapshot malformed")
    result: dict[str, int] = {}
    for name in ("oom", "oom_kill", "oom_group_kill"):
        if type(left.get(name)) is not int or type(right.get(name)) is not int:
            raise ProofRunnerError("memory event field malformed")
        result[name] = right[name] - left[name]
    return result

def _pinned_regular_binding(
    path: Path, *, expected_sha256: str, expected_bytes: int | None = None,
) -> dict[str, Any]:
    target = Path(path)
    descriptor = _safe_open_regular(target)
    try:
        before = os.fstat(descriptor)
        payload = _read_fd_stable(
            descriptor,
            cap=(expected_bytes if expected_bytes is not None else JSON_MAX_BYTES),
        )
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    actual = hashlib.sha256(payload).hexdigest()
    if actual != expected_sha256:
        raise ProofRunnerError(f"pinned SHA-256 mismatch: {target}")
    if expected_bytes is not None and len(payload) != expected_bytes:
        raise ProofRunnerError(f"pinned byte count mismatch: {target}")
    return {
        "path": str(target),
        "realpath": str(target.resolve(strict=True)),
        "sha256": actual,
        "bytes": len(payload),
        "device": before.st_dev,
        "inode": before.st_ino,
        "mode": stat.S_IMODE(before.st_mode),
        "uid": before.st_uid,
        "stable": bool(
            (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns)
            == (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns)
        ),
    }


def _system_preload_absence_binding() -> dict[str, Any]:
    etc_path = Path("/etc")
    if etc_path.resolve(strict=True) != etc_path:
        raise ProofRunnerError("/etc is not a canonical real directory")
    directory_fd = os.open(
        etc_path, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
    )
    try:
        before = os.fstat(directory_fd)
        if (
            not stat.S_ISDIR(before.st_mode)
            or before.st_uid != 0
            or stat.S_IMODE(before.st_mode) & 0o022
        ):
            raise ProofRunnerError("/etc is not a root-owned non-writable TCB directory")
        try:
            os.stat("ld.so.preload", dir_fd=directory_fd, follow_symlinks=False)
        except FileNotFoundError:
            absent = True
        else:
            absent = False
        after = os.fstat(directory_fd)
    finally:
        os.close(directory_fd)
    if (
        not absent
        or (before.st_dev, before.st_ino, before.st_mode, before.st_uid)
        != (after.st_dev, after.st_ino, after.st_mode, after.st_uid)
    ):
        raise ProofRunnerError("/etc/ld.so.preload exists or /etc changed")
    return {
        "path": "/etc/ld.so.preload",
        "absent": True,
        "etc_device": before.st_dev,
        "etc_inode": before.st_ino,
        "etc_mode": stat.S_IMODE(before.st_mode),
        "etc_uid": before.st_uid,
        "trusted_against_unprivileged_mutation": True,
    }


def _dynamic_elf_tcb_binding() -> dict[str, Any]:
    objects: list[dict[str, Any]] = []
    expected_names = {spec[0] for spec in ELF_OBJECT_SPECS}
    for soname, realpath, alias, expected_bytes, expected_sha256, needed in ELF_OBJECT_SPECS:
        if set(needed) - expected_names:
            raise ProofRunnerError("dynamic ELF dependency escapes frozen closure")
        resolved = alias.resolve(strict=True)
        if resolved != realpath:
            raise ProofRunnerError(f"dynamic ELF alias changed: {alias}")
        lexical = os.stat(alias, follow_symlinks=False)
        final_is_symlink = stat.S_ISLNK(lexical.st_mode)
        binding = _pinned_regular_binding(
            realpath,
            expected_sha256=expected_sha256,
            expected_bytes=expected_bytes,
        )
        if binding["stable"] is not True:
            raise ProofRunnerError("dynamic ELF object changed during binding")
        objects.append({
            "soname": soname,
            "alias_path": str(alias),
            "alias_parent_realpath": str(alias.parent.resolve(strict=True)),
            "alias_final_is_symlink": final_is_symlink,
            "alias_link_target": os.readlink(alias) if final_is_symlink else None,
            "resolved_realpath": str(realpath),
            "physical": binding,
            "direct_needed": list(needed),
            "rpath": None,
            "runpath": None,
        })
    programs: list[dict[str, Any]] = []
    for role in ("cadical-rel-1.9.5", "drat-trim", "lrat-check"):
        spec = ELF_PROGRAM_SPECS[role]
        direct_needed = tuple(spec["direct_needed"])
        if set(direct_needed) - expected_names:
            raise ProofRunnerError("program dependency escapes frozen ELF closure")
        physical = _pinned_regular_binding(
            spec["path"],
            expected_sha256=spec["sha256"],
            expected_bytes=spec["bytes"],
        )
        if physical["stable"] is not True:
            raise ProofRunnerError("dynamic ELF program changed during binding")
        programs.append({
            "role": role,
            "physical": physical,
            "pt_interp_lexical": str(ELF_INTERPRETER_LEXICAL),
            "pt_interp_realpath": str(ELF_INTERPRETER_LEXICAL.resolve(strict=True)),
            "direct_needed_order": list(direct_needed),
            "rpath": None,
            "runpath": None,
        })
    loader_realpath = ELF_OBJECT_SPECS[0][1]
    if ELF_INTERPRETER_LEXICAL.resolve(strict=True) != loader_realpath:
        raise ProofRunnerError("program interpreter realpath changed")
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dynamic-elf-userspace-tcb-v2",
        "programs": programs,
        "objects": objects,
        "explicit_loader_execution": True,
        "inhibit_cache": True,
        "system_preload_absence": _system_preload_absence_binding(),
        "private_library_directory_mode": 0o700,
        "staged_library_mode": 0o400,
        "host_kernel_vdso_trusted_boundary": True,
    })


def _python_binding() -> dict[str, Any]:
    lexical = os.stat(SCIENCE_PYTHON, follow_symlinks=False)
    if not stat.S_ISLNK(lexical.st_mode):
        raise ProofRunnerError("science Python path must remain the audited venv symlink")
    link_target = os.readlink(SCIENCE_PYTHON)
    realpath = SCIENCE_PYTHON.resolve(strict=True)
    if realpath != EXPECTED_PYTHON_REALPATH:
        raise ProofRunnerError("science Python realpath changed")
    physical = _pinned_regular_binding(
        realpath, expected_sha256=EXPECTED_PYTHON_SHA256,
    )
    return {
        "invocation_path": str(SCIENCE_PYTHON),
        "symlink_target": link_target,
        "symlink_device": lexical.st_dev,
        "symlink_inode": lexical.st_ino,
        "realpath": str(realpath),
        "physical": physical,
        "required_flags": ["-I", "-B"],
    }


def _source_binding() -> dict[str, Any]:
    expected = (
        (RUNNER_RELATIVE_PATH, None),
        (OLD_RUNNER_RELATIVE_PATH, EXPECTED_OLD_RUNNER_SHA256),
        (OLD_MODULE_RELATIVE_PATH, EXPECTED_OLD_MODULE_SHA256),
        (OLD_TEST_RELATIVE_PATH, EXPECTED_OLD_TEST_SHA256),
    )
    files: list[dict[str, Any]] = []
    for relative, expected_sha in expected:
        path = PROJECT / relative
        descriptor = _safe_open_regular(path)
        try:
            payload = _read_fd_stable(descriptor, cap=16 << 20)
        finally:
            os.close(descriptor)
        actual = hashlib.sha256(payload).hexdigest()
        if expected_sha is not None and actual != expected_sha:
            raise ProofRunnerError(f"audited source changed: {relative}")
        files.append({
            "relative_path": relative,
            "sha256": actual,
            "bytes": len(payload),
        })
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-proof-source-binding-v2",
        "project_realpath": str(PROJECT.resolve(strict=True)),
        "files": files,
        "science_python": _python_binding(),
    })


def _toolchain_binding() -> dict[str, Any]:
    solver = _pinned_regular_binding(
        SOLVER_PATH,
        expected_sha256=EXPECTED_SOLVER_SHA256,
        expected_bytes=EXPECTED_SOLVER_BYTES,
    )
    audit = _pinned_regular_binding(
        SOLVER_AUDIT_PATH,
        expected_sha256=EXPECTED_SOLVER_AUDIT_SHA256,
    )
    audit_json = _decode_json(
        _read_file_stable(SOLVER_AUDIT_PATH), canonical=False
    )
    try:
        audit_semantics = bool(
            audit_json["schema_version"] == 1
            and audit_json["kind"] == "cadical-rel-1.9.5-standalone-audit-v1"
            and audit_json["status"] == "PASS"
            and audit_json["scope"]["n400_solver_invoked"] is False
            and audit_json["upstream"]["commit_git_sha1"] == EXPECTED_SOLVER_COMMIT
            and audit_json["build"]["generated_files"]["build/cadical"]["sha256"]
            == EXPECTED_SOLVER_SHA256
            and audit_json["build"]["generated_files"]["build/cadical"]["bytes"]
            == EXPECTED_SOLVER_BYTES
            and audit_json["cli_audit"]["default_proof_format"] == "binary DRAT"
            and audit_json["cli_audit"]["version"]["stdout"] == EXPECTED_SOLVER_VERSION
            and audit_json["cli_audit"]["exit_codes"]
            == {"sat": 10, "unsat": 20, "unknown": 0}
        )
    except (KeyError, TypeError):
        audit_semantics = False
    if not audit_semantics:
        raise ProofRunnerError("standalone solver audit semantics mismatch")

    policy = _pinned_regular_binding(
        TRUST_POLICY_PATH,
        expected_sha256=EXPECTED_POLICY_FILE_SHA256,
    )
    policy_json = _decode_json(
        _read_file_stable(TRUST_POLICY_PATH), canonical=True
    )
    if not selfhash_valid(policy_json, "policy_sha256"):
        raise ProofRunnerError("trusted checker policy self-hash mismatch")
    if policy_json.get("policy_sha256") != EXPECTED_POLICY_CANONICAL_SHA256:
        raise ProofRunnerError("trusted checker canonical pin mismatch")
    if set(policy_json) != {
        "schema_version", "kind", "checkers", "policy_sha256",
    }:
        raise ProofRunnerError("trusted checker policy field set mismatch")
    checkers = policy_json.get("checkers")
    if type(checkers) is not dict or set(checkers) != {
        "drat-trim-v05.22.2023-gcc13.3.0-x86_64",
        "lrat-check-v05.22.2023-gcc13.3.0-x86_64",
    }:
        raise ProofRunnerError("trusted checker policy checker set mismatch")
    drat_policy = checkers["drat-trim-v05.22.2023-gcc13.3.0-x86_64"]
    lrat_policy = checkers["lrat-check-v05.22.2023-gcc13.3.0-x86_64"]
    for record, expected_hash, expected_format, expected_role, marker_hash in (
        (
            drat_policy, EXPECTED_DRAT_TRIM_SHA256, "drat", "drat-trim-verify",
            hashlib.sha256(b"s VERIFIED\n").hexdigest(),
        ),
        (
            lrat_policy, EXPECTED_LRAT_CHECK_SHA256, "lrat", "lrat-check",
            hashlib.sha256(b"c VERIFIED\n").hexdigest(),
        ),
    ):
        if (
            type(record) is not dict
            or record.get("binary_sha256") != expected_hash
            or record.get("proof_format") != expected_format
            or record.get("checker_role") != expected_role
            or record.get("timeout_s") != CHECKER_TIMEOUT_S
            or record.get("max_proof_bytes") != PROOF_MAX_BYTES
            or record.get("source_commit") != EXPECTED_CHECKER_SOURCE_COMMIT
            or record.get("semantic_stdout_sha256") != marker_hash
            or record.get("argv_roles") != ["binary", "dimacs", "proof"]
        ):
            raise ProofRunnerError("trusted checker policy semantic mismatch")
    drat = _pinned_regular_binding(
        DRAT_TRIM_PATH, expected_sha256=EXPECTED_DRAT_TRIM_SHA256, expected_bytes=EXPECTED_DRAT_TRIM_BYTES,
    )
    lrat = _pinned_regular_binding(
        LRAT_CHECK_PATH, expected_sha256=EXPECTED_LRAT_CHECK_SHA256, expected_bytes=EXPECTED_LRAT_CHECK_BYTES,
    )
    dynamic_elf_tcb = _dynamic_elf_tcb_binding()
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-proof-toolchain-binding-v2",
        "solver": solver,
        "solver_version": EXPECTED_SOLVER_VERSION,
        "solver_commit": EXPECTED_SOLVER_COMMIT,
        "solver_proof_format": "binary-drat-default",
        "solver_audit": audit,
        "trusted_checker_policy": policy,
        "trusted_checker_policy_sha256": EXPECTED_POLICY_CANONICAL_SHA256,
        "drat_trim": drat,
        "lrat_check": lrat,
        "dynamic_elf_tcb": dynamic_elf_tcb,
        "checker_source_commit": EXPECTED_CHECKER_SOURCE_COMMIT,
        "checker_timeout_s": CHECKER_TIMEOUT_S,
        "proof_max_bytes": PROOF_MAX_BYTES,
        "lrat_max_bytes": LRAT_MAX_BYTES,
        "authority_wording": (
            "pinned executable bytes and private staged userspace ELF closure; "
            "host kernel and vDSO are the explicit trusted boundary"
        ),
    })


def _validate_old_preflight(value: Any) -> dict[str, Any]:
    if type(value) is not dict or not selfhash_valid(value, "preflight_sha256"):
        raise ProofRunnerError("old final_v13 preflight self-hash mismatch")
    expected_fields = {
        "schema_version", "gate", "solver_invoked", "optimized_report",
        "source_bundle", "dimacs", "execution", "publication_certificate",
        "upload_authorized", "preflight_sha256",
    }
    if set(value) != expected_fields:
        raise ProofRunnerError("old final_v13 preflight field set mismatch")
    dimacs = value.get("dimacs")
    if type(dimacs) is not dict or set(dimacs) != {
        "sha256", "bytes", "cnf_sha256", "num_variables", "num_clauses",
    }:
        raise ProofRunnerError("old final_v13 DIMACS field set mismatch")
    expected_dimacs = {
        "sha256": EXPECTED_BASE_DIMACS_SHA256,
        "bytes": EXPECTED_BASE_DIMACS_BYTES,
        "cnf_sha256": EXPECTED_BASE_CNF_SHA256,
        "num_variables": EXPECTED_BASE_NUM_VARIABLES,
        "num_clauses": EXPECTED_BASE_NUM_CLAUSES,
    }
    if not json_type_equal(dimacs, expected_dimacs):
        raise ProofRunnerError("old final_v13 preflight DIMACS mismatch")
    if (
        value.get("schema_version") != 14
        or value.get("solver_invoked") is not False
        or value.get("publication_certificate") is not False
        or value.get("upload_authorized") is not False
        or type(value.get("optimized_report")) is not dict
        or value["optimized_report"].get("solver_invoked") is not False
    ):
        raise ProofRunnerError("old final_v13 preflight authority mismatch")
    return value

def _scientific_summary(report: Mapping[str, Any]) -> dict[str, Any]:
    try:
        baseline = report["baseline"]["preflight"]
        candidates = report["candidate_bindings"]
        rowspace = report["rowspace_certificate"]
        projection = report["logical_projection_certificate"]
        coset = report["coset_minimal_certificate"]
        cnf = report["cnf"]
        parameters = baseline["parameters"]
        weights = baseline["weights"]
        parity = candidates["parity"]
        symmetry = candidates["logical_symmetry"]
        isometry = candidates["xz_isometry"]
        w6 = candidates["w6"]
        target = candidates["target"]
    except (KeyError, TypeError) as exc:
        raise ProofRunnerError("optimized report scientific tree mismatch") from exc
    checks = {
        "report_selfhash_valid": selfhash_valid(report, "report_sha256"),
        "report_solver_invoked_false": report.get("solver_invoked") is False,
        "parameters_n400_k16": parameters == {
            "n": 400, "k": 16, "rank_Hx": 192, "rank_Hz": 192,
        },
        "both_check_row_weights_six": (
            weights.get("Hx_rows") == [6] and weights.get("Hz_rows") == [6]
        ),
        "combined_column_degree_six": weights.get("combined_column_degree") == [6],
        "w6_passed": w6.get("passed") is True,
        "even_X_normalizer": parity.get("all_X_normalizer_operators_even") is True,
        "even_Z_normalizer": parity.get("all_Z_normalizer_operators_even") is True,
        "logical_symmetry_verified": symmetry.get("verified") is True,
        "logical_bit0_partition_complete": (
            symmetry.get("canonical_Z_partition")
            == {"partition_index": 0, "anchor_indices": [], "complete_up_to_symmetry": True}
        ),
        "xz_isometry_verified": isometry.get("verified") is True,
        "xz_both_sectors_covered": isometry.get("covered_sectors") == ["X", "Z"],
        "rowspace_equal": rowspace.get("rowspace_equal") is True,
        "rowspace_rank192": (
            rowspace.get("full_rank") == 192 and rowspace.get("basis_rank") == 192
        ),
        "logical_projection_equisatisfiable": (
            projection.get("operator_projection_equisatisfiable") is True
        ),
        "coset_reduction_sound": (
            coset.get("coset_representative_reduction_sound") is True
        ),
        "target_required_distance20": target.get("required_distance") == 20,
        "target_rejection_cutoff19": target.get("rejection_cutoff") == 19,
        "optimized_cnf_exact": (
            cnf.get("cnf_sha256") == EXPECTED_BASE_CNF_SHA256
            and cnf.get("num_variables") == EXPECTED_BASE_NUM_VARIABLES
            and cnf.get("num_clauses") == EXPECTED_BASE_NUM_CLAUSES
            and cnf.get("dimacs_sha256") == EXPECTED_BASE_DIMACS_SHA256
            and cnf.get("dimacs_bytes") == EXPECTED_BASE_DIMACS_BYTES
        ),
    }
    if not all(value is True for value in checks.values()):
        failed = [name for name, passed in checks.items() if passed is not True]
        raise ProofRunnerError(f"scientific prerequisite failed: {failed}")
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-lower20-scientific-binding-v2",
        "checks": checks,
        "optimized_report_sha256": report["report_sha256"],
        "baseline_preflight_sha256": baseline["preflight_sha256"],
        "matrix_sha256": candidates["matrix_sha256"],
        "w6_report_sha256": w6["report_sha256"],
        "parity_report_sha256": parity["report_sha256"],
        "logical_symmetry_report_sha256": symmetry["report_sha256"],
        "xz_isometry_report_sha256": isometry["report_sha256"],
        "target_binding_sha256": target["binding_sha256"],
        "rowspace_report_sha256": rowspace["report_sha256"],
        "logical_projection_report_sha256": projection["report_sha256"],
        "coset_minimal_report_sha256": coset["report_sha256"],
        "base_cnf_sha256": EXPECTED_BASE_CNF_SHA256,
        "base_dimacs_sha256": EXPECTED_BASE_DIMACS_SHA256,
        "max_excluded_weight": 18,
        "parity_lifts_exclusion_through_weight": 19,
        "distance_lower_bound": 20,
    })


def _builder_helper() -> int:
    if list(sys.argv) != [str(sys.argv[0]), "__prepare_builder"]:
        raise ProofRunnerError("internal builder argv mismatch")
    if sys.flags.isolated != 1 or sys.flags.dont_write_bytecode != 1:
        raise ProofRunnerError("internal builder requires -I -B")
    sys.path.insert(0, str(PROJECT))
    from evaluation import paper400_dic5_optimized_cnf_final_v13 as optimized

    if Path(optimized.__file__).resolve(strict=True) != PROJECT / OLD_MODULE_RELATIVE_PATH:
        raise ProofRunnerError("optimized module origin mismatch")
    if file_sha256(PROJECT / OLD_MODULE_RELATIVE_PATH) != EXPECTED_OLD_MODULE_SHA256:
        raise ProofRunnerError("optimized module physical hash mismatch")
    source_before = optimized.deterministic_source_closure()
    runtime_before = optimized.deterministic_runtime_seal()
    instance = optimized.build_optimized_instance()
    source_after = optimized.deterministic_source_closure()
    runtime_after = optimized.deterministic_runtime_seal()
    if not optimized.json_type_equal(source_before, source_after):
        raise ProofRunnerError("optimized source closure changed during build")
    if not optimized.json_type_equal(runtime_before, runtime_after):
        raise ProofRunnerError("optimized runtime changed during build")
    base_sha = hashlib.sha256(instance.dimacs).hexdigest()
    if (
        base_sha != EXPECTED_BASE_DIMACS_SHA256
        or len(instance.dimacs) != EXPECTED_BASE_DIMACS_BYTES
        or instance.cnf.get("cnf_sha256") != EXPECTED_BASE_CNF_SHA256
        or instance.cnf.get("num_variables") != EXPECTED_BASE_NUM_VARIABLES
        or instance.cnf.get("num_clauses") != EXPECTED_BASE_NUM_CLAUSES
    ):
        raise ProofRunnerError("fresh optimized base mismatch")
    science = _scientific_summary(instance.report)
    result = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-fresh-builder-output-v2",
        "solver_invoked": False,
        "dimacs_base64": base64.b64encode(instance.dimacs).decode("ascii"),
        "base": {
            "cnf_sha256": instance.cnf["cnf_sha256"],
            "dimacs_sha256": base_sha,
            "num_variables": instance.cnf["num_variables"],
            "num_clauses": instance.cnf["num_clauses"],
            "dimacs_bytes": len(instance.dimacs),
        },
        "optimized_report": instance.report,
        "scientific_binding": science,
        "source_closure": source_before,
        "runtime_seal": runtime_before,
    })
    sys.stdout.buffer.write(canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    return 0


def _validate_builder_output(value: Any) -> tuple[dict[str, Any], bytes]:
    fields = {
        "schema_version", "kind", "solver_invoked", "dimacs_base64", "base",
        "optimized_report", "scientific_binding", "source_closure",
        "runtime_seal", "record_sha256",
    }
    if type(value) is not dict or set(value) != fields or not selfhash_valid(value):
        raise ProofRunnerError("fresh builder output schema/self-hash mismatch")
    if (
        value.get("schema_version") != SCHEMA_VERSION
        or value.get("kind") != "paper400-dic5-fresh-builder-output-v2"
        or value.get("solver_invoked") is not False
        or type(value.get("dimacs_base64")) is not str
    ):
        raise ProofRunnerError("fresh builder output authority mismatch")
    try:
        dimacs = base64.b64decode(value["dimacs_base64"], validate=True)
    except (ValueError, TypeError) as exc:
        raise ProofRunnerError("fresh builder DIMACS base64 invalid") from exc
    expected_base = {
        "cnf_sha256": EXPECTED_BASE_CNF_SHA256,
        "dimacs_sha256": EXPECTED_BASE_DIMACS_SHA256,
        "num_variables": EXPECTED_BASE_NUM_VARIABLES,
        "num_clauses": EXPECTED_BASE_NUM_CLAUSES,
        "dimacs_bytes": EXPECTED_BASE_DIMACS_BYTES,
    }
    if not json_type_equal(value.get("base"), expected_base):
        raise ProofRunnerError("fresh builder base binding mismatch")
    if (
        len(dimacs) != EXPECTED_BASE_DIMACS_BYTES
        or hashlib.sha256(dimacs).hexdigest() != EXPECTED_BASE_DIMACS_SHA256
    ):
        raise ProofRunnerError("fresh builder DIMACS bytes mismatch")
    science = _scientific_summary(value.get("optimized_report", {}))
    if not json_type_equal(science, value.get("scientific_binding")):
        raise ProofRunnerError("fresh builder scientific binding mismatch")
    return value, dimacs


def _process_clean(process: Mapping[str, Any], *, rc: int) -> bool:
    return bool(
        type(rc) is int
        and type(process) is dict
        and type(process.get("exit_code")) is int
        and process["exit_code"] == rc
        and process.get("signal") is None
        and process.get("timed_out") is False
        and process.get("stdout_overflow") is False
        and process.get("stderr_overflow") is False
        and process.get("watched_file_overflow") is False
        and process.get("lingering_process_group") is False
        and json_type_equal(
            process.get("child_lifecycle_policy"), _child_lifecycle_policy(),
        )
        and type(process.get("supervisor_pid")) is int
        and process["supervisor_pid"] > 0
        and type(process.get("child_pid")) is int
        and process["child_pid"] > 0
        and type(process.get("process_group_id")) is int
        and process["process_group_id"] == process["child_pid"]
        and process.get("pdeathsig_setup_confirmed") is True
        and process.get("session_setup_confirmed") is True
        and process.get("forwarded_parent_signal") is None
        and process.get("direct_child_reaped") is True
        and process.get("process_group_empty") is True
        and process.get("launch_error") is None
    )

def _prepare_materials() -> tuple[dict[str, Any], bytes, bytes]:
    sources_before = _source_binding()
    tools_before = _toolchain_binding()
    old_argv = [
        str(SCIENCE_PYTHON), "-I", "-B", str(PROJECT / OLD_RUNNER_RELATIVE_PATH),
        "preflight",
    ]
    old_process, old_stdout, old_stderr = _run_capped_process(
        old_argv,
        timeout_s=PREPARE_TIMEOUT_S,
        stdout_cap=PREPARE_LOG_MAX_BYTES,
        stderr_cap=PREPARE_LOG_MAX_BYTES,
        cwd=PROJECT,
        file_size_cap=PREPARE_LOG_MAX_BYTES,
    )
    if not _process_clean(old_process, rc=0) or old_stderr != b"":
        raise ProofRunnerError(f"independent old v13 preflight failed: {old_process}")
    old_value = _validate_old_preflight(_decode_json(old_stdout, canonical=True))

    builder_argv = [
        str(SCIENCE_PYTHON), "-I", "-B", "-c", _BUILDER_BOOTSTRAP_CODE,
        str(Path(__file__).resolve()), "__prepare_builder",
    ]
    builder_process, builder_stdout, builder_stderr = _run_capped_process(
        builder_argv,
        timeout_s=PREPARE_TIMEOUT_S,
        stdout_cap=PREPARE_LOG_MAX_BYTES,
        stderr_cap=PREPARE_LOG_MAX_BYTES,
        cwd=PROJECT,
        file_size_cap=PREPARE_LOG_MAX_BYTES,
    )
    if not _process_clean(builder_process, rc=0) or builder_stderr != b"":
        raise ProofRunnerError(f"fresh optimized builder failed: {builder_process}")
    builder_value, dimacs = _validate_builder_output(
        _decode_json(builder_stdout, canonical=True)
    )
    if not json_type_equal(old_value["dimacs"], {
        "sha256": builder_value["base"]["dimacs_sha256"],
        "bytes": builder_value["base"]["dimacs_bytes"],
        "cnf_sha256": builder_value["base"]["cnf_sha256"],
        "num_variables": builder_value["base"]["num_variables"],
        "num_clauses": builder_value["base"]["num_clauses"],
    }):
        raise ProofRunnerError("independent old preflight and fresh builder disagree")
    sources_after = _source_binding()
    tools_after = _toolchain_binding()
    if not json_type_equal(sources_before, sources_after):
        raise ProofRunnerError("source binding changed during preparation")
    if not json_type_equal(tools_before, tools_after):
        raise ProofRunnerError("toolchain binding changed during preparation")
    summary = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-standalone-static-preflight-v2",
        "gate": GATE,
        "solver_invoked": False,
        "source_binding": sources_before,
        "toolchain_binding": tools_before,
        "old_preflight_process": old_process,
        "old_preflight_sha256": old_value["preflight_sha256"],
        "old_preflight_file_sha256": hashlib.sha256(old_stdout).hexdigest(),
        "fresh_builder_process": builder_process,
        "fresh_builder_record_sha256": builder_value["record_sha256"],
        "instance_binding": {
            "base": builder_value["base"],
            "optimized_report": builder_value["optimized_report"],
            "scientific_binding": builder_value["scientific_binding"],
            "source_closure": builder_value["source_closure"],
            "runtime_seal": builder_value["runtime_seal"],
        },
        "three_process_peak_policy": [
            "independent-old-v13-preflight-exits",
            "fresh-final-v13-builder-exits",
            "stdlib-supervisor-seals-static-artifacts",
        ],
        "publication_certificate": False,
        "upload_authorized": False,
    })
    return summary, old_stdout, dimacs

def _direct_cli_context(action: str, root: Path | None) -> dict[str, Any]:
    runner_path = PROJECT / RUNNER_RELATIVE_PATH
    runner = runner_path.resolve(strict=True)
    main_module = sys.modules.get("__main__")
    main_origin = getattr(main_module, "__file__", None)
    try:
        main_realpath = (
            None if type(main_origin) is not str
            else str(Path(main_origin).resolve(strict=True))
        )
        argv0_realpath = (
            None if not sys.argv or type(sys.argv[0]) is not str
            else str(Path(sys.argv[0]).resolve(strict=True))
        )
        executable_realpath = str(Path(sys.executable).resolve(strict=True))
    except (OSError, RuntimeError):
        main_realpath = argv0_realpath = executable_realpath = None
    expected_argv = (
        [str(runner), "preflight"]
        if action == "preflight"
        else [str(runner), action, "--root", str(root)]
    )
    python_flags = {
        "isolated": sys.flags.isolated,
        "dont_write_bytecode": sys.flags.dont_write_bytecode,
        "optimize": sys.flags.optimize,
        "no_site": sys.flags.no_site,
        "ignore_environment": sys.flags.ignore_environment,
        "no_user_site": sys.flags.no_user_site,
        "safe_path": sys.flags.safe_path,
    }
    checks = {
        "module_is_main": __name__ == "__main__",
        "main_file_string_is_absolute_runner": (
            type(main_origin) is str and main_origin == str(runner)
        ),
        "main_file_is_runner": main_realpath == str(runner),
        "argv0_string_is_absolute_runner": (
            bool(sys.argv) and type(sys.argv[0]) is str
            and sys.argv[0] == str(runner)
        ),
        "argv0_is_runner": argv0_realpath == str(runner),
        "argv_is_exact": list(sys.argv) == expected_argv,
        "isolated_flag_is_one": (
            type(sys.flags.isolated) is int and sys.flags.isolated == 1
        ),
        "dont_write_bytecode_flag_is_one": (
            type(sys.flags.dont_write_bytecode) is int
            and sys.flags.dont_write_bytecode == 1
        ),
        "optimize_flag_is_zero": (
            type(sys.flags.optimize) is int and sys.flags.optimize == 0
        ),
        "site_import_is_enabled": (
            type(sys.flags.no_site) is int and sys.flags.no_site == 0
        ),
        "environment_is_ignored": (
            type(sys.flags.ignore_environment) is int
            and sys.flags.ignore_environment == 1
        ),
        "safe_path_is_enabled": sys.flags.safe_path is True,
        "science_python_invocation_exact": sys.executable == str(SCIENCE_PYTHON),
        "science_python_realpath_exact": (
            executable_realpath == str(EXPECTED_PYTHON_REALPATH)
        ),
        "runner_is_not_symlink": not runner_path.is_symlink(),
        "root_is_normalized_absolute": (
            True if root is None else (
                root.is_absolute() and str(root) == os.path.abspath(str(root))
            )
        ),
    }
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-proof-direct-cli-context-v2",
        "action": action,
        "runner_realpath": str(runner),
        "runner_sha256": file_sha256(runner),
        "main_file_string": main_origin,
        "main_file_realpath": main_realpath,
        "argv0_string": sys.argv[0] if sys.argv else None,
        "argv0_realpath": argv0_realpath,
        "python_invocation_path": sys.executable,
        "python_realpath": executable_realpath,
        "python_flags": python_flags,
        "normalized_argv": expected_argv[1:],
        "checks": checks,
        "passed": all(value is True for value in checks.values()),
    })


def _require_production_cli(
    action: str, root: Path | None, nonce: object | None,
) -> dict[str, Any]:
    if nonce is not _PRODUCTION_CLI_NONCE:
        raise ProofRunnerError("production action requires private direct-CLI authority")
    context = _direct_cli_context(action, root)
    if context["passed"] is not True:
        raise ProofRunnerError(f"production direct CLI context failed: {context}")
    return context


def _predecessor(root: Path, relative: Path, self_field: str = "record_sha256") -> dict[str, Any]:
    value = _strict_json(root / relative)
    if not selfhash_valid(value, self_field):
        raise ProofRunnerError(f"predecessor self-hash invalid: {relative}")
    physical = _physical_record(
        root / relative, root, "predecessor", cap=JSON_MAX_BYTES,
    )
    return {
        "relative_path": relative.as_posix(),
        "file_sha256": physical["file_sha256"],
        "record_sha256": value[self_field],
    }


def _static_manifest(
    root: Path,
    context: Mapping[str, Any],
    summary: Mapping[str, Any],
    old_preflight_record: Mapping[str, Any],
    base_record: Mapping[str, Any],
    *,
    authority: str,
) -> dict[str, Any]:
    test_only = authority != AUTHORITY_PRODUCTION
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-standalone-static-manifest-v2",
        "gate": GATE,
        "state": "STATIC_SEALED",
        "authority": authority,
        "test_only": test_only,
        "production_eligible": not test_only,
        "root": str(root),
        "root_identity": _root_identity(root),
        "direct_cli_context": dict(context),
        "preflight_summary": dict(summary),
        "static_artifacts": [dict(old_preflight_record), dict(base_record)],
        "base": {
            "cnf_sha256": EXPECTED_BASE_CNF_SHA256,
            "dimacs_sha256": EXPECTED_BASE_DIMACS_SHA256,
            "num_variables": EXPECTED_BASE_NUM_VARIABLES,
            "num_clauses": EXPECTED_BASE_NUM_CLAUSES,
            "dimacs_bytes": EXPECTED_BASE_DIMACS_BYTES,
            "sector": "Z",
            "logical_partition_index": 0,
            "maximum_excluded_weight": 18,
        },
        "resource_policy": {
            "solver_timeout_s": SOLVER_TIMEOUT_S,
            "checker_timeout_s": CHECKER_TIMEOUT_S,
            "proof_max_bytes": PROOF_MAX_BYTES,
            "lrat_max_bytes": LRAT_MAX_BYTES,
            "disk_reserve_margin_bytes": DISK_RESERVE_MARGIN_BYTES,
            "solver_stdout_max_bytes": SOLVER_STDOUT_MAX_BYTES,
            "solver_stderr_max_bytes": SOLVER_STDERR_MAX_BYTES,
            "checker_log_max_bytes": CHECKER_LOG_MAX_BYTES,
            "fresh_gate_before_solver": True,
            "fresh_gate_before_lrat_generation": True,
        },
        "state_machine": {
            "resume": False,
            "retry_same_root": False,
            "workers": 1,
            "three_stage_low_peak": True,
            "raw_unsat_is_lower_bound": False,
            "proof_carrying_lower_requires_lrat_verified": True,
        },
        "publication_certificate": False,
        "upload_authorized": False,
    })


def _static_commit_value(
    root: Path,
    manifest_record: Mapping[str, Any],
    old_preflight_record: Mapping[str, Any],
    base_record: Mapping[str, Any],
    *,
    authority: str,
) -> dict[str, Any]:
    test_only = authority != AUTHORITY_PRODUCTION
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-proof-state-commit-v2",
        "gate": GATE,
        "state": "STATIC_SEALED",
        "authority": authority,
        "test_only": test_only,
        "production_eligible": not test_only,
        "root": str(root),
        "predecessor": None,
        "artifacts": [
            dict(manifest_record), dict(old_preflight_record), dict(base_record),
        ],
        "publication_certificate": False,
        "upload_authorized": False,
    })


def prepare_root(
    root: Path, *, _production_nonce: object | None = None,
) -> dict[str, Any]:
    target = _validate_root_argument(Path(root), must_exist=False)
    context = _require_production_cli("prepare", target, _production_nonce)
    summary, old_preflight_bytes, dimacs = _prepare_materials()
    _mkdir_root(target)
    for name in ("static", "state", "artifacts", "logs"):
        _mkdir_new(target, name)
    _atomic_publish_bytes(target / "static", STATIC_PREFLIGHT.name, old_preflight_bytes)
    _atomic_publish_bytes(target / "static", STATIC_DIMACS.name, dimacs)
    old_record = _physical_record(
        target / STATIC_PREFLIGHT, target, "independent-old-v13-preflight",
        cap=PREPARE_LOG_MAX_BYTES,
    )
    base_record = _physical_record(
        target / STATIC_DIMACS, target, "optimized-base-dimacs",
        cap=EXPECTED_BASE_DIMACS_BYTES,
    )
    manifest = _static_manifest(
        target, context, summary, old_record, base_record,
        authority=AUTHORITY_PRODUCTION,
    )
    _atomic_publish_json(target / "static", STATIC_MANIFEST.name, manifest)
    manifest_record = _physical_record(
        target / STATIC_MANIFEST, target, "static-manifest", cap=JSON_MAX_BYTES,
    )
    commit = _static_commit_value(
        target, manifest_record, old_record, base_record,
        authority=AUTHORITY_PRODUCTION,
    )
    _atomic_publish_json(target / "state", STATIC_COMMIT.name, commit)
    validated = _validate_static(target, fresh_source_and_tools=True)
    if not json_type_equal(validated["commit"], commit):
        raise ProofRunnerError("post-commit static replay mismatch")
    return commit



def _prepare_process_matches(
    process: Any, *, argv: Sequence[str], stdout_payload: bytes,
) -> bool:
    return bool(
        _validate_process_record(process)
        and _process_clean(process, rc=0)
        and json_type_equal(process.get("argv"), list(argv))
        and process.get("cwd") == str(PROJECT)
        and process.get("timeout_s") == PREPARE_TIMEOUT_S
        and process.get("stdout_cap_bytes") == PREPARE_LOG_MAX_BYTES
        and process.get("stderr_cap_bytes") == PREPARE_LOG_MAX_BYTES
        and process.get("file_size_cap_bytes") == PREPARE_LOG_MAX_BYTES
        and process.get("stdout") == _hash_record(stdout_payload)
        and process.get("stderr") == _hash_record(b"")
        and json_type_equal(process.get("environment"), _clean_env())
    )



def _validate_static(
    root: Path, *, fresh_source_and_tools: bool,
) -> dict[str, Any]:
    target = _validate_root_argument(Path(root), must_exist=True)
    manifest = _strict_json(target / STATIC_MANIFEST)
    commit = _strict_json(target / STATIC_COMMIT)
    old_preflight = _validate_old_preflight(
        _strict_json(target / STATIC_PREFLIGHT),
    )
    manifest_fields = {
        "schema_version", "kind", "gate", "state", "authority", "test_only",
        "production_eligible", "root", "root_identity", "direct_cli_context",
        "preflight_summary", "static_artifacts", "base", "resource_policy",
        "state_machine", "publication_certificate", "upload_authorized",
        "record_sha256",
    }
    commit_fields = {
        "schema_version", "kind", "gate", "state", "authority", "test_only",
        "production_eligible", "root", "predecessor", "artifacts",
        "publication_certificate", "upload_authorized", "record_sha256",
    }
    if (
        type(manifest) is not dict
        or set(manifest) != manifest_fields
        or not selfhash_valid(manifest)
        or type(commit) is not dict
        or set(commit) != commit_fields
        or not selfhash_valid(commit)
    ):
        raise ProofRunnerError("static manifest/commit schema/self-hash mismatch")
    authority = manifest.get("authority")
    if (
        authority != AUTHORITY_PRODUCTION
        or manifest.get("test_only") is not False
        or manifest.get("production_eligible") is not True
        or commit.get("authority") != AUTHORITY_PRODUCTION
        or commit.get("test_only") is not False
        or commit.get("production_eligible") is not True
    ):
        raise ProofRunnerError("static production authority/taint mismatch")
    _validate_stored_direct_cli_context(
        manifest.get("direct_cli_context"), action="prepare", target=target,
    )
    old_record = _physical_record(
        target / STATIC_PREFLIGHT, target, "independent-old-v13-preflight",
        cap=PREPARE_LOG_MAX_BYTES,
    )
    base_record = _physical_record(
        target / STATIC_DIMACS, target, "optimized-base-dimacs",
        cap=EXPECTED_BASE_DIMACS_BYTES,
    )
    old_payload = canonical_bytes(old_preflight) + b"\n"
    dimacs = _read_file_stable(
        target / STATIC_DIMACS, cap=EXPECTED_BASE_DIMACS_BYTES,
    )
    if (
        old_record["file_sha256"] != hashlib.sha256(old_payload).hexdigest()
        or base_record["file_sha256"] != EXPECTED_BASE_DIMACS_SHA256
        or base_record["bytes"] != EXPECTED_BASE_DIMACS_BYTES
        or len(dimacs) != EXPECTED_BASE_DIMACS_BYTES
        or hashlib.sha256(dimacs).hexdigest() != EXPECTED_BASE_DIMACS_SHA256
    ):
        raise ProofRunnerError("static physical base/preflight binding mismatch")
    summary = manifest.get("preflight_summary")
    summary_fields = {
        "schema_version", "kind", "gate", "solver_invoked",
        "source_binding", "toolchain_binding", "old_preflight_process",
        "old_preflight_sha256", "old_preflight_file_sha256",
        "fresh_builder_process", "fresh_builder_record_sha256",
        "instance_binding", "three_process_peak_policy",
        "publication_certificate", "upload_authorized", "record_sha256",
    }
    if (
        type(summary) is not dict
        or set(summary) != summary_fields
        or not selfhash_valid(summary)
        or type(summary.get("schema_version")) is not int
        or summary["schema_version"] != SCHEMA_VERSION
        or summary.get("kind")
        != "paper400-dic5-standalone-static-preflight-v2"
        or summary.get("gate") != GATE
        or summary.get("solver_invoked") is not False
        or summary.get("publication_certificate") is not False
        or summary.get("upload_authorized") is not False
        or type(summary.get("source_binding")) is not dict
        or not selfhash_valid(summary["source_binding"])
        or type(summary.get("toolchain_binding")) is not dict
        or not selfhash_valid(summary["toolchain_binding"])
    ):
        raise ProofRunnerError("static preflight summary envelope mismatch")
    instance = summary.get("instance_binding")
    if type(instance) is not dict or set(instance) != {
        "base", "optimized_report", "scientific_binding", "source_closure",
        "runtime_seal",
    }:
        raise ProofRunnerError("static instance binding field set mismatch")
    source_closure = instance.get("source_closure")
    runtime_seal = instance.get("runtime_seal")
    if (
        type(source_closure) is not dict
        or not selfhash_valid(source_closure, "closure_sha256")
        or type(source_closure.get("schema_version")) is not int
        or source_closure.get("complete") is not True
        or type(runtime_seal) is not dict
        or not selfhash_valid(runtime_seal, "runtime_sha256")
        or type(runtime_seal.get("schema_version")) is not int
        or runtime_seal["schema_version"] != 2
    ):
        raise ProofRunnerError("static source/runtime closure binding mismatch")
    science = _scientific_summary(instance.get("optimized_report", {}))
    if not json_type_equal(science, instance.get("scientific_binding")):
        raise ProofRunnerError("static scientific binding mismatch")
    builder_value = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-fresh-builder-output-v2",
        "solver_invoked": False,
        "dimacs_base64": base64.b64encode(dimacs).decode("ascii"),
        "base": instance.get("base"),
        "optimized_report": instance.get("optimized_report"),
        "scientific_binding": instance.get("scientific_binding"),
        "source_closure": source_closure,
        "runtime_seal": runtime_seal,
    })
    validated_builder, rebuilt_dimacs = _validate_builder_output(builder_value)
    if rebuilt_dimacs != dimacs:
        raise ProofRunnerError("static builder/base byte reconstruction mismatch")
    old_argv = [
        str(SCIENCE_PYTHON), "-I", "-B",
        str(PROJECT / OLD_RUNNER_RELATIVE_PATH), "preflight",
    ]
    builder_argv = [
        str(SCIENCE_PYTHON), "-I", "-B", "-c", _BUILDER_BOOTSTRAP_CODE,
        str(PROJECT / RUNNER_RELATIVE_PATH), "__prepare_builder",
    ]
    builder_payload = canonical_bytes(validated_builder) + b"\n"
    if (
        not _prepare_process_matches(
            summary.get("old_preflight_process"), argv=old_argv,
            stdout_payload=old_payload,
        )
        or not _prepare_process_matches(
            summary.get("fresh_builder_process"), argv=builder_argv,
            stdout_payload=builder_payload,
        )
        or summary.get("old_preflight_sha256")
        != old_preflight["preflight_sha256"]
        or summary.get("old_preflight_file_sha256")
        != hashlib.sha256(old_payload).hexdigest()
        or summary.get("fresh_builder_record_sha256")
        != validated_builder["record_sha256"]
    ):
        raise ProofRunnerError("static independent process/output binding mismatch")
    expected_summary = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-standalone-static-preflight-v2",
        "gate": GATE,
        "solver_invoked": False,
        "source_binding": summary["source_binding"],
        "toolchain_binding": summary["toolchain_binding"],
        "old_preflight_process": summary["old_preflight_process"],
        "old_preflight_sha256": old_preflight["preflight_sha256"],
        "old_preflight_file_sha256": hashlib.sha256(old_payload).hexdigest(),
        "fresh_builder_process": summary["fresh_builder_process"],
        "fresh_builder_record_sha256": validated_builder["record_sha256"],
        "instance_binding": instance,
        "three_process_peak_policy": [
            "independent-old-v13-preflight-exits",
            "fresh-final-v13-builder-exits",
            "stdlib-supervisor-seals-static-artifacts",
        ],
        "publication_certificate": False,
        "upload_authorized": False,
    })
    if not json_type_equal(summary, expected_summary):
        raise ProofRunnerError("static preflight summary canonical reconstruction mismatch")
    expected_manifest = _static_manifest(
        target, manifest["direct_cli_context"], expected_summary,
        old_record, base_record, authority=AUTHORITY_PRODUCTION,
    )
    if not json_type_equal(manifest, expected_manifest):
        raise ProofRunnerError("static manifest canonical reconstruction mismatch")
    manifest_record = _physical_record(
        target / STATIC_MANIFEST, target, "static-manifest", cap=JSON_MAX_BYTES,
    )
    expected_commit = _static_commit_value(
        target, manifest_record, old_record, base_record,
        authority=AUTHORITY_PRODUCTION,
    )
    if not json_type_equal(commit, expected_commit):
        raise ProofRunnerError("static commit canonical reconstruction mismatch")
    if fresh_source_and_tools:
        if not json_type_equal(summary["source_binding"], _source_binding()):
            raise ProofRunnerError("static source binding changed")
        if not json_type_equal(summary["toolchain_binding"], _toolchain_binding()):
            raise ProofRunnerError("static toolchain binding changed")
    return {
        "manifest": manifest,
        "commit": commit,
        "old_preflight": old_preflight,
        "base_record": base_record,
        "authority": AUTHORITY_PRODUCTION,
        "test_only": False,
        "scientific_binding": science,
    }

def preflight_only(*, _production_nonce: object | None = None) -> dict[str, Any]:
    context = _require_production_cli("preflight", None, _production_nonce)
    summary, old_preflight, dimacs = _prepare_materials()
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-standalone-proof-preflight-v2",
        "gate": GATE,
        "direct_cli_context": context,
        "preflight_summary": summary,
        "old_preflight_file_sha256": hashlib.sha256(old_preflight).hexdigest(),
        "base_dimacs_sha256": hashlib.sha256(dimacs).hexdigest(),
        "base_dimacs_bytes": len(dimacs),
        "solver_invoked": False,
        "proof_checker_invoked": False,
        "root_created": False,
        "publication_certificate": False,
        "upload_authorized": False,
    })

def _create_private_output(parent: Path, stem: str) -> tuple[int, str]:
    if not stem or "/" in stem:
        raise ProofRunnerError("unsafe private output stem")
    directory = os.open(parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    name = f".{stem}.private-{os.getpid()}-{os.urandom(16).hex()}"
    try:
        descriptor = os.open(
            name,
            os.O_RDWR | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
            0o600,
            dir_fd=directory,
        )
        os.fsync(directory)
    finally:
        os.close(directory)
    return descriptor, name


def _discard_private(parent: Path, name: str, descriptor: int) -> None:
    try:
        os.close(descriptor)
    finally:
        directory = os.open(parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
        try:
            try:
                os.unlink(name, dir_fd=directory)
            except FileNotFoundError:
                pass
            os.fsync(directory)
        finally:
            os.close(directory)



def _publish_private_output(
    parent: Path,
    private_name: str,
    descriptor: int,
    final_name: str,
    *,
    expected_sha256: str,
    expected_bytes: int,
) -> Path:
    os.fsync(descriptor)
    actual_sha, actual_bytes, before = _hash_fd_stable(
        descriptor, cap=max(expected_bytes, 1),
    )
    if actual_sha != expected_sha256 or actual_bytes != expected_bytes:
        raise ProofRunnerError("private output changed before publication")
    directory = os.open(parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    published = False
    try:
        lexical = os.stat(private_name, dir_fd=directory, follow_symlinks=False)
        if (
            (lexical.st_dev, lexical.st_ino) != (before.st_dev, before.st_ino)
            or not stat.S_ISREG(lexical.st_mode)
        ):
            raise ProofRunnerError("private output path inode changed")
        os.link(
            private_name, final_name,
            src_dir_fd=directory, dst_dir_fd=directory, follow_symlinks=False,
        )
        published = True
        os.fsync(directory)
        os.unlink(private_name, dir_fd=directory)
        os.fsync(directory)
        final_info = os.stat(final_name, dir_fd=directory, follow_symlinks=False)
        if (final_info.st_dev, final_info.st_ino) != (before.st_dev, before.st_ino):
            raise ProofRunnerError("published output inode mismatch")
    except BaseException:
        if published:
            try:
                os.unlink(final_name, dir_fd=directory)
                os.fsync(directory)
            except FileNotFoundError:
                pass
        raise
    finally:
        os.close(directory)
        os.close(descriptor)
    return parent / final_name


def _sealed_memfd_from_bytes(
    name: str, payload: bytes, *, executable: bool = False,
) -> tuple[int, dict[str, Any]]:
    descriptor = os.memfd_create(
        name,
        getattr(os, "MFD_CLOEXEC", 0) | getattr(os, "MFD_ALLOW_SEALING", 0),
    )
    try:
        _write_all(descriptor, payload)
        os.fchmod(descriptor, 0o500 if executable else 0o400)
        seals = (
            fcntl.F_SEAL_WRITE | fcntl.F_SEAL_GROW | fcntl.F_SEAL_SHRINK
            | fcntl.F_SEAL_SEAL
        )
        fcntl.fcntl(descriptor, fcntl.F_ADD_SEALS, seals)
        if fcntl.fcntl(descriptor, fcntl.F_GET_SEALS) != seals:
            raise ProofRunnerError("byte memfd seal mismatch")
        os.lseek(descriptor, 0, os.SEEK_SET)
        return descriptor, {
            "sha256": hashlib.sha256(payload).hexdigest(),
            "bytes": len(payload),
            "executable": executable,
            "sealed_memfd": True,
            "seals": ["WRITE", "GROW", "SHRINK", "SEAL"],
        }
    except BaseException:
        os.close(descriptor)
        raise


def _pack_bits_stdlib(bits: Sequence[int]) -> dict[str, Any]:
    if any(type(bit) is not int or bit not in (0, 1) for bit in bits):
        raise ProofRunnerError("bit vector domain invalid")
    packed = bytearray((len(bits) + 7) // 8)
    for index, bit in enumerate(bits):
        if bit:
            packed[index // 8] |= 1 << (index % 8)
    raw = bytes(packed)
    return {
        "length": len(bits),
        "weight": sum(bits),
        "packed_hex": raw.hex(),
        "sha256": hashlib.sha256(f"{len(bits)}:".encode("ascii") + raw).hexdigest(),
    }


def _parse_complete_model(stdout: bytes, *, num_variables: int) -> list[int]:
    try:
        lines = stdout.decode("ascii").splitlines()
    except UnicodeDecodeError as exc:
        raise ProofRunnerError("solver stdout is not ASCII") from exc
    statuses = [line for line in lines if line.startswith("s ")]
    if statuses != ["s SATISFIABLE"]:
        raise ProofRunnerError("SAT status line set mismatch")
    model_tokens: list[str] = []
    for line in lines:
        if line.startswith("v "):
            model_tokens.extend(line[2:].split())
        elif line == "v":
            pass
        elif line == "s SATISFIABLE" or line.startswith("c ") or line == "":
            pass
        else:
            raise ProofRunnerError("unexpected solver stdout line")
    if not model_tokens or model_tokens[-1] != "0" or "0" in model_tokens[:-1]:
        raise ProofRunnerError("SAT model needs one final zero terminator")
    literals: list[int] = []
    for token in model_tokens[:-1]:
        try:
            literal = int(token)
        except ValueError as exc:
            raise ProofRunnerError("non-integer SAT model token") from exc
        if literal == 0 or abs(literal) > num_variables:
            raise ProofRunnerError("SAT model literal out of range")
        literals.append(literal)
    if len(literals) != num_variables:
        raise ProofRunnerError("SAT model is not complete")
    seen = [False] * num_variables
    bits = [0] * num_variables
    for literal in literals:
        index = abs(literal) - 1
        if seen[index]:
            raise ProofRunnerError("SAT model variable duplicated")
        seen[index] = True
        bits[index] = int(literal > 0)
    if not all(seen):
        raise ProofRunnerError("SAT model variable missing")
    return bits


def _sat_replay_helper(model_fd_number: int) -> int:
    if sys.flags.isolated != 1 or sys.flags.dont_write_bytecode != 1:
        raise ProofRunnerError("SAT replay helper requires -I -B")
    if type(model_fd_number) is not int or model_fd_number < 0:
        raise ProofRunnerError("SAT replay model fd invalid")
    duplicate = os.dup(model_fd_number)
    try:
        model_payload = _read_fd_stable(
            duplicate, cap=SOLVER_STDOUT_MAX_BYTES,
        )
    finally:
        os.close(duplicate)
    sys.path.insert(0, str(PROJECT))
    from evaluation import paper400_dic5_optimized_cnf_final_v13 as optimized

    instance = optimized.build_optimized_instance()
    if hashlib.sha256(instance.dimacs).hexdigest() != EXPECTED_BASE_DIMACS_SHA256:
        raise ProofRunnerError("SAT replay rebuilt DIMACS mismatch")
    bits = _parse_complete_model(
        model_payload, num_variables=EXPECTED_BASE_NUM_VARIABLES,
    )
    import numpy as np

    model = np.asarray(bits, dtype=np.uint8)
    model_holds = optimized._model_satisfies(instance, model)
    operator = np.ascontiguousarray(model[:400])
    syndrome = ((instance.lx @ operator) & 1).astype(int).tolist()
    evidence = {
        "outcome": "sat",
        "operator": optimized._pack_bits(operator),
        "logical_syndrome": syndrome,
        "partition_index": 0,
        "anchor_indices": [],
        "zero_anchor_indices": [],
        "one_anchor_index": None,
        "anchor_cube_sha256": None,
        "objective": int(operator.sum()),
        "max_weight": 18,
    }
    official_failures = optimized.baseline.verify_css_threshold_sat_witness(
        evidence, instance.hx, instance.lx,
    )
    passed = bool(
        model_holds
        and not official_failures
        and int(operator.sum()) <= 18
        and syndrome
        and syndrome[0] == 1
        and any(syndrome)
    )
    result = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-full-sat-replay-v2",
        "base_dimacs_sha256": EXPECTED_BASE_DIMACS_SHA256,
        "solver_stdout_sha256": hashlib.sha256(model_payload).hexdigest(),
        "full_model": _pack_bits_stdlib(bits),
        "operator": _pack_bits_stdlib(bits[:400]),
        "objective": int(operator.sum()),
        "logical_syndrome": syndrome,
        "complete_model_variable_count": len(bits),
        "full_12022_clause_model_replay": bool(model_holds),
        "official_full_Hx_Lx_replay_invoked": True,
        "official_full_Hx_Lx_failures": official_failures,
        "passed": passed,
        "solver_invoked": False,
    })
    sys.stdout.buffer.write(canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    return 0


def _run_sat_replay(stdout: bytes) -> tuple[dict[str, Any], dict[str, Any] | None]:
    model_fd, _ = _sealed_memfd_from_bytes("qcode-sat-model", stdout)
    try:
        argv = [
            str(SCIENCE_PYTHON), "-I", "-B", "-c", _BUILDER_BOOTSTRAP_CODE,
            str(Path(__file__).resolve()), "__sat_replay", str(model_fd),
        ]
        process, child_stdout, child_stderr = _run_capped_process(
            argv,
            timeout_s=PREPARE_TIMEOUT_S,
            stdout_cap=CHECKER_LOG_MAX_BYTES,
            stderr_cap=CHECKER_LOG_MAX_BYTES,
            cwd=PROJECT,
            pass_fds=(model_fd,),
            file_size_cap=CHECKER_LOG_MAX_BYTES,
        )
    finally:
        os.close(model_fd)
    if not _process_clean(process, rc=0) or child_stderr != b"":
        return process, None
    try:
        replay = _decode_json(child_stdout, canonical=True)
    except ProofRunnerError:
        return process, None
    expected_fields = {
        "schema_version", "kind", "base_dimacs_sha256",
        "solver_stdout_sha256", "full_model", "operator", "objective",
        "logical_syndrome", "complete_model_variable_count",
        "full_12022_clause_model_replay",
        "official_full_Hx_Lx_replay_invoked",
        "official_full_Hx_Lx_failures", "passed", "solver_invoked",
        "record_sha256",
    }
    if (
        set(replay) != expected_fields
        or not selfhash_valid(replay)
        or replay.get("passed") is not True
        or replay.get("solver_invoked") is not False
        or replay.get("solver_stdout_sha256") != hashlib.sha256(stdout).hexdigest()
    ):
        return process, None
    return process, replay

def _solver_semantics(
    process: Mapping[str, Any],
    stdout: bytes,
    stderr: bytes,
    *,
    expected: str,
) -> bool:
    if expected not in {"SATISFIABLE", "UNSATISFIABLE"}:
        raise ProofRunnerError("invalid solver semantic expectation")
    return bool(
        _process_clean(process, rc=10 if expected == "SATISFIABLE" else 20)
        and stderr == b""
        and _status_lines(stdout) == [f"s {expected}".encode("ascii")]
    )


def _artifact_reference(record: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "relative_path": record["relative_path"],
        "file_sha256": record["file_sha256"],
        "bytes": record["bytes"],
    }


def solve_root(
    root: Path, *, _production_nonce: object | None = None,
) -> dict[str, Any]:
    target = _validate_root_argument(Path(root), must_exist=True)
    context = _require_production_cli("solve", target, _production_nonce)
    static = _validate_static(target, fresh_source_and_tools=True)
    if static["authority"] != AUTHORITY_PRODUCTION:
        raise ProofRunnerError("production solve requires production static authority")
    if (target / SOLVE_CLAIM).exists() or (target / RAW_COMMIT).exists():
        raise ProofRunnerError("solve stage already claimed or committed")
    root_before = _root_identity(target)
    resource_before = _resource_gate(target, output_cap=PROOF_MAX_BYTES)
    claim = _create_claim(target, SOLVE_CLAIM, "solve")
    claim_record = _physical_record(
        target / SOLVE_CLAIM, target, "solve-claim", cap=JSON_MAX_BYTES,
    )

    proof_fd, private_proof_name = _create_private_output(
        target / "artifacts", "base.drat",
    )
    solver_fd = base_fd = -1
    runtime_handle: dict[str, Any] | None = None
    process: dict[str, Any]
    stdout = stderr = b""
    invocation: dict[str, Any]
    try:
        solver_fd, solver_memfd = _seal_memfd_from_path(
            SOLVER_PATH,
            expected_sha256=EXPECTED_SOLVER_SHA256,
            expected_bytes=EXPECTED_SOLVER_BYTES,
            executable=True,
        )
        base_fd, base_memfd = _seal_memfd_from_path(
            target / STATIC_DIMACS,
            expected_sha256=EXPECTED_BASE_DIMACS_SHA256,
            expected_bytes=EXPECTED_BASE_DIMACS_BYTES,
            executable=False,
        )
        runtime_handle = _stage_dynamic_runtime()
        runtime_record = runtime_handle["record"]
        loader_fd = runtime_handle["loader_fd"]
        runtime_directory_fd = runtime_handle["directory_fd"]
        argv = [
            f"/proc/self/fd/{loader_fd}",
            "--inhibit-cache",
            "--library-path", runtime_record["library_path"],
            "--argv0", "cadical-rel-1.9.5",
            f"/proc/self/fd/{solver_fd}",
            "-q", "-t", str(SOLVER_TIMEOUT_S),
            f"/proc/self/fd/{base_fd}", f"/proc/self/fd/{proof_fd}",
        ]
        invocation = seal({
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-standalone-solver-invocation-v2",
            "argv_roles": [
                "sealed-loader-memfd", "--inhibit-cache", "--library-path",
                "private-runtime-dirfd", "--argv0", "cadical-rel-1.9.5",
                "sealed-cadical195-memfd", "-q", "-t", "43200",
                "sealed-base-dimacs-memfd", "private-o_excl-binary-drat-fd",
            ],
            "actual_argv_sha256": canonical_sha256(argv),
            "dynamic_runtime": runtime_record,
            "solver": solver_memfd,
            "base": base_memfd,
            "proof_format": "binary-drat-default",
            "solver_timeout_s": SOLVER_TIMEOUT_S,
            "workers": 1,
            "resume": False,
            "stdin": "DEVNULL",
            "stdout_cap_bytes": SOLVER_STDOUT_MAX_BYTES,
            "stderr_cap_bytes": SOLVER_STDERR_MAX_BYTES,
            "proof_cap_bytes": PROOF_MAX_BYTES,
            "environment": _clean_env(),
        })
        process, stdout, stderr = _run_capped_process(
            argv,
            timeout_s=SOLVER_TIMEOUT_S,
            stdout_cap=SOLVER_STDOUT_MAX_BYTES,
            stderr_cap=SOLVER_STDERR_MAX_BYTES,
            cwd=target,
            pass_fds=(
                loader_fd, runtime_directory_fd, solver_fd, base_fd, proof_fd,
            ),
            file_size_cap=PROOF_MAX_BYTES,
            watched_fds=((proof_fd, PROOF_MAX_BYTES),),
        )
        _validate_staged_dynamic_runtime(runtime_handle)
    finally:
        if solver_fd >= 0:
            os.close(solver_fd)
        if base_fd >= 0:
            os.close(base_fd)
        if runtime_handle is not None:
            _destroy_dynamic_runtime(runtime_handle)

    proof_sha: str | None = None
    proof_bytes: int | None = None
    proof_hash_error: str | None = None
    try:
        os.fsync(proof_fd)
        proof_sha, proof_bytes, _ = _hash_fd_stable(proof_fd, cap=PROOF_MAX_BYTES)
    except (OSError, ProofRunnerError) as exc:
        proof_hash_error = f"{type(exc).__name__}: {exc}"
    resource_after = _instant_resource(target)
    oom_delta = _oom_delta(resource_before, resource_after)
    no_new_oom = all(value == 0 for value in oom_delta.values())
    root_after_solver = _root_identity(target)
    if not json_type_equal(root_before, root_after_solver):
        _discard_private(target / "artifacts", private_proof_name, proof_fd)
        raise ProofRunnerError("root identity changed during solver")

    _atomic_publish_bytes(target / "logs", "solver.stdout", stdout)
    _atomic_publish_bytes(target / "logs", "solver.stderr", stderr)
    stdout_record = _physical_record(
        target / "logs/solver.stdout", target, "solver-stdout",
        cap=SOLVER_STDOUT_MAX_BYTES,
    )
    stderr_record = _physical_record(
        target / "logs/solver.stderr", target, "solver-stderr",
        cap=SOLVER_STDERR_MAX_BYTES,
    )

    sat_replay_process: dict[str, Any] | None = None
    sat_replay: dict[str, Any] | None = None
    proof_record: dict[str, Any] | None = None
    valid_unsat = bool(
        _solver_semantics(process, stdout, stderr, expected="UNSATISFIABLE")
        and no_new_oom
        and proof_hash_error is None
        and type(proof_sha) is str
        and type(proof_bytes) is int
        and proof_bytes > 0
        and proof_bytes <= PROOF_MAX_BYTES
    )
    valid_sat_process = bool(
        _solver_semantics(process, stdout, stderr, expected="SATISFIABLE")
        and no_new_oom
    )
    if valid_unsat:
        assert proof_sha is not None and proof_bytes is not None
        _publish_private_output(
            target / "artifacts",
            private_proof_name,
            proof_fd,
            DRAT_ARTIFACT.name,
            expected_sha256=proof_sha,
            expected_bytes=proof_bytes,
        )
        proof_record = _physical_record(
            target / DRAT_ARTIFACT, target, "raw-binary-drat",
            cap=PROOF_MAX_BYTES,
        )
        state = "RAW_UNSAT"
    else:
        _discard_private(target / "artifacts", private_proof_name, proof_fd)
        if valid_sat_process:
            sat_replay_process, sat_replay = _run_sat_replay(stdout)
        state = (
            "RAW_SAT"
            if sat_replay is not None and sat_replay.get("passed") is True
            else "UNRESOLVED"
        )

    summary = static["manifest"]["preflight_summary"]
    sources_after = _source_binding()
    tools_after = _toolchain_binding()
    bindings_stable = bool(
        json_type_equal(sources_after, summary["source_binding"])
        and json_type_equal(tools_after, summary["toolchain_binding"])
    )
    if not bindings_stable:
        raise ProofRunnerError("source/tool binding changed during solver stage")
    decision_complete = state in {"RAW_SAT", "RAW_UNSAT"}
    raw = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-standalone-raw-result-v2",
        "gate": GATE,
        "state": state,
        "authority": AUTHORITY_PRODUCTION,
        "test_only": False,
        "production_eligible": decision_complete,
        "root": str(target),
        "root_identity": root_before,
        "direct_cli_context": context,
        "predecessor": _predecessor(target, STATIC_COMMIT),
        "claim": claim,
        "claim_artifact": claim_record,
        "resource_gate_before": resource_before,
        "resource_snapshot_after": resource_after,
        "oom_event_delta": oom_delta,
        "source_binding_after": sources_after,
        "toolchain_binding_after": tools_after,
        "bindings_stable": bindings_stable,
        "invocation": invocation,
        "process": process,
        "status_lines_ascii": [
            line.decode("ascii", errors="replace") for line in _status_lines(stdout)
        ],
        "logs": [stdout_record, stderr_record],
        "proof": proof_record,
        "proof_hash_error": proof_hash_error,
        "sat_replay_process": sat_replay_process,
        "sat_replay": sat_replay,
        "solver_invocations": 1,
        "decision_complete": decision_complete,
        "strict_raw_unsat": state == "RAW_UNSAT",
        "strict_verified_sat_rejection": state == "RAW_SAT",
        "raw_unsat_is_distance_lower_bound": False,
        "durable_proof_independently_verified": False,
        "publication_certificate": False,
        "upload_authorized": False,
    })
    _atomic_publish_json(target / "state", RAW_COMMIT.name, raw)
    replay = _validate_raw(target, fresh_source_and_tools=True)
    if not json_type_equal(replay["raw"], raw):
        raise ProofRunnerError("post-commit raw replay mismatch")
    return raw



def _validate_memory_pressure(value: Any) -> bool:
    fields = {"avg10", "avg60", "avg300", "total"}
    if type(value) is not dict or set(value) != {"some", "full"}:
        return False
    for record in (value["some"], value["full"]):
        if type(record) is not dict or set(record) != fields:
            return False
        if (
            any(
                type(record[name]) is not float
                or not math.isfinite(record[name])
                or record[name] < 0.0
                for name in ("avg10", "avg60", "avg300")
            )
            or type(record["total"]) is not int
            or record["total"] < 0
        ):
            return False
    return True


def _validate_resource_record(value: Any, *, required_cap: int) -> bool:
    fields = {
        "schema_version", "kind", "cpu", "affinity", "niceness",
        "busy_percent", "cpu_safe", "memory_current", "memory_max",
        "file_bytes", "inactive_file_bytes", "reclaimable_file_bytes",
        "raw_headroom_bytes", "effective_current_bytes",
        "effective_headroom_bytes", "effective_current_fraction",
        "memory_events", "memory_pressure", "memory_capacity_safe",
        "pressure_safe", "oom_safe", "filesystem_device",
        "filesystem_block_size", "filesystem_bavail_blocks",
        "filesystem_bavail_bytes", "output_cap_bytes",
        "reserve_margin_bytes", "disk_required_bytes", "disk_safe",
        "thread_environment", "thread_environment_safe", "passed",
        "record_sha256",
    }
    if (
        type(required_cap) is not int
        or required_cap < 0
        or type(value) is not dict
        or set(value) != fields
        or not selfhash_valid(value)
        or type(value.get("schema_version")) is not int
        or value["schema_version"] != SCHEMA_VERSION
        or value.get("kind") != "standalone-resource-gate-v2"
        or type(value.get("cpu")) is not int
        or value["cpu"] < 0
        or type(value.get("affinity")) is not list
        or len(value["affinity"]) != 1
        or type(value["affinity"][0]) is not int
        or value["affinity"][0] != value["cpu"]
        or type(value.get("niceness")) is not int
        or value["niceness"] != 19
    ):
        return False
    busy = value.get("busy_percent")
    if (
        type(busy) is not list
        or len(busy) != RESOURCE_CPU_INTERVALS
        or any(
            type(number) is not float
            or not math.isfinite(number)
            or number < 0.0
            or number > 100.0
            for number in busy
        )
    ):
        return False
    expected_cpu_safe = all(
        number < RESOURCE_MAX_BUSY_PERCENT for number in busy
    )
    current = value.get("memory_current")
    maximum = value.get("memory_max")
    file_bytes = value.get("file_bytes")
    inactive_file = value.get("inactive_file_bytes")
    reclaimable = value.get("reclaimable_file_bytes")
    effective_current = value.get("effective_current_bytes")
    for number in (current, file_bytes, inactive_file, reclaimable, effective_current):
        if type(number) is not int or number < 0:
            return False
    if not (maximum is None or type(maximum) is int and maximum > 0):
        return False
    expected_reclaimable = max(0, min(file_bytes, inactive_file))
    expected_effective_current = max(0, current - expected_reclaimable)
    if (
        reclaimable != expected_reclaimable
        or effective_current != expected_effective_current
    ):
        return False
    raw_headroom = value.get("raw_headroom_bytes")
    effective_headroom = value.get("effective_headroom_bytes")
    fraction = value.get("effective_current_fraction")
    if type(fraction) is not float or not math.isfinite(fraction):
        return False
    if maximum is None:
        if raw_headroom is not None or effective_headroom is not None:
            return False
    elif (
        type(raw_headroom) is not int
        or type(effective_headroom) is not int
    ):
        return False
    if maximum is None:
        expected_raw_headroom = None
        expected_effective_headroom = None
        expected_fraction = 0.0
        expected_memory_safe = True
    else:
        expected_raw_headroom = maximum - current
        expected_effective_headroom = maximum - effective_current
        expected_fraction = effective_current / maximum
        expected_memory_safe = bool(
            expected_raw_headroom >= RESOURCE_MIN_RAW_HEADROOM
            and expected_effective_headroom >= RESOURCE_MIN_EFFECTIVE_HEADROOM
            and expected_fraction <= RESOURCE_MAX_EFFECTIVE_FRACTION
        )
    if (
        raw_headroom != expected_raw_headroom
        or effective_headroom != expected_effective_headroom
        or fraction != expected_fraction
    ):
        return False
    events = value.get("memory_events")
    if (
        type(events) is not dict
        or any(type(key) is not str for key in events)
        or any(type(number) is not int or number < 0 for number in events.values())
        or any(type(events.get(name)) is not int for name in (
            "oom", "oom_kill", "oom_group_kill",
        ))
    ):
        return False
    pressure = value.get("memory_pressure")
    if not _validate_memory_pressure(pressure):
        return False
    full = pressure["full"]
    expected_pressure_safe = bool(
        full["avg10"] < RESOURCE_MAX_MEMORY_PSI_FULL_AVG10
        and full["avg60"] < RESOURCE_MAX_MEMORY_PSI_FULL_AVG60
    )
    expected_oom_safe = all(
        events[name] == 0 for name in ("oom", "oom_kill", "oom_group_kill")
    )
    for name in (
        "filesystem_device", "filesystem_block_size",
        "filesystem_bavail_blocks", "filesystem_bavail_bytes",
        "output_cap_bytes", "reserve_margin_bytes", "disk_required_bytes",
    ):
        if type(value.get(name)) is not int or value[name] < 0:
            return False
    expected_available = (
        value["filesystem_block_size"] * value["filesystem_bavail_blocks"]
    )
    expected_required = required_cap + DISK_RESERVE_MARGIN_BYTES
    expected_disk_safe = expected_available >= expected_required
    expected_threads = {name: "1" for name in THREAD_ENV}
    if (
        value["filesystem_bavail_bytes"] != expected_available
        or value["output_cap_bytes"] != required_cap
        or value["reserve_margin_bytes"] != DISK_RESERVE_MARGIN_BYTES
        or value["disk_required_bytes"] != expected_required
        or not json_type_equal(value.get("thread_environment"), expected_threads)
    ):
        return False
    expected_passed = bool(
        expected_cpu_safe
        and expected_memory_safe
        and expected_pressure_safe
        and expected_oom_safe
        and expected_disk_safe
    )
    return bool(
        value.get("cpu_safe") is expected_cpu_safe
        and value.get("memory_capacity_safe") is expected_memory_safe
        and value.get("pressure_safe") is expected_pressure_safe
        and value.get("oom_safe") is expected_oom_safe
        and value.get("disk_safe") is expected_disk_safe
        and value.get("thread_environment_safe") is True
        and value.get("passed") is expected_passed
        and expected_passed is True
    )


def _validate_process_record(value: Any) -> bool:
    expected_fields = {
        "schema_version", "kind", "argv", "cwd", "environment", "timeout_s",
        "stdout_cap_bytes", "stderr_cap_bytes", "file_size_cap_bytes",
        "exit_code", "signal", "timed_out", "stdout_overflow",
        "stderr_overflow", "watched_file_overflow",
        "lingering_process_group", "launch_error", "elapsed_ns",
        "child_lifecycle_policy", "supervisor_pid", "child_pid",
        "process_group_id", "pdeathsig_setup_confirmed",
        "session_setup_confirmed",
        "forwarded_parent_signal", "direct_child_reaped",
        "process_group_empty",
        "stdout", "stderr", "record_sha256",
    }
    if type(value) is not dict or set(value) != expected_fields or not selfhash_valid(value):
        return False
    if (
        type(value.get("schema_version")) is not int
        or value["schema_version"] != SCHEMA_VERSION
        or value.get("kind") != "bounded-process-result-v2"
        or type(value.get("argv")) is not list
        or not value["argv"]
        or any(type(item) is not str for item in value["argv"])
        or type(value.get("cwd")) is not str
        or not Path(value["cwd"]).is_absolute()
        or type(value.get("environment")) is not dict
        or not json_type_equal(value["environment"], _clean_env())
        or type(value.get("elapsed_ns")) is not int
        or value["elapsed_ns"] < 0
        or not json_type_equal(
            value.get("child_lifecycle_policy"), _child_lifecycle_policy(),
        )
        or type(value.get("supervisor_pid")) is not int
        or value["supervisor_pid"] <= 0
        or value.get("forwarded_parent_signal") is not None
    ):
        return False
    for key in (
        "timeout_s", "stdout_cap_bytes", "stderr_cap_bytes",
        "file_size_cap_bytes",
    ):
        if type(value.get(key)) is not int or value[key] < 0:
            return False
    exit_code = value.get("exit_code")
    signum = value.get("signal")
    if exit_code is not None and type(exit_code) is not int:
        return False
    if signum is not None and (type(signum) is not int or signum <= 0):
        return False
    if type(exit_code) is int and exit_code < 0:
        if type(signum) is not int or signum != -exit_code:
            return False
    elif signum is not None:
        return False
    child_pid = value.get("child_pid")
    process_group_id = value.get("process_group_id")
    if child_pid is None:
        if (
            process_group_id is not None
            or value.get("pdeathsig_setup_confirmed") is not False
            or value.get("session_setup_confirmed") is not False
            or value.get("direct_child_reaped") is not False
            or value.get("launch_error") is None
        ):
            return False
    elif (
        type(child_pid) is not int
        or child_pid <= 0
        or type(process_group_id) is not int
        or process_group_id != child_pid
        or value.get("pdeathsig_setup_confirmed") is not True
        or value.get("session_setup_confirmed") is not True
        or value.get("direct_child_reaped") is not True
        or value.get("process_group_empty") is not True
    ):
        return False
    if type(value.get("process_group_empty")) is not bool:
        return False
    launch_error = value.get("launch_error")
    if launch_error is not None and type(launch_error) is not str:
        return False
    for key in (
        "timed_out", "stdout_overflow", "stderr_overflow",
        "watched_file_overflow", "lingering_process_group",
    ):
        if type(value.get(key)) is not bool:
            return False
    for key in ("stdout", "stderr"):
        record = value.get(key)
        if (
            type(record) is not dict
            or set(record) != {"bytes", "sha256"}
            or type(record.get("bytes")) is not int
            or record["bytes"] < 0
            or not is_sha256(record.get("sha256"))
        ):
            return False
    return True



def _validate_solver_invocation(
    value: Any,
    *,
    process: Mapping[str, Any],
    target: Path,
    source_tcb: Mapping[str, Any],
) -> bool:
    fields = {
        "schema_version", "kind", "argv_roles", "actual_argv_sha256",
        "dynamic_runtime", "solver", "base", "proof_format",
        "solver_timeout_s", "workers", "resume", "stdin",
        "stdout_cap_bytes", "stderr_cap_bytes", "proof_cap_bytes",
        "environment", "record_sha256",
    }
    expected_roles = [
        "sealed-loader-memfd", "--inhibit-cache", "--library-path",
        "private-runtime-dirfd", "--argv0", "cadical-rel-1.9.5",
        "sealed-cadical195-memfd", "-q", "-t", "43200",
        "sealed-base-dimacs-memfd", "private-o_excl-binary-drat-fd",
    ]
    if (
        type(value) is not dict
        or set(value) != fields
        or not selfhash_valid(value)
        or type(value.get("schema_version")) is not int
        or value["schema_version"] != SCHEMA_VERSION
        or value.get("kind") != "paper400-standalone-solver-invocation-v2"
        or not json_type_equal(value.get("argv_roles"), expected_roles)
        or not _validate_memfd_record(
            value.get("solver"), source_path=SOLVER_PATH,
            expected_sha256=EXPECTED_SOLVER_SHA256,
            expected_bytes=EXPECTED_SOLVER_BYTES, executable=True,
        )
        or not _validate_memfd_record(
            value.get("base"), source_path=target / STATIC_DIMACS,
            expected_sha256=EXPECTED_BASE_DIMACS_SHA256,
            expected_bytes=EXPECTED_BASE_DIMACS_BYTES, executable=False,
        )
        or not _validate_historical_dynamic_runtime(
            value.get("dynamic_runtime"), source_tcb=source_tcb,
        )
        or value.get("proof_format") != "binary-drat-default"
        or type(value.get("solver_timeout_s")) is not int
        or value["solver_timeout_s"] != SOLVER_TIMEOUT_S
        or type(value.get("workers")) is not int
        or value["workers"] != 1
        or value.get("resume") is not False
        or value.get("stdin") != "DEVNULL"
        or type(value.get("stdout_cap_bytes")) is not int
        or value["stdout_cap_bytes"] != SOLVER_STDOUT_MAX_BYTES
        or type(value.get("stderr_cap_bytes")) is not int
        or value["stderr_cap_bytes"] != SOLVER_STDERR_MAX_BYTES
        or type(value.get("proof_cap_bytes")) is not int
        or value["proof_cap_bytes"] != PROOF_MAX_BYTES
        or not json_type_equal(value.get("environment"), _clean_env())
        or not _validate_process_record(process)
    ):
        return False
    argv = process.get("argv")
    if type(argv) is not list or len(argv) != 12:
        return False
    descriptor_numbers = [
        _proc_fd_number(argv[index]) for index in (0, 3, 6, 10, 11)
    ]
    return bool(
        all(number is not None for number in descriptor_numbers)
        and len(set(descriptor_numbers)) == len(descriptor_numbers)
        and argv[1:3] == ["--inhibit-cache", "--library-path"]
        and argv[3] == value["dynamic_runtime"]["library_path"]
        and argv[4:10] == [
            "--argv0", "cadical-rel-1.9.5", argv[6], "-q", "-t",
            str(SOLVER_TIMEOUT_S),
        ]
        and value.get("actual_argv_sha256") == canonical_sha256(argv)
        and process.get("cwd") == str(target)
        and json_type_equal(process.get("environment"), _clean_env())
        and process.get("timeout_s") == SOLVER_TIMEOUT_S
        and process.get("stdout_cap_bytes") == SOLVER_STDOUT_MAX_BYTES
        and process.get("stderr_cap_bytes") == SOLVER_STDERR_MAX_BYTES
        and process.get("file_size_cap_bytes") == PROOF_MAX_BYTES
    )


def _validate_sat_replay_record(
    replay: Any,
    process: Any,
    *,
    solver_stdout: bytes,
) -> bool:
    fields = {
        "schema_version", "kind", "base_dimacs_sha256",
        "solver_stdout_sha256", "full_model", "operator", "objective",
        "logical_syndrome", "complete_model_variable_count",
        "full_12022_clause_model_replay",
        "official_full_Hx_Lx_replay_invoked",
        "official_full_Hx_Lx_failures", "passed", "solver_invoked",
        "record_sha256",
    }
    if (
        type(replay) is not dict
        or set(replay) != fields
        or not selfhash_valid(replay)
        or type(replay.get("schema_version")) is not int
        or replay["schema_version"] != SCHEMA_VERSION
        or replay.get("kind") != "paper400-dic5-full-sat-replay-v2"
        or replay.get("base_dimacs_sha256") != EXPECTED_BASE_DIMACS_SHA256
        or replay.get("solver_stdout_sha256")
        != hashlib.sha256(solver_stdout).hexdigest()
        or type(replay.get("complete_model_variable_count")) is not int
        or replay["complete_model_variable_count"] != EXPECTED_BASE_NUM_VARIABLES
        or replay.get("full_12022_clause_model_replay") is not True
        or replay.get("official_full_Hx_Lx_replay_invoked") is not True
        or not json_type_equal(replay.get("official_full_Hx_Lx_failures"), [])
        or replay.get("passed") is not True
        or replay.get("solver_invoked") is not False
        or not _validate_process_record(process)
    ):
        return False
    try:
        bits = _parse_complete_model(
            solver_stdout, num_variables=EXPECTED_BASE_NUM_VARIABLES,
        )
    except ProofRunnerError:
        return False
    syndrome = replay.get("logical_syndrome")
    if (
        not json_type_equal(replay.get("full_model"), _pack_bits_stdlib(bits))
        or not json_type_equal(replay.get("operator"), _pack_bits_stdlib(bits[:400]))
        or type(replay.get("objective")) is not int
        or replay["objective"] != sum(bits[:400])
        or replay["objective"] > 18
        or type(syndrome) is not list
        or len(syndrome) != 16
        or any(type(bit) is not int or bit not in (0, 1) for bit in syndrome)
        or syndrome[0] != 1
    ):
        return False
    argv = process["argv"]
    replay_bytes = canonical_bytes(replay) + b"\n"
    return bool(
        len(argv) == 8
        and argv[:5] == [
            str(SCIENCE_PYTHON), "-I", "-B", "-c", _BUILDER_BOOTSTRAP_CODE,
        ]
        and argv[5:7] == [str(Path(__file__).resolve()), "__sat_replay"]
        and type(argv[7]) is str
        and argv[7].isdigit()
        and int(argv[7]) >= 3
        and process.get("cwd") == str(PROJECT)
        and process.get("timeout_s") == PREPARE_TIMEOUT_S
        and process.get("stdout_cap_bytes") == CHECKER_LOG_MAX_BYTES
        and process.get("stderr_cap_bytes") == CHECKER_LOG_MAX_BYTES
        and process.get("file_size_cap_bytes") == CHECKER_LOG_MAX_BYTES
        and process.get("stdout") == _hash_record(replay_bytes)
        and process.get("stderr") == _hash_record(b"")
        and _process_clean(process, rc=0)
    )


def _validate_raw(
    root: Path, *, fresh_source_and_tools: bool,
) -> dict[str, Any]:
    target = _validate_root_argument(Path(root), must_exist=True)
    static = _validate_static(target, fresh_source_and_tools=fresh_source_and_tools)
    raw = _strict_json(target / RAW_COMMIT)
    fields = {
        "schema_version", "kind", "gate", "state", "authority", "test_only",
        "production_eligible", "root", "root_identity", "direct_cli_context",
        "predecessor", "claim", "claim_artifact", "resource_gate_before",
        "resource_snapshot_after", "oom_event_delta", "source_binding_after",
        "toolchain_binding_after", "bindings_stable", "invocation", "process",
        "status_lines_ascii", "logs", "proof", "proof_hash_error",
        "sat_replay_process", "sat_replay", "solver_invocations",
        "decision_complete", "strict_raw_unsat",
        "strict_verified_sat_rejection", "raw_unsat_is_distance_lower_bound",
        "durable_proof_independently_verified", "publication_certificate",
        "upload_authorized", "record_sha256",
    }
    if (
        type(raw) is not dict
        or set(raw) != fields
        or not selfhash_valid(raw)
        or type(raw.get("schema_version")) is not int
        or raw["schema_version"] != SCHEMA_VERSION
        or raw.get("kind") != "paper400-dic5-standalone-raw-result-v2"
        or raw.get("gate") != GATE
    ):
        raise ProofRunnerError("raw result schema/self-hash mismatch")
    state = raw.get("state")
    if type(state) is not str or state not in {"RAW_SAT", "RAW_UNSAT", "UNRESOLVED"}:
        raise ProofRunnerError("raw result state invalid")
    _validate_stored_direct_cli_context(
        raw.get("direct_cli_context"), action="solve", target=target,
    )
    summary = static["manifest"]["preflight_summary"]
    process = raw.get("process")
    source_tcb = summary["toolchain_binding"]["dynamic_elf_tcb"]
    if (
        raw.get("authority") != static["authority"]
        or type(raw.get("test_only")) is not bool
        or raw.get("test_only") is not static["test_only"]
        or raw.get("root") != str(target)
        or not json_type_equal(raw.get("root_identity"), _root_identity(target))
        or not json_type_equal(raw.get("predecessor"), _predecessor(target, STATIC_COMMIT))
        or type(raw.get("solver_invocations")) is not int
        or raw["solver_invocations"] != 1
        or raw.get("raw_unsat_is_distance_lower_bound") is not False
        or raw.get("durable_proof_independently_verified") is not False
        or raw.get("publication_certificate") is not False
        or raw.get("upload_authorized") is not False
        or not _validate_resource_record(
            raw.get("resource_gate_before"), required_cap=PROOF_MAX_BYTES,
        )
        or not _validate_resource_snapshot(raw.get("resource_snapshot_after"))
        or not _validate_process_record(process)
        or not _validate_solver_invocation(
            raw.get("invocation"), process=process, target=target,
            source_tcb=source_tcb,
        )
        or not json_type_equal(raw.get("source_binding_after"), summary["source_binding"])
        or not json_type_equal(raw.get("toolchain_binding_after"), summary["toolchain_binding"])
        or type(raw.get("bindings_stable")) is not bool
        or raw.get("bindings_stable") is not True
        or not (
            raw.get("proof_hash_error") is None
            or type(raw.get("proof_hash_error")) is str
        )
    ):
        raise ProofRunnerError("raw common binding mismatch")
    claim = _strict_json(target / SOLVE_CLAIM)
    _validate_claim_record(claim, action="solve", target=target)
    if (
        not selfhash_valid(claim)
        or not json_type_equal(raw.get("claim"), claim)
        or not json_type_equal(
            raw.get("claim_artifact"),
            _physical_record(target / SOLVE_CLAIM, target, "solve-claim", cap=JSON_MAX_BYTES),
        )
    ):
        raise ProofRunnerError("raw claim binding mismatch")
    stdout_record = _physical_record(
        target / "logs/solver.stdout", target, "solver-stdout",
        cap=SOLVER_STDOUT_MAX_BYTES,
    )
    stderr_record = _physical_record(
        target / "logs/solver.stderr", target, "solver-stderr",
        cap=SOLVER_STDERR_MAX_BYTES,
    )
    if not json_type_equal(raw.get("logs"), [stdout_record, stderr_record]):
        raise ProofRunnerError("raw log physical binding mismatch")
    stdout = _read_file_stable(
        target / "logs/solver.stdout", cap=SOLVER_STDOUT_MAX_BYTES,
    )
    stderr = _read_file_stable(
        target / "logs/solver.stderr", cap=SOLVER_STDERR_MAX_BYTES,
    )
    process = raw["process"]
    if process["stdout"] != _hash_record(stdout) or process["stderr"] != _hash_record(stderr):
        raise ProofRunnerError("raw process/log hash mismatch")
    oom_delta = raw.get("oom_event_delta")
    expected_oom_delta = _oom_delta(
        raw["resource_gate_before"], raw["resource_snapshot_after"],
    )
    if (
        type(oom_delta) is not dict
        or not json_type_equal(oom_delta, expected_oom_delta)
        or set(oom_delta) != {"oom", "oom_kill", "oom_group_kill"}
        or any(type(value) is not int or value < 0 for value in oom_delta.values())
    ):
        raise ProofRunnerError("raw OOM delta invalid")
    expected_status_lines = [
        line.decode("ascii") for line in _status_lines(stdout)
    ]
    if not json_type_equal(raw.get("status_lines_ascii"), expected_status_lines):
        raise ProofRunnerError("raw stored status-line binding mismatch")
    no_new_oom = all(value == 0 for value in oom_delta.values())
    proof = raw.get("proof")
    sat_replay = raw.get("sat_replay")
    strict_unsat = bool(
        state == "RAW_UNSAT"
        and _solver_semantics(process, stdout, stderr, expected="UNSATISFIABLE")
        and no_new_oom
        and type(proof) is dict
        and proof.get("bytes", 0) > 0
        and proof.get("bytes", PROOF_MAX_BYTES + 1) <= PROOF_MAX_BYTES
        and json_type_equal(
            proof,
            _physical_record(
                target / DRAT_ARTIFACT, target, "raw-binary-drat",
                cap=PROOF_MAX_BYTES,
            ),
        )
        and raw.get("proof_hash_error") is None
        and raw.get("sat_replay") is None
        and raw.get("sat_replay_process") is None
    )
    strict_sat = bool(
        state == "RAW_SAT"
        and _solver_semantics(process, stdout, stderr, expected="SATISFIABLE")
        and no_new_oom
        and proof is None
        and _validate_sat_replay_record(
            sat_replay, raw.get("sat_replay_process"), solver_stdout=stdout,
        )
    )
    unresolved = state == "UNRESOLVED"
    if not (strict_unsat or strict_sat or unresolved):
        raise ProofRunnerError("raw state truth table mismatch")
    if (
        raw.get("decision_complete") is not (strict_unsat or strict_sat)
        or raw.get("production_eligible") is not (
            (strict_unsat or strict_sat) and not static["test_only"]
        )
        or raw.get("strict_raw_unsat") is not strict_unsat
        or raw.get("strict_verified_sat_rejection") is not strict_sat
    ):
        raise ProofRunnerError("raw decision booleans mismatch")
    if fresh_source_and_tools:
        summary = static["manifest"]["preflight_summary"]
        if not json_type_equal(raw.get("source_binding_after"), _source_binding()):
            raise ProofRunnerError("raw source binding changed")
        if not json_type_equal(raw.get("toolchain_binding_after"), _toolchain_binding()):
            raise ProofRunnerError("raw toolchain binding changed")
        if not json_type_equal(raw["source_binding_after"], summary["source_binding"]):
            raise ProofRunnerError("raw/static source binding mismatch")
        if not json_type_equal(raw["toolchain_binding_after"], summary["toolchain_binding"]):
            raise ProofRunnerError("raw/static toolchain binding mismatch")
    return {
        "static": static,
        "raw": raw,
        "state": state,
        "proof": proof,
        "strict_raw_unsat": strict_unsat,
        "strict_sat": strict_sat,
    }

def _open_bound_input(
    path: Path, root: Path, role: str, *, expected_sha256: str, cap: int,
) -> tuple[int, dict[str, Any]]:
    descriptor = _safe_open_regular(path)
    try:
        actual, total, info = _hash_fd_stable(descriptor, cap=cap)
        if actual != expected_sha256:
            raise ProofRunnerError(f"bound checker input hash mismatch: {path}")
        record = _physical_record_from_hash(
            path, root, role, digest=actual, total=total, info=info,
        )
        os.lseek(descriptor, 0, os.SEEK_SET)
        return descriptor, record
    except BaseException:
        os.close(descriptor)
        raise


def _assert_bound_input_unchanged(
    descriptor: int,
    path: Path,
    root: Path,
    role: str,
    *,
    expected_record: Mapping[str, Any],
    cap: int,
) -> None:
    digest, total, info = _hash_fd_stable(descriptor, cap=cap)
    current = _physical_record_from_hash(
        path, root, role, digest=digest, total=total, info=info,
    )
    if (
        digest != expected_record.get("file_sha256")
        or total != expected_record.get("bytes")
        or (info.st_dev, info.st_ino)
        != (expected_record.get("device"), expected_record.get("inode"))
        or not json_type_equal(current, expected_record)
    ):
        raise ProofRunnerError("checker input changed during execution")




def _checker_terminal_lines(payload: bytes, marker: bytes) -> list[bytes] | None:
    if b"\x00" in payload:
        return None
    try:
        lines = payload.decode("ascii").splitlines()
    except UnicodeDecodeError:
        return None
    if marker == b"s VERIFIED":
        selected = [line for line in lines if line.startswith("s ")]
    elif marker == b"c VERIFIED":
        terminal_words = ("VERIFIED", "INVALID", "FAILED", "ERROR")
        selected = [
            line for line in lines
            if line.startswith("c ")
            and any(word in line.upper() for word in terminal_words)
        ]
    else:
        return None
    return [line.encode("ascii") for line in selected]


def _checker_success(
    process: Mapping[str, Any],
    stdout: bytes,
    stderr: bytes,
    *,
    marker: bytes,
) -> bool:
    return bool(
        _process_clean(process, rc=0)
        and stderr == b""
        and _checker_terminal_lines(stdout, marker) == [marker]
    )

def _checker_invocation(
    *,
    role: str,
    checker_memfd: Mapping[str, Any],
    dynamic_runtime: Mapping[str, Any],
    base_memfd: Mapping[str, Any],
    proof_record: Mapping[str, Any],
    argv: Sequence[str],
    output_role: str | None,
) -> dict[str, Any]:
    tool_roles = {
        "drat-verify": [
            "sealed-drat-trim", "sealed-base-dimacs", "opened-drat-fd",
            "-t", "604800",
        ],
        "drat-to-lrat": [
            "sealed-drat-trim", "sealed-base-dimacs", "opened-drat-fd",
            "-L", "private-o_excl-lrat-fd", "-t", "604800",
        ],
        "lrat-check": [
            "sealed-lrat-check", "sealed-base-dimacs", "opened-lrat-fd",
        ],
        "final-drat-replay": [
            "sealed-drat-trim", "sealed-base-dimacs", "opened-drat-fd",
            "-t", "604800",
        ],
        "final-lrat-replay": [
            "sealed-lrat-check", "sealed-base-dimacs", "opened-lrat-fd",
        ],
    }[role]
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-proof-checker-invocation-v2",
        "role": role,
        "checker": dict(checker_memfd),
        "dynamic_runtime": dict(dynamic_runtime),
        "base": dict(base_memfd),
        "proof_input": _artifact_reference(proof_record),
        "argv_roles": [
            "sealed-loader-memfd", "--inhibit-cache", "--library-path",
            "private-runtime-dirfd", "--argv0", role,
        ] + tool_roles,
        "actual_argv_sha256": canonical_sha256(list(argv)),
        "timeout_s": CHECKER_TIMEOUT_S,
        "stdout_cap_bytes": CHECKER_LOG_MAX_BYTES,
        "stderr_cap_bytes": CHECKER_LOG_MAX_BYTES,
        "output_role": output_role,
        "environment": _clean_env(),
    })


def _run_checker(
    *,
    target: Path,
    role: str,
    checker_path: Path,
    checker_sha256: str,
    proof_path: Path,
    proof_record: Mapping[str, Any],
    proof_cap: int,
    marker: bytes,
    output_fd: int | None = None,
) -> tuple[dict[str, Any], bytes, bytes, dict[str, Any]]:
    if checker_path == DRAT_TRIM_PATH and checker_sha256 == EXPECTED_DRAT_TRIM_SHA256:
        checker_bytes = EXPECTED_DRAT_TRIM_BYTES
    elif checker_path == LRAT_CHECK_PATH and checker_sha256 == EXPECTED_LRAT_CHECK_SHA256:
        checker_bytes = EXPECTED_LRAT_CHECK_BYTES
    else:
        raise ProofRunnerError("checker path/hash pair is not frozen")
    checker_fd = base_fd = proof_fd = -1
    runtime_handle: dict[str, Any] | None = None
    try:
        checker_fd, checker_memfd = _seal_memfd_from_path(
            checker_path,
            expected_sha256=checker_sha256,
            expected_bytes=checker_bytes,
            executable=True,
        )
        base_fd, base_memfd = _seal_memfd_from_path(
            target / STATIC_DIMACS,
            expected_sha256=EXPECTED_BASE_DIMACS_SHA256,
            expected_bytes=EXPECTED_BASE_DIMACS_BYTES,
            executable=False,
        )
        proof_fd, bound_proof = _open_bound_input(
            proof_path, target, proof_record["role"],
            expected_sha256=proof_record["file_sha256"], cap=proof_cap,
        )
        runtime_handle = _stage_dynamic_runtime()
        runtime_record = runtime_handle["record"]
        loader_fd = runtime_handle["loader_fd"]
        runtime_directory_fd = runtime_handle["directory_fd"]
        prefix = [
            f"/proc/self/fd/{loader_fd}",
            "--inhibit-cache",
            "--library-path", runtime_record["library_path"],
            "--argv0", role,
            f"/proc/self/fd/{checker_fd}",
        ]
        if role in {"drat-verify", "final-drat-replay"}:
            tool_args = [
                f"/proc/self/fd/{base_fd}", f"/proc/self/fd/{proof_fd}",
                "-t", str(CHECKER_TIMEOUT_S),
            ]
        elif role == "drat-to-lrat":
            if output_fd is None:
                raise ProofRunnerError("DRAT conversion needs LRAT output fd")
            tool_args = [
                f"/proc/self/fd/{base_fd}", f"/proc/self/fd/{proof_fd}",
                "-L", f"/proc/self/fd/{output_fd}",
                "-t", str(CHECKER_TIMEOUT_S),
            ]
        elif role in {"lrat-check", "final-lrat-replay"}:
            tool_args = [
                f"/proc/self/fd/{base_fd}", f"/proc/self/fd/{proof_fd}",
            ]
        else:
            raise ProofRunnerError("unknown checker role")
        argv = prefix + tool_args
        pass_fds = [
            loader_fd, runtime_directory_fd, checker_fd, base_fd, proof_fd,
        ]
        watched: list[tuple[int, int]] = []
        if output_fd is not None:
            pass_fds.append(output_fd)
            watched.append((output_fd, LRAT_MAX_BYTES))
        invocation = _checker_invocation(
            role=role,
            checker_memfd=checker_memfd,
            dynamic_runtime=runtime_record,
            base_memfd=base_memfd,
            proof_record=bound_proof,
            argv=argv,
            output_role=("lrat" if output_fd is not None else None),
        )
        process, stdout, stderr = _run_capped_process(
            argv,
            timeout_s=CHECKER_TIMEOUT_S,
            stdout_cap=CHECKER_LOG_MAX_BYTES,
            stderr_cap=CHECKER_LOG_MAX_BYTES,
            cwd=target,
            pass_fds=pass_fds,
            file_size_cap=(LRAT_MAX_BYTES if output_fd is not None else proof_cap),
            watched_fds=watched,
        )
        _assert_bound_input_unchanged(
            proof_fd, proof_path, target, proof_record["role"],
            expected_record=bound_proof, cap=proof_cap,
        )
        _validate_staged_dynamic_runtime(runtime_handle)
        check = seal({
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-proof-checker-result-v2",
            "role": role,
            "invocation": invocation,
            "process": process,
            "semantic_marker": marker.decode("ascii"),
            "semantic_marker_count": _semantic_marker_count(stdout, marker),
            "semantic_marker_sha256": hashlib.sha256(marker + b"\n").hexdigest(),
            "stderr_empty": stderr == b"",
            "verified": _checker_success(
                process, stdout, stderr, marker=marker,
            ),
        })
        return check, stdout, stderr, bound_proof
    finally:
        if checker_fd >= 0:
            os.close(checker_fd)
        if base_fd >= 0:
            os.close(base_fd)
        if proof_fd >= 0:
            os.close(proof_fd)
        if runtime_handle is not None:
            _destroy_dynamic_runtime(runtime_handle)


def _publish_checker_logs(
    target: Path, prefix: str, stdout: bytes, stderr: bytes,
) -> list[dict[str, Any]]:
    _atomic_publish_bytes(target / "logs", f"{prefix}.stdout", stdout)
    _atomic_publish_bytes(target / "logs", f"{prefix}.stderr", stderr)
    return [
        _physical_record(
            target / "logs" / f"{prefix}.stdout", target,
            f"{prefix}-stdout", cap=CHECKER_LOG_MAX_BYTES,
        ),
        _physical_record(
            target / "logs" / f"{prefix}.stderr", target,
            f"{prefix}-stderr", cap=CHECKER_LOG_MAX_BYTES,
        ),
    ]


def verify_root(
    root: Path, *, _production_nonce: object | None = None,
) -> dict[str, Any]:
    target = _validate_root_argument(Path(root), must_exist=True)
    context = _require_production_cli("verify", target, _production_nonce)
    raw_validation = _validate_raw(target, fresh_source_and_tools=True)
    if (
        raw_validation["static"]["authority"] != AUTHORITY_PRODUCTION
        or raw_validation["static"]["test_only"] is not False
        or raw_validation["raw"].get("authority") != AUTHORITY_PRODUCTION
        or raw_validation["raw"].get("test_only") is not False
        or raw_validation["raw"].get("production_eligible") is not True
    ):
        raise ProofRunnerError("production verify rejects tainted RAW predecessor")
    if raw_validation["state"] != "RAW_UNSAT" or raw_validation["strict_raw_unsat"] is not True:
        raise ProofRunnerError("proof verification requires strict RAW_UNSAT")
    if (target / VERIFY_CLAIM).exists() or (target / DRAT_COMMIT).exists():
        raise ProofRunnerError("verify stage already claimed or committed")
    root_before = _root_identity(target)
    resource_before = _resource_gate(target, output_cap=LRAT_MAX_BYTES)
    claim = _create_claim(target, VERIFY_CLAIM, "verify")
    claim_record = _physical_record(
        target / VERIFY_CLAIM, target, "verify-claim", cap=JSON_MAX_BYTES,
    )
    proof_record = raw_validation["proof"]
    assert type(proof_record) is dict

    drat_check, drat_stdout, drat_stderr, bound_drat = _run_checker(
        target=target,
        role="drat-verify",
        checker_path=DRAT_TRIM_PATH,
        checker_sha256=EXPECTED_DRAT_TRIM_SHA256,
        proof_path=target / DRAT_ARTIFACT,
        proof_record=proof_record,
        proof_cap=PROOF_MAX_BYTES,
        marker=b"s VERIFIED",
    )
    drat_logs = _publish_checker_logs(
        target, "drat-verify", drat_stdout, drat_stderr,
    )
    resource_after_drat = _instant_resource(target)
    drat_oom_delta = _oom_delta(resource_before, resource_after_drat)
    drat_passed = bool(
        drat_check["verified"] is True
        and all(value == 0 for value in drat_oom_delta.values())
        and json_type_equal(root_before, _root_identity(target))
    )
    drat_state = "DRAT_VERIFIED" if drat_passed else "UNRESOLVED"
    drat_record = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-drat-verification-v2",
        "gate": GATE,
        "state": drat_state,
        "authority": AUTHORITY_PRODUCTION,
        "test_only": False,
        "production_eligible": drat_passed,
        "root": str(target),
        "root_identity": root_before,
        "direct_cli_context": context,
        "predecessor": _predecessor(target, RAW_COMMIT),
        "claim": claim,
        "claim_artifact": claim_record,
        "resource_gate_before": resource_before,
        "resource_snapshot_after": resource_after_drat,
        "oom_event_delta": drat_oom_delta,
        "bound_base_dimacs_sha256": EXPECTED_BASE_DIMACS_SHA256,
        "bound_drat": bound_drat,
        "checker": drat_check,
        "logs": drat_logs,
        "verified": drat_passed,
        "distance_lower_bound": None,
        "publication_certificate": False,
        "upload_authorized": False,
    })
    _atomic_publish_json(target / "state", DRAT_COMMIT.name, drat_record)
    if not drat_passed:
        return drat_record

    lrat_resource_gate = _resource_gate(target, output_cap=LRAT_MAX_BYTES)

    lrat_fd, private_lrat_name = _create_private_output(
        target / "artifacts", "base.lrat",
    )
    conversion, convert_stdout, convert_stderr, conversion_bound_drat = _run_checker(
        target=target,
        role="drat-to-lrat",
        checker_path=DRAT_TRIM_PATH,
        checker_sha256=EXPECTED_DRAT_TRIM_SHA256,
        proof_path=target / DRAT_ARTIFACT,
        proof_record=proof_record,
        proof_cap=PROOF_MAX_BYTES,
        marker=b"s VERIFIED",
        output_fd=lrat_fd,
    )
    convert_logs = _publish_checker_logs(
        target, "drat-to-lrat", convert_stdout, convert_stderr,
    )
    lrat_sha: str | None = None
    lrat_bytes: int | None = None
    lrat_hash_error: str | None = None
    try:
        os.fsync(lrat_fd)
        lrat_sha, lrat_bytes, _ = _hash_fd_stable(lrat_fd, cap=LRAT_MAX_BYTES)
    except (OSError, ProofRunnerError) as exc:
        lrat_hash_error = f"{type(exc).__name__}: {exc}"
    resource_after_conversion = _instant_resource(target)
    conversion_oom_delta = _oom_delta(lrat_resource_gate, resource_after_conversion)
    conversion_passed = bool(
        conversion["verified"] is True
        and all(value == 0 for value in conversion_oom_delta.values())
        and lrat_hash_error is None
        and type(lrat_sha) is str
        and type(lrat_bytes) is int
        and lrat_bytes > 0
        and lrat_bytes <= LRAT_MAX_BYTES
    )
    lrat_artifact: dict[str, Any] | None = None
    if conversion_passed:
        assert lrat_sha is not None and lrat_bytes is not None
        _publish_private_output(
            target / "artifacts",
            private_lrat_name,
            lrat_fd,
            LRAT_ARTIFACT.name,
            expected_sha256=lrat_sha,
            expected_bytes=lrat_bytes,
        )
        lrat_artifact = _physical_record(
            target / LRAT_ARTIFACT, target, "converted-lrat",
            cap=LRAT_MAX_BYTES,
        )
    else:
        _discard_private(target / "artifacts", private_lrat_name, lrat_fd)

    lrat_check: dict[str, Any] | None = None
    lrat_logs: list[dict[str, Any]] | None = None
    lrat_bound: dict[str, Any] | None = None
    if conversion_passed and lrat_artifact is not None:
        lrat_check, lrat_stdout, lrat_stderr, lrat_bound = _run_checker(
            target=target,
            role="lrat-check",
            checker_path=LRAT_CHECK_PATH,
            checker_sha256=EXPECTED_LRAT_CHECK_SHA256,
            proof_path=target / LRAT_ARTIFACT,
            proof_record=lrat_artifact,
            proof_cap=LRAT_MAX_BYTES,
            marker=b"c VERIFIED",
        )
        lrat_logs = _publish_checker_logs(
            target, "lrat-check", lrat_stdout, lrat_stderr,
        )
    resource_after_lrat = _instant_resource(target)
    lrat_oom_delta = _oom_delta(lrat_resource_gate, resource_after_lrat)
    lrat_passed = bool(
        conversion_passed
        and type(lrat_check) is dict
        and lrat_check.get("verified") is True
        and all(value == 0 for value in lrat_oom_delta.values())
        and json_type_equal(root_before, _root_identity(target))
    )
    lrat_state = "LRAT_VERIFIED" if lrat_passed else "UNRESOLVED"
    lrat_record = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-lrat-verification-v2",
        "gate": GATE,
        "state": lrat_state,
        "authority": AUTHORITY_PRODUCTION,
        "test_only": False,
        "production_eligible": lrat_passed,
        "root": str(target),
        "root_identity": root_before,
        "predecessor": _predecessor(target, DRAT_COMMIT),
        "resource_gate_before_conversion": lrat_resource_gate,
        "resource_snapshot_after_conversion": resource_after_conversion,
        "resource_snapshot_after_lrat": resource_after_lrat,
        "oom_event_delta": lrat_oom_delta,
        "bound_drat": conversion_bound_drat,
        "conversion": conversion,
        "conversion_logs": convert_logs,
        "lrat_hash_error": lrat_hash_error,
        "lrat_artifact": lrat_artifact,
        "bound_lrat": lrat_bound,
        "lrat_checker": lrat_check,
        "lrat_checker_logs": lrat_logs,
        "verified": lrat_passed,
        "distance_lower_bound": None,
        "publication_certificate": False,
        "upload_authorized": False,
    })
    _atomic_publish_json(target / "state", LRAT_COMMIT.name, lrat_record)
    if lrat_passed:
        replay = _validate_lrat(target, fresh_source_and_tools=True)
        if not json_type_equal(replay["lrat"], lrat_record):
            raise ProofRunnerError("post-commit LRAT replay mismatch")
    return lrat_record



def _validate_checker_record(
    value: Any,
    *,
    stdout: bytes,
    stderr: bytes,
    expected_role: str,
    marker: bytes,
    expected_checker_sha256: str,
    target: Path,
    expected_proof_record: Mapping[str, Any],
    proof_cap: int,
    expected_output_role: str | None,
    source_tcb: Mapping[str, Any],
) -> bool:
    fields = {
        "schema_version", "kind", "role", "invocation", "process",
        "semantic_marker", "semantic_marker_count",
        "semantic_marker_sha256", "stderr_empty", "verified",
        "record_sha256",
    }
    invocation_fields = {
        "schema_version", "kind", "role", "checker", "dynamic_runtime",
        "base", "proof_input", "argv_roles", "actual_argv_sha256",
        "timeout_s", "stdout_cap_bytes", "stderr_cap_bytes", "output_role",
        "environment", "record_sha256",
    }
    if (
        type(value) is not dict
        or set(value) != fields
        or not selfhash_valid(value)
        or type(value.get("schema_version")) is not int
        or value["schema_version"] != SCHEMA_VERSION
        or value.get("kind") != "paper400-proof-checker-result-v2"
        or value.get("role") != expected_role
    ):
        return False
    if (
        expected_checker_sha256 == EXPECTED_DRAT_TRIM_SHA256
        and expected_role in {
            "drat-verify", "drat-to-lrat", "final-drat-replay",
        }
    ):
        checker_path = DRAT_TRIM_PATH
        checker_bytes = EXPECTED_DRAT_TRIM_BYTES
    elif (
        expected_checker_sha256 == EXPECTED_LRAT_CHECK_SHA256
        and expected_role in {"lrat-check", "final-lrat-replay"}
    ):
        checker_path = LRAT_CHECK_PATH
        checker_bytes = EXPECTED_LRAT_CHECK_BYTES
    else:
        return False
    invocation = value.get("invocation")
    if (
        type(invocation) is not dict
        or set(invocation) != invocation_fields
        or not selfhash_valid(invocation)
        or type(invocation.get("schema_version")) is not int
        or invocation["schema_version"] != SCHEMA_VERSION
        or invocation.get("kind") != "paper400-proof-checker-invocation-v2"
        or invocation.get("role") != expected_role
        or not _validate_memfd_record(
            invocation.get("checker"), source_path=checker_path,
            expected_sha256=expected_checker_sha256,
            expected_bytes=checker_bytes, executable=True,
        )
        or not _validate_memfd_record(
            invocation.get("base"), source_path=target / STATIC_DIMACS,
            expected_sha256=EXPECTED_BASE_DIMACS_SHA256,
            expected_bytes=EXPECTED_BASE_DIMACS_BYTES, executable=False,
        )
        or not json_type_equal(
            invocation.get("proof_input"),
            _artifact_reference(expected_proof_record),
        )
        or not json_type_equal(
            invocation.get("argv_roles"), _checker_argv_roles(expected_role),
        )
        or type(invocation.get("timeout_s")) is not int
        or invocation["timeout_s"] != CHECKER_TIMEOUT_S
        or type(invocation.get("stdout_cap_bytes")) is not int
        or invocation["stdout_cap_bytes"] != CHECKER_LOG_MAX_BYTES
        or type(invocation.get("stderr_cap_bytes")) is not int
        or invocation["stderr_cap_bytes"] != CHECKER_LOG_MAX_BYTES
        or invocation.get("output_role") != expected_output_role
        or not json_type_equal(invocation.get("environment"), _clean_env())
        or not _validate_historical_dynamic_runtime(
            invocation.get("dynamic_runtime"), source_tcb=source_tcb,
        )
    ):
        return False
    process = value.get("process")
    if not _validate_process_record(process):
        return False
    argv = process["argv"]
    if expected_role in {"drat-verify", "final-drat-replay"}:
        expected_length = 11
        expected_tail = ["-t", str(CHECKER_TIMEOUT_S)]
        fd_positions = (0, 3, 6, 7, 8)
    elif expected_role == "drat-to-lrat":
        expected_length = 13
        expected_tail = ["-L", None, "-t", str(CHECKER_TIMEOUT_S)]
        fd_positions = (0, 3, 6, 7, 8, 10)
    else:
        expected_length = 9
        expected_tail = []
        fd_positions = (0, 3, 6, 7, 8)
    if len(argv) != expected_length:
        return False
    descriptor_numbers = [_proc_fd_number(argv[index]) for index in fd_positions]
    if (
        any(number is None for number in descriptor_numbers)
        or len(set(descriptor_numbers)) != len(descriptor_numbers)
        or argv[1:3] != ["--inhibit-cache", "--library-path"]
        or argv[3] != invocation["dynamic_runtime"]["library_path"]
        or argv[4:6] != ["--argv0", expected_role]
    ):
        return False
    if expected_role == "drat-to-lrat":
        if argv[9] != expected_tail[0] or argv[11:] != expected_tail[2:]:
            return False
    elif argv[9:] != expected_tail:
        return False
    expected_file_cap = (
        LRAT_MAX_BYTES if expected_output_role == "lrat" else proof_cap
    )
    if (
        invocation.get("actual_argv_sha256") != canonical_sha256(argv)
        or process.get("cwd") != str(target)
        or not json_type_equal(process.get("environment"), _clean_env())
        or process.get("timeout_s") != CHECKER_TIMEOUT_S
        or process.get("stdout_cap_bytes") != CHECKER_LOG_MAX_BYTES
        or process.get("stderr_cap_bytes") != CHECKER_LOG_MAX_BYTES
        or process.get("file_size_cap_bytes") != expected_file_cap
        or process.get("stdout") != _hash_record(stdout)
        or process.get("stderr") != _hash_record(stderr)
        or not _process_clean(process, rc=0)
    ):
        return False
    return bool(
        value.get("semantic_marker") == marker.decode("ascii")
        and stderr == b""
        and _checker_terminal_lines(stdout, marker) == [marker]
        and type(value.get("semantic_marker_count")) is int
        and value["semantic_marker_count"] == 1
        and value["semantic_marker_count"]
        == _semantic_marker_count(stdout, marker)
        and value.get("semantic_marker_sha256")
        == hashlib.sha256(marker + b"\n").hexdigest()
        and value.get("stderr_empty") is (stderr == b"")
        and value.get("stderr_empty") is True
        and value.get("verified")
        is _checker_success(process, stdout, stderr, marker=marker)
        and value.get("verified") is True
    )


def _validate_drat(
    root: Path, *, fresh_source_and_tools: bool,
) -> dict[str, Any]:
    target = _validate_root_argument(Path(root), must_exist=True)
    raw = _validate_raw(target, fresh_source_and_tools=fresh_source_and_tools)
    if (
        raw["static"]["authority"] != AUTHORITY_PRODUCTION
        or raw["static"]["test_only"] is not False
        or raw["raw"].get("authority") != AUTHORITY_PRODUCTION
        or raw["raw"].get("test_only") is not False
        or raw["raw"].get("production_eligible") is not True
    ):
        raise ProofRunnerError("DRAT validator rejects tainted RAW predecessor")
    if raw["state"] != "RAW_UNSAT" or raw["strict_raw_unsat"] is not True:
        raise ProofRunnerError("DRAT record lacks strict RAW_UNSAT predecessor")
    record = _strict_json(target / DRAT_COMMIT)
    fields = {
        "schema_version", "kind", "gate", "state", "authority", "test_only",
        "production_eligible", "root", "root_identity",
        "direct_cli_context", "predecessor", "claim", "claim_artifact",
        "resource_gate_before", "resource_snapshot_after",
        "oom_event_delta", "bound_base_dimacs_sha256", "bound_drat",
        "checker", "logs", "verified", "distance_lower_bound",
        "publication_certificate", "upload_authorized", "record_sha256",
    }
    if (
        type(record) is not dict
        or set(record) != fields
        or not selfhash_valid(record)
        or type(record.get("schema_version")) is not int
        or record["schema_version"] != SCHEMA_VERSION
        or record.get("kind") != "paper400-dic5-drat-verification-v2"
        or record.get("gate") != GATE
    ):
        raise ProofRunnerError("DRAT record schema/self-hash mismatch")
    _validate_stored_direct_cli_context(
        record.get("direct_cli_context"), action="verify", target=target,
    )
    if (
        record.get("authority") != AUTHORITY_PRODUCTION
        or record.get("test_only") is not False
        or record.get("root") != str(target)
        or not json_type_equal(record.get("root_identity"), _root_identity(target))
        or not json_type_equal(record.get("predecessor"), _predecessor(target, RAW_COMMIT))
        or record.get("bound_base_dimacs_sha256") != EXPECTED_BASE_DIMACS_SHA256
        or not json_type_equal(record.get("bound_drat"), raw["proof"])
        or not _validate_resource_snapshot(record.get("resource_snapshot_after"))
        or not _validate_resource_record(
            record.get("resource_gate_before"), required_cap=LRAT_MAX_BYTES,
        )
        or record.get("distance_lower_bound") is not None
        or record.get("publication_certificate") is not False
        or record.get("upload_authorized") is not False
    ):
        raise ProofRunnerError("DRAT common binding mismatch")
    claim = _strict_json(target / VERIFY_CLAIM)
    _validate_claim_record(claim, action="verify", target=target)
    if (
        not selfhash_valid(claim)
        or not json_type_equal(record.get("claim"), claim)
        or not json_type_equal(
            record.get("claim_artifact"),
            _physical_record(
                target / VERIFY_CLAIM, target, "verify-claim", cap=JSON_MAX_BYTES,
            ),
        )
    ):
        raise ProofRunnerError("DRAT claim binding mismatch")
    logs = [
        _physical_record(
            target / "logs/drat-verify.stdout", target,
            "drat-verify-stdout", cap=CHECKER_LOG_MAX_BYTES,
        ),
        _physical_record(
            target / "logs/drat-verify.stderr", target,
            "drat-verify-stderr", cap=CHECKER_LOG_MAX_BYTES,
        ),
    ]
    if not json_type_equal(record.get("logs"), logs):
        raise ProofRunnerError("DRAT logs physical mismatch")
    stdout = _read_file_stable(
        target / "logs/drat-verify.stdout", cap=CHECKER_LOG_MAX_BYTES,
    )
    stderr = _read_file_stable(
        target / "logs/drat-verify.stderr", cap=CHECKER_LOG_MAX_BYTES,
    )
    checker_valid = _validate_checker_record(
        record.get("checker"),
        stdout=stdout,
        stderr=stderr,
        expected_role="drat-verify",
        marker=b"s VERIFIED",
        expected_checker_sha256=EXPECTED_DRAT_TRIM_SHA256,
        target=target,
        expected_proof_record=raw["proof"],
        proof_cap=PROOF_MAX_BYTES,
        expected_output_role=None,
        source_tcb=raw["static"]["manifest"]["preflight_summary"][
            "toolchain_binding"
        ]["dynamic_elf_tcb"],
    )
    expected_delta = _oom_delta(
        record["resource_gate_before"], record["resource_snapshot_after"],
    )
    if not json_type_equal(record.get("oom_event_delta"), expected_delta):
        raise ProofRunnerError("DRAT OOM delta mismatch")
    passed = bool(checker_valid and all(value == 0 for value in expected_delta.values()))
    expected_state = "DRAT_VERIFIED" if passed else "UNRESOLVED"
    if (
        record.get("state") != expected_state
        or record.get("verified") is not passed
        or record.get("production_eligible") is not passed
    ):
        raise ProofRunnerError("DRAT verification truth table mismatch")
    return {
        "raw": raw,
        "drat": record,
        "state": expected_state,
        "verified": passed,
    }


def _validate_lrat(
    root: Path, *, fresh_source_and_tools: bool,
) -> dict[str, Any]:
    target = _validate_root_argument(Path(root), must_exist=True)
    drat = _validate_drat(target, fresh_source_and_tools=fresh_source_and_tools)
    if (
        drat["raw"]["static"]["authority"] != AUTHORITY_PRODUCTION
        or drat["raw"]["static"]["test_only"] is not False
        or drat["raw"]["raw"].get("authority") != AUTHORITY_PRODUCTION
        or drat["raw"]["raw"].get("test_only") is not False
        or drat["drat"].get("authority") != AUTHORITY_PRODUCTION
        or drat["drat"].get("test_only") is not False
    ):
        raise ProofRunnerError("LRAT validator rejects tainted proof chain")
    if drat["state"] != "DRAT_VERIFIED" or drat["verified"] is not True:
        raise ProofRunnerError("LRAT record lacks DRAT_VERIFIED predecessor")
    record = _strict_json(target / LRAT_COMMIT)
    fields = {
        "schema_version", "kind", "gate", "state", "authority", "test_only",
        "production_eligible", "root", "root_identity", "predecessor",
        "resource_gate_before_conversion", "resource_snapshot_after_conversion", "resource_snapshot_after_lrat",
        "oom_event_delta", "bound_drat", "conversion", "conversion_logs",
        "lrat_hash_error", "lrat_artifact", "bound_lrat", "lrat_checker",
        "lrat_checker_logs", "verified", "distance_lower_bound",
        "publication_certificate", "upload_authorized", "record_sha256",
    }
    if (
        type(record) is not dict
        or set(record) != fields
        or not selfhash_valid(record)
        or type(record.get("schema_version")) is not int
        or record["schema_version"] != SCHEMA_VERSION
        or record.get("kind") != "paper400-dic5-lrat-verification-v2"
        or record.get("gate") != GATE
    ):
        raise ProofRunnerError("LRAT record schema/self-hash mismatch")
    if (
        record.get("authority") != AUTHORITY_PRODUCTION
        or record.get("test_only") is not False
        or record.get("root") != str(target)
        or not json_type_equal(record.get("root_identity"), _root_identity(target))
        or not json_type_equal(record.get("predecessor"), _predecessor(target, DRAT_COMMIT))
        or not _validate_resource_snapshot(
            record.get("resource_snapshot_after_conversion"),
        )
        or not _validate_resource_snapshot(
            record.get("resource_snapshot_after_lrat"),
        )
        or not _validate_resource_record(
            record.get("resource_gate_before_conversion"),
            required_cap=LRAT_MAX_BYTES,
        )
        or record.get("distance_lower_bound") is not None
        or record.get("publication_certificate") is not False
        or record.get("upload_authorized") is not False
        or not json_type_equal(record.get("bound_drat"), drat["raw"]["proof"])
    ):
        raise ProofRunnerError("LRAT common binding mismatch")
    conversion_logs = [
        _physical_record(
            target / "logs/drat-to-lrat.stdout", target,
            "drat-to-lrat-stdout", cap=CHECKER_LOG_MAX_BYTES,
        ),
        _physical_record(
            target / "logs/drat-to-lrat.stderr", target,
            "drat-to-lrat-stderr", cap=CHECKER_LOG_MAX_BYTES,
        ),
    ]
    if not json_type_equal(record.get("conversion_logs"), conversion_logs):
        raise ProofRunnerError("LRAT conversion logs mismatch")
    convert_stdout = _read_file_stable(
        target / "logs/drat-to-lrat.stdout", cap=CHECKER_LOG_MAX_BYTES,
    )
    convert_stderr = _read_file_stable(
        target / "logs/drat-to-lrat.stderr", cap=CHECKER_LOG_MAX_BYTES,
    )
    conversion_valid = _validate_checker_record(
        record.get("conversion"),
        stdout=convert_stdout,
        stderr=convert_stderr,
        expected_role="drat-to-lrat",
        marker=b"s VERIFIED",
        expected_checker_sha256=EXPECTED_DRAT_TRIM_SHA256,
        target=target,
        expected_proof_record=drat["raw"]["proof"],
        proof_cap=PROOF_MAX_BYTES,
        expected_output_role="lrat",
        source_tcb=drat["raw"]["static"]["manifest"]["preflight_summary"][
            "toolchain_binding"
        ]["dynamic_elf_tcb"],
    )
    lrat_artifact = record.get("lrat_artifact")
    lrat_physical_valid = False
    if type(lrat_artifact) is dict:
        lrat_physical_valid = json_type_equal(
            lrat_artifact,
            _physical_record(
                target / LRAT_ARTIFACT, target, "converted-lrat",
                cap=LRAT_MAX_BYTES,
            ),
        ) and 0 < lrat_artifact.get("bytes", 0) <= LRAT_MAX_BYTES
    lrat_logs_value = record.get("lrat_checker_logs")
    checker_valid = False
    if type(lrat_logs_value) is list and len(lrat_logs_value) == 2:
        expected_logs = [
            _physical_record(
                target / "logs/lrat-check.stdout", target,
                "lrat-check-stdout", cap=CHECKER_LOG_MAX_BYTES,
            ),
            _physical_record(
                target / "logs/lrat-check.stderr", target,
                "lrat-check-stderr", cap=CHECKER_LOG_MAX_BYTES,
            ),
        ]
        if json_type_equal(lrat_logs_value, expected_logs):
            lrat_stdout = _read_file_stable(
                target / "logs/lrat-check.stdout", cap=CHECKER_LOG_MAX_BYTES,
            )
            lrat_stderr = _read_file_stable(
                target / "logs/lrat-check.stderr", cap=CHECKER_LOG_MAX_BYTES,
            )
            checker_valid = _validate_checker_record(
                record.get("lrat_checker"),
                stdout=lrat_stdout,
                stderr=lrat_stderr,
                expected_role="lrat-check",
                marker=b"c VERIFIED",
                expected_checker_sha256=EXPECTED_LRAT_CHECK_SHA256,
                target=target,
                expected_proof_record=lrat_artifact,
                proof_cap=LRAT_MAX_BYTES,
                expected_output_role=None,
                source_tcb=drat["raw"]["static"]["manifest"][
                    "preflight_summary"
                ]["toolchain_binding"]["dynamic_elf_tcb"],
            )
    conversion_delta = _oom_delta(
        record["resource_gate_before_conversion"],
        record["resource_snapshot_after_conversion"],
    )
    expected_delta = _oom_delta(
        record["resource_gate_before_conversion"],
        record["resource_snapshot_after_lrat"],
    )
    if not json_type_equal(record.get("oom_event_delta"), expected_delta):
        raise ProofRunnerError("LRAT OOM delta mismatch")
    passed = bool(
        conversion_valid
        and lrat_physical_valid
        and record.get("lrat_hash_error") is None
        and json_type_equal(record.get("bound_lrat"), lrat_artifact)
        and checker_valid
        and all(value == 0 for value in conversion_delta.values())
        and all(value == 0 for value in expected_delta.values())
    )
    expected_state = "LRAT_VERIFIED" if passed else "UNRESOLVED"
    if (
        record.get("state") != expected_state
        or record.get("verified") is not passed
        or record.get("production_eligible") is not passed
    ):
        raise ProofRunnerError("LRAT verification truth table mismatch")
    return {
        "drat": drat,
        "lrat": record,
        "state": expected_state,
        "verified": passed,
    }


def _chain_reference(root: Path, relative: Path) -> dict[str, Any]:
    value = _strict_json(root / relative)
    if not selfhash_valid(value):
        raise ProofRunnerError(f"chain record self-hash invalid: {relative}")
    physical = _physical_record(
        root / relative, root, relative.stem, cap=JSON_MAX_BYTES,
    )
    return {
        "relative_path": relative.as_posix(),
        "file_sha256": physical["file_sha256"],
        "record_sha256": value["record_sha256"],
    }


def _fresh_replay(
    target: Path,
    lrat_validation: Mapping[str, Any],
) -> dict[str, Any]:
    static_summary = lrat_validation["drat"]["raw"]["static"]["manifest"][
        "preflight_summary"
    ]
    fresh_summary, fresh_old_preflight, fresh_dimacs = _prepare_materials()
    static_dimacs = _read_file_stable(
        target / STATIC_DIMACS, cap=EXPECTED_BASE_DIMACS_BYTES,
    )
    scientific_equal = json_type_equal(
        fresh_summary["instance_binding"], static_summary["instance_binding"],
    )
    sources_equal = json_type_equal(
        fresh_summary["source_binding"], static_summary["source_binding"],
    )
    tools_equal = json_type_equal(
        fresh_summary["toolchain_binding"], static_summary["toolchain_binding"],
    )
    base_equal = fresh_dimacs == static_dimacs
    old_preflight_equal = (
        hashlib.sha256(fresh_old_preflight).hexdigest()
        == static_summary["old_preflight_file_sha256"]
    )
    if not all((
        scientific_equal, sources_equal, tools_equal, base_equal,
        old_preflight_equal,
    )):
        raise ProofRunnerError("fresh final scientific/source/tool replay mismatch")

    drat_artifact = lrat_validation["drat"]["raw"]["proof"]
    lrat_artifact = lrat_validation["lrat"]["lrat_artifact"]
    drat_check, drat_stdout, drat_stderr, bound_drat = _run_checker(
        target=target,
        role="final-drat-replay",
        checker_path=DRAT_TRIM_PATH,
        checker_sha256=EXPECTED_DRAT_TRIM_SHA256,
        proof_path=target / DRAT_ARTIFACT,
        proof_record=drat_artifact,
        proof_cap=PROOF_MAX_BYTES,
        marker=b"s VERIFIED",
    )
    lrat_check, lrat_stdout, lrat_stderr, bound_lrat = _run_checker(
        target=target,
        role="final-lrat-replay",
        checker_path=LRAT_CHECK_PATH,
        checker_sha256=EXPECTED_LRAT_CHECK_SHA256,
        proof_path=target / LRAT_ARTIFACT,
        proof_record=lrat_artifact,
        proof_cap=LRAT_MAX_BYTES,
        marker=b"c VERIFIED",
    )
    if drat_check["verified"] is not True or lrat_check["verified"] is not True:
        raise ProofRunnerError("fresh final proof checker replay failed")
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-fresh-final-replay-v2",
        "scientific_instance_binding_equal": scientific_equal,
        "source_binding_equal": sources_equal,
        "toolchain_binding_equal": tools_equal,
        "base_dimacs_byte_equal": base_equal,
        "old_v13_preflight_byte_equal": old_preflight_equal,
        "base_dimacs_sha256": hashlib.sha256(fresh_dimacs).hexdigest(),
        "bound_drat": bound_drat,
        "bound_lrat": bound_lrat,
        "drat_checker": drat_check,
        "drat_stdout": _hash_record(drat_stdout),
        "drat_stdout_base64": base64.b64encode(drat_stdout).decode("ascii"),
        "drat_stderr": _hash_record(drat_stderr),
        "drat_stderr_base64": base64.b64encode(drat_stderr).decode("ascii"),
        "lrat_checker": lrat_check,
        "lrat_stdout": _hash_record(lrat_stdout),
        "lrat_stdout_base64": base64.b64encode(lrat_stdout).decode("ascii"),
        "lrat_stderr": _hash_record(lrat_stderr),
        "lrat_stderr_base64": base64.b64encode(lrat_stderr).decode("ascii"),
        "all_fresh_replay_passed": True,
        "solver_invoked": False,
    })


def _certificate_value(
    target: Path,
    lrat_validation: Mapping[str, Any],
    context: Mapping[str, Any],
    claim: Mapping[str, Any],
    claim_artifact: Mapping[str, Any],
    resource_before: Mapping[str, Any],
    resource_after: Mapping[str, Any],
    fresh_replay: Mapping[str, Any],
) -> dict[str, Any]:
    science = lrat_validation["drat"]["raw"]["static"]["scientific_binding"]
    drat_artifact = lrat_validation["drat"]["raw"]["proof"]
    lrat_artifact = lrat_validation["lrat"]["lrat_artifact"]
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-proof-carrying-lower-certificate-v2",
        "gate": GATE,
        "state": "PROOF_CARRYING_LOWER_20",
        "authority": AUTHORITY_PRODUCTION,
        "test_only": False,
        "production_eligible": True,
        "root": str(target),
        "root_identity": _root_identity(target),
        "direct_cli_context": dict(context),
        "predecessor": _predecessor(target, LRAT_COMMIT),
        "claim": dict(claim),
        "claim_artifact": dict(claim_artifact),
        "chain": [
            _chain_reference(target, STATIC_COMMIT),
            _chain_reference(target, RAW_COMMIT),
            _chain_reference(target, DRAT_COMMIT),
            _chain_reference(target, LRAT_COMMIT),
        ],
        "resource_gate_before": dict(resource_before),
        "resource_snapshot_after": dict(resource_after),
        "oom_event_delta": _oom_delta(resource_before, resource_after),
        "fresh_replay": dict(fresh_replay),
        "scientific_binding": science,
        "code": {
            "n": 400,
            "k": 16,
            "max_stabilizer_check_row_weight": 6,
            "distance_lower_bound": 20,
            "distance_exact": None,
            "paper_unverified_upper_bound": 22,
        },
        "fom_lower": {
            "definition": "k*d_lower^2/n",
            "numerator": 16,
            "denominator": 1,
        },
        "strict_threshold": {
            "numerator": 61,
            "denominator": 4,
        },
        "integer_cross_product": {
            "lhs_4_k_d_lower_squared": 25_600,
            "rhs_61_n": 24_400,
            "strict": True,
        },
        "excluded_operator_weights": {
            "cnf_max_weight": 18,
            "all_logicals_even": True,
            "parity_lift_excludes_weight_19": True,
            "both_X_and_Z_covered_by_isometry": True,
        },
        "proofs": {
            "base_dimacs": _artifact_reference(
                lrat_validation["drat"]["raw"]["static"]["base_record"]
            ),
            "binary_drat": _artifact_reference(drat_artifact),
            "converted_lrat": _artifact_reference(lrat_artifact),
            "drat_independently_verified": True,
            "lrat_independently_verified": True,
            "trusted_policy_sha256": EXPECTED_POLICY_CANONICAL_SHA256,
        },
        "claim_semantics": {
            "distance_claim": "d>=20",
            "fom_claim": "FOM>=16>61/4",
            "exact_distance_claimed": False,
            "paper_upper_bound_used_as_exact": False,
        },
        "publication_certificate": True,
        "upload_authorized": False,
    })


def _final_commit_value(
    target: Path,
    certificate_record: Mapping[str, Any],
    certificate: Mapping[str, Any],
) -> dict[str, Any]:
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-proof-carrying-final-commit-v2",
        "gate": GATE,
        "state": "PROOF_CARRYING_LOWER_20",
        "authority": AUTHORITY_PRODUCTION,
        "test_only": False,
        "production_eligible": True,
        "root": str(target),
        "predecessor": _predecessor(target, LRAT_COMMIT),
        "certificate": dict(certificate_record),
        "certificate_record_sha256": certificate["record_sha256"],
        "distance_lower_bound": 20,
        "distance_exact": None,
        "max_stabilizer_check_row_weight": 6,
        "fom_lower_numerator": 16,
        "fom_lower_denominator": 1,
        "strictly_exceeds_61_over_4": True,
        "publication_certificate": True,
        "upload_authorized": False,
        "no_further_root_writes_after_this_commit": True,
    })




def _create_empty_directory_at(parent_fd: int, name: str) -> dict[str, int]:
    if not name or "/" in name or name in {".", ".."}:
        raise ProofRunnerError("unsafe empty-directory component")
    os.mkdir(name, 0o700, dir_fd=parent_fd)
    descriptor = os.open(
        name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
        dir_fd=parent_fd,
    )
    try:
        info = os.fstat(descriptor)
        if (
            not stat.S_ISDIR(info.st_mode)
            or stat.S_IMODE(info.st_mode) != 0o700
            or info.st_uid != os.geteuid()
            or os.listdir(descriptor)
        ):
            raise ProofRunnerError("reserved publication directory is not empty/0700")
        os.fsync(descriptor)
        result = {
            "device": info.st_dev,
            "inode": info.st_ino,
            "mode": stat.S_IMODE(info.st_mode),
            "uid": info.st_uid,
        }
    finally:
        os.close(descriptor)
    os.fsync(parent_fd)
    return result


def _replace_empty_directory_at(
    parent_fd: int,
    source_name: str,
    destination_name: str,
    *,
    expected_destination: Mapping[str, Any],
    transition_state: dict[str, str],
    transition_value: str,
) -> None:
    for component in (source_name, destination_name):
        if not component or "/" in component or component in {".", ".."}:
            raise ProofRunnerError("unsafe publication rename component")
    source_fd = os.open(
        source_name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
        dir_fd=parent_fd,
    )
    destination_fd = os.open(
        destination_name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
        dir_fd=parent_fd,
    )
    try:
        source = os.fstat(source_fd)
        destination = os.fstat(destination_fd)
        actual_destination = {
            "device": destination.st_dev,
            "inode": destination.st_ino,
            "mode": stat.S_IMODE(destination.st_mode),
            "uid": destination.st_uid,
        }
        if (
            not stat.S_ISDIR(source.st_mode)
            or not stat.S_ISDIR(destination.st_mode)
            or not json_type_equal(actual_destination, expected_destination)
            or os.listdir(destination_fd)
        ):
            raise ProofRunnerError("publication destination is not the reserved empty directory")
        source_identity = (
            source.st_dev, source.st_ino, source.st_mode, source.st_uid,
        )
        blocked_signals = {
            signal.SIGINT, signal.SIGTERM, signal.SIGHUP, signal.SIGQUIT,
        }
        previous_mask = signal.pthread_sigmask(
            signal.SIG_BLOCK, blocked_signals,
        )
        try:
            os.rename(
                source_name, destination_name,
                src_dir_fd=parent_fd, dst_dir_fd=parent_fd,
            )
            transition_state["location"] = transition_value
        finally:
            signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)
        os.fsync(parent_fd)
        published = os.stat(
            destination_name, dir_fd=parent_fd, follow_symlinks=False,
        )
        if (
            not stat.S_ISDIR(published.st_mode)
            or source_identity
            != (published.st_dev, published.st_ino, published.st_mode, published.st_uid)
        ):
            raise ProofRunnerError("published directory identity mismatch")
        try:
            os.stat(source_name, dir_fd=parent_fd, follow_symlinks=False)
        except FileNotFoundError:
            pass
        else:
            raise ProofRunnerError("publication source name survived atomic rename")
    finally:
        os.close(destination_fd)
        os.close(source_fd)


def _tree_file_cap(relative: str) -> int:
    if relative == DRAT_ARTIFACT.as_posix():
        return PROOF_MAX_BYTES
    if relative == LRAT_ARTIFACT.as_posix():
        return LRAT_MAX_BYTES
    if relative == STATIC_DIMACS.as_posix():
        return EXPECTED_BASE_DIMACS_BYTES
    if relative == STATIC_PREFLIGHT.as_posix():
        return PREPARE_LOG_MAX_BYTES
    if relative.startswith("logs/"):
        return (
            SOLVER_STDOUT_MAX_BYTES
            if relative == "logs/solver.stdout"
            else SOLVER_STDERR_MAX_BYTES
            if relative == "logs/solver.stderr"
            else CHECKER_LOG_MAX_BYTES
        )
    return JSON_MAX_BYTES


def _snapshot_closed_tree(target: Path, *, phase: str) -> dict[str, Any]:
    failures = _closed_tree_failures(target, phase=phase)
    if failures:
        raise ProofRunnerError(f"closed tree snapshot invalid: {failures}")
    _directories, files = _expected_final_tree()
    if phase == "before-certificate":
        files -= {CERTIFICATE.as_posix(), FINAL_COMMIT.as_posix()}
    elif phase == "before-commit":
        files -= {FINAL_COMMIT.as_posix()}
    elif phase != "final":
        raise ProofRunnerError("unknown closed-tree snapshot phase")
    records: dict[str, Any] = {}
    for relative in sorted(files):
        records[relative] = _physical_record(
            target / relative, target, "closed-tree-snapshot",
            cap=_tree_file_cap(relative),
        )
    return records


def _held_artifacts_match_at(
    held: Sequence[tuple[int, Path, str, dict[str, Any], int]],
    *,
    old_root: Path,
    current_root: Path,
) -> None:
    for descriptor, old_path, role, bound, cap in held:
        relative = old_path.relative_to(old_root)
        _assert_bound_input_unchanged(
            descriptor, current_root / relative, current_root, role,
            expected_record=bound, cap=cap,
        )



def _publish_commit_from_quarantined_root(
    *,
    target: Path,
    root_before: Mapping[str, Any],
    held: Sequence[tuple[int, Path, str, dict[str, Any], int]],
    expected_lrat: Mapping[str, Any],
    certificate: Mapping[str, Any],
    commit: Mapping[str, Any],
) -> dict[str, Any]:
    precommit_snapshot = _snapshot_closed_tree(target, phase="before-commit")
    parent_fd = os.open(
        target.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
    )
    quarantine_name = (
        f".{target.name}.proof-finalizing-{os.getpid()}-"
        f"{os.urandom(32).hex()}"
    )
    quarantine = target.parent / quarantine_name
    quarantine_reservation: dict[str, int] | None = None
    target_placeholder: dict[str, int] | None = None
    location = {"location": "TARGET_PRECOMMIT"}
    private_commit_created = False
    try:
        parent_before = os.fstat(parent_fd)
        quarantine_reservation = _create_empty_directory_at(
            parent_fd, quarantine_name,
        )
        _replace_empty_directory_at(
            parent_fd, target.name, quarantine_name,
            expected_destination=quarantine_reservation,
            transition_state=location,
            transition_value="QUARANTINED_UNDURABLE",
        )
        quarantine_reservation = None
        location["location"] = "QUARANTINED_DURABLE"
        target_placeholder = _create_empty_directory_at(parent_fd, target.name)
        parent_after = os.fstat(parent_fd)
        if (
            (parent_before.st_dev, parent_before.st_ino, parent_before.st_mode)
            != (parent_after.st_dev, parent_after.st_ino, parent_after.st_mode)
        ):
            raise ProofRunnerError("result parent changed during quarantine rename")
        private_identity = _root_identity(quarantine)
        if any(
            private_identity[name] != root_before[name]
            for name in ("device", "inode", "mode", "uid")
        ):
            raise ProofRunnerError("quarantined root identity mismatch")
        private_snapshot = _snapshot_closed_tree(
            quarantine, phase="before-commit",
        )
        if not json_type_equal(private_snapshot, precommit_snapshot):
            raise ProofRunnerError("tree changed across quarantine boundary")
        _held_artifacts_match_at(
            held, old_root=target, current_root=quarantine,
        )
        expected_chain_values = {
            STATIC_COMMIT.as_posix(): expected_lrat["drat"]["raw"]["static"]["commit"],
            RAW_COMMIT.as_posix(): expected_lrat["drat"]["raw"]["raw"],
            DRAT_COMMIT.as_posix(): expected_lrat["drat"]["drat"],
            LRAT_COMMIT.as_posix(): expected_lrat["lrat"],
            CERTIFICATE.as_posix(): certificate,
        }
        for relative, expected in expected_chain_values.items():
            if not json_type_equal(_strict_json(quarantine / relative), expected):
                raise ProofRunnerError(
                    f"quarantined semantic record changed: {relative}"
                )
        private_commit_created = True
        _atomic_publish_json(quarantine, FINAL_COMMIT.name, commit)
        stored_commit = _strict_json(quarantine / FINAL_COMMIT)
        if not json_type_equal(stored_commit, commit):
            raise ProofRunnerError("private final COMMIT readback mismatch")
        final_snapshot = _snapshot_closed_tree(quarantine, phase="final")
        for relative, expected in precommit_snapshot.items():
            if not json_type_equal(final_snapshot.get(relative), expected):
                raise ProofRunnerError(
                    f"tree changed while private COMMIT was written: {relative}"
                )
        _held_artifacts_match_at(
            held, old_root=target, current_root=quarantine,
        )
        assert target_placeholder is not None
        _replace_empty_directory_at(
            parent_fd, quarantine_name, target.name,
            expected_destination=target_placeholder,
            transition_state=location,
            transition_value="PUBLISHED_UNDURABLE",
        )
        location["location"] = "PUBLISHED_DURABLE"
        target_placeholder = None
        if not json_type_equal(root_before, _root_identity(target)):
            raise ProofRunnerError("published root identity mismatch")
        _held_artifacts_match_at(
            held, old_root=target, current_root=target,
        )
        post_snapshot = _snapshot_closed_tree(target, phase="final")
        if not json_type_equal(post_snapshot, final_snapshot):
            raise ProofRunnerError("tree changed across final publication rename")
        post_lrat = _validate_lrat(target, fresh_source_and_tools=True)
        if not json_type_equal(post_lrat, expected_lrat):
            raise ProofRunnerError("published LRAT chain reconstruction mismatch")
        stored_certificate = _strict_json(target / CERTIFICATE)
        if not json_type_equal(stored_certificate, certificate):
            raise ProofRunnerError("published certificate changed")
        _validate_certificate_semantics(
            stored_certificate, target, post_lrat,
        )
        if not json_type_equal(_strict_json(target / FINAL_COMMIT), commit):
            raise ProofRunnerError("published COMMIT changed")
        return stored_commit
    except BaseException as exc:
        if (
            location["location"].startswith("QUARANTINED")
            and not private_commit_created
        ):
            try:
                if target_placeholder is None:
                    target_placeholder = _create_empty_directory_at(
                        parent_fd, target.name,
                    )
                _replace_empty_directory_at(
                    parent_fd, quarantine_name, target.name,
                    expected_destination=target_placeholder,
                    transition_state=location,
                    transition_value="RESTORED_UNDURABLE",
                )
                location["location"] = "RESTORED_DURABLE"
                target_placeholder = None
            except BaseException as restore_exc:
                raise ProofRunnerError(
                    f"finalize failed and poisoned root remains at {quarantine}"
                ) from restore_exc
        if location["location"].startswith("PUBLISHED"):
            raise ProofRunnerError(
                "final COMMIT is published but post-publication durability/"
                "validation failed; authoritative validate must fail closed"
            ) from exc
        if location["location"].startswith("QUARANTINED"):
            raise ProofRunnerError(
                f"private final root withheld at {quarantine}; COMMIT was not exposed"
            ) from exc
        raise
    finally:
        if quarantine_reservation is not None:
            try:
                descriptor = os.open(
                    quarantine_name,
                    os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                    dir_fd=parent_fd,
                )
                try:
                    info = os.fstat(descriptor)
                    actual = {
                        "device": info.st_dev,
                        "inode": info.st_ino,
                        "mode": stat.S_IMODE(info.st_mode),
                        "uid": info.st_uid,
                    }
                    if (
                        not json_type_equal(actual, quarantine_reservation)
                        or os.listdir(descriptor)
                    ):
                        raise ProofRunnerError(
                            "unused quarantine reservation changed"
                        )
                finally:
                    os.close(descriptor)
                os.rmdir(quarantine_name, dir_fd=parent_fd)
                os.fsync(parent_fd)
            except FileNotFoundError:
                pass
        os.close(parent_fd)


def finalize_root(
    root: Path, *, _production_nonce: object | None = None,
) -> dict[str, Any]:
    target = _validate_root_argument(Path(root), must_exist=True)
    context = _require_production_cli("finalize", target, _production_nonce)
    lrat = _validate_lrat(target, fresh_source_and_tools=True)
    if (
        lrat["drat"]["raw"]["static"]["authority"] != AUTHORITY_PRODUCTION
        or lrat["drat"]["raw"]["static"]["test_only"] is not False
        or lrat["drat"]["raw"]["raw"].get("authority") != AUTHORITY_PRODUCTION
        or lrat["drat"]["raw"]["raw"].get("test_only") is not False
        or lrat["drat"]["drat"].get("authority") != AUTHORITY_PRODUCTION
        or lrat["drat"]["drat"].get("test_only") is not False
        or lrat["lrat"].get("authority") != AUTHORITY_PRODUCTION
        or lrat["lrat"].get("test_only") is not False
    ):
        raise ProofRunnerError("finalize rejects tainted proof chain")
    if lrat["state"] != "LRAT_VERIFIED" or lrat["verified"] is not True:
        raise ProofRunnerError("finalize requires strict LRAT_VERIFIED")
    if (
        (target / FINALIZE_CLAIM).exists()
        or (target / CERTIFICATE).exists()
        or (target / FINAL_COMMIT).exists()
    ):
        raise ProofRunnerError("finalize stage already claimed or committed")
    root_before = _root_identity(target)
    resource_before = _resource_gate(target, output_cap=0)
    claim = _create_claim(target, FINALIZE_CLAIM, "finalize")
    claim_artifact = _physical_record(
        target / FINALIZE_CLAIM, target, "finalize-claim", cap=JSON_MAX_BYTES,
    )
    held: list[tuple[int, Path, str, dict[str, Any], int]] = []
    try:
        fresh = _fresh_replay(target, lrat)
        expected_inputs = (
            (
                target / STATIC_DIMACS,
                lrat["drat"]["raw"]["static"]["base_record"],
                EXPECTED_BASE_DIMACS_BYTES,
            ),
            (
                target / DRAT_ARTIFACT,
                lrat["drat"]["raw"]["proof"],
                PROOF_MAX_BYTES,
            ),
            (
                target / LRAT_ARTIFACT,
                lrat["lrat"]["lrat_artifact"],
                LRAT_MAX_BYTES,
            ),
        )
        for path, expected_record, cap in expected_inputs:
            if type(expected_record) is not dict:
                raise ProofRunnerError("final bound artifact record missing")
            descriptor, bound = _open_bound_input(
                path, target, expected_record["role"],
                expected_sha256=expected_record["file_sha256"], cap=cap,
            )
            held.append((descriptor, path, expected_record["role"], bound, cap))
            if not json_type_equal(bound, expected_record):
                raise ProofRunnerError("final held artifact differs from predecessor")
        if (
            not json_type_equal(fresh["bound_drat"], held[1][3])
            or not json_type_equal(fresh["bound_lrat"], held[2][3])
        ):
            raise ProofRunnerError("fresh checker inputs differ from held artifacts")
        resource_after = _instant_resource(target)
        oom_delta = _oom_delta(resource_before, resource_after)
        if any(value != 0 for value in oom_delta.values()):
            raise ProofRunnerError("OOM event during final replay")
        if not json_type_equal(root_before, _root_identity(target)):
            raise ProofRunnerError("root identity changed during final replay")
        tree_failures = _closed_tree_failures(
            target, phase="before-certificate",
        )
        if tree_failures:
            raise ProofRunnerError(f"pre-certificate tree invalid: {tree_failures}")
        replayed_lrat = _validate_lrat(
            target, fresh_source_and_tools=True,
        )
        if not json_type_equal(replayed_lrat, lrat):
            raise ProofRunnerError("LRAT chain changed after fresh replay")
        for descriptor, path, role, bound, cap in held:
            _assert_bound_input_unchanged(
                descriptor, path, target, role,
                expected_record=bound, cap=cap,
            )
        certificate = _certificate_value(
            target, replayed_lrat, context, claim, claim_artifact,
            resource_before, resource_after, fresh,
        )
        _validate_certificate_semantics(certificate, target, replayed_lrat)
        _atomic_publish_json(target, CERTIFICATE.name, certificate)
        stored_certificate = _strict_json(target / CERTIFICATE)
        if not json_type_equal(stored_certificate, certificate):
            raise ProofRunnerError("certificate readback mismatch")
        _validate_certificate_semantics(
            stored_certificate, target, replayed_lrat,
        )
        tree_failures = _closed_tree_failures(target, phase="before-commit")
        if tree_failures:
            raise ProofRunnerError(f"pre-COMMIT tree invalid: {tree_failures}")
        final_lrat = _validate_lrat(target, fresh_source_and_tools=True)
        if not json_type_equal(final_lrat, replayed_lrat):
            raise ProofRunnerError("LRAT chain changed before COMMIT")
        _held_artifacts_match_at(
            held, old_root=target, current_root=target,
        )
        certificate_record = _physical_record(
            target / CERTIFICATE, target, "proof-carrying-certificate",
            cap=JSON_MAX_BYTES,
        )
        commit = _final_commit_value(
            target, certificate_record, stored_certificate,
        )
        stored_commit = _publish_commit_from_quarantined_root(
            target=target,
            root_before=root_before,
            held=held,
            expected_lrat=final_lrat,
            certificate=stored_certificate,
            commit=commit,
        )
        if not json_type_equal(stored_commit, commit):
            raise ProofRunnerError("final COMMIT publication mismatch")
        return commit
    finally:
        for descriptor, _path, _role, _bound, _cap in held:
            os.close(descriptor)



def _valid_hash_record(value: Any, *, cap: int) -> bool:
    return bool(
        type(value) is dict
        and set(value) == {"bytes", "sha256"}
        and type(value.get("bytes")) is int
        and 0 <= value["bytes"] <= cap
        and is_sha256(value.get("sha256"))
    )


def _proc_fd_number(value: Any) -> int | None:
    prefix = "/proc/self/fd/"
    if type(value) is not str or not value.startswith(prefix):
        return None
    suffix = value[len(prefix):]
    if not suffix.isascii() or not suffix.isdigit():
        return None
    descriptor = int(suffix)
    return descriptor if descriptor >= 3 and suffix == str(descriptor) else None


def _validate_stored_direct_cli_context(
    value: Any, *, action: str, target: Path,
) -> None:
    fields = {
        "schema_version", "kind", "action", "runner_realpath",
        "runner_sha256", "main_file_string", "main_file_realpath",
        "argv0_string", "argv0_realpath", "python_invocation_path",
        "python_realpath", "python_flags", "normalized_argv", "checks",
        "passed", "record_sha256",
    }
    if type(value) is not dict or set(value) != fields or not selfhash_valid(value):
        raise ProofRunnerError("stored direct CLI context schema/self-hash mismatch")
    runner_path = PROJECT / RUNNER_RELATIVE_PATH
    runner = runner_path.resolve(strict=True)
    expected_flags = {
        "isolated": 1,
        "dont_write_bytecode": 1,
        "optimize": 0,
        "no_site": 0,
        "ignore_environment": 1,
        "no_user_site": 1,
        "safe_path": True,
    }
    check_names = {
        "module_is_main", "main_file_string_is_absolute_runner",
        "main_file_is_runner", "argv0_string_is_absolute_runner",
        "argv0_is_runner", "argv_is_exact", "isolated_flag_is_one",
        "dont_write_bytecode_flag_is_one", "optimize_flag_is_zero",
        "site_import_is_enabled", "environment_is_ignored",
        "safe_path_is_enabled", "science_python_invocation_exact",
        "science_python_realpath_exact", "runner_is_not_symlink",
        "root_is_normalized_absolute",
    }
    checks = value.get("checks")
    if (
        type(value.get("schema_version")) is not int
        or value["schema_version"] != SCHEMA_VERSION
        or value.get("kind") != "paper400-proof-direct-cli-context-v2"
        or value.get("action") != action
        or value.get("runner_realpath") != str(runner)
        or value.get("runner_sha256") != file_sha256(runner)
        or value.get("main_file_string") != str(runner)
        or value.get("main_file_realpath") != str(runner)
        or value.get("argv0_string") != str(runner)
        or value.get("argv0_realpath") != str(runner)
        or value.get("python_invocation_path") != str(SCIENCE_PYTHON)
        or value.get("python_realpath") != str(EXPECTED_PYTHON_REALPATH)
        or not json_type_equal(value.get("python_flags"), expected_flags)
        or not json_type_equal(
            value.get("normalized_argv"), [action, "--root", str(target)],
        )
        or type(checks) is not dict
        or set(checks) != check_names
        or any(type(item) is not bool or item is not True for item in checks.values())
        or value.get("passed") is not True
    ):
        raise ProofRunnerError("stored direct CLI context binding mismatch")


def _validate_claim_record(
    claim: Any, *, action: str, target: Path,
) -> None:
    fields = {
        "schema_version", "kind", "gate", "action", "root", "nonce_hex",
        "pid", "terminal", "record_sha256",
    }
    if type(claim) is not dict or set(claim) != fields or not selfhash_valid(claim):
        raise ProofRunnerError("stage claim schema/self-hash mismatch")
    if (
        type(claim.get("schema_version")) is not int
        or claim["schema_version"] != SCHEMA_VERSION
        or claim.get("kind") != "paper400-proof-stage-claim-v2"
        or claim.get("gate") != GATE
        or claim.get("action") != action
        or claim.get("root") != str(target)
        or not is_sha256(claim.get("nonce_hex"))
        or type(claim.get("pid")) is not int
        or claim["pid"] <= 0
        or claim.get("terminal") is not False
    ):
        raise ProofRunnerError("stage claim semantic binding mismatch")


def _validate_memfd_record(
    value: Any,
    *,
    source_path: Path,
    expected_sha256: str,
    expected_bytes: int,
    executable: bool,
) -> bool:
    expected = {
        "source_path": str(source_path),
        "sha256": expected_sha256,
        "bytes": expected_bytes,
        "executable": executable,
        "sealed_memfd": True,
        "seals": ["WRITE", "GROW", "SHRINK", "SEAL"],
    }
    return json_type_equal(value, expected)


def _validate_historical_dynamic_runtime(
    value: Any, *, source_tcb: Mapping[str, Any],
) -> bool:
    fields = {
        "schema_version", "kind", "source_tcb_record_sha256",
        "system_preload_absence", "loader_memfd", "directory",
        "library_path", "staged_objects", "loader_options",
        "host_kernel_vdso_trusted_boundary", "record_sha256",
    }
    if type(value) is not dict or set(value) != fields or not selfhash_valid(value):
        return False
    if type(source_tcb) is not dict or not selfhash_valid(source_tcb):
        return False
    if (
        type(value.get("schema_version")) is not int
        or value["schema_version"] != SCHEMA_VERSION
        or value.get("kind") != "paper400-private-dynamic-elf-runtime-v2"
        or value.get("source_tcb_record_sha256") != source_tcb.get("record_sha256")
        or not json_type_equal(
            value.get("system_preload_absence"),
            source_tcb.get("system_preload_absence"),
        )
        or not _validate_memfd_record(
            value.get("loader_memfd"),
            source_path=ELF_OBJECT_SPECS[0][1],
            expected_sha256=ELF_OBJECT_SPECS[0][4],
            expected_bytes=ELF_OBJECT_SPECS[0][3],
            executable=True,
        )
        or value.get("loader_options")
        != ["--inhibit-cache", "--library-path", "--argv0"]
        or value.get("host_kernel_vdso_trusted_boundary") is not True
        or _proc_fd_number(value.get("library_path")) is None
    ):
        return False
    directory = value.get("directory")
    if (
        type(directory) is not dict
        or set(directory) != {"device", "inode", "mode", "uid"}
        or type(directory.get("device")) is not int
        or directory["device"] < 0
        or type(directory.get("inode")) is not int
        or directory["inode"] <= 0
        or type(directory.get("mode")) is not int
        or directory["mode"] != 0o700
        or type(directory.get("uid")) is not int
        or directory["uid"] != os.geteuid()
    ):
        return False
    staged = value.get("staged_objects")
    if type(staged) is not list or len(staged) != len(ELF_OBJECT_SPECS):
        return False
    for item, spec in zip(staged, ELF_OBJECT_SPECS, strict=True):
        soname, realpath, _alias, expected_bytes, expected_sha256, _needed = spec
        if (
            type(item) is not dict
            or set(item) != {
                "soname", "source_realpath", "sha256", "bytes", "device",
                "inode", "mode", "uid",
            }
            or item.get("soname") != soname
            or item.get("source_realpath") != str(realpath)
            or item.get("sha256") != expected_sha256
            or type(item.get("bytes")) is not int
            or item["bytes"] != expected_bytes
            or type(item.get("device")) is not int
            or item["device"] < 0
            or type(item.get("inode")) is not int
            or item["inode"] <= 0
            or type(item.get("mode")) is not int
            or item["mode"] != 0o400
            or type(item.get("uid")) is not int
            or item["uid"] != os.geteuid()
        ):
            return False
    return True



def _checker_argv_roles(role: str) -> list[str]:
    tool_roles = {
        "drat-verify": [
            "sealed-drat-trim", "sealed-base-dimacs", "opened-drat-fd",
            "-t", "604800",
        ],
        "drat-to-lrat": [
            "sealed-drat-trim", "sealed-base-dimacs", "opened-drat-fd",
            "-L", "private-o_excl-lrat-fd", "-t", "604800",
        ],
        "lrat-check": [
            "sealed-lrat-check", "sealed-base-dimacs", "opened-lrat-fd",
        ],
        "final-drat-replay": [
            "sealed-drat-trim", "sealed-base-dimacs", "opened-drat-fd",
            "-t", "604800",
        ],
        "final-lrat-replay": [
            "sealed-lrat-check", "sealed-base-dimacs", "opened-lrat-fd",
        ],
    }.get(role)
    if tool_roles is None:
        raise ProofRunnerError("unexpected proof checker role")
    return [
        "sealed-loader-memfd", "--inhibit-cache", "--library-path",
        "private-runtime-dirfd", "--argv0", role,
    ] + tool_roles


def _validate_fresh_checker_binding(
    value: Any,
    *,
    role: str,
    marker: bytes,
    checker_path: Path,
    checker_sha256: str,
    checker_bytes: int,
    proof_record: Mapping[str, Any],
    proof_cap: int,
    stdout_record: Any,
    stderr_record: Any,
    stdout_payload: bytes,
    stderr_payload: bytes,
    target: Path,
    source_tcb: Mapping[str, Any],
) -> None:
    fields = {
        "schema_version", "kind", "role", "invocation", "process",
        "semantic_marker", "semantic_marker_count",
        "semantic_marker_sha256", "stderr_empty", "verified",
        "record_sha256",
    }
    if type(value) is not dict or set(value) != fields or not selfhash_valid(value):
        raise ProofRunnerError("fresh checker result schema/self-hash mismatch")
    invocation = value.get("invocation")
    invocation_fields = {
        "schema_version", "kind", "role", "checker", "dynamic_runtime",
        "base", "proof_input", "argv_roles", "actual_argv_sha256",
        "timeout_s", "stdout_cap_bytes", "stderr_cap_bytes", "output_role",
        "environment", "record_sha256",
    }
    if (
        type(invocation) is not dict
        or set(invocation) != invocation_fields
        or not selfhash_valid(invocation)
        or type(invocation.get("schema_version")) is not int
        or invocation["schema_version"] != SCHEMA_VERSION
        or invocation.get("kind") != "paper400-proof-checker-invocation-v2"
        or invocation.get("role") != role
        or not _validate_memfd_record(
            invocation.get("checker"), source_path=checker_path,
            expected_sha256=checker_sha256, expected_bytes=checker_bytes,
            executable=True,
        )
        or not _validate_memfd_record(
            invocation.get("base"), source_path=target / STATIC_DIMACS,
            expected_sha256=EXPECTED_BASE_DIMACS_SHA256,
            expected_bytes=EXPECTED_BASE_DIMACS_BYTES, executable=False,
        )
        or not json_type_equal(
            invocation.get("proof_input"), _artifact_reference(proof_record),
        )
        or not json_type_equal(invocation.get("argv_roles"), _checker_argv_roles(role))
        or type(invocation.get("timeout_s")) is not int
        or invocation["timeout_s"] != CHECKER_TIMEOUT_S
        or type(invocation.get("stdout_cap_bytes")) is not int
        or invocation["stdout_cap_bytes"] != CHECKER_LOG_MAX_BYTES
        or type(invocation.get("stderr_cap_bytes")) is not int
        or invocation["stderr_cap_bytes"] != CHECKER_LOG_MAX_BYTES
        or invocation.get("output_role") is not None
        or not json_type_equal(invocation.get("environment"), _clean_env())
        or not _validate_historical_dynamic_runtime(
            invocation.get("dynamic_runtime"), source_tcb=source_tcb,
        )
    ):
        raise ProofRunnerError("fresh checker invocation binding mismatch")
    process = value.get("process")
    if not _validate_process_record(process):
        raise ProofRunnerError("fresh checker process schema mismatch")
    argv = process["argv"]
    dynamic_runtime = invocation["dynamic_runtime"]
    descriptor_numbers = [
        _proc_fd_number(argv[index]) for index in (0, 3, 6, 7, 8)
    ]
    expected_tail = (
        ["-t", str(CHECKER_TIMEOUT_S)]
        if role == "final-drat-replay" else []
    )
    if (
        len(argv) != (11 if role == "final-drat-replay" else 9)
        or any(number is None for number in descriptor_numbers)
        or len(set(descriptor_numbers)) != len(descriptor_numbers)
        or _proc_fd_number(argv[0]) is None
        or argv[1:3] != ["--inhibit-cache", "--library-path"]
        or argv[3] != dynamic_runtime["library_path"]
        or argv[4:6] != ["--argv0", role]
        or _proc_fd_number(argv[6]) is None
        or _proc_fd_number(argv[7]) is None
        or _proc_fd_number(argv[8]) is None
        or argv[9:] != expected_tail
        or invocation.get("actual_argv_sha256") != canonical_sha256(argv)
        or process.get("cwd") != str(target)
        or not json_type_equal(process.get("environment"), _clean_env())
        or process.get("timeout_s") != CHECKER_TIMEOUT_S
        or process.get("stdout_cap_bytes") != CHECKER_LOG_MAX_BYTES
        or process.get("stderr_cap_bytes") != CHECKER_LOG_MAX_BYTES
        or process.get("file_size_cap_bytes") != proof_cap
        or not _process_clean(process, rc=0)
    ):
        raise ProofRunnerError("fresh checker process/invocation mismatch")
    if (
        not _valid_hash_record(stdout_record, cap=CHECKER_LOG_MAX_BYTES)
        or type(stdout_payload) is not bytes
        or type(stderr_payload) is not bytes
        or not json_type_equal(stdout_record, _hash_record(stdout_payload))
        or not json_type_equal(stderr_record, _hash_record(stderr_payload))
        or _checker_terminal_lines(stdout_payload, marker) != [marker]
        or stderr_payload != b""
        or not _valid_hash_record(stderr_record, cap=CHECKER_LOG_MAX_BYTES)
        or not json_type_equal(process.get("stdout"), stdout_record)
        or not json_type_equal(process.get("stderr"), stderr_record)
        or not json_type_equal(stderr_record, _hash_record(b""))
        or type(value.get("schema_version")) is not int
        or value.get("schema_version") != SCHEMA_VERSION
        or value.get("kind") != "paper400-proof-checker-result-v2"
        or value.get("role") != role
        or value.get("semantic_marker") != marker.decode("ascii")
        or type(value.get("semantic_marker_count")) is not int
        or value["semantic_marker_count"]
        != _semantic_marker_count(stdout_payload, marker)
        or value["semantic_marker_count"] != 1
        or value.get("semantic_marker_sha256")
        != hashlib.sha256(marker + b"\n").hexdigest()
        or value.get("stderr_empty") is not True
        or value.get("verified")
        is not _checker_success(
            process, stdout_payload, stderr_payload, marker=marker,
        )
        or value.get("verified") is not True
    ):
        raise ProofRunnerError("fresh checker semantic/log binding mismatch")



def _decode_canonical_base64(value: Any, *, cap: int) -> bytes:
    if type(value) is not str or len(value) > 4 * ((cap + 2) // 3):
        raise ProofRunnerError("embedded checker output base64 is invalid/oversized")
    try:
        payload = base64.b64decode(value.encode("ascii"), validate=True)
    except (UnicodeEncodeError, ValueError) as exc:
        raise ProofRunnerError("embedded checker output base64 is invalid") from exc
    if len(payload) > cap or base64.b64encode(payload).decode("ascii") != value:
        raise ProofRunnerError("embedded checker output base64 is noncanonical/oversized")
    return payload


def _validate_fresh_replay_record(
    fresh: Any, *, target: Path, lrat_validation: Mapping[str, Any],
) -> None:
    fields = {
        "schema_version", "kind", "scientific_instance_binding_equal",
        "source_binding_equal", "toolchain_binding_equal",
        "base_dimacs_byte_equal", "old_v13_preflight_byte_equal",
        "base_dimacs_sha256", "bound_drat", "bound_lrat", "drat_checker",
        "drat_stdout", "drat_stdout_base64", "drat_stderr",
        "drat_stderr_base64", "lrat_checker", "lrat_stdout",
        "lrat_stdout_base64", "lrat_stderr", "lrat_stderr_base64",
        "all_fresh_replay_passed", "solver_invoked", "record_sha256",
    }
    if type(fresh) is not dict or set(fresh) != fields or not selfhash_valid(fresh):
        raise ProofRunnerError("certificate fresh replay schema/self-hash mismatch")
    drat_artifact = lrat_validation["drat"]["raw"]["proof"]
    lrat_artifact = lrat_validation["lrat"]["lrat_artifact"]
    static_summary = lrat_validation["drat"]["raw"]["static"]["manifest"][
        "preflight_summary"
    ]
    source_tcb = static_summary["toolchain_binding"]["dynamic_elf_tcb"]
    if (
        type(fresh.get("schema_version")) is not int
        or fresh["schema_version"] != SCHEMA_VERSION
        or fresh.get("kind") != "paper400-dic5-fresh-final-replay-v2"
        or any(
            fresh.get(name) is not True
            for name in (
                "scientific_instance_binding_equal", "source_binding_equal",
                "toolchain_binding_equal", "base_dimacs_byte_equal",
                "old_v13_preflight_byte_equal", "all_fresh_replay_passed",
            )
        )
        or fresh.get("solver_invoked") is not False
        or fresh.get("base_dimacs_sha256") != EXPECTED_BASE_DIMACS_SHA256
        or not json_type_equal(fresh.get("bound_drat"), drat_artifact)
        or not json_type_equal(fresh.get("bound_lrat"), lrat_artifact)
    ):
        raise ProofRunnerError("certificate fresh replay common binding mismatch")
    drat_stdout = _decode_canonical_base64(
        fresh.get("drat_stdout_base64"), cap=CHECKER_LOG_MAX_BYTES,
    )
    drat_stderr = _decode_canonical_base64(
        fresh.get("drat_stderr_base64"), cap=CHECKER_LOG_MAX_BYTES,
    )
    lrat_stdout = _decode_canonical_base64(
        fresh.get("lrat_stdout_base64"), cap=CHECKER_LOG_MAX_BYTES,
    )
    lrat_stderr = _decode_canonical_base64(
        fresh.get("lrat_stderr_base64"), cap=CHECKER_LOG_MAX_BYTES,
    )
    _validate_fresh_checker_binding(
        fresh.get("drat_checker"), role="final-drat-replay",
        marker=b"s VERIFIED", checker_path=DRAT_TRIM_PATH,
        checker_sha256=EXPECTED_DRAT_TRIM_SHA256,
        checker_bytes=EXPECTED_DRAT_TRIM_BYTES, proof_record=drat_artifact,
        proof_cap=PROOF_MAX_BYTES, stdout_record=fresh.get("drat_stdout"),
        stderr_record=fresh.get("drat_stderr"), stdout_payload=drat_stdout,
        stderr_payload=drat_stderr, target=target, source_tcb=source_tcb,
    )
    _validate_fresh_checker_binding(
        fresh.get("lrat_checker"), role="final-lrat-replay",
        marker=b"c VERIFIED", checker_path=LRAT_CHECK_PATH,
        checker_sha256=EXPECTED_LRAT_CHECK_SHA256,
        checker_bytes=EXPECTED_LRAT_CHECK_BYTES, proof_record=lrat_artifact,
        proof_cap=LRAT_MAX_BYTES, stdout_record=fresh.get("lrat_stdout"),
        stderr_record=fresh.get("lrat_stderr"), stdout_payload=lrat_stdout,
        stderr_payload=lrat_stderr, target=target, source_tcb=source_tcb,
    )


def _validate_resource_snapshot(value: Any) -> bool:
    fields = {
        "memory_current", "memory_max", "memory_stat", "memory_events",
        "memory_pressure", "filesystem_device", "filesystem_block_size",
        "filesystem_bavail_blocks", "filesystem_bavail_bytes",
    }
    if type(value) is not dict or set(value) != fields:
        return False
    if (
        type(value.get("memory_current")) is not int
        or value["memory_current"] < 0
        or not (
            value.get("memory_max") is None
            or type(value.get("memory_max")) is int
            and value["memory_max"] > 0
        )
    ):
        return False
    for name in ("memory_stat", "memory_events"):
        item = value.get(name)
        if (
            type(item) is not dict
            or any(type(key) is not str for key in item)
            or any(type(number) is not int or number < 0 for number in item.values())
        ):
            return False
    pressure = value.get("memory_pressure")
    if not _validate_memory_pressure(pressure):
        return False
    for name in (
        "filesystem_device", "filesystem_block_size",
        "filesystem_bavail_blocks", "filesystem_bavail_bytes",
    ):
        if type(value.get(name)) is not int or value[name] < 0:
            return False
    return True


def _validate_certificate_semantics(
    certificate: Any,
    target: Path,
    lrat_validation: Mapping[str, Any],
) -> None:
    fields = {
        "schema_version", "kind", "gate", "state", "authority", "test_only",
        "production_eligible", "root", "root_identity",
        "direct_cli_context", "predecessor", "claim", "claim_artifact",
        "chain", "resource_gate_before", "resource_snapshot_after",
        "oom_event_delta", "fresh_replay", "scientific_binding", "code",
        "fom_lower", "strict_threshold", "integer_cross_product",
        "excluded_operator_weights", "proofs", "claim_semantics",
        "publication_certificate", "upload_authorized", "record_sha256",
    }
    if type(certificate) is not dict or set(certificate) != fields or not selfhash_valid(certificate):
        raise ProofRunnerError("certificate schema/self-hash mismatch")
    if (
        type(certificate.get("schema_version")) is not int
        or certificate["schema_version"] != SCHEMA_VERSION
        or certificate.get("kind")
        != "paper400-dic5-proof-carrying-lower-certificate-v2"
        or certificate.get("gate") != GATE
        or lrat_validation.get("state") != "LRAT_VERIFIED"
        or lrat_validation.get("verified") is not True
    ):
        raise ProofRunnerError("certificate envelope/predecessor state mismatch")
    expected_code = {
        "n": 400,
        "k": 16,
        "max_stabilizer_check_row_weight": 6,
        "distance_lower_bound": 20,
        "distance_exact": None,
        "paper_unverified_upper_bound": 22,
    }
    expected_fom = {
        "definition": "k*d_lower^2/n",
        "numerator": 16,
        "denominator": 1,
    }
    expected_threshold = {"numerator": 61, "denominator": 4}
    expected_cross = {
        "lhs_4_k_d_lower_squared": 25_600,
        "rhs_61_n": 24_400,
        "strict": True,
    }
    expected_exclusion = {
        "cnf_max_weight": 18,
        "all_logicals_even": True,
        "parity_lift_excludes_weight_19": True,
        "both_X_and_Z_covered_by_isometry": True,
    }
    expected_claim = {
        "distance_claim": "d>=20",
        "fom_claim": "FOM>=16>61/4",
        "exact_distance_claimed": False,
        "paper_upper_bound_used_as_exact": False,
    }
    if (
        certificate.get("state") != "PROOF_CARRYING_LOWER_20"
        or certificate.get("authority") != AUTHORITY_PRODUCTION
        or certificate.get("test_only") is not False
        or certificate.get("production_eligible") is not True
        or certificate.get("root") != str(target)
        or not json_type_equal(certificate.get("root_identity"), _root_identity(target))
        or not json_type_equal(certificate.get("predecessor"), _predecessor(target, LRAT_COMMIT))
        or not json_type_equal(certificate.get("code"), expected_code)
        or not json_type_equal(certificate.get("fom_lower"), expected_fom)
        or not json_type_equal(certificate.get("strict_threshold"), expected_threshold)
        or not json_type_equal(certificate.get("integer_cross_product"), expected_cross)
        or not json_type_equal(certificate.get("excluded_operator_weights"), expected_exclusion)
        or not json_type_equal(certificate.get("claim_semantics"), expected_claim)
        or certificate.get("publication_certificate") is not True
        or certificate.get("upload_authorized") is not False
    ):
        raise ProofRunnerError("certificate scientific/authority truth table mismatch")
    _validate_stored_direct_cli_context(
        certificate.get("direct_cli_context"), action="finalize", target=target,
    )
    stored_claim = _strict_json(target / FINALIZE_CLAIM)
    _validate_claim_record(stored_claim, action="finalize", target=target)
    expected_claim_artifact = _physical_record(
        target / FINALIZE_CLAIM, target, "finalize-claim", cap=JSON_MAX_BYTES,
    )
    if (
        not json_type_equal(certificate.get("claim"), stored_claim)
        or not json_type_equal(
            certificate.get("claim_artifact"), expected_claim_artifact,
        )
    ):
        raise ProofRunnerError("certificate finalize claim binding mismatch")
    expected_chain = [
        _chain_reference(target, STATIC_COMMIT),
        _chain_reference(target, RAW_COMMIT),
        _chain_reference(target, DRAT_COMMIT),
        _chain_reference(target, LRAT_COMMIT),
    ]
    if not json_type_equal(certificate.get("chain"), expected_chain):
        raise ProofRunnerError("certificate chain mismatch")
    science = lrat_validation["drat"]["raw"]["static"]["scientific_binding"]
    if not json_type_equal(certificate.get("scientific_binding"), science):
        raise ProofRunnerError("certificate scientific predecessor mismatch")
    drat_artifact = lrat_validation["drat"]["raw"]["proof"]
    lrat_artifact = lrat_validation["lrat"]["lrat_artifact"]
    expected_proofs = {
        "base_dimacs": _artifact_reference(
            lrat_validation["drat"]["raw"]["static"]["base_record"],
        ),
        "binary_drat": _artifact_reference(drat_artifact),
        "converted_lrat": _artifact_reference(lrat_artifact),
        "drat_independently_verified": True,
        "lrat_independently_verified": True,
        "trusted_policy_sha256": EXPECTED_POLICY_CANONICAL_SHA256,
    }
    if not json_type_equal(certificate.get("proofs"), expected_proofs):
        raise ProofRunnerError("certificate proof artifact binding mismatch")
    _validate_fresh_replay_record(
        certificate.get("fresh_replay"), target=target,
        lrat_validation=lrat_validation,
    )
    expected_delta = _oom_delta(
        certificate["resource_gate_before"], certificate["resource_snapshot_after"],
    )
    if (
        not _validate_resource_record(
            certificate.get("resource_gate_before"), required_cap=0,
        )
        or not _validate_resource_snapshot(certificate.get("resource_snapshot_after"))
        or not json_type_equal(certificate.get("oom_event_delta"), expected_delta)
        or any(type(value) is not int or value != 0 for value in expected_delta.values())
    ):
        raise ProofRunnerError("certificate resource/OOM binding mismatch")


def _expected_final_tree() -> tuple[set[str], set[str]]:
    directories = {"static", "state", "artifacts", "logs"}
    files = {
        STATIC_MANIFEST.as_posix(), STATIC_PREFLIGHT.as_posix(),
        STATIC_DIMACS.as_posix(), STATIC_COMMIT.as_posix(),
        SOLVE_CLAIM.as_posix(), RAW_COMMIT.as_posix(),
        VERIFY_CLAIM.as_posix(), DRAT_COMMIT.as_posix(),
        LRAT_COMMIT.as_posix(), FINALIZE_CLAIM.as_posix(),
        DRAT_ARTIFACT.as_posix(), LRAT_ARTIFACT.as_posix(),
        "logs/solver.stdout", "logs/solver.stderr",
        "logs/drat-verify.stdout", "logs/drat-verify.stderr",
        "logs/drat-to-lrat.stdout", "logs/drat-to-lrat.stderr",
        "logs/lrat-check.stdout", "logs/lrat-check.stderr",
        CERTIFICATE.as_posix(), FINAL_COMMIT.as_posix(),
    }
    return directories, files


def _closed_tree_failures(
    target: Path, *, phase: str,
) -> list[str]:
    expected_directories, expected_files = _expected_final_tree()
    if phase == "before-certificate":
        expected_files -= {CERTIFICATE.as_posix(), FINAL_COMMIT.as_posix()}
    elif phase == "before-commit":
        expected_files -= {FINAL_COMMIT.as_posix()}
    elif phase != "final":
        raise ProofRunnerError("unknown closed-tree validation phase")
    actual_directories: set[str] = set()
    actual_files: set[str] = set()
    failures: list[str] = []
    try:
        _root_identity(target)
    except ProofRunnerError as exc:
        failures.append(str(exc))
    for entry in target.rglob("*"):
        relative = entry.relative_to(target).as_posix()
        lexical = os.stat(entry, follow_symlinks=False)
        if stat.S_ISLNK(lexical.st_mode):
            failures.append(f"symlink in tree: {relative}")
        elif stat.S_ISDIR(lexical.st_mode):
            actual_directories.add(relative)
            if (
                stat.S_IMODE(lexical.st_mode) != 0o700
                or lexical.st_uid != os.geteuid()
            ):
                failures.append(f"non-0700/unowned directory: {relative}")
        elif stat.S_ISREG(lexical.st_mode):
            actual_files.add(relative)
            if (
                stat.S_IMODE(lexical.st_mode) != 0o600
                or lexical.st_uid != os.geteuid()
            ):
                failures.append(f"non-0600/unowned artifact: {relative}")
        else:
            failures.append(f"non-regular tree entry: {relative}")
    if actual_directories != expected_directories:
        failures.append("directory set mismatch")
    if actual_files != expected_files:
        failures.append(f"{phase} file set mismatch")
    return failures


def _closed_final_tree_failures(target: Path) -> list[str]:
    return _closed_tree_failures(target, phase="final")


def validate_final_root(
    root: Path,
    *,
    execute_fresh_replay: bool,
    _production_nonce: object | None = None,
) -> dict[str, Any]:
    target = _validate_root_argument(Path(root), must_exist=True)
    context = (
        _require_production_cli("validate", target, _production_nonce)
        if _production_nonce is not None else None
    )
    failures = _closed_final_tree_failures(target)
    certificate: dict[str, Any] = {}
    commit: dict[str, Any] = {}
    try:
        lrat = _validate_lrat(target, fresh_source_and_tools=True)
        if lrat["state"] != "LRAT_VERIFIED":
            failures.append("final predecessor is not LRAT_VERIFIED")
        certificate = _strict_json(target / CERTIFICATE)
        _validate_certificate_semantics(certificate, target, lrat)
        certificate_record = _physical_record(
            target / CERTIFICATE, target, "proof-carrying-certificate",
            cap=JSON_MAX_BYTES,
        )
        commit = _strict_json(target / FINAL_COMMIT)
        expected_commit = _final_commit_value(target, certificate_record, certificate)
        if not json_type_equal(commit, expected_commit):
            failures.append("final COMMIT fresh reconstruction mismatch")
        if execute_fresh_replay:
            resource = _resource_gate(target, output_cap=0)
            fresh = _fresh_replay(target, lrat)
            after = _instant_resource(target)
            if any(value != 0 for value in _oom_delta(resource, after).values()):
                failures.append("OOM event during independent validation replay")
            if fresh.get("all_fresh_replay_passed") is not True:
                failures.append("independent validation replay failed")
    except (OSError, KeyError, TypeError, ValueError, RuntimeError) as exc:
        failures.append(f"{type(exc).__name__}: {exc}")
    structurally_valid = not failures
    authority_valid = bool(
        _production_nonce is _PRODUCTION_CLI_NONCE
        and execute_fresh_replay is True
        and type(context) is dict
        and context.get("passed") is True
    )
    if structurally_valid and not authority_valid:
        failures.append(
            "authoritative validation requires direct production CLI and fresh replay"
        )
    valid = structurally_valid and authority_valid and not failures
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-proof-carrying-validation-v2",
        "gate": GATE,
        "root": str(target),
        "direct_cli_context": context,
        "structurally_valid": structurally_valid,
        "authority_valid": authority_valid,
        "valid": valid,
        "state": (
            "PROOF_CARRYING_LOWER_20" if valid else "UNRESOLVED"
        ),
        "authoritative_distance_lower_bound": 20 if valid else None,
        "distance_exact": None,
        "fom_lower_numerator": 16 if valid else None,
        "fom_lower_denominator": 1 if valid else None,
        "strictly_exceeds_61_over_4": valid,
        "certificate_record_sha256": certificate.get("record_sha256"),
        "final_commit_record_sha256": commit.get("record_sha256"),
        "fresh_replay_executed": execute_fresh_replay is True,
        "solver_invoked": False,
        "publication_certificate": valid,
        "upload_authorized": False,
        "failures": failures,
    })

def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    subparsers = parser.add_subparsers(dest="action", required=True)
    subparsers.add_parser(
        "preflight", help="fresh zero-solver source/tool/base replay",
        allow_abbrev=False,
    )
    for action, help_text in (
        ("prepare", "create one new STATIC_SEALED root"),
        ("solve", "run one standalone base-CNF solve"),
        ("verify", "verify DRAT, convert to LRAT, and verify LRAT"),
        ("finalize", "fresh-replay and commit the lower-bound certificate"),
        ("validate", "read-only fresh replay of a committed certificate"),
    ):
        child = subparsers.add_parser(
            action, help=help_text, allow_abbrev=False,
        )
        child.add_argument("--root", required=True, type=Path)
    return parser


def _terminate_by_forwarded_signal(signum: int) -> None:
    if type(signum) is not int or signum not in FORWARDED_PARENT_SIGNALS:
        os._exit(1)
    signal.signal(signum, signal.SIG_DFL)
    if hasattr(signal, "pthread_sigmask"):
        signal.pthread_sigmask(signal.SIG_UNBLOCK, {signum})
    os.kill(os.getpid(), signum)
    os._exit(128 + signum)


def main(argv: Sequence[str] | None = None) -> int:
    effective = list(sys.argv[1:] if argv is None else argv)
    if effective == ["__prepare_builder"]:
        return _builder_helper()
    if (
        len(effective) == 3
        and effective[:2] == ["__sat_replay", "--model-fd"]
    ):
        try:
            model_fd = int(effective[2])
        except ValueError as exc:
            raise ProofRunnerError("internal SAT replay fd is not an integer") from exc
        return _sat_replay_helper(model_fd)
    args = build_parser().parse_args(effective)
    if args.action == "preflight":
        result = preflight_only(_production_nonce=_PRODUCTION_CLI_NONCE)
    elif args.action == "prepare":
        result = prepare_root(
            args.root, _production_nonce=_PRODUCTION_CLI_NONCE,
        )
    elif args.action == "solve":
        result = solve_root(
            args.root, _production_nonce=_PRODUCTION_CLI_NONCE,
        )
    elif args.action == "verify":
        result = verify_root(
            args.root, _production_nonce=_PRODUCTION_CLI_NONCE,
        )
    elif args.action == "finalize":
        result = finalize_root(
            args.root, _production_nonce=_PRODUCTION_CLI_NONCE,
        )
    elif args.action == "validate":
        result = validate_final_root(
            args.root,
            execute_fresh_replay=True,
            _production_nonce=_PRODUCTION_CLI_NONCE,
        )
    else:
        raise ProofRunnerError("unreachable action")
    sys.stdout.buffer.write(canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    if args.action == "validate":
        return 0 if result.get("valid") is True else 2
    if args.action == "solve":
        return 0 if result.get("state") in {"RAW_SAT", "RAW_UNSAT"} else 2
    if args.action == "verify":
        return 0 if result.get("state") == "LRAT_VERIFIED" else 2
    return 0


if __name__ == "__main__":
    try:
        _exit_code = main()
    except _ForwardedParentSignal as _forwarded:
        _terminate_by_forwarded_signal(_forwarded.signum)
    raise SystemExit(_exit_code)
