#!/usr/bin/env python3
"""Proof-producing DMTCP runner for an authenticated adaptive cover.

The adaptive overlay and serialized switch evidence are not launch authority.
``prepare`` only admits immutable candidate material after fresh width-10 and
overlay replay plus a non-authoritative structural switch-record check.  A
strict first launch is possible only inside one switch-v4 atomic lease that
binds and first-starts the complete eight-descendant cover while keeping at
most four solvers live.  The atomic handoff is intentionally one-shot, even
after rollback.  DMTCP checkpoints remain transport-only records.  A descendant
UNSAT claim is created only after a dead, writer-free solver has emitted an
UNSAT stdout marker and its complete DRAT has passed DRAT verification,
DRAT-to-LRAT conversion, LRAT checking, and fresh replay of both proof formats.

Within one CLI invocation, v5 may reuse only pure campaign, overlay, and switch
structure replay results.  The capability remains process/thread-local, is
revalidated at every use, never enters a lease or serialized record, and is
revoked before the CLI returns.

This v5 runner is TEST_ONLY.  It is a replaceable solver-transport component;
neither an overlay nor a checkpoint is a scientific certificate.
"""

from __future__ import annotations

import argparse
import contextlib
import fcntl
import hashlib
import importlib
import json
import math
import os
import re
import resource
import stat
import subprocess
import sys
import sysconfig
import tempfile
import threading
import time
import types
import uuid
from collections.abc import Callable, Iterator, Mapping, Sequence
from pathlib import Path
from typing import Any


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

_CONTROLLER_SOURCE = PROJECT / "scripts/run_cadical_dmtcp_resume_v1.py"
_CONTROLLER_SOURCE_SHA256 = (
    "a71cb71e61061d7f925ccc04eb1ccaf48c00289d897b957394dfc8b730062505"
)
_SWITCH_V2_RELATIVE = Path(
    "scripts/paper400_dic5_adaptive_switch_evidence_v2.py"
)
_SWITCH_V4_RELATIVE = Path(
    "scripts/paper400_dic5_adaptive_switch_evidence_v4.py"
)
_SWITCH_V2_SOURCE = PROJECT / _SWITCH_V2_RELATIVE
_SWITCH_V4_SOURCE = PROJECT / _SWITCH_V4_RELATIVE
_SWITCH_V2_SOURCE_SHA256 = (
    "f4f6b7fbed84f5daf5a98a48d33b73299b3fd135ff92b3119b6fe1e241225da2"
)
_SWITCH_V4_SOURCE_SHA256 = (
    "a0d48a371fd535d00af62e2e406f313ce900a87f2cad07a50566ee01f0e2aac0"
)

_STRICT_VENV = Path(
    "/root/qcode-stage3-distqldpc-lower-v1/qcode-discovery/.venv"
)
_STRICT_PYTHON = _STRICT_VENV / "bin/python"
_STRICT_PYTHON_RESOLVED = Path("/usr/bin/python3.12")
_STRICT_PYTHON_SHA256 = (
    "1643dacd9feaedc58f3cc581e4d22577dfe25c09b10282936186ccf0f2e61118"
)
_STRICT_PYVENV_CFG = _STRICT_VENV / "pyvenv.cfg"
_STRICT_PYVENV_CFG_SHA256 = (
    "2b2b27a6515458a7785ae373b997223335651373c59ee5d0710bbc0c4191d436"
)
_STRICT_DEPENDENCY_ROOT = Path(
    "/root/qcode-stage3-distqldpc-lower-v1/qcode-discovery/.venv/"
    "lib/python3.12/site-packages"
)
# Calibrated by the no-follow streaming scanner below.  This is an execution
# pin, not a packaging-version approximation.
_STRICT_DEPENDENCY_EXPECTED_FILES = 13320
_STRICT_DEPENDENCY_EXPECTED_DIRECTORIES = 1387
_STRICT_DEPENDENCY_EXPECTED_SYMLINKS = 0
_STRICT_DEPENDENCY_EXPECTED_BYTES = 792451106
_STRICT_DEPENDENCY_EXPECTED_SHA256 = (
    "16f5f2904490d104904c7e656ea784266dfc21d6dcebff8d433376397edb0f33"
)
_STRICT_DEPENDENCY_EXPECTED_NUMBA_CACHE_FILES = 8
_STRICT_DEPENDENCY_EXPECTED_NUMBA_CACHE_BYTES = 127448
_STRICT_DEPENDENCY_EXPECTED_NUMBA_CACHE_SHA256 = (
    "ae570cd9238f196d9ad3a8c44f8e8c277ee94d8a4f75cdfd11dba29006214d43"
)
_STRICT_STDLIB_ROOT = Path("/usr/lib/python3.12")
_STRICT_PYTHON_ZIP = Path("/usr/lib/python312.zip")
_STRICT_STDLIB_EXPECTED_FILES = 1206
_STRICT_STDLIB_EXPECTED_DIRECTORIES = 91
_STRICT_STDLIB_EXPECTED_SYMLINKS = 3
_STRICT_STDLIB_EXPECTED_BYTES = 53230614
_STRICT_STDLIB_EXPECTED_SHA256 = (
    "ae16733e812b06f2f298c196dd017fe60bcdaeedba3920a1cf490f3ebac1fc74"
)
_STRICT_STDLIB_EXPECTED_SYMLINK_RECORDS = (
    ("_sysconfigdata__linux_x86_64-linux-gnu.py",
     "_sysconfigdata__x86_64-linux-gnu.py"),
    ("config-3.12-x86_64-linux-gnu/libpython3.12.so",
     "../../x86_64-linux-gnu/libpython3.12.so.1"),
    ("sitecustomize.py", "/etc/python3.12/sitecustomize.py"),
)
_STRICT_STDLIB_EXTERNAL_TARGETS = (
    Path("/etc/python3.12/sitecustomize.py"),
    Path("/usr/lib/x86_64-linux-gnu/libpython3.12.so.1.0"),
)
_STRICT_STDLIB_EXTERNAL_EXPECTED_FILES = 2
_STRICT_STDLIB_EXTERNAL_EXPECTED_BYTES = 9061155
_STRICT_STDLIB_EXTERNAL_EXPECTED_SHA256 = (
    "defd1fa2a69edd12c6854ce344db5f3bab8c6df11387727a0f4ad936630ebc6e"
)
_STRICT_SYSTEM_MAP_EXPECTED_RECORDS = (
    (
        "/usr/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2", 236616,
        "cd4df4f3c7b83673d61189bf2eaebd33ca4f2853ab9772b8a25e025ef99b1e81",
        0, 0o755, 1,
    ),
    (
        "/usr/lib/x86_64-linux-gnu/libbz2.so.1.0.4", 78944,
        "218c4abdabce31161f3c2778762986d1fe06633705c7eb004a740946a5ccdfff",
        0, 0o644, 1,
    ),
    (
        "/usr/lib/x86_64-linux-gnu/libc.so.6", 2125328,
        "8db37cf3f2169f59a0f07ef1fea308c35656668c64c8ff294e1860f4121eb161",
        0, 0o755, 1,
    ),
    (
        "/usr/lib/x86_64-linux-gnu/libcrypto.so.3", 5309400,
        "1451aceec262c3338052fa77542eb971d4ba311c6bf12d9aa70d0b56aca942f9",
        0, 0o644, 1,
    ),
    (
        "/usr/lib/x86_64-linux-gnu/libdl.so.2", 14408,
        "292d5f5af2e7360b3e18c56591a4960115373ecf40627660f9149b6c68a33f80",
        0, 0o644, 1,
    ),
    (
        "/usr/lib/x86_64-linux-gnu/libexpat.so.1.9.1", 174336,
        "c42ff317838b4b4639e2ea801905f0317177c6df7e31b2f0d0240e3c3ac0cfde",
        0, 0o644, 1,
    ),
    (
        "/usr/lib/x86_64-linux-gnu/libffi.so.8.1.4", 47672,
        "00f593fe192f2851b8ce23b25cec2488d769beb5a8f63e8c9e563071e1075153",
        0, 0o644, 1,
    ),
    (
        "/usr/lib/x86_64-linux-gnu/libgcc_s.so.1", 183024,
        "d93224d2b0dab4247598be683adca02f5cf00586f99c187579cd7e92058fb7cb",
        0, 0o644, 1,
    ),
    (
        "/usr/lib/x86_64-linux-gnu/libgomp.so.1.0.0", 352304,
        "135f3c8f006d2fe5e68e51281c7974cb991a03de3bfb3593d68d174dfcf854d1",
        0, 0o644, 1,
    ),
    (
        "/usr/lib/x86_64-linux-gnu/liblzma.so.5.4.5", 202904,
        "696e868dd0700a19a6d65fc01608ec2d70d3cb91f65710e89180cd2e688f30cb",
        0, 0o644, 1,
    ),
    (
        "/usr/lib/x86_64-linux-gnu/libm.so.6", 952616,
        "e9c4b28d340e415b8137480ec442662f981e1399386c5931dae0e886e3639e91",
        0, 0o644, 1,
    ),
    (
        "/usr/lib/x86_64-linux-gnu/libpthread.so.0", 14408,
        "a27ffa9bf233d61a5f02ddb0cf770dd6579021afc1aa8aec0fb58ee4a965281a",
        0, 0o644, 1,
    ),
    (
        "/usr/lib/x86_64-linux-gnu/librt.so.1", 14624,
        "c6e6288545e24b0b3cfbf33320bda9236521625d8c3d628f3444f1ed40e5c7c5",
        0, 0o644, 1,
    ),
    (
        "/usr/lib/x86_64-linux-gnu/libsqlite3.so.0.8.6", 1468440,
        "f2cd05de8b6f71ea9d0495a6f9ff9cae844b15d9c45b7ef49ee0af0f81658cc7",
        0, 0o644, 1,
    ),
    (
        "/usr/lib/x86_64-linux-gnu/libssl.so.3", 696512,
        "55869549f4c7d7221e311121696f135390a7172755459ad04aef831f855eb214",
        0, 0o644, 1,
    ),
    (
        "/usr/lib/x86_64-linux-gnu/libstdc++.so.6.0.33", 2592224,
        "1fd75fe70354a416d75aef22bcae68c47bd25d20e2d0568c30b1a9838cf62f11",
        0, 0o644, 1,
    ),
    (
        "/usr/lib/x86_64-linux-gnu/libz.so.1.3", 113000,
        "9b64150b28505a33d6bc3ecf709c279f6de97a1c184dbda65d06ee4537f6d286",
        0, 0o644, 1,
    ),
)
_STRICT_SYSTEM_MAP_EXPECTED_FILES = 17
_STRICT_SYSTEM_MAP_EXPECTED_BYTES = 14576760
_STRICT_SYSTEM_MAP_EXPECTED_SHA256 = (
    "8f635d72d68f1dcd88cf0c9a9a019b8cb0ff65e0bf1e4379a8ec4e3cf1935d49"
)
_STRICT_ENTRY_ENVIRONMENT = (
    ("LANG", "C"), ("LC_ALL", "C"), ("TZ", "UTC"),
)
_STRICT_JIT_EXEC_EXPECTED_PERMISSION_CLASS_COUNT = 2
_STRICT_JIT_EXEC_EXPECTED_BYTES = 90112
_STRICT_JIT_EXEC_EXPECTED_PERMISSIONS = ("r-xp", "rwxp")
_STRICT_FORBIDDEN_ENV_PREFIXES = (
    "NUMBA_", "OMP_", "OPENBLAS_", "MKL_", "BLIS_", "GOTO_",
    "NUMEXPR_", "VECLIB_",
)
_STRICT_DERIVED_THREAD_ENV = (
    ("OMP_NUM_THREADS", "1"),
    ("OMP_THREAD_LIMIT", "1"),
    ("OPENBLAS_NUM_THREADS", "1"),
    ("MKL_NUM_THREADS", "1"),
    ("NUMEXPR_NUM_THREADS", "1"),
    ("VECLIB_MAXIMUM_THREADS", "1"),
    ("BLIS_NUM_THREADS", "1"),
    ("NUMBA_NUM_THREADS", "1"),
    ("GOTO_NUM_THREADS", "1"),
)
_STRICT_DERIVED_ENV_WRITER_MODULE = (
    "scripts.run_paper400_dic5_w6_lower_final_v5"
)
_STRICT_DERIVED_ENV_WRITER = PROJECT / (
    "scripts/run_paper400_dic5_w6_lower_final_v5.py"
)
_STRICT_DERIVED_ENV_WRITER_SHA256 = (
    "defbea5b56981260d9d8de5f4efea0a5a45dca2fd294fe19783b09064e7edca6"
)
_STRICT_DEPENDENCY_LOCAL = threading.local()
_STRICT_FORBIDDEN_STARTUP_MODULES = frozenset({
    "site", "sitecustomize", "usercustomize", "_virtualenv",
})


def _stable_source_bytes(path: Path, expected_sha256: str) -> bytes:
    candidate = Path(path)
    lexical = os.stat(candidate, follow_symlinks=False)
    if (
        stat.S_ISLNK(lexical.st_mode) or not stat.S_ISREG(lexical.st_mode)
        or candidate.resolve(strict=True) != candidate
        or lexical.st_uid != os.geteuid() or lexical.st_nlink != 1
    ):
        raise RuntimeError(f"frozen source identity mismatch: {candidate}")
    descriptor = os.open(
        candidate, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW,
    )
    try:
        before = os.fstat(descriptor)
        payload = bytearray()
        while len(payload) <= (32 << 20):
            chunk = os.read(descriptor, 1 << 20)
            if not chunk:
                break
            payload.extend(chunk)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    identity = lambda item: (
        item.st_dev, item.st_ino, item.st_mode, item.st_uid, item.st_nlink,
        item.st_size, item.st_mtime_ns, item.st_ctime_ns,
    )
    raw = bytes(payload)
    if (
        len(raw) > (32 << 20) or identity(before) != identity(after)
        or len(raw) != before.st_size
        or hashlib.sha256(raw).hexdigest() != expected_sha256
    ):
        raise RuntimeError(f"frozen source bytes mismatch: {candidate}")
    return raw


def _load_exact_source_module(
    module_name: str, path: Path, expected_sha256: str,
) -> Any:
    payload = _stable_source_bytes(path, expected_sha256)
    module = types.ModuleType(module_name)
    module.__file__ = str(path)
    module.__package__ = module_name.rpartition(".")[0]
    module.__loader__ = None
    module.__spec__ = None
    sys.modules[module_name] = module
    try:
        code = compile(
            payload, str(path), "exec", dont_inherit=True, optimize=0,
        )
        exec(code, module.__dict__)
    except BaseException:
        if sys.modules.get(module_name) is module:
            del sys.modules[module_name]
        raise
    return module


controller = _load_exact_source_module(
    "scripts.run_cadical_dmtcp_resume_v1",
    _CONTROLLER_SOURCE,
    _CONTROLLER_SOURCE_SHA256,
)


SCHEMA_VERSION = 5
GATE = "paper400-dic5-adaptive-child-resume-v5"
STATIC_KIND = "paper400-dic5-adaptive-child-resume-static-v5"
SESSION_KIND = "paper400-dic5-adaptive-child-dmtcp-session-v5"
ACTION_CLAIM_KIND = "paper400-dic5-adaptive-child-action-claim-v5"
ACTION_COMMIT_KIND = "paper400-dic5-adaptive-child-action-commit-v5"
TERMINAL_CLAIM_KIND = "paper400-dic5-adaptive-child-terminal-claim-v5"
CERTIFICATE_KIND = "paper400-dic5-adaptive-descendant-unsat-v5"
FINAL_KIND = "paper400-dic5-adaptive-child-final-v5"
VERIFICATION_KIND = "paper400-dic5-adaptive-child-verification-v5"
HANDOFF_LINK_KIND = "paper400-dic5-adaptive-child-handoff-link-v5"
BATCH_SUMMARY_KIND = "paper400-dic5-adaptive-child-batch-action-v5"
AUTHORITY = "TEST_ONLY_CANDIDATE_ONLY_V5"
LANE_COUNT = 4
DESCENDANTS_PER_LANE = 2
COHORT_SIZE = LANE_COUNT
COVER_ROOT_COUNT = LANE_COUNT * DESCENDANTS_PER_LANE
TARGET_KEYS = tuple(
    (lane_index, descendant_index)
    for descendant_index in range(DESCENDANTS_PER_LANE)
    for lane_index in range(LANE_COUNT)
)

SOLVER = Path("/root/cadical-rel-1.9.5-standalone-audit/build/cadical")
DMTCP_PREFIX = Path("/root/dmtcp-v4.2.0-install")
DRAT_CHECKER = Path("/root/qcode-proof-tools/bin/drat-trim")
LRAT_CHECKER = Path("/root/qcode-proof-tools/bin/lrat-check")
SOLVER_ARGS = ("-q",)
EXPECTED_CADICAL_VERSION = "1.9.5"
EXPECTED_TOOL_SHA256 = {
    "cadical_solver": "f8b70724eb0af0ea3b5c0c305fa6a959822ce680326f04ceee7b44ce970d1171",
    "dmtcp_controller_source": "a71cb71e61061d7f925ccc04eb1ccaf48c00289d897b957394dfc8b730062505",
    "dmtcp_launch": "63f7e80bb6ea39cf1b7fe7998a809f791aa5724ff4e77731d400b6c7ab022891",
    "dmtcp_command": "a56701f7f2ee2156437501bd3b16e5e34cdefc6e4da9b05b01d9e0ac5a56e3fe",
    "dmtcp_restart": "a57d8d05dcc78ce6b04c1c79ea703e48d3ec5dd99857cfd5066ac3f0b493432b",
    "drat_checker": "a48ebed7b4b6b373d3ddbeb3368dae7622a9e17bab7fe6eb751ab996757f9fbe",
    "drat_to_lrat": "a48ebed7b4b6b373d3ddbeb3368dae7622a9e17bab7fe6eb751ab996757f9fbe",
    "lrat_checker": "5b87b3ee157db3b1c6b0b70e23faa40ab123c8dd6db63d9518d64312da579517",
}
TOOL_ROLES = frozenset(EXPECTED_TOOL_SHA256)

MAX_JSON_BYTES = 256 << 20
MAX_SOURCE_BYTES = 16 << 20
MAX_TOOL_BYTES = 512 << 20
MAX_LOG_BYTES = 1 << 20
MAX_PROOF_BYTES = 1 << 40
CHECKER_TIMEOUT_SECONDS = 24 * 60 * 60
HASH_CHUNK_BYTES = 8 << 20
SOLVER_MARKER = b"s UNSATISFIABLE"
DRAT_MARKER = b"s VERIFIED"
LRAT_MARKER = b"c VERIFIED"

STATIC_PARENT = Path("static/parent-manifest.json")
STATIC_WIDTH6 = Path("static/width6-campaign.json")
STATIC_WIDTH10 = Path("static/width10-campaign.json")
STATIC_OVERLAY = Path("static/adaptive-overlay.json")
STATIC_HARD_EVIDENCE = Path("static/hard-evidence.json")
STATIC_SWITCH_EVIDENCE = Path("static/switch-evidence.json")
STATIC_DESCENDANT_CNF = Path("static/descendant.cnf")
STATIC_COMMIT = Path("state/00-static.json")
SESSION_COMMIT = Path("state/10-session.json")
ACTIONS_DIR = Path("state/actions")
TERMINAL_BUNDLE = Path("terminal-v5")
TERMINAL_STAGING_PREFIX = ".terminal-v5.staging-"
TERMINAL_CLAIM = TERMINAL_BUNDLE / "terminal.claim.json"
CERTIFICATE = TERMINAL_BUNDLE / "certificate.json"
FINAL_COMMIT = TERMINAL_BUNDLE / "COMMIT.json"
RUNTIME_ROOT = Path("runtime/dmtcp")
DRAT_ARTIFACT = TERMINAL_BUNDLE / "descendant.drat"
LRAT_ARTIFACT = TERMINAL_BUNDLE / "descendant.lrat"
TERMINAL_BUNDLE_FILES = frozenset({
    TERMINAL_CLAIM.name, CERTIFICATE.name, FINAL_COMMIT.name,
    DRAT_ARTIFACT.name, LRAT_ARTIFACT.name,
})
ROOT_LOCK = Path(".adaptive-child.lock")
HANDOFF_LINK = Path("state/15-batch-handoff.json")
ACTION_RE = re.compile(
    r"^(?P<sequence>[0-9]{6})-(?P<action>[a-z-]+)\.(?P<stage>claim|commit)\.json$"
)


class AdaptiveChildResumeError(RuntimeError):
    """A static, transport, path, resource, switch, or proof gate failed."""


def _terminal_bundle_present(root: Path) -> bool:
    path = root / TERMINAL_BUNDLE
    try:
        info = os.stat(path, follow_symlinks=False)
    except FileNotFoundError:
        return False
    if (
        stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode)
        or info.st_uid != os.geteuid()
        or stat.S_IMODE(info.st_mode) != 0o700
    ):
        raise AdaptiveChildResumeError(
            "terminal bundle entry is not a plain owned 0700 directory"
        )
    return True


def canonical_bytes(value: Any) -> bytes:
    try:
        return json.dumps(
            value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
            allow_nan=False,
        ).encode("ascii")
    except (TypeError, ValueError, UnicodeEncodeError) as exc:
        raise AdaptiveChildResumeError(f"not strict canonical JSON: {exc}") from exc


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def seal(value: Mapping[str, Any]) -> dict[str, Any]:
    if type(value) is not dict or "record_sha256" in value:
        raise AdaptiveChildResumeError("invalid object passed to seal")
    result = dict(value)
    result["record_sha256"] = canonical_sha256(result)
    return result


def _is_sha256(value: Any) -> bool:
    if type(value) is not str or len(value) != 64:
        return False
    try:
        return bytes.fromhex(value).hex() == value
    except ValueError:
        return False


def selfhash_valid(value: Any) -> bool:
    if type(value) is not dict or not _is_sha256(value.get("record_sha256")):
        return False
    unsigned = dict(value)
    stored = unsigned.pop("record_sha256")
    try:
        return stored == canonical_sha256(unsigned)
    except AdaptiveChildResumeError:
        return False


def json_type_equal(left: Any, right: Any) -> bool:
    if type(left) is not type(right):
        return False
    if type(left) is dict:
        return set(left) == set(right) and all(
            json_type_equal(left[key], right[key]) for key in left
        )
    if type(left) is list:
        return len(left) == len(right) and all(
            json_type_equal(a, b) for a, b in zip(left, right, strict=True)
        )
    return bool(left == right)


def _require_sha256(value: Any, label: str) -> str:
    if not _is_sha256(value):
        raise AdaptiveChildResumeError(f"{label} is not a canonical SHA-256")
    return value

def _strict_stat_identity(info: os.stat_result) -> tuple[int, ...]:
    return (
        info.st_dev, info.st_ino, info.st_mode, info.st_uid, info.st_gid,
        info.st_nlink, info.st_size, info.st_mtime_ns, info.st_ctime_ns,
    )


def _strict_owned_read_only_entry(
    info: os.stat_result, *, directory: bool, label: str,
) -> None:
    expected_type = stat.S_ISDIR if directory else stat.S_ISREG
    if (
        not expected_type(info.st_mode)
        or info.st_uid != 0
        or stat.S_IMODE(info.st_mode) & 0o022
    ):
        raise AdaptiveChildResumeError(
            f"strict dependency {label} is not root-owned read-only "
            f"{'directory' if directory else 'file'}"
        )


def _scan_strict_owned_tree(
    root: Path, *, method: str, allow_symlinks: bool,
) -> dict[str, Any]:
    """No-follow hash of every regular file and directory in a fixed tree."""

    if (
        type(method) is not str or not method
        or type(allow_symlinks) is not bool
    ):
        raise AdaptiveChildResumeError("strict tree scanner policy malformed")
    root = Path(root)
    if (
        not root.is_absolute()
        or str(root) != os.path.abspath(str(root))
        or root.resolve(strict=True) != root
    ):
        raise AdaptiveChildResumeError(
            "strict dependency root is not canonical absolute"
        )
    lexical = os.stat(root, follow_symlinks=False)
    _strict_owned_read_only_entry(
        lexical, directory=True, label="root",
    )
    root_fd = os.open(
        root,
        os.O_RDONLY | os.O_CLOEXEC | os.O_DIRECTORY | os.O_NOFOLLOW,
    )
    records: list[dict[str, Any]] = [{
        "type": "D", "relative_path": ".", "size": 0,
        "content_sha256": None,
    }]
    file_count = 0
    directory_count = 1
    symlink_count = 0
    total_bytes = 0
    numba_cache_records: list[dict[str, Any]] = []
    symlink_records: list[dict[str, str]] = []
    broad_file_cap = 200_000
    broad_directory_cap = 50_000
    broad_byte_cap = 16 << 30

    def check_budget() -> None:
        if (
            file_count + symlink_count > broad_file_cap
            or directory_count > broad_directory_cap
            or total_bytes > broad_byte_cap
        ):
            raise AdaptiveChildResumeError(
                "strict dependency tree exceeds scan budget"
            )

    def walk(directory_fd: int, parts: tuple[str, ...]) -> None:
        nonlocal file_count, directory_count, symlink_count, total_bytes
        before = os.fstat(directory_fd)
        _strict_owned_read_only_entry(
            before, directory=True,
            label="directory " + (".".join(parts) or "."),
        )
        with os.scandir(directory_fd) as scanner:
            names = [entry.name for entry in scanner]
        encoded_names: list[tuple[bytes, str]] = []
        for name in names:
            if (
                type(name) is not str
                or name in {"", ".", ".."}
                or "/" in name
                or (os.altsep is not None and os.altsep in name)
            ):
                raise AdaptiveChildResumeError(
                    "strict dependency tree has unsafe entry name"
                )
            try:
                encoded = name.encode("utf-8", "strict")
            except UnicodeEncodeError as exc:
                raise AdaptiveChildResumeError(
                    "strict dependency path is not strict UTF-8"
                ) from exc
            encoded_names.append((encoded, name))
        if len({item[0] for item in encoded_names}) != len(encoded_names):
            raise AdaptiveChildResumeError(
                "strict dependency tree has duplicate UTF-8 names"
            )
        for _, name in sorted(encoded_names):
            info = os.stat(name, dir_fd=directory_fd, follow_symlinks=False)
            relative_parts = parts + (name,)
            relative = "/".join(relative_parts)
            try:
                relative.encode("utf-8", "strict")
            except UnicodeEncodeError as exc:
                raise AdaptiveChildResumeError(
                    "strict dependency relative path is not UTF-8"
                ) from exc
            if stat.S_ISLNK(info.st_mode):
                if not allow_symlinks:
                    raise AdaptiveChildResumeError(
                        f"strict dependency symlink forbidden: {relative}"
                    )
                target_before = os.readlink(name, dir_fd=directory_fd)
                try:
                    target_bytes = target_before.encode("utf-8", "strict")
                except UnicodeEncodeError as exc:
                    raise AdaptiveChildResumeError(
                        "strict symlink target is not UTF-8"
                    ) from exc
                target_after = os.readlink(name, dir_fd=directory_fd)
                after_link = os.stat(
                    name, dir_fd=directory_fd, follow_symlinks=False,
                )
                if (
                    info.st_uid != 0 or info.st_nlink != 1
                    or target_before != target_after
                    or _strict_stat_identity(info)
                    != _strict_stat_identity(after_link)
                ):
                    raise AdaptiveChildResumeError(
                        f"strict dependency symlink raced: {relative}"
                    )
                symlink_count += 1
                symlink_records.append({
                    "relative_path": relative, "target": target_before,
                })
                records.append({
                    "type": "L", "relative_path": relative,
                    "size": len(target_bytes),
                    "content_sha256": hashlib.sha256(
                        target_bytes
                    ).hexdigest(),
                })
                check_budget()
                continue
            if stat.S_ISDIR(info.st_mode):
                _strict_owned_read_only_entry(
                    info, directory=True, label=relative,
                )
                child_fd = os.open(
                    name,
                    os.O_RDONLY | os.O_CLOEXEC
                    | os.O_DIRECTORY | os.O_NOFOLLOW,
                    dir_fd=directory_fd,
                )
                try:
                    opened = os.fstat(child_fd)
                    if _strict_stat_identity(opened) != _strict_stat_identity(info):
                        raise AdaptiveChildResumeError(
                            f"strict dependency directory raced: {relative}"
                        )
                    directory_count += 1
                    records.append({
                        "type": "D", "relative_path": relative, "size": 0,
                        "content_sha256": None,
                    })
                    check_budget()
                    walk(child_fd, relative_parts)
                finally:
                    os.close(child_fd)
                continue
            if not stat.S_ISREG(info.st_mode):
                raise AdaptiveChildResumeError(
                    f"strict dependency special file forbidden: {relative}"
                )
            _strict_owned_read_only_entry(
                info, directory=False, label=relative,
            )
            descriptor = os.open(
                name,
                os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW,
                dir_fd=directory_fd,
            )
            try:
                opened = os.fstat(descriptor)
                if _strict_stat_identity(opened) != _strict_stat_identity(info):
                    raise AdaptiveChildResumeError(
                        f"strict dependency file raced before read: {relative}"
                    )
                digest = hashlib.sha256()
                observed_bytes = 0
                while True:
                    chunk = os.read(descriptor, HASH_CHUNK_BYTES)
                    if not chunk:
                        break
                    digest.update(chunk)
                    observed_bytes += len(chunk)
                    if total_bytes + observed_bytes > broad_byte_cap:
                        raise AdaptiveChildResumeError(
                            "strict dependency tree exceeds byte budget"
                        )
                after = os.fstat(descriptor)
            finally:
                os.close(descriptor)
            if (
                _strict_stat_identity(opened) != _strict_stat_identity(after)
                or observed_bytes != opened.st_size
            ):
                raise AdaptiveChildResumeError(
                    f"strict dependency file raced while hashing: {relative}"
                )
            file_count += 1
            total_bytes += observed_bytes
            file_record = {
                "type": "F", "relative_path": relative,
                "size": observed_bytes,
                "content_sha256": digest.hexdigest(),
            }
            records.append(file_record)
            if name.endswith((".nbi", ".nbc")):
                numba_cache_records.append(dict(file_record))
            check_budget()
        after = os.fstat(directory_fd)
        if _strict_stat_identity(before) != _strict_stat_identity(after):
            raise AdaptiveChildResumeError(
                "strict dependency directory changed during traversal"
            )

    try:
        opened_root = os.fstat(root_fd)
        if _strict_stat_identity(opened_root) != _strict_stat_identity(lexical):
            raise AdaptiveChildResumeError(
                "strict dependency root raced before traversal"
            )
        walk(root_fd, ())
        after_root = os.fstat(root_fd)
    finally:
        os.close(root_fd)
    if _strict_stat_identity(opened_root) != _strict_stat_identity(after_root):
        raise AdaptiveChildResumeError(
            "strict dependency root changed during traversal"
        )
    return {
        "method": method,
        "root": str(root),
        "file_count": file_count,
        "directory_count": directory_count,
        "symlink_count": symlink_count,
        "bytes": total_bytes,
        "tree_sha256": canonical_sha256(records),
        "coverage": "all-regular-files-including-pyc-and-cache-subtrees-v2",
        "symlink_policy": (
            "no-follow-record-target" if allow_symlinks else "forbidden"
        ),
        "symlinks": symlink_records,
        "numba_cache_file_count": len(numba_cache_records),
        "numba_cache_bytes": sum(
            item["size"] for item in numba_cache_records
        ),
        "numba_cache_sha256": canonical_sha256(numba_cache_records),
        "persistent_change_detection": True,
        "privileged_toctou_defended": False,
    }


def _scan_strict_dependency_tree() -> dict[str, Any]:
    return _scan_strict_owned_tree(
        _STRICT_DEPENDENCY_ROOT,
        method="fixed-site-all-files-no-follow-tree-v2",
        allow_symlinks=False,
    )


def _scan_strict_stdlib_tree() -> dict[str, Any]:
    return _scan_strict_owned_tree(
        _STRICT_STDLIB_ROOT,
        method="fixed-system-stdlib-all-files-no-follow-tree-v1",
        allow_symlinks=True,
    )


def _expected_strict_dependency_tree() -> dict[str, Any]:
    return {
        "method": "fixed-site-all-files-no-follow-tree-v2",
        "root": str(_STRICT_DEPENDENCY_ROOT),
        "file_count": _STRICT_DEPENDENCY_EXPECTED_FILES,
        "directory_count": _STRICT_DEPENDENCY_EXPECTED_DIRECTORIES,
        "symlink_count": _STRICT_DEPENDENCY_EXPECTED_SYMLINKS,
        "bytes": _STRICT_DEPENDENCY_EXPECTED_BYTES,
        "tree_sha256": _STRICT_DEPENDENCY_EXPECTED_SHA256,
        "coverage": "all-regular-files-including-pyc-and-cache-subtrees-v2",
        "symlink_policy": "forbidden",
        "symlinks": [],
        "numba_cache_file_count": (
            _STRICT_DEPENDENCY_EXPECTED_NUMBA_CACHE_FILES
        ),
        "numba_cache_bytes": _STRICT_DEPENDENCY_EXPECTED_NUMBA_CACHE_BYTES,
        "numba_cache_sha256": (
            _STRICT_DEPENDENCY_EXPECTED_NUMBA_CACHE_SHA256
        ),
        "persistent_change_detection": True,
        "privileged_toctou_defended": False,
    }


def _expected_strict_stdlib_tree() -> dict[str, Any]:
    return {
        "method": "fixed-system-stdlib-all-files-no-follow-tree-v1",
        "root": str(_STRICT_STDLIB_ROOT),
        "file_count": _STRICT_STDLIB_EXPECTED_FILES,
        "directory_count": _STRICT_STDLIB_EXPECTED_DIRECTORIES,
        "symlink_count": _STRICT_STDLIB_EXPECTED_SYMLINKS,
        "bytes": _STRICT_STDLIB_EXPECTED_BYTES,
        "tree_sha256": _STRICT_STDLIB_EXPECTED_SHA256,
        "coverage": "all-regular-files-including-pyc-and-cache-subtrees-v2",
        "symlink_policy": "no-follow-record-target",
        "symlinks": [
            {"relative_path": relative, "target": target}
            for relative, target in _STRICT_STDLIB_EXPECTED_SYMLINK_RECORDS
        ],
        "numba_cache_file_count": 0,
        "numba_cache_bytes": 0,
        "numba_cache_sha256": canonical_sha256([]),
        "persistent_change_detection": True,
        "privileged_toctou_defended": False,
    }


def _verified_strict_dependency_tree() -> dict[str, Any]:
    observed = _scan_strict_dependency_tree()
    if not json_type_equal(observed, _expected_strict_dependency_tree()):
        raise AdaptiveChildResumeError(
            "strict dependency tree differs from frozen all-files pin"
        )
    return observed


def _verified_strict_stdlib_tree() -> dict[str, Any]:
    observed = _scan_strict_stdlib_tree()
    if not json_type_equal(observed, _expected_strict_stdlib_tree()):
        raise AdaptiveChildResumeError(
            "strict system stdlib differs from frozen all-files pin"
        )
    return observed


def _strict_plain_directory(path: Path, label: str) -> dict[str, Any]:
    try:
        lexical = os.stat(path, follow_symlinks=False)
        resolved = path.resolve(strict=True)
    except (OSError, RuntimeError) as exc:
        raise AdaptiveChildResumeError(
            f"strict Python {label} cannot be resolved"
        ) from exc
    _strict_owned_read_only_entry(
        lexical, directory=True, label=label,
    )
    if resolved != path:
        raise AdaptiveChildResumeError(
            f"strict Python {label} is aliased"
        )
    return {
        "path": str(path), "device": lexical.st_dev, "inode": lexical.st_ino,
        "uid": lexical.st_uid, "mode": stat.S_IMODE(lexical.st_mode),
    }


def _stable_strict_runtime_file(
    path: Path, *, root: Path | None = None,
    mapped_identity: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    candidate = Path(path)
    if (
        not candidate.is_absolute()
        or str(candidate) != os.path.abspath(str(candidate))
        or candidate.resolve(strict=True) != candidate
    ):
        raise AdaptiveChildResumeError(
            f"strict runtime file path is not canonical: {candidate}"
        )
    lexical = os.stat(candidate, follow_symlinks=False)
    _strict_owned_read_only_entry(
        lexical, directory=False, label=f"runtime file {candidate}",
    )
    descriptor = os.open(
        candidate, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW,
    )
    try:
        before = os.fstat(descriptor)
        if (
            _strict_stat_identity(before) != _strict_stat_identity(lexical)
            or before.st_size > (1 << 30)
        ):
            raise AdaptiveChildResumeError(
                f"strict runtime file identity mismatch: {candidate}"
            )
        digest = hashlib.sha256()
        total = 0
        while True:
            chunk = os.read(descriptor, HASH_CHUNK_BYTES)
            if not chunk:
                break
            digest.update(chunk)
            total += len(chunk)
            if total > (1 << 30):
                raise AdaptiveChildResumeError(
                    "strict runtime file exceeds hash budget"
                )
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    if (
        _strict_stat_identity(before) != _strict_stat_identity(after)
        or total != before.st_size
    ):
        raise AdaptiveChildResumeError(
            f"strict runtime file changed while hashing: {candidate}"
        )
    if mapped_identity is not None:
        fields = {"device_major", "device_minor", "inode"}
        if (
            type(mapped_identity) is not dict
            or set(mapped_identity) != fields
            or mapped_identity["device_major"] != os.major(before.st_dev)
            or mapped_identity["device_minor"] != os.minor(before.st_dev)
            or mapped_identity["inode"] != before.st_ino
        ):
            raise AdaptiveChildResumeError(
                f"mapped runtime inode differs from path: {candidate}"
            )
    record = {
        "bytes": total, "sha256": digest.hexdigest(), "uid": before.st_uid,
        "mode": stat.S_IMODE(before.st_mode), "links": before.st_nlink,
    }
    if root is None:
        record["path"] = str(candidate)
    else:
        try:
            record["relative_path"] = candidate.relative_to(root).as_posix()
        except ValueError as exc:
            raise AdaptiveChildResumeError(
                "mapped runtime file escapes its frozen tree"
            ) from exc
    return record


def _strict_stdlib_external_target_binding() -> dict[str, Any]:
    resolved_external: list[Path] = []
    for relative, expected_target in _STRICT_STDLIB_EXPECTED_SYMLINK_RECORDS:
        link = _STRICT_STDLIB_ROOT / relative
        lexical = os.stat(link, follow_symlinks=False)
        if (
            not stat.S_ISLNK(lexical.st_mode)
            or lexical.st_uid != 0
            or lexical.st_nlink != 1
            or os.readlink(link) != expected_target
        ):
            raise AdaptiveChildResumeError(
                f"strict stdlib symlink changed: {relative}"
            )
        resolved = link.resolve(strict=True)
        try:
            resolved.relative_to(_STRICT_STDLIB_ROOT)
        except ValueError:
            resolved_external.append(resolved)
    if tuple(sorted(resolved_external, key=str)) != tuple(
        sorted(_STRICT_STDLIB_EXTERNAL_TARGETS, key=str)
    ):
        raise AdaptiveChildResumeError(
            "strict stdlib external symlink target set changed"
        )
    records = [
        _stable_strict_runtime_file(path)
        for path in sorted(resolved_external, key=str)
    ]
    summary = {
        "file_count": len(records),
        "bytes": sum(record["bytes"] for record in records),
        "files_sha256": canonical_sha256(records),
    }
    expected = {
        "file_count": _STRICT_STDLIB_EXTERNAL_EXPECTED_FILES,
        "bytes": _STRICT_STDLIB_EXTERNAL_EXPECTED_BYTES,
        "files_sha256": _STRICT_STDLIB_EXTERNAL_EXPECTED_SHA256,
    }
    if not json_type_equal(summary, expected):
        raise AdaptiveChildResumeError(
            "strict stdlib external symlink targets differ from frozen pin"
        )
    return {
        "method": "fixed-stdlib-external-symlink-target-files-v1",
        "files": records, "summary": summary,
        "persistent_change_detection": True,
        "privileged_toctou_defended": False,
    }


def _parse_proc_maps(payload: bytes) -> dict[str, Any]:
    if type(payload) is not bytes or not payload or not payload.endswith(b"\n"):
        raise AdaptiveChildResumeError("/proc maps payload framing mismatch")
    try:
        lines = payload.decode("ascii", "strict").splitlines()
    except UnicodeDecodeError as exc:
        raise AdaptiveChildResumeError(
            "/proc maps is not strict ASCII"
        ) from exc
    files: dict[str, dict[str, int]] = {}
    anonymous_exec: list[dict[str, Any]] = []
    semaphores: list[str] = []
    for line in lines:
        fields = line.split(None, 5)
        if len(fields) not in {5, 6}:
            raise AdaptiveChildResumeError("/proc maps line is malformed")
        address, permissions, offset, device, inode_text = fields[:5]
        if (
            re.fullmatch(r"[0-9a-f]+-[0-9a-f]+", address) is None
            or re.fullmatch(r"[r-][w-][x-][ps]", permissions) is None
            or re.fullmatch(r"[0-9a-f]+", offset) is None
            or re.fullmatch(r"[0-9a-f]+:[0-9a-f]+", device) is None
            or re.fullmatch(r"[0-9]+", inode_text) is None
        ):
            raise AdaptiveChildResumeError(
                "/proc maps metadata is non-canonical"
            )
        start_text, stop_text = address.split("-", 1)
        start, stop = int(start_text, 16), int(stop_text, 16)
        inode = int(inode_text)
        major_text, minor_text = device.split(":", 1)
        major, minor = int(major_text, 16), int(minor_text, 16)
        if start >= stop:
            raise AdaptiveChildResumeError(
                "/proc maps has an invalid address interval"
            )
        pathname = fields[5] if len(fields) == 6 else None
        if pathname is None:
            if "x" in permissions:
                anonymous_exec.append({
                    "permissions": permissions, "bytes": stop - start,
                })
            continue
        if pathname.startswith("[") and pathname.endswith("]"):
            continue
        if pathname.endswith(" (deleted)"):
            if (
                re.fullmatch(
                    r"/dev/shm/sem\.[A-Za-z0-9]+ \(deleted\)", pathname,
                ) is not None
                and permissions == "rw-s"
                and inode > 0 and (major, minor) != (0, 0)
            ):
                semaphores.append(permissions)
                continue
            raise AdaptiveChildResumeError(
                "deleted mapped file is forbidden"
            )
        if (
            not pathname.startswith("/")
            or "\\" in pathname
            or pathname != os.path.abspath(pathname)
            or inode <= 0
            or (major, minor) == (0, 0)
        ):
            raise AdaptiveChildResumeError(
                "named /proc mapping is unsafe or ambiguous"
            )
        identity = {
            "device_major": major, "device_minor": minor, "inode": inode,
        }
        previous = files.setdefault(pathname, identity)
        if not json_type_equal(previous, identity):
            raise AdaptiveChildResumeError(
                "one mapped path refers to multiple inodes"
            )
    anonymous_summary = {
        # Raw VMA boundaries vary between otherwise identical Numba runs.  The
        # stable quantity is the non-empty permission-class aggregate.
        "count_method": "nonempty-permission-classes-v1",
        "count": len({item["permissions"] for item in anonymous_exec}),
        "bytes": sum(item["bytes"] for item in anonymous_exec),
        "permissions": sorted({
            item["permissions"] for item in anonymous_exec
        }),
        "raw_vma_boundaries_recorded": False,
    }
    return {
        "files": {path: files[path] for path in sorted(files)},
        "anonymous_executable": anonymous_summary,
        "openmp_deleted_semaphore": {
            "category": "posix-openmp-semaphore-deleted-nonexec-shared-rw",
            "count": len(semaphores),
            "permissions": sorted(set(semaphores)),
            "random_basenames_recorded": False,
        },
        "bracket_mappings_ignored": True,
    }


def _read_proc_maps() -> dict[str, Any]:
    path = Path(f"/proc/{os.getpid()}/maps")
    descriptor = os.open(
        path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW,
    )
    try:
        payload = bytearray()
        while len(payload) <= (16 << 20):
            chunk = os.read(descriptor, 1 << 20)
            if not chunk:
                break
            payload.extend(chunk)
    finally:
        os.close(descriptor)
    if len(payload) > (16 << 20):
        raise AdaptiveChildResumeError("/proc maps exceeds fixed cap")
    return _parse_proc_maps(bytes(payload))


def _mapped_path_category(path: Path) -> str:
    candidate = Path(path)
    if candidate == _STRICT_PYTHON_RESOLVED:
        return "python"
    for root, category in (
        (_STRICT_DEPENDENCY_ROOT, "site"),
        (_STRICT_STDLIB_ROOT, "stdlib"),
        (Path("/usr/lib"), "system"),
    ):
        try:
            candidate.relative_to(root)
        except ValueError:
            continue
        return category
    raise AdaptiveChildResumeError(
        f"mapped file is outside frozen runtime roots: {candidate}"
    )


def _strict_mapped_runtime_closure(
    dependency_tree: Mapping[str, Any],
    stdlib_tree: Mapping[str, Any],
) -> dict[str, Any]:
    state = _active_strict_dependency_context()
    before = _read_proc_maps()
    entry = state["entry_maps"]
    if (
        not set(entry["files"]).issubset(before["files"])
        or any(
            not json_type_equal(identity, before["files"].get(path))
            for path, identity in entry["files"].items()
        )
    ):
        raise AdaptiveChildResumeError(
            "entry mapped-file set is not an inode-stable final subset"
        )
    proc_exe = Path(f"/proc/{os.getpid()}/exe")
    exe_target = os.readlink(proc_exe)
    if (
        exe_target.endswith(" (deleted)")
        or Path(exe_target).resolve(strict=True) != _STRICT_PYTHON_RESOLVED
    ):
        raise AdaptiveChildResumeError(
            "/proc/self/exe differs from fixed Python"
        )
    groups: dict[str, list[dict[str, Any]]] = {
        "site": [], "stdlib": [], "system": [],
    }
    python_record: dict[str, Any] | None = None
    for raw_path, mapped_identity in before["files"].items():
        path = Path(raw_path)
        category = _mapped_path_category(path)
        root = (
            _STRICT_DEPENDENCY_ROOT if category == "site"
            else _STRICT_STDLIB_ROOT if category == "stdlib"
            else None
        )
        record = _stable_strict_runtime_file(
            path, root=root, mapped_identity=mapped_identity,
        )
        if category == "python":
            if (
                python_record is not None
                or record["sha256"] != _STRICT_PYTHON_SHA256
            ):
                raise AdaptiveChildResumeError(
                    "mapped Python executable differs from frozen pin"
                )
            python_record = record
        else:
            groups[category].append(record)
    if python_record is None:
        raise AdaptiveChildResumeError(
            "fixed Python executable is absent from mapped closure"
        )
    after = _read_proc_maps()
    if not json_type_equal(before, after):
        raise AdaptiveChildResumeError(
            "mapped runtime closure changed while it was hashed"
        )
    expected_system_files = [
        {
            "path": path, "bytes": size, "sha256": sha256,
            "uid": uid, "mode": mode, "links": links,
        }
        for path, size, sha256, uid, mode, links
        in _STRICT_SYSTEM_MAP_EXPECTED_RECORDS
    ]
    system_summary = {
        "file_count": len(groups["system"]),
        "bytes": sum(item["bytes"] for item in groups["system"]),
        "files_sha256": canonical_sha256(groups["system"]),
    }
    expected_system = {
        "file_count": _STRICT_SYSTEM_MAP_EXPECTED_FILES,
        "bytes": _STRICT_SYSTEM_MAP_EXPECTED_BYTES,
        "files_sha256": _STRICT_SYSTEM_MAP_EXPECTED_SHA256,
    }
    if (
        not json_type_equal(groups["system"], expected_system_files)
        or not json_type_equal(system_summary, expected_system)
    ):
        raise AdaptiveChildResumeError(
            "mapped system-file closure differs from frozen manifest"
        )
    jit = before["anonymous_executable"]
    if (
        jit.get("count_method") != "nonempty-permission-classes-v1"
        or jit.get("count")
        != _STRICT_JIT_EXEC_EXPECTED_PERMISSION_CLASS_COUNT
        or jit.get("bytes") != _STRICT_JIT_EXEC_EXPECTED_BYTES
        or jit.get("permissions")
        != list(_STRICT_JIT_EXEC_EXPECTED_PERMISSIONS)
    ):
        raise AdaptiveChildResumeError(
            "anonymous executable JIT aggregate differs from frozen policy"
        )
    summaries = {
        category: {
            "file_count": len(records),
            "bytes": sum(item["bytes"] for item in records),
            "files_sha256": canonical_sha256(records),
        }
        for category, records in groups.items()
    }
    return {
        "method": "proc-maps-double-snapshot-frozen-file-closure-v1",
        "proc_self_exe": python_record,
        "entry_file_count": len(entry["files"]),
        "entry_files_sha256": canonical_sha256(sorted(entry["files"])),
        "site_tree_sha256": dependency_tree["tree_sha256"],
        "stdlib_tree_sha256": stdlib_tree["tree_sha256"],
        "site_files": groups["site"],
        "stdlib_files": groups["stdlib"],
        "system_files": groups["system"],
        "summaries": summaries,
        "system_manifest_frozen_in_source": True,
        "anonymous_executable": {
            **jit,
            "jit_derivative_allowed": True,
            "random_addresses_recorded": False,
            "derivation_binding": {
                "dependency_tree_sha256": dependency_tree["tree_sha256"],
                "numba_cache_file_count": (
                    dependency_tree["numba_cache_file_count"]
                ),
                "numba_cache_bytes": dependency_tree["numba_cache_bytes"],
                "numba_cache_sha256": (
                    dependency_tree["numba_cache_sha256"]
                ),
                "source_prefixes": ["llvmlite/", "numba/"],
            },
        },
        "openmp_deleted_semaphore": before[
            "openmp_deleted_semaphore"
        ],
        "anonymous_nonexec_and_bracket_mappings_ignored": True,
        "persistent_change_detection": True,
        "privileged_toctou_defended": False,
    }


def _require_absent_numba_config(path: Path) -> None:
    candidate = Path(path)
    try:
        os.stat(candidate, follow_symlinks=False)
    except FileNotFoundError:
        return
    raise AdaptiveChildResumeError(
        "strict execution forbids project-local .numba_config.yaml"
    )


def _strict_environment_snapshot() -> dict[str, str]:
    observed: dict[str, str] = {}
    for key, value in os.environ.items():
        if (
            key in {"LD_PRELOAD", "LD_LIBRARY_PATH", "LD_AUDIT"}
            or key.startswith(_STRICT_FORBIDDEN_ENV_PREFIXES)
        ):
            observed[key] = value
    return {key: observed[key] for key in sorted(observed)}


def _strict_process_environment_snapshot() -> dict[str, str]:
    return {
        key: value for key, value in sorted(os.environ.items())
    }


def _expected_strict_process_environment(
    *, derived: bool,
) -> dict[str, str]:
    if type(derived) is not bool:
        raise AdaptiveChildResumeError(
            "strict derived-environment flag is malformed"
        )
    expected = dict(_STRICT_ENTRY_ENVIRONMENT)
    if derived:
        expected.update(dict(_STRICT_DERIVED_THREAD_ENV))
    return {key: expected[key] for key in sorted(expected)}


def _require_strict_process_environment(
    *, derived: bool,
) -> dict[str, str]:
    observed = _strict_process_environment_snapshot()
    expected = _expected_strict_process_environment(derived=derived)
    if not json_type_equal(observed, expected):
        stage = "derived" if derived else "entry"
        raise AdaptiveChildResumeError(
            f"strict {stage} process environment differs from exact pin"
        )
    return observed


def _strict_launch_filesystem_binding() -> dict[str, Any]:
    cwd_text = os.getcwd()
    project_identity = _strict_plain_directory(PROJECT, "project cwd")
    current_identity = _strict_plain_directory(
        Path(cwd_text), "current cwd",
    )
    if (
        cwd_text != str(PROJECT)
        or Path(cwd_text).resolve(strict=True) != PROJECT
        or not json_type_equal(project_identity, current_identity)
    ):
        raise AdaptiveChildResumeError(
            "strict execution cwd differs from the fixed project"
        )
    numba_config = PROJECT / ".numba_config.yaml"
    _require_absent_numba_config(numba_config)
    if os.path.lexists(_STRICT_PYTHON_ZIP):
        raise AdaptiveChildResumeError(
            "strict absent python312.zip path unexpectedly exists"
        )
    return {
        "method": "fixed-cwd-no-numba-config-no-python312-zip-v1",
        "cwd": str(PROJECT), "cwd_identity": project_identity,
        "numba_config_path": str(numba_config),
        "numba_config_absent": True,
        "python312_zip": str(_STRICT_PYTHON_ZIP),
        "python312_zip_absent": True,
    }


def _strict_launch_input_binding() -> dict[str, Any]:
    observed = _require_strict_process_environment(derived=False)
    filesystem = _strict_launch_filesystem_binding()
    return {
        "method": "fixed-launch-inputs-exact-minimal-environment-v3",
        "filesystem": filesystem,
        "forbidden_environment_prefixes": list(
            _STRICT_FORBIDDEN_ENV_PREFIXES
        ),
        "dynamic_loader_environment_keys": [
            "LD_AUDIT", "LD_LIBRARY_PATH", "LD_PRELOAD",
        ],
        "entry_environment_policy": (
            "exact-lang-c-lc-all-c-tz-utc-no-other-keys-v1"
        ),
        "entry_environment": observed,
    }


def _expected_strict_derived_env_writer_record() -> dict[str, Any]:
    payload = _stable_source_bytes(
        _STRICT_DERIVED_ENV_WRITER,
        _STRICT_DERIVED_ENV_WRITER_SHA256,
    )
    return {
        "module": _STRICT_DERIVED_ENV_WRITER_MODULE,
        "path": str(_STRICT_DERIVED_ENV_WRITER),
        "sha256": _STRICT_DERIVED_ENV_WRITER_SHA256,
        "bytes": len(payload),
        "externally_bound": False,
        "execution": "compile-exact-source-bytes-v4",
    }


def _strict_derived_env_writer_from_executed_sources(
    executed_sources: Any,
) -> dict[str, Any]:
    if type(executed_sources) is not list:
        raise AdaptiveChildResumeError(
            "science executed-source closure has the wrong exact type"
        )
    expected = _expected_strict_derived_env_writer_record()
    seen_modules: set[str] = set()
    matches: list[dict[str, Any]] = []
    for record in executed_sources:
        if (
            type(record) is not dict
            or set(record) != set(expected)
            or type(record.get("module")) is not str
            or record["module"] in seen_modules
            or type(record.get("path")) is not str
            or not _is_sha256(record.get("sha256"))
            or type(record.get("bytes")) is not int
            or record["bytes"] < 1
            or type(record.get("externally_bound")) is not bool
            or record.get("execution") != "compile-exact-source-bytes-v4"
        ):
            raise AdaptiveChildResumeError(
                "science executed-source closure is not type-exact"
            )
        seen_modules.add(record["module"])
        if (
            record["module"] == _STRICT_DERIVED_ENV_WRITER_MODULE
            or record["path"] == str(_STRICT_DERIVED_ENV_WRITER)
        ):
            matches.append(record)
    if len(matches) != 1 or not json_type_equal(matches[0], expected):
        raise AdaptiveChildResumeError(
            "science executed-source closure lacks one exact environment writer"
        )
    return dict(matches[0])


def _strict_derived_environment_binding(
    writer_source: Mapping[str, Any],
) -> dict[str, Any]:
    expected_writer = _expected_strict_derived_env_writer_record()
    if type(writer_source) is not dict or not json_type_equal(
        writer_source, expected_writer,
    ):
        raise AdaptiveChildResumeError(
            "science-derived environment writer record differs from exact pin"
        )
    full_environment = _require_strict_process_environment(
        derived=True,
    )
    filesystem = _strict_launch_filesystem_binding()
    observed = _strict_environment_snapshot()
    expected = {
        key: value for key, value in sorted(_STRICT_DERIVED_THREAD_ENV)
    }
    if not json_type_equal(observed, expected):
        raise AdaptiveChildResumeError(
            "science-derived native thread environment differs from exact pin: "
            + ",".join(observed)
        )
    value = {
        "method": "exact-post-science-derived-thread-environment-v3",
        "filesystem": filesystem,
        "entry_environment": dict(_STRICT_ENTRY_ENVIRONMENT),
        "environment": observed,
        "effective_environment": full_environment,
        "writer_source": dict(writer_source),
        "effect_scope": (
            "sets-listed-keys-before-lower-final-v5-own-"
            "numpy-and-qldpc-imports-v1"
        ),
        "entry_environment_policy": (
            "exact-lang-c-lc-all-c-tz-utc-no-other-keys-v1"
        ),
        "derived_only_after_exact_science_load": True,
        "writer_selected_from_type_exact_executed_source_closure": True,
    }
    value["derived_environment_sha256"] = canonical_sha256(value)
    return value


def _strict_runtime_binding() -> dict[str, Any]:
    launch_inputs = _strict_launch_input_binding()
    isolated = sys.flags.isolated == 1
    no_site = sys.flags.no_site == 1
    no_bytecode = sys.flags.dont_write_bytecode == 1
    safe_path = getattr(sys.flags, "safe_path", False) is True
    if not (isolated and no_site and no_bytecode and safe_path):
        raise AdaptiveChildResumeError(
            "strict execution requires fixed Python -I -S -B startup"
        )
    if (
        sys.executable != str(_STRICT_PYTHON)
        or getattr(sys, "_base_executable", None)
        != str(_STRICT_PYTHON_RESOLVED)
    ):
        raise AdaptiveChildResumeError(
            "strict execution uses the wrong Python executable"
        )
    expected_base_path = [
        str(PROJECT), "/usr/lib/python312.zip", "/usr/lib/python3.12",
        "/usr/lib/python3.12/lib-dynload",
    ]
    if type(sys.path) is not list or sys.path != expected_base_path:
        raise AdaptiveChildResumeError(
            "strict execution base sys.path differs from fixed -I -S path"
        )
    directories = [
        _strict_plain_directory(_STRICT_VENV, "venv"),
        _strict_plain_directory(_STRICT_VENV / "bin", "venv bin"),
        _strict_plain_directory(_STRICT_VENV / "lib", "venv lib"),
        _strict_plain_directory(
            _STRICT_VENV / "lib/python3.12", "venv python library",
        ),
        _strict_plain_directory(
            _STRICT_DEPENDENCY_ROOT, "dependency root",
        ),
    ]
    link_before = os.stat(_STRICT_PYTHON, follow_symlinks=False)
    if (
        not stat.S_ISLNK(link_before.st_mode)
        or link_before.st_uid != 0
        or link_before.st_nlink != 1
        or os.readlink(_STRICT_PYTHON)
        != str(_STRICT_PYTHON_RESOLVED)
        or _STRICT_PYTHON.resolve(strict=True) != _STRICT_PYTHON_RESOLVED
    ):
        raise AdaptiveChildResumeError(
            "strict venv Python symlink identity mismatch"
        )
    link_after = os.stat(_STRICT_PYTHON, follow_symlinks=False)
    if _strict_stat_identity(link_before) != _strict_stat_identity(link_after):
        raise AdaptiveChildResumeError(
            "strict venv Python symlink raced"
        )
    for path, expected, label in (
        (_STRICT_PYTHON_RESOLVED, _STRICT_PYTHON_SHA256, "Python executable"),
        (_STRICT_PYVENV_CFG, _STRICT_PYVENV_CFG_SHA256, "pyvenv.cfg"),
    ):
        info = os.stat(path, follow_symlinks=False)
        _strict_owned_read_only_entry(info, directory=False, label=label)
        if (
            info.st_nlink != 1
            or hashlib.sha256(_stable_source_bytes(path, expected)).hexdigest()
            != expected
        ):
            raise AdaptiveChildResumeError(
                f"strict {label} identity mismatch"
            )
    cfg_size = os.stat(
        _STRICT_PYVENV_CFG, follow_symlinks=False,
    ).st_size
    python_size = os.stat(
        _STRICT_PYTHON_RESOLVED, follow_symlinks=False,
    ).st_size
    cache_tag = sys.implementation.cache_tag
    soabi = sysconfig.get_config_var("SOABI")
    multiarch = sysconfig.get_config_var("MULTIARCH")
    if (
        cache_tag != "cpython-312"
        or soabi != "cpython-312-x86_64-linux-gnu"
        or multiarch != "x86_64-linux-gnu"
    ):
        raise AdaptiveChildResumeError(
            "strict Python ABI identity mismatch"
        )
    value = {
        "method": "fixed-venv-python-and-no-site-path-v1",
        "sys_executable": str(_STRICT_PYTHON),
        "base_executable": str(_STRICT_PYTHON_RESOLVED),
        "python_sha256": _STRICT_PYTHON_SHA256,
        "python_bytes": python_size,
        "pyvenv_cfg": str(_STRICT_PYVENV_CFG),
        "pyvenv_cfg_sha256": _STRICT_PYVENV_CFG_SHA256,
        "pyvenv_cfg_bytes": cfg_size,
        "dependency_root": str(_STRICT_DEPENDENCY_ROOT),
        "base_sys_path": expected_base_path,
        "cache_tag": cache_tag, "soabi": soabi, "multiarch": multiarch,
        "directories": directories,
        "isolated": True, "no_site": True, "dont_write_bytecode": True,
        "safe_path": True,
        "launch_inputs": launch_inputs,
        "dynamic_loader_environment_absent": True,
        "persistent_change_detection": True,
        "privileged_toctou_defended": False,
    }
    value["runtime_binding_sha256"] = canonical_sha256(value)
    return value


def _strict_module_from_dependency_root(module: Any) -> bool:
    source = getattr(module, "__file__", None)
    if type(source) is not str or not os.path.isabs(source):
        return False
    try:
        Path(source).relative_to(_STRICT_DEPENDENCY_ROOT)
    except ValueError:
        return False
    return True


def _strict_forbidden_modules_absent() -> None:
    present = sorted(
        name for name in _STRICT_FORBIDDEN_STARTUP_MODULES
        if name in sys.modules
    )
    if present:
        raise AdaptiveChildResumeError(
            "strict startup customization module is present: "
            + ",".join(present)
        )


def _active_strict_dependency_context(
    *, allow_derived_adoption: bool = False,
) -> dict[str, Any]:
    if type(allow_derived_adoption) is not bool:
        raise AdaptiveChildResumeError(
            "strict dependency adoption flag is malformed"
        )
    state = getattr(_STRICT_DEPENDENCY_LOCAL, "state", None)
    fields = {
        "pid", "thread", "active", "runtime_binding", "pre_tree",
        "post_tree", "pre_stdlib_tree", "post_stdlib_tree",
        "pre_stdlib_external", "post_stdlib_external", "entry_maps",
        "derived_environment", "original_sys_path", "installed_sys_path",
        "original_dont_write_bytecode", "original_pycache_prefix",
        "pycache_path", "pycache_identity",
    }
    path_valid = (
        type(sys.path) is list
        and type(state) is dict
        and sys.path == state.get("installed_sys_path")
    )
    if (
        type(state) is not dict
        or set(state) != fields
        or state.get("active") is not True
        or state.get("pid") != os.getpid()
        or state.get("thread") is not threading.current_thread()
        or not path_valid
        or sys.dont_write_bytecode is not True
        or sys.pycache_prefix != state.get("pycache_path")
    ):
        raise AdaptiveChildResumeError(
            "strict dependency context owner/lifecycle mismatch"
        )
    _strict_forbidden_modules_absent()
    derived = state["derived_environment"]
    if derived is None:
        if allow_derived_adoption:
            _require_strict_process_environment(derived=True)
            expected_filesystem = state["runtime_binding"][
                "launch_inputs"
            ]["filesystem"]
            if not json_type_equal(
                _strict_launch_filesystem_binding(), expected_filesystem,
            ):
                raise AdaptiveChildResumeError(
                    "strict launch filesystem changed before science adoption"
                )
        elif not json_type_equal(
            _strict_launch_input_binding(),
            state["runtime_binding"]["launch_inputs"],
        ):
            raise AdaptiveChildResumeError(
                "strict launch inputs changed within dependency context"
            )
    elif not json_type_equal(
        _strict_derived_environment_binding(
            derived.get("writer_source") if type(derived) is dict else None
        ),
        derived,
    ):
        raise AdaptiveChildResumeError(
            "strict derived environment changed within dependency context"
        )
    pycache = Path(state["pycache_path"])
    if (
        not json_type_equal(
            state["pycache_identity"],
            _directory_identity(pycache, require_mode_0700=True),
        )
        or any(pycache.iterdir())
    ):
        raise AdaptiveChildResumeError(
            "strict private pycache is not stable and empty"
        )
    return state


def _adopt_strict_derived_environment(
    executed_sources: Any,
) -> dict[str, Any] | None:
    writer_source = _strict_derived_env_writer_from_executed_sources(
        executed_sources
    )
    if getattr(_STRICT_DEPENDENCY_LOCAL, "state", None) is None:
        return None
    state = _active_strict_dependency_context(
        allow_derived_adoption=True,
    )
    observed = _strict_derived_environment_binding(writer_source)
    if state["derived_environment"] is None:
        state["derived_environment"] = observed
    elif not json_type_equal(state["derived_environment"], observed):
        raise AdaptiveChildResumeError(
            "strict derived environment differs across science loads"
        )
    return dict(state["derived_environment"])


def _verify_strict_dependency_post_import() -> dict[str, Any]:
    state = _active_strict_dependency_context()
    if state["post_tree"] is None:
        for name, module in tuple(sys.modules.items()):
            if not _strict_module_from_dependency_root(module):
                continue
            source = getattr(module, "__file__", "")
            loader = getattr(getattr(module, "__spec__", None), "loader", None)
            cached = getattr(module, "__cached__", None)
            if (
                source.endswith(".pyc")
                or type(loader).__name__ == "SourcelessFileLoader"
                or (
                    cached is not None
                    and (
                        type(cached) is not str
                        or not cached.startswith(state["pycache_path"] + os.sep)
                        or os.path.lexists(cached)
                    )
                )
            ):
                raise AdaptiveChildResumeError(
                    f"strict dependency module used bytecode: {name}"
                )
        observed = _verified_strict_dependency_tree()
        observed_stdlib = _verified_strict_stdlib_tree()
        observed_external = _strict_stdlib_external_target_binding()
        if (
            not json_type_equal(observed, state["pre_tree"])
            or not json_type_equal(
                observed_stdlib, state["pre_stdlib_tree"],
            )
            or not json_type_equal(
                observed_external, state["pre_stdlib_external"],
            )
        ):
            raise AdaptiveChildResumeError(
                "strict site/stdlib trees changed across science imports"
            )
        state["post_tree"] = observed
        state["post_stdlib_tree"] = observed_stdlib
        state["post_stdlib_external"] = observed_external
    return dict(state["post_tree"])


@contextlib.contextmanager
def _strict_dependency_context() -> Iterator[None]:
    if getattr(_STRICT_DEPENDENCY_LOCAL, "state", None) is not None:
        raise AdaptiveChildResumeError(
            "nested strict dependency contexts are forbidden"
        )
    _strict_forbidden_modules_absent()
    if any(
        _strict_module_from_dependency_root(module)
        for module in tuple(sys.modules.values())
    ):
        raise AdaptiveChildResumeError(
            "strict dependency modules were loaded before authentication"
        )
    runtime_binding = _strict_runtime_binding()
    pre_tree = _verified_strict_dependency_tree()
    pre_stdlib_tree = _verified_strict_stdlib_tree()
    pre_stdlib_external = _strict_stdlib_external_target_binding()
    entry_maps = _read_proc_maps()
    original_sys_path = list(sys.path)
    original_dont_write_bytecode = sys.dont_write_bytecode
    original_pycache_prefix = sys.pycache_prefix
    dependency_text = str(_STRICT_DEPENDENCY_ROOT)
    if dependency_text in original_sys_path:
        raise AdaptiveChildResumeError(
            "strict dependency root was present before authentication"
        )
    pycache = Path(tempfile.mkdtemp(
        prefix="paper400-v5-pycache-", dir="/tmp",
    ))
    os.chmod(pycache, 0o700, follow_symlinks=False)
    pycache_identity = _directory_identity(
        pycache, require_mode_0700=True,
    )
    if any(pycache.iterdir()):
        raise AdaptiveChildResumeError(
            "new strict private pycache is not empty"
        )
    installed_sys_path = [
        item for item in original_sys_path
        if item != str(_STRICT_PYTHON_ZIP)
    ] + [dependency_text]
    state = {
        "pid": os.getpid(), "thread": threading.current_thread(),
        "active": True, "runtime_binding": runtime_binding,
        "pre_tree": pre_tree, "post_tree": None,
        "pre_stdlib_tree": pre_stdlib_tree, "post_stdlib_tree": None,
        "pre_stdlib_external": pre_stdlib_external,
        "post_stdlib_external": None, "entry_maps": entry_maps,
        "derived_environment": None,
        "original_sys_path": original_sys_path,
        "installed_sys_path": installed_sys_path,
        "original_dont_write_bytecode": original_dont_write_bytecode,
        "original_pycache_prefix": original_pycache_prefix,
        "pycache_path": str(pycache),
        "pycache_identity": pycache_identity,
    }
    _STRICT_DEPENDENCY_LOCAL.state = state
    try:
        sys.dont_write_bytecode = True
        sys.pycache_prefix = str(pycache)
        sys.path[:] = installed_sys_path
        _active_strict_dependency_context()
        yield
    finally:
        environment_error: BaseException | None = None
        try:
            if state["derived_environment"] is None:
                _require_strict_process_environment(derived=False)
            elif not json_type_equal(
                _strict_derived_environment_binding(
                    state["derived_environment"].get("writer_source")
                    if type(state["derived_environment"]) is dict else None
                ),
                state["derived_environment"],
            ):
                raise AdaptiveChildResumeError(
                    "derived native environment changed before context exit"
                )
        except BaseException as exc:
            environment_error = exc
        finally:
            for key in list(_strict_environment_snapshot()):
                os.environ.pop(key, None)
            try:
                _require_strict_process_environment(derived=False)
            except BaseException as exc:
                if environment_error is None:
                    environment_error = exc
        state["active"] = False
        sys.path = list(original_sys_path)
        sys.dont_write_bytecode = original_dont_write_bytecode
        sys.pycache_prefix = original_pycache_prefix
        if getattr(_STRICT_DEPENDENCY_LOCAL, "state", None) is state:
            delattr(_STRICT_DEPENDENCY_LOCAL, "state")
        if not json_type_equal(
            pycache_identity,
            _directory_identity(pycache, require_mode_0700=True),
        ):
            raise AdaptiveChildResumeError(
                "strict private pycache identity changed before cleanup"
            )
        if any(pycache.iterdir()):
            raise AdaptiveChildResumeError(
                "strict private pycache is not empty at cleanup"
            )
        os.rmdir(pycache)
        if environment_error is not None:
            raise environment_error


def _directory_identity(path: Path, *, require_mode_0700: bool) -> dict[str, Any]:
    target = Path(path)
    if not target.is_absolute() or str(target) != os.path.abspath(str(target)):
        raise AdaptiveChildResumeError("directory path must be normalized absolute")
    try:
        lexical = os.stat(target, follow_symlinks=False)
        resolved = target.resolve(strict=True)
    except (OSError, RuntimeError) as exc:
        raise AdaptiveChildResumeError(f"cannot resolve directory: {target}") from exc
    if (
        resolved != target or stat.S_ISLNK(lexical.st_mode)
        or not stat.S_ISDIR(lexical.st_mode) or lexical.st_uid != os.geteuid()
        or (require_mode_0700 and stat.S_IMODE(lexical.st_mode) != 0o700)
    ):
        raise AdaptiveChildResumeError("directory identity/ownership/mode mismatch")
    return {
        "path": str(target), "device": lexical.st_dev, "inode": lexical.st_ino,
        "uid": lexical.st_uid, "mode": stat.S_IMODE(lexical.st_mode),
    }


def _new_root(root: Path) -> Path:
    target = Path(root)
    if not target.is_absolute() or str(target) != os.path.abspath(str(target)):
        raise AdaptiveChildResumeError("root must be normalized absolute")
    if target.exists() or target.is_symlink():
        raise AdaptiveChildResumeError("new root already exists")
    parent = target.parent.resolve(strict=True)
    if parent != target.parent or target.parent.is_symlink():
        raise AdaptiveChildResumeError("root parent is aliased")
    os.mkdir(target, 0o700)
    os.chmod(target, 0o700, follow_symlinks=False)
    descriptor = os.open(parent, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    _directory_identity(target, require_mode_0700=True)
    return target


def _existing_root(root: Path) -> Path:
    _directory_identity(Path(root), require_mode_0700=True)
    return Path(root)


def _mkdir(parent: Path, name: str) -> None:
    if not name or "/" in name or name in {".", ".."}:
        raise AdaptiveChildResumeError("unsafe directory component")
    os.mkdir(parent / name, 0o700)
    descriptor = os.open(parent, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


class _TransferableRootLock:
    """EX/NB outer lock whose open-file-description can move into switch-v4."""

    __slots__ = (
        "root", "_root_identity", "_lock_identity", "_fd", "_entered",
        "_transferred",
    )

    def __init__(self, root: Path) -> None:
        self.root = _existing_root(root)
        self._root_identity: dict[str, Any] | None = None
        self._lock_identity: dict[str, Any] | None = None
        self._fd = -1
        self._entered = False
        self._transferred = False

    def __enter__(self) -> "_TransferableRootLock":
        if self._entered:
            raise AdaptiveChildResumeError("transferable root lock reused")
        self._root_identity = _directory_identity(
            self.root, require_mode_0700=True,
        )
        self._lock_identity = _lock_identity(self.root)
        descriptor = os.open(
            self.root / ROOT_LOCK,
            os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW,
        )
        try:
            observed = os.fstat(descriptor)
            if (
                observed.st_dev, observed.st_ino
            ) != (
                self._lock_identity["device"],
                self._lock_identity["inode"],
            ):
                raise AdaptiveChildResumeError(
                    "transferable outer lock changed before acquire"
                )
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BaseException:
            os.close(descriptor)
            raise
        self._fd = descriptor
        self._entered = True
        return self

    def fileno(self) -> int:
        if not self._entered or self._transferred or self._fd < 0:
            raise AdaptiveChildResumeError(
                "transferable outer lock has no owned descriptor"
            )
        return self._fd

    def validated_transfer_fd(self) -> int:
        if (
            not self._entered or self._transferred or self._fd < 0
            or not json_type_equal(
                self._root_identity,
                _directory_identity(self.root, require_mode_0700=True),
            )
            or not json_type_equal(
                self._lock_identity, _lock_identity(self.root),
            )
        ):
            raise AdaptiveChildResumeError("outer lock transfer mismatch")
        observed = os.fstat(self._fd)
        if (
            observed.st_dev, observed.st_ino
        ) != (
            self._lock_identity["device"], self._lock_identity["inode"],
        ):
            raise AdaptiveChildResumeError(
                "outer lock descriptor changed before transfer"
            )
        return self._fd

    def complete_transfer(self) -> None:
        descriptor = self.validated_transfer_fd()
        # switch-v4 dup() now owns the same open-file-description.  Closing
        # this reference preserves flock through its duplicate; LOCK_UN here
        # would incorrectly unlock both references.
        self._fd = -1
        self._transferred = True
        os.close(descriptor)

    def __exit__(self, exc_type: Any, exc: Any, traceback: Any) -> None:
        del exc_type, exc, traceback
        if not self._entered:
            return
        if self._transferred:
            return
        descriptor = self._fd
        self._fd = -1
        try:
            if (
                not json_type_equal(
                    self._root_identity,
                    _directory_identity(self.root, require_mode_0700=True),
                )
                or not json_type_equal(
                    self._lock_identity, _lock_identity(self.root),
                )
            ):
                raise AdaptiveChildResumeError(
                    "root changed while transferable lock held"
                )
        finally:
            with contextlib.suppress(OSError):
                fcntl.flock(descriptor, fcntl.LOCK_UN)
            os.close(descriptor)


def _relinquish_adopted_outer_locks(
    outer_locks: Sequence[Any], outer_fds: Sequence[int], *,
    exact_transferable_locks: bool,
) -> None:
    """Drop all caller OFD references without any partial LOCK_UN window."""

    if exact_transferable_locks:
        # v4 already dup'ed every descriptor. Mark all wrappers transferred
        # before the first close, because close itself may fail.
        for lock in outer_locks:
            lock._transferred = True
        for lock in outer_locks:
            lock._fd = -1
        failures: list[str] = []
        for descriptor in outer_fds:
            try:
                os.close(descriptor)
            except OSError as exc:
                failures.append(f"fd {descriptor}: {exc}")
        if failures:
            raise AdaptiveChildResumeError(
                "adopted caller descriptor close failed after complete "
                "v4 adoption: " + "; ".join(failures)
            )
        return

    # Unit-test seam only. Strict CLI constructs exact lock objects internally.
    for lock in outer_locks:
        lock.complete_transfer()


def _initialize_outer_lock(root: Path) -> None:
    descriptor = os.open(
        root / ROOT_LOCK,
        os.O_RDWR | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW,
        0o600,
    )
    try:
        os.fchmod(descriptor, 0o600)
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _lock_identity(root: Path) -> dict[str, Any]:
    info = os.stat(root / ROOT_LOCK, follow_symlinks=False)
    if (
        not stat.S_ISREG(info.st_mode) or stat.S_IMODE(info.st_mode) != 0o600
        or info.st_uid != os.geteuid() or info.st_nlink != 1 or info.st_size != 0
    ):
        raise AdaptiveChildResumeError("outer lock identity mismatch")
    return {
        "relative_path": ROOT_LOCK.as_posix(), "device": info.st_dev,
        "inode": info.st_ino, "uid": info.st_uid, "mode": 0o600,
        "links": 1, "bytes": 0,
    }


@contextlib.contextmanager
def _root_lock(root: Path, *, exclusive: bool) -> Iterator[None]:
    before_root = _directory_identity(root, require_mode_0700=True)
    before_lock = _lock_identity(root)
    descriptor = os.open(root / ROOT_LOCK, os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        observed = os.fstat(descriptor)
        if (observed.st_dev, observed.st_ino) != (
            before_lock["device"], before_lock["inode"],
        ):
            raise AdaptiveChildResumeError("outer lock changed before acquire")
        operation = fcntl.LOCK_EX if exclusive else fcntl.LOCK_SH
        try:
            fcntl.flock(descriptor, operation | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise AdaptiveChildResumeError("outer lock is busy") from exc
        yield
        if (
            not json_type_equal(
                before_root, _directory_identity(root, require_mode_0700=True)
            ) or not json_type_equal(before_lock, _lock_identity(root))
        ):
            raise AdaptiveChildResumeError("root or outer lock changed while held")
    finally:
        with contextlib.suppress(OSError):
            fcntl.flock(descriptor, fcntl.LOCK_UN)
        os.close(descriptor)


def _publish_bytes(path: Path, payload: bytes, *, mode: int = 0o600) -> None:
    controller._atomic_publish(path, payload, mode=mode)


def _publish_json(path: Path, value: Mapping[str, Any]) -> None:
    _publish_bytes(path, canonical_bytes(dict(value)) + b"\n")


def _safe_root_path(root: Path, relative: Path, *, require_file: bool = True) -> Path:
    if relative.is_absolute() or not relative.parts or ".." in relative.parts:
        raise AdaptiveChildResumeError("unsafe root-relative path")
    cursor = root
    for component in relative.parts[:-1]:
        cursor = cursor / component
        info = os.stat(cursor, follow_symlinks=False)
        if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
            raise AdaptiveChildResumeError("root-relative ancestor is not plain")
    target = root.joinpath(*relative.parts)
    if require_file:
        info = os.stat(target, follow_symlinks=False)
        if stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode):
            raise AdaptiveChildResumeError("root-relative target is not a plain file")
    return target


def _stream_record(
    path: Path, *, cap: int, root: Path | None = None, role: str,
) -> dict[str, Any]:
    if type(cap) is not int or not 1 <= cap <= MAX_PROOF_BYTES:
        raise AdaptiveChildResumeError(f"invalid streaming cap for {role}")
    candidate = Path(path)
    if root is not None:
        relative = candidate.relative_to(root)
        candidate = _safe_root_path(root, relative)
    flags = os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW
    descriptor = os.open(candidate, flags)
    try:
        before = os.fstat(descriptor)
        if (
            not stat.S_ISREG(before.st_mode) or before.st_size > cap
            or before.st_uid != os.geteuid() or before.st_nlink != 1
        ):
            raise AdaptiveChildResumeError(f"bounded file identity failed for {role}")
        digest = hashlib.sha256()
        total = 0
        while True:
            chunk = os.read(descriptor, HASH_CHUNK_BYTES)
            if not chunk:
                break
            total += len(chunk)
            if total > cap:
                raise AdaptiveChildResumeError(f"stream cap exceeded for {role}")
            digest.update(chunk)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    identity = lambda info: (
        info.st_dev, info.st_ino, info.st_mode, info.st_uid, info.st_nlink,
        info.st_size, info.st_mtime_ns, info.st_ctime_ns,
    )
    if identity(before) != identity(after) or total != before.st_size:
        raise AdaptiveChildResumeError(f"file changed while streaming for {role}")
    record = {
        "role": role, "sha256": digest.hexdigest(), "bytes": total,
        "device": before.st_dev, "inode": before.st_ino, "uid": before.st_uid,
        "mode": stat.S_IMODE(before.st_mode), "links": before.st_nlink,
    }
    if root is None:
        record["path"] = str(candidate.resolve(strict=True))
    else:
        record["relative_path"] = candidate.relative_to(root).as_posix()
    return record


def _read_bounded(path: Path, *, cap: int, root: Path | None, role: str) -> bytes:
    record = _stream_record(path, cap=cap, root=root, role=role)
    descriptor = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        payload = bytearray()
        while len(payload) <= cap:
            chunk = os.read(descriptor, min(1 << 20, cap + 1 - len(payload)))
            if not chunk:
                break
            payload.extend(chunk)
    finally:
        os.close(descriptor)
    result = bytes(payload)
    if len(result) != record["bytes"] or hashlib.sha256(result).hexdigest() != record["sha256"]:
        raise AdaptiveChildResumeError(f"file changed during bounded read for {role}")
    return result


def _read_json(path: Path, *, root: Path) -> dict[str, Any]:
    payload = _read_bounded(path, cap=MAX_JSON_BYTES, root=root, role="strict-json")
    def object_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise AdaptiveChildResumeError(f"duplicate JSON key: {key}")
            result[key] = value
        return result
    try:
        value = json.loads(
            payload.decode("ascii"), object_pairs_hook=object_pairs,
            parse_constant=lambda item: (_ for _ in ()).throw(
                AdaptiveChildResumeError(f"non-finite JSON constant: {item}")
            ),
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise AdaptiveChildResumeError(f"invalid JSON: {path}") from exc
    if type(value) is not dict or payload != canonical_bytes(value) + b"\n":
        raise AdaptiveChildResumeError(f"JSON is not canonical object: {path}")
    return value


def _stream_copy(
    source: Path, destination: Path, *, cap: int, expected: Mapping[str, Any] | None,
) -> dict[str, Any]:
    source_fd = os.open(source, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    destination_fd = os.open(
        destination,
        os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW,
        0o600,
    )
    try:
        before = os.fstat(source_fd)
        if not stat.S_ISREG(before.st_mode) or before.st_size > cap:
            raise AdaptiveChildResumeError("stream-copy source exceeds cap")
        digest = hashlib.sha256()
        total = 0
        while True:
            chunk = os.read(source_fd, HASH_CHUNK_BYTES)
            if not chunk:
                break
            total += len(chunk)
            if total > cap:
                raise AdaptiveChildResumeError("stream-copy source exceeds cap")
            digest.update(chunk)
            view = memoryview(chunk)
            while view:
                count = os.write(destination_fd, view)
                if count <= 0:
                    raise AdaptiveChildResumeError("short stream-copy write")
                view = view[count:]
        os.fsync(destination_fd)
        after = os.fstat(source_fd)
    finally:
        os.close(source_fd)
        os.close(destination_fd)
    identity = lambda info: (
        info.st_dev, info.st_ino, info.st_mode, info.st_uid, info.st_nlink,
        info.st_size, info.st_mtime_ns, info.st_ctime_ns,
    )
    digest_value = digest.hexdigest()
    if identity(before) != identity(after) or total != before.st_size:
        raise AdaptiveChildResumeError("stream-copy source changed")
    if expected is not None and (
        expected.get("sha256") != digest_value or expected.get("bytes") != total
    ):
        raise AdaptiveChildResumeError("stream-copy expected hash/size mismatch")
    return _stream_record(destination, cap=cap, root=None, role="private-copy")


def _publish_stream(
    source: Path, destination: Path, *, cap: int,
    expected: Mapping[str, Any], root: Path,
) -> dict[str, Any]:
    """Publish a streamed artifact and leave exactly one immutable hardlink."""

    private = destination.parent / f".{destination.name}.private-{uuid.uuid4().hex}"
    linked = False
    try:
        _stream_copy(source, private, cap=cap, expected=expected)
        os.link(private, destination, follow_symlinks=False)
        linked = True
        # Remove the private name before checking the final single-link identity.
        private.unlink()
        descriptor = os.open(
            destination.parent,
            os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW,
        )
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
        result = _stream_record(
            destination, cap=cap, root=root, role=expected["role"],
        )
        if (
            result["sha256"] != expected["sha256"]
            or result["bytes"] != expected["bytes"]
            or result["links"] != 1
        ):
            raise AdaptiveChildResumeError("published stream binding mismatch")
        return result
    except FileExistsError as exc:
        raise AdaptiveChildResumeError(
            f"immutable artifact already exists: {destination}"
        ) from exc
    finally:
        with contextlib.suppress(FileNotFoundError):
            private.unlink()
        if linked:
            descriptor = os.open(
                destination.parent,
                os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW,
            )
            try:
                os.fsync(descriptor)
            finally:
                os.close(descriptor)

def _fsync_plain_directory(path: Path) -> None:
    _directory_identity(Path(path), require_mode_0700=True)
    descriptor = os.open(
        path,
        os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW,
    )
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _new_terminal_staging(root: Path) -> Path:
    name = f"{TERMINAL_STAGING_PREFIX}{uuid.uuid4().hex}"
    _mkdir(root, name)
    staging = root / name
    _directory_identity(staging, require_mode_0700=True)
    return staging


def _discard_terminal_staging(root: Path, staging: Path) -> None:
    # Best effort over an exact freshly-created direct child. Unknown entries
    # are never traversed/deleted; an unclean orphan remains non-authoritative.
    if (
        staging.parent != root
        or not staging.name.startswith(TERMINAL_STAGING_PREFIX)
    ):
        return
    try:
        _directory_identity(staging, require_mode_0700=True)
    except (OSError, AdaptiveChildResumeError):
        return
    for name in TERMINAL_BUNDLE_FILES:
        candidate = staging / name
        try:
            info = os.stat(candidate, follow_symlinks=False)
            if stat.S_ISREG(info.st_mode) and info.st_uid == os.geteuid():
                candidate.unlink()
        except FileNotFoundError:
            pass
        except OSError:
            pass
    with contextlib.suppress(OSError):
        staging.rmdir()
    with contextlib.suppress(OSError, AdaptiveChildResumeError):
        _fsync_plain_directory(root)


def _rebased_terminal_artifact(
    value: Mapping[str, Any], *, staged_relative: Path,
    final_relative: Path, role: str,
) -> dict[str, Any]:
    fields = {
        "role", "sha256", "bytes", "device", "inode", "uid",
        "mode", "links", "relative_path",
    }
    if (
        type(value) is not dict or set(value) != fields
        or value.get("role") != role
        or not _is_sha256(value.get("sha256"))
        or type(value.get("bytes")) is not int or value["bytes"] <= 0
        or any(
            type(value.get(field)) is not int
            for field in ("device", "inode", "uid", "mode", "links")
        )
        or value["uid"] != os.geteuid()
        or value["mode"] != 0o600 or value["links"] != 1
        or value["relative_path"] != staged_relative.as_posix()
        or final_relative.parent != TERMINAL_BUNDLE
        or final_relative.name not in TERMINAL_BUNDLE_FILES
    ):
        raise AdaptiveChildResumeError(
            f"staged {role} artifact identity mismatch"
        )
    result = dict(value)
    result["relative_path"] = final_relative.as_posix()
    return result


def _commit_terminal_bundle(root: Path, staging: Path) -> Path:
    if (
        staging.parent != root
        or not staging.name.startswith(TERMINAL_STAGING_PREFIX)
    ):
        raise AdaptiveChildResumeError("terminal staging path mismatch")
    entries = list(staging.iterdir())
    if {item.name for item in entries} != TERMINAL_BUNDLE_FILES:
        raise AdaptiveChildResumeError(
            "terminal staging is not the exact five-file bundle"
        )
    for item in entries:
        info = os.stat(item, follow_symlinks=False)
        if (
            stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode)
            or info.st_uid != os.geteuid()
            or stat.S_IMODE(info.st_mode) != 0o600
            or info.st_nlink != 1
        ):
            raise AdaptiveChildResumeError(
                "terminal staging contains a non-canonical file"
            )
    final = root / TERMINAL_BUNDLE
    _validate_new_output_path(final, label="terminal bundle")
    before = _directory_identity(staging, require_mode_0700=True)
    _fsync_plain_directory(staging)
    os.rename(staging, final)
    _fsync_plain_directory(root)
    after = _directory_identity(final, require_mode_0700=True)
    for field in ("device", "inode", "uid", "mode"):
        if before[field] != after[field]:
            raise AdaptiveChildResumeError(
                "terminal bundle identity changed across atomic rename"
            )
    return final


_CLI_REPLAY_LOCAL = threading.local()
_CLI_REPLAY_STATE_FIELDS = frozenset({
    "pid", "thread", "active", "poisoned", "stack",
    "science_modules", "science_switch", "science_loader",
    "science_loader_code", "science_source_record",
    "science_executed_sources", "instance_binding",
    "campaign_binding", "overlay_cache", "switch_cache",
})


@contextlib.contextmanager
def _cli_replay_scope() -> Iterator[None]:
    """Bound pure replay reuse to one process, thread, and CLI invocation."""

    if getattr(_CLI_REPLAY_LOCAL, "state", None) is not None:
        raise AdaptiveChildResumeError(
            "nested CLI replay scopes are forbidden"
        )
    stack = contextlib.ExitStack()
    state = {
        "pid": os.getpid(),
        "thread": threading.current_thread(),
        "active": True,
        "poisoned": False,
        "stack": stack,
        "science_modules": None,
        "science_switch": None,
        "science_loader": None,
        "science_loader_code": None,
        "science_source_record": None,
        "science_executed_sources": None,
        "instance_binding": None,
        "campaign_binding": None,
        "overlay_cache": {},
        "switch_cache": {},
    }
    _CLI_REPLAY_LOCAL.state = state
    try:
        with stack:
            yield
    finally:
        state["active"] = False
        state["science_modules"] = None
        state["science_switch"] = None
        state["science_loader"] = None
        state["science_loader_code"] = None
        state["science_source_record"] = None
        state["science_executed_sources"] = None
        state["instance_binding"] = None
        state["campaign_binding"] = None
        state["overlay_cache"].clear()
        state["switch_cache"].clear()
        if getattr(_CLI_REPLAY_LOCAL, "state", None) is state:
            delattr(_CLI_REPLAY_LOCAL, "state")


def _active_cli_replay_scope() -> dict[str, Any] | None:
    state = getattr(_CLI_REPLAY_LOCAL, "state", None)
    if state is None:
        return None
    if (
        type(state) is not dict
        or set(state) != _CLI_REPLAY_STATE_FIELDS
        or state.get("active") is not True
        or state.get("pid") != os.getpid()
        or state.get("thread") is not threading.current_thread()
    ):
        if type(state) is dict:
            state["poisoned"] = True
        raise AdaptiveChildResumeError(
            "CLI replay scope owner/lifecycle mismatch"
        )
    if state.get("poisoned") is not False:
        raise AdaptiveChildResumeError("CLI replay scope is poisoned")
    return state


def _poison_cli_replay_scope(state: dict[str, Any] | None) -> None:
    if type(state) is dict:
        state["poisoned"] = True


def _validated_science_source_record(
    value: Any, *, expected_execution: str,
) -> bytes:
    if (
        type(value) is not dict
        or set(value) != {
            "role", "relative_path", "sha256", "bytes", "execution",
        }
        or value.get("role") != "adaptive_leaf_overlay_v2_source"
        or value.get("relative_path")
        != "investigations/paper400_dic5_adaptive_leaf_overlay_v2.py"
        or not _is_sha256(value.get("sha256"))
        or type(value.get("bytes")) is not int
        or value.get("bytes") < 1
        or value.get("execution") != expected_execution
    ):
        raise AdaptiveChildResumeError(
            "switch-v4 overlay source record is malformed"
        )
    payload = _stable_source_bytes(
        PROJECT / value["relative_path"], value["sha256"],
    )
    if len(payload) != value["bytes"]:
        raise AdaptiveChildResumeError(
            "switch-v4 overlay source byte count changed"
        )
    return canonical_bytes(value)


def _validated_executed_sources(value: Any) -> bytes:
    if type(value) is not list or len(value) < 4:
        raise AdaptiveChildResumeError(
            "switch-v4 executed source closure is malformed"
        )
    seen_modules: set[str] = set()
    for record in value:
        if (
            type(record) is not dict
            or set(record) != {
                "module", "path", "sha256", "bytes",
                "externally_bound", "execution",
            }
            or type(record.get("module")) is not str
            or record["module"] in seen_modules
            or type(record.get("path")) is not str
            or not _is_sha256(record.get("sha256"))
            or type(record.get("bytes")) is not int
            or record["bytes"] < 1
            or type(record.get("externally_bound")) is not bool
            or record.get("execution") != "compile-exact-source-bytes-v4"
        ):
            raise AdaptiveChildResumeError(
                "switch-v4 executed source record is malformed"
            )
        seen_modules.add(record["module"])
        path = Path(record["path"])
        try:
            path.relative_to(PROJECT)
        except ValueError as exc:
            raise AdaptiveChildResumeError(
                "executed source escapes project"
            ) from exc
        payload = _stable_source_bytes(path, record["sha256"])
        if len(payload) != record["bytes"]:
            raise AdaptiveChildResumeError(
                "executed source byte count changed"
            )
    return canonical_bytes(value)


def _science_modules_impl(
    switch_evidence: Mapping[str, Any],
) -> tuple[tuple[Any, Any, Any, Any], list[dict[str, Any]]]:
    """Execute once per CLI while freshly hashing every executed source."""

    state = _active_cli_replay_scope()
    switch = _switch_v4_module(_SWITCH_V4_SOURCE_SHA256)
    record_source_bytes = _switch_record_overlay_source(switch_evidence)
    serialized_source_record = json.loads(
        record_source_bytes.decode("ascii")
    )
    serialized_source_identity = canonical_bytes({
        key: value for key, value in serialized_source_record.items()
        if key != "execution"
    })
    loader = getattr(switch, "_load_overlay_exact", None)
    if not callable(loader):
        raise AdaptiveChildResumeError(
            "switch-v4 exact overlay loader is absent"
        )
    if state is not None and state["science_modules"] is not None:
        try:
            if (
                state["science_switch"] is not switch
                or state["science_loader"] is not loader
                or state["science_loader_code"] is not loader.__code__
            ):
                raise AdaptiveChildResumeError(
                    "cached exact science loader identity changed"
                )
            source_record = json.loads(
                state["science_source_record"].decode("ascii")
            )
            executed_sources = json.loads(
                state["science_executed_sources"].decode("ascii")
            )
            if (
                _validated_science_source_record(
                    source_record,
                    expected_execution="compile-exact-source-bytes-v4",
                )
                != state["science_source_record"]
                or canonical_bytes({
                    key: value for key, value in source_record.items()
                    if key != "execution"
                }) != serialized_source_identity
                or _validated_executed_sources(executed_sources)
                != state["science_executed_sources"]
            ):
                raise AdaptiveChildResumeError(
                    "cached exact science source closure changed"
                )
            return state["science_modules"], executed_sources
        except Exception:
            _poison_cli_replay_scope(state)
            raise

    overlay, source_record, executed_sources = loader()
    try:
        source_bytes = _validated_science_source_record(
            source_record,
            expected_execution="compile-exact-source-bytes-v4",
        )
        if canonical_bytes({
            key: value for key, value in source_record.items()
            if key != "execution"
        }) != serialized_source_identity:
            raise AdaptiveChildResumeError(
                "switch record overlay source differs from exact loader"
            )
        executed_bytes = _validated_executed_sources(executed_sources)
        canonical_executed_sources = json.loads(
            executed_bytes.decode("ascii")
        )
        modules = (
            overlay, overlay.width10, overlay.adaptive, overlay.cube16
        )
    except Exception:
        _poison_cli_replay_scope(state)
        raise
    if state is not None:
        state["science_modules"] = modules
        state["science_switch"] = switch
        state["science_loader"] = loader
        state["science_loader_code"] = loader.__code__
        state["science_source_record"] = source_bytes
        state["science_executed_sources"] = executed_bytes
    return modules, canonical_executed_sources


def _normalize_strict_science_sys_path() -> None:
    dependency_state = getattr(_STRICT_DEPENDENCY_LOCAL, "state", None)
    if dependency_state is None:
        return
    installed = dependency_state.get("installed_sys_path")
    if type(sys.path) is not list or type(installed) is not list:
        raise AdaptiveChildResumeError(
            "science loader changed strict sys.path type"
        )
    project_count = 0
    while (
        project_count < len(sys.path)
        and sys.path[project_count] == str(PROJECT)
    ):
        project_count += 1
    if (
        not 1 <= project_count <= 8
        or sys.path[project_count:] != installed[1:]
    ):
        raise AdaptiveChildResumeError(
            "science loader changed strict sys.path outside pinned project"
        )
    sys.path[:] = installed


def _science_modules(
    switch_evidence: Mapping[str, Any],
) -> tuple[Any, Any, Any, Any]:
    if getattr(_STRICT_DEPENDENCY_LOCAL, "state", None) is not None:
        _active_strict_dependency_context()
    _normalize_strict_science_sys_path()
    try:
        modules, executed_sources = _science_modules_impl(switch_evidence)
    finally:
        _normalize_strict_science_sys_path()
    _adopt_strict_derived_environment(executed_sources)
    return modules


def _strict_scoped_instance(
    modules: tuple[Any, Any, Any, Any],
) -> Any:
    if getattr(_STRICT_DEPENDENCY_LOCAL, "state", None) is not None:
        _active_strict_dependency_context()
    state = _active_cli_replay_scope()
    builder = modules[1].cube16.optimized.build_optimized_instance
    if state is None:
        return builder()
    binding = state["instance_binding"]
    try:
        if binding is None:
            instance = builder()
            fingerprint = modules[0]._instance_replay_fingerprint(
                instance, strict_base=True,
            )
            state["instance_binding"] = {
                "modules": modules,
                "builder": builder,
                "builder_code": builder.__code__,
                "instance": instance,
                "fingerprint": fingerprint,
            }
            return instance
        if (
            type(binding) is not dict
            or any(
                left is not right
                for left, right in zip(
                    binding["modules"], modules, strict=True
                )
            )
            or binding["builder"] is not builder
            or binding["builder_code"] is not builder.__code__
            or modules[0]._instance_replay_fingerprint(
                binding["instance"], strict_base=True,
            ) != binding["fingerprint"]
        ):
            raise AdaptiveChildResumeError(
                "CLI replay optimized instance binding changed"
            )
        return binding["instance"]
    except Exception:
        _poison_cli_replay_scope(state)
        raise


_SWITCH_V4_CACHE: dict[str, Any] = {}


def _switch_record_overlay_source(record: Mapping[str, Any]) -> bytes:
    """Parse real v2 switch-record provenance without selecting v4 code."""

    binding = record.get("source_binding") if type(record) is dict else None
    fields = {
        "schema_version", "method", "legacy_project", "legacy_sources",
        "legacy_executed_source_closure", "current_sources",
        "overlay_executed_source_closure",
        "sitecustomize_imported_by_loader",
        "pyc_executed_by_loader", "source_binding_sha256",
    }
    if (
        type(binding) is not dict or set(binding) != fields
        or binding.get("schema_version") != 2
        or type(binding.get("schema_version")) is not int
        or binding.get("method")
        != "manifest-pinned-source-bytes-compile-exec-no-pyc-v2"
        or type(binding.get("legacy_project")) is not str
        or type(binding.get("legacy_sources")) is not list
        or type(binding.get("legacy_executed_source_closure")) is not list
        or type(binding.get("overlay_executed_source_closure")) is not list
        or binding.get("sitecustomize_imported_by_loader") is not False
        or binding.get("pyc_executed_by_loader") is not False
        or not _is_sha256(binding.get("source_binding_sha256"))
    ):
        raise AdaptiveChildResumeError(
            "switch record source binding is not the real v2 schema"
        )
    unsigned = dict(binding)
    stored = unsigned.pop("source_binding_sha256")
    if canonical_sha256(unsigned) != stored:
        raise AdaptiveChildResumeError(
            "switch record source binding self-hash mismatch"
        )
    sources = binding["current_sources"]
    if type(sources) is not list or len(sources) != 2:
        raise AdaptiveChildResumeError(
            "switch record current source list is not exact"
        )
    v2_source, overlay_source = sources
    if (
        type(v2_source) is not dict
        or set(v2_source) != {"role", "relative_path", "sha256"}
        or v2_source.get("role")
        != "adaptive_switch_evidence_v2_source"
        or v2_source.get("relative_path")
        != _SWITCH_V2_RELATIVE.as_posix()
        or v2_source.get("sha256") != _SWITCH_V2_SOURCE_SHA256
    ):
        raise AdaptiveChildResumeError(
            "switch record misses the frozen v2 source pin"
        )
    try:
        return _validated_science_source_record(
            overlay_source,
            expected_execution="compile-exact-source-bytes-v3",
        )
    except Exception as exc:
        raise AdaptiveChildResumeError(
            "switch record overlay source binding is invalid"
        ) from exc


def _verify_exact_switch_module(module: Any) -> None:
    _stable_source_bytes(_SWITCH_V2_SOURCE, _SWITCH_V2_SOURCE_SHA256)
    _stable_source_bytes(_SWITCH_V4_SOURCE, _SWITCH_V4_SOURCE_SHA256)
    v4_record = getattr(module, "_V4_SOURCE_RECORD", None)
    v2_record = getattr(module, "_BASE_SOURCE_RECORD", None)
    if (
        type(v4_record) is not dict
        or v4_record.get("relative_path") != _SWITCH_V4_RELATIVE.as_posix()
        or v4_record.get("sha256") != _SWITCH_V4_SOURCE_SHA256
        or type(v2_record) is not dict
        or v2_record.get("relative_path") != _SWITCH_V2_RELATIVE.as_posix()
        or v2_record.get("sha256") != _SWITCH_V2_SOURCE_SHA256
        or Path(getattr(module, "__file__", "")).resolve(strict=True)
            != _SWITCH_V4_SOURCE.resolve(strict=True)
        or Path(
            getattr(getattr(module, "base", None), "__file__", "")
        ).resolve(strict=True) != _SWITCH_V2_SOURCE.resolve(strict=True)
    ):
        raise AdaptiveChildResumeError(
            "executed switch module source capture mismatch"
        )


def _switch_v4_module(expected_sha256: str) -> Any:
    expected = _require_sha256(expected_sha256, "switch-v4 source pin")
    if expected != _SWITCH_V4_SOURCE_SHA256:
        raise AdaptiveChildResumeError(
            "switch-v4 source differs from frozen pin"
        )
    cached = _SWITCH_V4_CACHE.get(expected)
    if cached is None:
        _stable_source_bytes(_SWITCH_V2_SOURCE, _SWITCH_V2_SOURCE_SHA256)
        cached = _load_exact_source_module(
            "scripts.paper400_dic5_adaptive_switch_evidence_v4",
            _SWITCH_V4_SOURCE, _SWITCH_V4_SOURCE_SHA256,
        )
        _SWITCH_V4_CACHE[expected] = cached
    _verify_exact_switch_module(cached)
    return cached


def _default_switch_verifier(record: Mapping[str, Any]) -> Mapping[str, Any]:
    switch = _switch_v4_module(_SWITCH_V4_SOURCE_SHA256)
    _switch_record_overlay_source(record)
    return switch.validate_switch_record_structure(record)


def _source_binding() -> dict[str, Any]:
    """Bind only this self-contained runner source."""

    path = Path(__file__).resolve(strict=True)
    record = _stream_record(
        path, cap=MAX_SOURCE_BYTES, root=None,
        role="adaptive_child_runner_v5_source",
    )
    try:
        record["relative_path"] = path.relative_to(PROJECT).as_posix()
    except ValueError as exc:
        raise AdaptiveChildResumeError("runner source escapes project") from exc
    record.pop("path", None)
    value = {
        "method": "self-contained-runner-current-source-streaming-sha256-v5",
        "sources": {"adaptive_child_runner_v5_source": record},
    }
    value["source_binding_sha256"] = canonical_sha256(value)
    return value


def _module_source_record(
    module: Any, *, role: str, relative: Path,
) -> dict[str, Any]:
    expected = (PROJECT / relative).resolve(strict=True)
    source = getattr(module, "__file__", None)
    if source is None or Path(source).resolve(strict=True) != expected:
        raise AdaptiveChildResumeError(f"executed module path mismatch: {role}")
    record = _stream_record(
        expected, cap=MAX_SOURCE_BYTES, root=None, role=role,
    )
    record["relative_path"] = relative.as_posix()
    record.pop("path", None)
    return record


def _execution_module_binding(
    modules: tuple[Any, Any, Any, Any],
    switch_evidence: Mapping[str, Any], *, strict_base: bool,
) -> dict[str, Any]:
    if not strict_base:
        value = {
            "method": "synthetic-injected-modules-v1",
            "strict_base": False,
            "production_eligible": False,
            "modules_source_authenticated": False,
        }
        value["execution_module_binding_sha256"] = canonical_sha256(value)
        return value
    overlay, width10, adaptive, cube16 = modules
    _switch_record_overlay_source(switch_evidence)
    switch_module = _switch_v4_module(_SWITCH_V4_SOURCE_SHA256)
    sources = {
        "controller": _module_source_record(
            controller, role="executed-dmtcp-controller-source",
            relative=Path("scripts/run_cadical_dmtcp_resume_v1.py"),
        ),
        "switch_v4": _module_source_record(
            switch_module, role="executed-switch-v4-source",
            relative=_SWITCH_V4_RELATIVE,
        ),
        "switch_v2": _module_source_record(
            switch_module.base,
            role="executed-switch-v2-primitives-source",
            relative=_SWITCH_V2_RELATIVE,
        ),
        "overlay_v2": _module_source_record(
            overlay, role="executed-overlay-v2-source",
            relative=Path(
                "investigations/paper400_dic5_adaptive_leaf_overlay_v2.py"
            ),
        ),
        "adaptive_core_v2": _module_source_record(
            adaptive, role="executed-adaptive-core-v2-source",
            relative=Path("investigations/paper400_dic5_adaptive_cnc_v2.py"),
        ),
        "width10": _module_source_record(
            width10, role="executed-width10-source",
            relative=Path(
                "investigations/paper400_dic5_nested_width10_campaign_v1.py"
            ),
        ),
        "cube16": _module_source_record(
            cube16, role="executed-cube16-source",
            relative=Path("investigations/paper400_dic5_cube16.py"),
        ),
    }
    if (
        sources["switch_v4"]["sha256"] != _SWITCH_V4_SOURCE_SHA256
        or sources["switch_v2"]["sha256"] != _SWITCH_V2_SOURCE_SHA256
    ):
        raise AdaptiveChildResumeError(
            "executed switch v2/v4 misses frozen source pins"
        )
    instance = _strict_scoped_instance(modules)
    instance_fingerprint = overlay._instance_replay_fingerprint(
        instance, strict_base=True,
    )
    if type(instance_fingerprint) is not bytes:
        raise AdaptiveChildResumeError(
            "strict optimized-instance fingerprint is not bytes"
        )
    dependency_tree = _verify_strict_dependency_post_import()
    state = _active_strict_dependency_context()
    stdlib_tree = state["post_stdlib_tree"]
    stdlib_external = state["post_stdlib_external"]
    derived_environment = state["derived_environment"]
    if (
        type(stdlib_tree) is not dict
        or type(stdlib_external) is not dict
        or type(derived_environment) is not dict
    ):
        raise AdaptiveChildResumeError(
            "strict post-import stdlib binding is absent"
        )
    mapped_runtime = _strict_mapped_runtime_closure(
        dependency_tree, stdlib_tree,
    )
    value = {
        "method": (
            "exact-project-sources-frozen-input-trees-and-observed-maps-v3"
        ),
        "strict_base": True,
        "production_eligible": False,
        "switch_v2_source_sha256": _SWITCH_V2_SOURCE_SHA256,
        "switch_v4_source_sha256": _SWITCH_V4_SOURCE_SHA256,
        "sources": sources,
        "dependency_tree": dependency_tree,
        "system_stdlib_tree": stdlib_tree,
        "stdlib_external_symlink_targets": stdlib_external,
        "science_derived_environment": derived_environment,
        "optimized_instance_fingerprint": {
            "bytes": len(instance_fingerprint),
            "sha256": hashlib.sha256(instance_fingerprint).hexdigest(),
        },
        "mapped_runtime_closure": mapped_runtime,
        "persistent_change_detection": True,
        "privileged_toctou_defended": False,
    }
    value["execution_module_binding_sha256"] = canonical_sha256(value)
    return value

def _python_startup_binding(strict_base: bool) -> dict[str, Any]:
    if type(strict_base) is not bool:
        raise AdaptiveChildResumeError("strict_base startup flag is malformed")
    isolated = sys.flags.isolated == 1
    no_site = sys.flags.no_site == 1
    no_bytecode = sys.flags.dont_write_bytecode == 1
    safe_path = getattr(sys.flags, "safe_path", False) is True
    if strict_base and not (
        isolated and no_site and no_bytecode and safe_path
    ):
        raise AdaptiveChildResumeError(
            "strict execution requires fixed Python -I -S -B startup"
        )
    state = _active_strict_dependency_context() if strict_base else None
    value = {
        "method": "python-isolated-no-site-safe-path-fixed-dependencies-v2",
        "strict_base": strict_base,
        "isolated": isolated, "no_site": no_site,
        "dont_write_bytecode": no_bytecode, "safe_path": safe_path,
        "version_info": list(sys.version_info[:3]),
        "startup_customization_permitted": not strict_base,
        "strict_runtime_binding": (
            None if state is None else dict(state["runtime_binding"])
        ),
        "dependency_tree": (
            None if state is None else dict(state["pre_tree"])
        ),
        "system_stdlib_tree": (
            None if state is None else dict(state["pre_stdlib_tree"])
        ),
        "stdlib_external_symlink_targets": (
            None if state is None
            else dict(state["pre_stdlib_external"])
        ),
        "python312_zip_absent": (
            None if state is None else True
        ),
        "bytecode_policy": (
            "unrestricted-synthetic"
            if state is None else
            "private-empty-0700-pycache-prefix-no-read-no-write-v1"
        ),
    }
    value["python_startup_sha256"] = canonical_sha256(value)
    return value


def _default_tool_paths() -> dict[str, Path]:
    return {
        "cadical_solver": SOLVER,
        "dmtcp_controller_source": _CONTROLLER_SOURCE,
        "dmtcp_launch": DMTCP_PREFIX / "bin/dmtcp_launch",
        "dmtcp_command": DMTCP_PREFIX / "bin/dmtcp_command",
        "dmtcp_restart": DMTCP_PREFIX / "bin/dmtcp_restart",
        "drat_checker": DRAT_CHECKER,
        "drat_to_lrat": DRAT_CHECKER,
        "lrat_checker": LRAT_CHECKER,
    }


def _runtime_libraries(solver: Path) -> list[Path]:
    process = subprocess.run(
        ["/usr/bin/ldd", str(solver)], stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30, check=False,
        env={"LANG": "C", "LC_ALL": "C", "PATH": "/usr/bin:/bin"},
    )
    if process.returncode != 0 or process.stderr or len(process.stdout) > MAX_LOG_BYTES:
        raise AdaptiveChildResumeError("ldd runtime-closure probe failed")
    libraries: set[Path] = set()
    for raw in process.stdout.decode("ascii", "strict").splitlines():
        line = raw.strip()
        if not line or "linux-vdso" in line:
            continue
        target = line.split("=>", 1)[1].strip().split()[0] if "=>" in line else line.split()[0]
        if target == "not":
            raise AdaptiveChildResumeError("ldd reported a missing runtime library")
        if target.startswith("/"):
            libraries.add(Path(target).resolve(strict=True))
    if not libraries:
        raise AdaptiveChildResumeError("empty solver runtime-library closure")
    return sorted(libraries, key=str)


def _toolchain_binding(
    tool_paths: Mapping[str, Path], expected_hashes: Mapping[str, str],
) -> dict[str, Any]:
    if type(tool_paths) is not dict or set(tool_paths) != TOOL_ROLES:
        raise AdaptiveChildResumeError("tool path role set mismatch")
    if type(expected_hashes) is not dict or set(expected_hashes) != TOOL_ROLES:
        raise AdaptiveChildResumeError("tool hash role set mismatch")
    tools: dict[str, Any] = {}
    for role in sorted(TOOL_ROLES):
        expected = _require_sha256(expected_hashes[role], f"tool {role}")
        record = _stream_record(
            Path(tool_paths[role]).resolve(strict=True), cap=MAX_TOOL_BYTES,
            root=None, role=role,
        )
        if record["sha256"] != expected:
            raise AdaptiveChildResumeError(f"tool hash mismatch: {role}")
        if role != "dmtcp_controller_source" and not (
            os.stat(record["path"], follow_symlinks=False).st_mode & 0o111
        ):
            raise AdaptiveChildResumeError(f"tool is not executable: {role}")
        tools[role] = record
    version = subprocess.run(
        [tools["cadical_solver"]["path"], "--version"],
        stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        timeout=10, check=False,
        env={"LANG": "C", "LC_ALL": "C", "PATH": "/usr/bin:/bin"},
    )
    if (
        version.returncode != 0 or version.stderr
        or version.stdout.decode("ascii", "strict").strip() != EXPECTED_CADICAL_VERSION
    ):
        raise AdaptiveChildResumeError("CaDiCaL 1.9.5 version probe mismatch")
    dmtcp_prefix = Path(tools["dmtcp_launch"]["path"]).parent.parent
    with _fixed_environment():
        dmtcp = controller.build_dmtcp_binding(dmtcp_prefix)
    binary_hashes = {
        Path(item["path"]).name: item["sha256"] for item in dmtcp["binaries"]
    }
    for role, binary in (
        ("dmtcp_launch", "dmtcp_launch"),
        ("dmtcp_command", "dmtcp_command"),
        ("dmtcp_restart", "dmtcp_restart"),
    ):
        if binary_hashes.get(binary) != tools[role]["sha256"]:
            raise AdaptiveChildResumeError("DMTCP complete binding/tool mismatch")
    runtime = [
        controller.stable_file_record(path)
        for path in _runtime_libraries(Path(tools["cadical_solver"]["path"]))
    ]
    value = {
        "method": "fixed-path-hash-version-and-runtime-closure-v1",
        "cadical_version": EXPECTED_CADICAL_VERSION,
        "tools": tools,
        "dmtcp": dmtcp,
        "runtime_libraries": runtime,
        "proof_format": "binary-drat+converted-ascii-lrat-v1",
    }
    value["toolchain_sha256"] = canonical_sha256(value)
    return value


def _normalize_caps(caps: Mapping[str, Any]) -> dict[str, Any]:
    fields = {"proof_max_bytes"}
    if type(caps) is not dict or set(caps) != fields:
        raise AdaptiveChildResumeError("resource-cap field set mismatch")
    if any(type(caps[key]) is not int for key in fields):
        raise AdaptiveChildResumeError("resource caps must be strict integers")
    if not 1 <= caps["proof_max_bytes"] <= MAX_PROOF_BYTES:
        raise AdaptiveChildResumeError("proof cap outside policy")
    result = dict(caps)
    result.update({
        "checker_timeout_seconds": CHECKER_TIMEOUT_SECONDS,
        "checker_log_max_bytes": MAX_LOG_BYTES,
        "worker_processes_per_root": 1,
        "proof_and_lrat_streaming_only": True,
        "dmtcp_checkpoint_resource_hard_limit": None,
        "dmtcp_checkpoint_oom_risk_accepted": True,
    })
    return result


def _candidate_list(value: Sequence[int]) -> list[int]:
    if type(value) not in (list, tuple):
        raise AdaptiveChildResumeError("candidate variables must be list/tuple")
    result = list(value)
    if (
        not result or any(type(item) is not int or not 1 <= item <= 400 for item in result)
        or len(set(result)) != len(result)
    ):
        raise AdaptiveChildResumeError("candidate variables are malformed")
    return sorted(result)


def _switch_policy(timeout_seconds: float, elapsed: Sequence[float]) -> dict[str, Any]:
    if type(timeout_seconds) is not float or not math.isfinite(timeout_seconds) or timeout_seconds <= 0:
        raise AdaptiveChildResumeError("timeout_seconds must be a positive finite float")
    if (
        type(elapsed) is not list or len(elapsed) != 4
        or any(type(item) is not float or not math.isfinite(item) or item < 0 for item in elapsed)
    ):
        raise AdaptiveChildResumeError("elapsed_seconds_by_lane must be four finite floats")
    return {
        "timeout_seconds": timeout_seconds,
        "elapsed_seconds_by_lane": list(elapsed),
    }


def _manifest_pin(value: Mapping[str, Any], *, field: str, expected: str, label: str) -> None:
    if type(value) is not dict or value.get(field) != expected:
        raise AdaptiveChildResumeError(f"{label} misses external pin")
    unsigned = dict(value)
    stored = unsigned.pop(field, None)
    if canonical_sha256(unsigned) != stored:
        raise AdaptiveChildResumeError(f"{label} self-hash mismatch")


def _scoped_campaign_replay(
    *, parent: Mapping[str, Any], width6: Mapping[str, Any],
    width10: Mapping[str, Any], instance: Any, strict_base: bool,
    modules: tuple[Any, Any, Any, Any],
) -> tuple[
    Mapping[str, Any], Mapping[str, Any], Mapping[str, Any], Any
]:
    state = _active_cli_replay_scope()
    if state is None:
        raise AdaptiveChildResumeError(
            "campaign replay cache requires an active CLI scope"
        )
    overlay_module = modules[0]
    try:
        input_bytes = (
            overlay_module.canonical_bytes(width10),
            overlay_module.canonical_bytes(width6),
            overlay_module.canonical_bytes(parent),
        )
        pins = (
            width10.get("manifest_sha256"),
            width6.get("manifest_sha256"),
            parent.get("manifest_sha256"),
        )
        if any(not _is_sha256(value) for value in pins):
            raise AdaptiveChildResumeError(
                "campaign replay source manifest pin is malformed"
            )
        binding = state["campaign_binding"]
        if binding is None:
            manager = overlay_module.acquire_campaign_replay_token(
                width10,
                width6,
                parent,
                instance,
                expected_width10_campaign_sha256=pins[0],
                expected_width6_campaign_sha256=pins[1],
                expected_parent_manifest_sha256=pins[2],
                parent_cube_index=(
                    modules[1].TARGET_PARENT_CUBE_INDEX
                ),
                strict_base=strict_base,
            )
            token = state["stack"].enter_context(manager)
            binding = {
                "modules": modules,
                "instance": instance,
                "strict_base": strict_base,
                "input_bytes": input_bytes,
                "pins": pins,
                "parent": parent,
                "width6": width6,
                "width10": width10,
                "token": token,
            }
            state["campaign_binding"] = binding
        if (
            type(binding) is not dict
            or set(binding) != {
                "modules", "instance", "strict_base", "input_bytes",
                "pins", "parent", "width6", "width10", "token",
            }
            or any(
                left is not right
                for left, right in zip(
                    binding["modules"], modules, strict=True
                )
            )
            or binding["instance"] is not instance
            or binding["strict_base"] is not strict_base
            or binding["input_bytes"] != input_bytes
            or binding["pins"] != pins
        ):
            raise AdaptiveChildResumeError(
                "CLI campaign replay binding changed"
            )
        return (
            binding["parent"],
            binding["width6"],
            binding["width10"],
            binding["token"],
        )
    except Exception:
        _poison_cli_replay_scope(state)
        raise


def _scoped_overlay_replay(
    *, parent: Mapping[str, Any], width6: Mapping[str, Any],
    width10: Mapping[str, Any], overlay_manifest: Mapping[str, Any],
    hard_evidence: Mapping[str, Any], instance: Any,
    global_leaf_index: int, candidates: Sequence[int],
    overlay_pin: str, hard_pin: str, strict_base: bool,
    modules: tuple[Any, Any, Any, Any],
) -> tuple[dict[str, Any], dict[str, Any], bytes]:
    state = _active_cli_replay_scope()
    if state is None:
        raise AdaptiveChildResumeError(
            "overlay replay cache requires an active CLI scope"
        )
    overlay_module, width10_module, _, _ = modules
    try:
        owned_parent, owned_width6, owned_width10, token = (
            _scoped_campaign_replay(
                parent=parent,
                width6=width6,
                width10=width10,
                instance=instance,
                strict_base=strict_base,
                modules=modules,
            )
        )
        campaign_verification = (
            overlay_module._campaign_replay_verification(
                token,
                owned_width10,
                owned_width6,
                owned_parent,
                instance,
                strict_base=strict_base,
            )
        )
        key = (
            overlay_pin,
            hard_pin,
            global_leaf_index,
            tuple(candidates),
            strict_base,
        )
        overlay_bytes = overlay_module.canonical_bytes(
            overlay_manifest
        )
        evidence_bytes = overlay_module.canonical_bytes(hard_evidence)
        cached = state["overlay_cache"].get(key)
        if cached is None:
            overlay_verification = (
                overlay_module.verify_overlay_manifest(
                    overlay_manifest,
                    owned_width10,
                    owned_width6,
                    owned_parent,
                    instance,
                    global_leaf_index=global_leaf_index,
                    hard_evidence=hard_evidence,
                    expected_hard_evidence_sha256=hard_pin,
                    candidate_variables=candidates,
                    expected_overlay_sha256=overlay_pin,
                    strict_base=strict_base,
                    _campaign_replay_token=token,
                )
            )
            parent_payload = (
                width10_module.verified_child_dimacs_from_verification(
                    owned_width10,
                    owned_width6,
                    owned_parent,
                    instance,
                    verification_record=campaign_verification,
                    global_leaf_index=global_leaf_index,
                    parent_cube_index=(
                        width10_module.TARGET_PARENT_CUBE_INDEX
                    ),
                    strict_base=strict_base,
                )
            )
            overlay_module._campaign_replay_verification(
                token,
                owned_width10,
                owned_width6,
                owned_parent,
                instance,
                strict_base=strict_base,
            )
            if len(state["overlay_cache"]) >= COVER_ROOT_COUNT:
                raise AdaptiveChildResumeError(
                    "CLI overlay replay cache exceeded cover size"
                )
            cached = (
                overlay_bytes,
                evidence_bytes,
                overlay_module.canonical_bytes(
                    overlay_verification
                ),
                parent_payload,
            )
            state["overlay_cache"][key] = cached
        else:
            if (
                type(cached) is not tuple
                or len(cached) != 4
                or cached[0] != overlay_bytes
                or cached[1] != evidence_bytes
                or type(cached[2]) is not bytes
                or type(cached[3]) is not bytes
            ):
                raise AdaptiveChildResumeError(
                    "CLI overlay replay cache binding changed"
                )
            overlay_verification = json.loads(
                cached[2].decode("ascii")
            )
            parent_payload = cached[3]
        if (
            type(overlay_verification) is not dict
            or not overlay_module.selfhash_valid(
                overlay_verification, "record_sha256"
            )
            or overlay_module.canonical_bytes(overlay_verification)
            != cached[2]
        ):
            raise AdaptiveChildResumeError(
                "CLI overlay verification cache is malformed"
            )
        return (
            overlay_verification,
            campaign_verification,
            parent_payload,
        )
    except Exception:
        _poison_cli_replay_scope(state)
        raise


def _scoped_switch_structure(
    verifier: Callable[..., Mapping[str, Any]],
    switch_evidence: Mapping[str, Any],
    switch_pin: str,
) -> dict[str, Any]:
    state = _active_cli_replay_scope()
    if state is None:
        return dict(verifier(switch_evidence))
    try:
        evidence_bytes = canonical_bytes(switch_evidence)
        code = getattr(verifier, "__code__", None)
        cached = state["switch_cache"].get(switch_pin)
        if cached is None:
            structure = verifier(switch_evidence)
            if type(structure) is not dict:
                raise AdaptiveChildResumeError(
                    "switch structure verifier returned a non-object"
                )
            cached = (
                evidence_bytes,
                verifier,
                code,
                canonical_bytes(structure),
            )
            if len(state["switch_cache"]) >= COVER_ROOT_COUNT:
                raise AdaptiveChildResumeError(
                    "CLI switch structure cache exceeded cover size"
                )
            state["switch_cache"][switch_pin] = cached
        else:
            if (
                type(cached) is not tuple
                or len(cached) != 4
                or cached[0] != evidence_bytes
                or cached[1] is not verifier
                or cached[2] is not code
                or type(cached[3]) is not bytes
            ):
                raise AdaptiveChildResumeError(
                    "CLI switch structure cache binding changed"
                )
            structure = json.loads(cached[3].decode("ascii"))
        if (
            type(structure) is not dict
            or canonical_bytes(structure) != cached[3]
        ):
            raise AdaptiveChildResumeError(
                "CLI switch structure cache is malformed"
            )
        return structure
    except Exception:
        _poison_cli_replay_scope(state)
        raise


def _fresh_target(
    *, parent: Mapping[str, Any], width6: Mapping[str, Any], width10: Mapping[str, Any],
    overlay_manifest: Mapping[str, Any], hard_evidence: Mapping[str, Any],
    switch_evidence: Mapping[str, Any], batch_root: Path,
    expected_overlay_sha256: str, expected_hard_evidence_sha256: str,
    expected_switch_evidence_sha256: str, expected_batch_manifest_sha256: str,
    descendant_index: int, candidate_variables: Sequence[int],
    timeout_seconds: float, elapsed_seconds_by_lane: Sequence[float],
    instance: Any, strict_base: bool,
    switch_verifier: Callable[..., Mapping[str, Any]],
    science_modules: tuple[Any, Any, Any, Any] | None,
) -> dict[str, Any]:
    overlay_module, width10_module, adaptive, cube16 = (
        _science_modules(switch_evidence) if science_modules is None else science_modules
    )
    overlay_pin = _require_sha256(expected_overlay_sha256, "overlay pin")
    hard_pin = _require_sha256(expected_hard_evidence_sha256, "hard-evidence pin")
    switch_pin = _require_sha256(expected_switch_evidence_sha256, "switch pin")
    batch_pin = _require_sha256(expected_batch_manifest_sha256, "batch pin")
    _manifest_pin(overlay_manifest, field="manifest_sha256", expected=overlay_pin, label="overlay")
    _manifest_pin(hard_evidence, field="evidence_sha256", expected=hard_pin, label="hard evidence")
    _manifest_pin(switch_evidence, field="record_sha256", expected=switch_pin, label="switch evidence")
    if type(descendant_index) is not int:
        raise AdaptiveChildResumeError("descendant_index must be a strict integer")
    candidates = _candidate_list(candidate_variables)
    policy = _switch_policy(timeout_seconds, elapsed_seconds_by_lane)
    parent_scope = overlay_manifest.get("parent_scope")
    if type(parent_scope) is not dict or type(parent_scope.get("global_leaf_index")) is not int:
        raise AdaptiveChildResumeError("overlay parent scope is malformed")
    global_leaf_index = parent_scope["global_leaf_index"]
    try:
        if _active_cli_replay_scope() is None:
            overlay_verification = (
                overlay_module.verify_overlay_manifest(
                    overlay_manifest,
                    width10,
                    width6,
                    parent,
                    instance,
                    global_leaf_index=global_leaf_index,
                    hard_evidence=hard_evidence,
                    expected_hard_evidence_sha256=hard_pin,
                    candidate_variables=candidates,
                    expected_overlay_sha256=overlay_pin,
                    strict_base=strict_base,
                )
            )
            campaign_verification = (
                width10_module.verify_campaign_manifest(
                    width10,
                    width6,
                    parent,
                    instance,
                    parent_cube_index=(
                        width10_module.TARGET_PARENT_CUBE_INDEX
                    ),
                    strict_base=strict_base,
                )
            )
            parent_payload = (
                width10_module.verified_child_dimacs_from_verification(
                    width10,
                    width6,
                    parent,
                    instance,
                    verification_record=campaign_verification,
                    global_leaf_index=global_leaf_index,
                    parent_cube_index=(
                        width10_module.TARGET_PARENT_CUBE_INDEX
                    ),
                    strict_base=strict_base,
                )
            )
        else:
            (
                overlay_verification,
                campaign_verification,
                parent_payload,
            ) = _scoped_overlay_replay(
                parent=parent,
                width6=width6,
                width10=width10,
                overlay_manifest=overlay_manifest,
                hard_evidence=hard_evidence,
                instance=instance,
                global_leaf_index=global_leaf_index,
                candidates=candidates,
                overlay_pin=overlay_pin,
                hard_pin=hard_pin,
                strict_base=strict_base,
                modules=(
                    overlay_module,
                    width10_module,
                    adaptive,
                    cube16,
                ),
            )
    except Exception as exc:
        raise AdaptiveChildResumeError(f"fresh overlay/width10 replay failed: {exc}") from exc
    if (
        overlay_verification.get("valid") is not True
        or overlay_verification.get("current_source_exact_replay") is not True
        or campaign_verification.get("valid") is not True
        or campaign_verification.get("mutually_exclusive") is not True
        or campaign_verification.get("exhaustive") is not True
        or campaign_verification.get("parent000_formula_equivalence_certified") is not True
    ):
        raise AdaptiveChildResumeError("fresh overlay/campaign verification did not authenticate")
    descendants = overlay_manifest.get("descendants")
    if (
        type(descendants) is not list or not 0 <= descendant_index < len(descendants)
        or type(descendants[descendant_index]) is not dict
    ):
        raise AdaptiveChildResumeError("wrong descendant index")
    descendant = descendants[descendant_index]
    assumptions = descendant.get("relative_assignment_literals")
    if (
        descendant.get("descendant_index") != descendant_index
        or descendant.get("pending") is not True
        or descendant.get("observed_status") != "PENDING"
        or descendant.get("status_source") != "generated-frontier-v1"
        or descendant.get("solver_terminal_authenticated") is not False
        or type(assumptions) is not list or len(assumptions) != 1
        or any(type(item) is not int for item in assumptions)
    ):
        raise AdaptiveChildResumeError("selected descendant is not exact PENDING target")
    child_payload = adaptive.render_cube_dimacs(parent_payload, assumptions)
    parsed = adaptive.parse_dimacs(child_payload)
    structured_hash = cube16._cnf_sha256(
        num_variables=parsed["num_variables"], clauses=parsed["clauses"],
        native_atmost=None,
    )
    exact = {
        "child_cnf_sha256": structured_hash,
        "child_dimacs_sha256": hashlib.sha256(child_payload).hexdigest(),
        "child_num_variables": parsed["num_variables"],
        "child_num_clauses": parsed["num_clauses"],
        "child_dimacs_bytes": len(child_payload),
    }
    for field, expected in exact.items():
        if type(descendant.get(field)) is not type(expected) or descendant.get(field) != expected:
            raise AdaptiveChildResumeError(f"descendant exact bytes/count/hash mismatch: {field}")
    if (
        hashlib.sha256(parent_payload).hexdigest()
        != parent_scope.get("verified_child_payload_sha256")
        or len(parent_payload) != parent_scope.get("verified_child_payload_bytes")
    ):
        raise AdaptiveChildResumeError("width10 verified-child byte binding mismatch")
    try:
        structure = _scoped_switch_structure(
            switch_verifier, switch_evidence, switch_pin,
        )
    except Exception as exc:
        raise AdaptiveChildResumeError(
            f"switch-v4 structure validation failed: {exc}"
        ) from exc
    if (
        type(structure) is not dict
        or structure.get("valid") is not True
        or structure.get("authenticated") is not False
        or structure.get("launch_authorized") is not False
        or structure.get("production_eligible") is not False
        or structure.get("scientific_claim") is not False
    ):
        raise AdaptiveChildResumeError(
            "serialized switch validation attempted authority"
        )
    switch_structure_validation = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-switch-structure-summary-v5",
        "valid": True,
        "authenticated": False,
        "launch_authorized": False,
        "scientific_claim": False,
        "production_eligible": False,
        "switch_evidence_sha256": switch_pin,
        "validator_output_sha256": canonical_sha256(structure),
        "atomic_lease_required_for_launch": True,
    })
    return {
        "overlay_verification": overlay_verification,
        "campaign_verification": campaign_verification,
        "switch_structure_validation": switch_structure_validation,
        "global_leaf_index": global_leaf_index,
        "descendant": dict(descendant),
        "parent_payload_sha256": hashlib.sha256(parent_payload).hexdigest(),
        "parent_payload_bytes": len(parent_payload),
        "child_payload": child_payload,
        "child_structured_sha256": structured_hash,
        "candidate_variables": candidates,
        "switch_policy": policy,
    }


def _material_record(root: Path, relative: Path, role: str, cap: int) -> dict[str, Any]:
    return _stream_record(root / relative, cap=cap, root=root, role=role)


def _static_value(
    *, root: Path, batch_root: Path, parent: Mapping[str, Any], width6: Mapping[str, Any],
    width10: Mapping[str, Any], overlay_manifest: Mapping[str, Any],
    hard_evidence: Mapping[str, Any], switch_evidence: Mapping[str, Any],
    expected_overlay_sha256: str, expected_hard_evidence_sha256: str,
    expected_switch_evidence_sha256: str, expected_batch_manifest_sha256: str,
    descendant_index: int, candidate_variables: Sequence[int], timeout_seconds: float,
    elapsed_seconds_by_lane: Sequence[float], instance: Any, strict_base: bool,
    switch_verifier: Callable[..., Mapping[str, Any]],
    science_modules: tuple[Any, Any, Any, Any] | None,
    tool_paths: Mapping[str, Path], expected_tool_sha256: Mapping[str, str],
    resource_caps: Mapping[str, Any],
) -> tuple[dict[str, Any], bytes]:
    fresh = _fresh_target(
        parent=parent, width6=width6, width10=width10,
        overlay_manifest=overlay_manifest, hard_evidence=hard_evidence,
        switch_evidence=switch_evidence, batch_root=batch_root,
        expected_overlay_sha256=expected_overlay_sha256,
        expected_hard_evidence_sha256=expected_hard_evidence_sha256,
        expected_switch_evidence_sha256=expected_switch_evidence_sha256,
        expected_batch_manifest_sha256=expected_batch_manifest_sha256,
        descendant_index=descendant_index, candidate_variables=candidate_variables,
        timeout_seconds=timeout_seconds,
        elapsed_seconds_by_lane=elapsed_seconds_by_lane, instance=instance,
        strict_base=strict_base, switch_verifier=switch_verifier,
        science_modules=science_modules,
    )
    child = fresh["child_payload"]
    observed = _read_bounded(
        root / STATIC_DESCENDANT_CNF, cap=max(len(child), 1), root=root,
        role="exact-descendant-cnf",
    )
    if observed != child:
        raise AdaptiveChildResumeError("stored descendant CNF differs from exact replay bytes")
    materials = {
        "parent_manifest": _material_record(root, STATIC_PARENT, "parent-manifest", MAX_JSON_BYTES),
        "width6_campaign": _material_record(root, STATIC_WIDTH6, "width6-campaign", MAX_JSON_BYTES),
        "width10_campaign": _material_record(root, STATIC_WIDTH10, "width10-campaign", MAX_JSON_BYTES),
        "adaptive_overlay": _material_record(root, STATIC_OVERLAY, "adaptive-overlay", MAX_JSON_BYTES),
        "hard_evidence": _material_record(root, STATIC_HARD_EVIDENCE, "hard-evidence", MAX_JSON_BYTES),
        "switch_evidence": _material_record(root, STATIC_SWITCH_EVIDENCE, "switch-evidence", MAX_JSON_BYTES),
        "descendant_cnf": _material_record(root, STATIC_DESCENDANT_CNF, "exact-descendant-cnf", max(len(child), 1)),
    }
    toolchain = _toolchain_binding(tool_paths, expected_tool_sha256)
    sources = _source_binding()
    execution_modules = _execution_module_binding(
        science_modules if science_modules is not None else _science_modules(switch_evidence),
        switch_evidence, strict_base=strict_base,
    )
    caps = _normalize_caps(resource_caps)
    descendant = fresh["descendant"]
    value = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": STATIC_KIND,
        "gate": GATE,
        "state": "RESUMABLE_STATIC_SEALED",
        "authority": AUTHORITY,
        "test_only": True,
        "production_eligible": False,
        "root": str(root),
        "root_identity": _directory_identity(root, require_mode_0700=True),
        "root_lock_identity": _lock_identity(root),
        "batch_root_identity": _directory_identity(batch_root, require_mode_0700=True),
        "strict_base": strict_base,
        "python_startup": _python_startup_binding(strict_base),
        "external_pins": {
            "expected_overlay_sha256": expected_overlay_sha256,
            "expected_hard_evidence_sha256": expected_hard_evidence_sha256,
            "expected_switch_evidence_sha256": expected_switch_evidence_sha256,
            "expected_batch_manifest_sha256": expected_batch_manifest_sha256,
        },
        "selection": {
            "global_leaf_index": fresh["global_leaf_index"],
            "descendant_index": descendant_index,
            "descendant_sha256": descendant["descendant_sha256"],
            "adaptive_node_id": descendant.get("adaptive_node_id"),
            "relative_assignment_literals": descendant["relative_assignment_literals"],
            "candidate_variables": fresh["candidate_variables"],
        },
        "switch_policy": fresh["switch_policy"],
        "material_files": materials,
        "campaign_manifest_sha256": width10.get("manifest_sha256"),
        "overlay_manifest_sha256": expected_overlay_sha256,
        "hard_evidence_sha256": expected_hard_evidence_sha256,
        "switch_evidence_sha256": expected_switch_evidence_sha256,
        "overlay_verification": fresh["overlay_verification"],
        "campaign_verification": fresh["campaign_verification"],
        "switch_structure_validation": fresh["switch_structure_validation"],
        "descendant": descendant,
        "descendant_cnf": {
            "structured_sha256": fresh["child_structured_sha256"],
            "dimacs_sha256": hashlib.sha256(child).hexdigest(),
            "bytes": len(child),
            "num_variables": descendant["child_num_variables"],
            "num_clauses": descendant["child_num_clauses"],
            "parent_verified_child_sha256": fresh["parent_payload_sha256"],
            "parent_verified_child_bytes": fresh["parent_payload_bytes"],
        },
        "source_binding": sources,
        "execution_module_binding": execution_modules,
        "toolchain_binding": toolchain,
        "resource_policy": caps,
        "launch_attestation": {
            "serialized_overlay_launch_authorized": False,
            "serialized_switch_launch_authorized": False,
            "serialized_composite_launch_authorized": False,
            "candidate_exact_bytes_replayed": True,
            "atomic_switch_v4_lease_required": True,
            "strict_first_start_requires_complete_eight_root_cover": True,
            "adaptive_handoff_reentry_supported": False,
            "maximum_live_workers_during_handoff": COHORT_SIZE,
        },
        "resume_policy": {
            "single_process": True, "single_cpu": True,
            "cpu_rlimit_unlimited": True, "proof_fsize_cap_required": True,
            "dmtcp_checkpoint_resource_hard_limit": None,
            "dmtcp_checkpoint_oom_risk_accepted": True,
            "controller": controller.CONTROLLER,
            "checkpoint_has_scientific_authority": False,
            "resume_has_scientific_authority": False,
        },
        "claim_scope": {
            "pending_is_solver_evidence": False,
            "overlay_proves_leaf_unsat": False,
            "switch_record_proves_leaf_unsat": False,
            "checkpoint_proves_leaf_unsat": False,
            "only_final_fresh_drat_lrat_certificate_authenticates_leaf_unsat": True,
            "parent_leaf_unsat_claim": False,
            "distance_lower_bound_claim": False,
        },
        "publication_certificate": False,
        "upload_authorized": False,
    })
    return value, child


def prepare_root_from_material(
    root: Path, *, batch_root: Path, parent_manifest: Mapping[str, Any],
    width6_campaign: Mapping[str, Any], width10_campaign: Mapping[str, Any],
    overlay_manifest: Mapping[str, Any], hard_evidence: Mapping[str, Any],
    switch_evidence: Mapping[str, Any], expected_overlay_sha256: str,
    expected_hard_evidence_sha256: str, expected_switch_evidence_sha256: str,
    expected_batch_manifest_sha256: str, descendant_index: int,
    candidate_variables: Sequence[int], timeout_seconds: float,
    elapsed_seconds_by_lane: Sequence[float], resource_caps: Mapping[str, Any],
    instance: Any | None = None, strict_base: bool = True,
    switch_verifier: Callable[..., Mapping[str, Any]] | None = None,
    science_modules: tuple[Any, Any, Any, Any] | None = None,
    tool_paths: Mapping[str, Path] | None = None,
    expected_tool_sha256: Mapping[str, str] | None = None,
) -> dict[str, Any]:
    if type(strict_base) is not bool:
        raise AdaptiveChildResumeError("strict_base must be a strict boolean")
    if strict_base and any(item is not None for item in (
        instance, switch_verifier, science_modules, tool_paths,
        expected_tool_sha256,
    )):
        raise AdaptiveChildResumeError(
            "strict prepare forbids injected instance/verifier/modules/tools"
        )
    _python_startup_binding(strict_base)
    modules = (
        _science_modules(switch_evidence)
        if science_modules is None else science_modules
    )
    if strict_base:
        if instance is not None:
            raise AdaptiveChildResumeError("strict prepare cannot inject an instance")
        instance = _strict_scoped_instance(modules)
    elif instance is None:
        raise AdaptiveChildResumeError("synthetic prepare requires an instance")
    verifier = _default_switch_verifier if switch_verifier is None else switch_verifier
    paths = _default_tool_paths() if tool_paths is None else dict(tool_paths)
    hashes = dict(EXPECTED_TOOL_SHA256 if expected_tool_sha256 is None else expected_tool_sha256)
    target = _new_root(root)
    _initialize_outer_lock(target)
    try:
        for name in ("static", "state", "artifacts", "runtime"):
            _mkdir(target, name)
        _mkdir(target / "state", "actions")
        for relative, value in (
            (STATIC_PARENT, parent_manifest), (STATIC_WIDTH6, width6_campaign),
            (STATIC_WIDTH10, width10_campaign), (STATIC_OVERLAY, overlay_manifest),
            (STATIC_HARD_EVIDENCE, hard_evidence),
            (STATIC_SWITCH_EVIDENCE, switch_evidence),
        ):
            _publish_json(target / relative, value)
        fresh = _fresh_target(
            parent=parent_manifest, width6=width6_campaign, width10=width10_campaign,
            overlay_manifest=overlay_manifest, hard_evidence=hard_evidence,
            switch_evidence=switch_evidence, batch_root=Path(batch_root),
            expected_overlay_sha256=expected_overlay_sha256,
            expected_hard_evidence_sha256=expected_hard_evidence_sha256,
            expected_switch_evidence_sha256=expected_switch_evidence_sha256,
            expected_batch_manifest_sha256=expected_batch_manifest_sha256,
            descendant_index=descendant_index, candidate_variables=candidate_variables,
            timeout_seconds=timeout_seconds,
            elapsed_seconds_by_lane=elapsed_seconds_by_lane, instance=instance,
            strict_base=strict_base, switch_verifier=verifier,
            science_modules=modules,
        )
        _publish_bytes(target / STATIC_DESCENDANT_CNF, fresh["child_payload"])
        with _root_lock(target, exclusive=True):
            record, _ = _static_value(
                root=target, batch_root=Path(batch_root), parent=parent_manifest,
                width6=width6_campaign, width10=width10_campaign,
                overlay_manifest=overlay_manifest, hard_evidence=hard_evidence,
                switch_evidence=switch_evidence,
                expected_overlay_sha256=expected_overlay_sha256,
                expected_hard_evidence_sha256=expected_hard_evidence_sha256,
                expected_switch_evidence_sha256=expected_switch_evidence_sha256,
                expected_batch_manifest_sha256=expected_batch_manifest_sha256,
                descendant_index=descendant_index,
                candidate_variables=candidate_variables,
                timeout_seconds=timeout_seconds,
                elapsed_seconds_by_lane=elapsed_seconds_by_lane,
                instance=instance, strict_base=strict_base,
                switch_verifier=verifier, science_modules=modules,
                tool_paths=paths, expected_tool_sha256=hashes,
                resource_caps=resource_caps,
            )
            _publish_json(target / STATIC_COMMIT, record)
        return record
    except BaseException:
        # Retain the newly created root as failed, immutable evidence.
        raise


def _tool_inputs(record: Mapping[str, Any]) -> tuple[dict[str, Path], dict[str, str]]:
    tools = record.get("toolchain_binding", {}).get("tools")
    if type(tools) is not dict or set(tools) != TOOL_ROLES:
        raise AdaptiveChildResumeError("stored toolchain is malformed")
    return (
        {role: Path(tools[role]["path"]) for role in TOOL_ROLES},
        {role: tools[role]["sha256"] for role in TOOL_ROLES},
    )


def _load_static(
    root: Path, *, instance: Any | None,
    switch_verifier: Callable[..., Mapping[str, Any]] | None,
    science_modules: tuple[Any, Any, Any, Any] | None,
) -> dict[str, Any]:
    target = _existing_root(root)
    record = _read_json(target / STATIC_COMMIT, root=target)
    if (
        not selfhash_valid(record) or record.get("kind") != STATIC_KIND
        or record.get("gate") != GATE or record.get("root") != str(target)
        or record.get("authority") != AUTHORITY or record.get("test_only") is not True
        or record.get("production_eligible") is not False
    ):
        raise AdaptiveChildResumeError("static record header/self-hash mismatch")
    strict_base = record.get("strict_base")
    if type(strict_base) is not bool:
        raise AdaptiveChildResumeError("stored strict_base is malformed")
    _python_startup_binding(strict_base)
    if strict_base and any(item is not None for item in (
        instance, switch_verifier, science_modules,
    )):
        raise AdaptiveChildResumeError(
            "strict action forbids injected instance/verifier/modules"
        )
    switch_evidence = _read_json(target / STATIC_SWITCH_EVIDENCE, root=target)
    modules = (
        _science_modules(switch_evidence)
        if science_modules is None else science_modules
    )
    if strict_base:
        if instance is not None:
            raise AdaptiveChildResumeError("strict action cannot inject an instance")
        instance = _strict_scoped_instance(modules)
    elif instance is None:
        raise AdaptiveChildResumeError("synthetic action requires an instance")
    verifier = _default_switch_verifier if switch_verifier is None else switch_verifier
    parent = _read_json(target / STATIC_PARENT, root=target)
    width6 = _read_json(target / STATIC_WIDTH6, root=target)
    width10 = _read_json(target / STATIC_WIDTH10, root=target)
    overlay_manifest = _read_json(target / STATIC_OVERLAY, root=target)
    hard_evidence = _read_json(target / STATIC_HARD_EVIDENCE, root=target)
    pins = record.get("external_pins")
    selection = record.get("selection")
    policy = record.get("switch_policy")
    caps = record.get("resource_policy")
    if not all(type(value) is dict for value in (pins, selection, policy, caps)):
        raise AdaptiveChildResumeError("static replay inputs are malformed")
    tool_paths, tool_hashes = _tool_inputs(record)
    if strict_base and (
        {key: str(value) for key, value in tool_paths.items()}
        != {key: str(value) for key, value in _default_tool_paths().items()}
        or tool_hashes != EXPECTED_TOOL_SHA256
    ):
        raise AdaptiveChildResumeError("strict action tool policy mismatch")
    batch_root = Path(record.get("batch_root_identity", {}).get("path", ""))
    expected, child = _static_value(
        root=target, batch_root=batch_root, parent=parent, width6=width6,
        width10=width10, overlay_manifest=overlay_manifest,
        hard_evidence=hard_evidence, switch_evidence=switch_evidence,
        expected_overlay_sha256=pins.get("expected_overlay_sha256"),
        expected_hard_evidence_sha256=pins.get("expected_hard_evidence_sha256"),
        expected_switch_evidence_sha256=pins.get("expected_switch_evidence_sha256"),
        expected_batch_manifest_sha256=pins.get("expected_batch_manifest_sha256"),
        descendant_index=selection.get("descendant_index"),
        candidate_variables=selection.get("candidate_variables"),
        timeout_seconds=policy.get("timeout_seconds"),
        elapsed_seconds_by_lane=policy.get("elapsed_seconds_by_lane"),
        instance=instance, strict_base=strict_base, switch_verifier=verifier,
        science_modules=modules, tool_paths=tool_paths,
        expected_tool_sha256=tool_hashes,
        resource_caps={
            "proof_max_bytes": caps.get("proof_max_bytes"),
        },
    )
    if not json_type_equal(record, expected):
        raise AdaptiveChildResumeError("static record differs from fresh type-exact replay")
    return {
        "record": record, "parent": parent, "width6": width6, "width10": width10,
        "overlay": overlay_manifest, "hard_evidence": hard_evidence,
        "switch_evidence": switch_evidence, "child_payload": child,
        "instance": instance, "switch_verifier": verifier,
        "science_modules": modules,
    }


@contextlib.contextmanager
def _fixed_environment() -> Iterator[None]:
    previous = dict(os.environ)
    clean = controller._clean_dmtcp_environment()
    os.environ.clear()
    os.environ.update(clean)
    try:
        yield
    finally:
        os.environ.clear()
        os.environ.update(previous)


def _single_cpu() -> int:
    cpus = os.sched_getaffinity(0)
    if len(cpus) != 1:
        raise AdaptiveChildResumeError(f"action requires one CPU, got {sorted(cpus)}")
    return next(iter(cpus))


def _preflight_solver_limits(cap: int) -> None:
    if type(cap) is not int or not 1 <= cap <= MAX_PROOF_BYTES:
        raise AdaptiveChildResumeError("invalid proof cap preflight")
    cpu = resource.getrlimit(resource.RLIMIT_CPU)
    fsize = resource.getrlimit(resource.RLIMIT_FSIZE)
    core = resource.getrlimit(resource.RLIMIT_CORE)
    if cpu[1] != resource.RLIM_INFINITY:
        raise AdaptiveChildResumeError("hard RLIMIT_CPU must be unlimited")
    if fsize[1] != resource.RLIM_INFINITY and fsize[1] < cap:
        raise AdaptiveChildResumeError("hard RLIMIT_FSIZE is below proof cap")
    if core[1] != resource.RLIM_INFINITY and core[1] < 0:
        raise AdaptiveChildResumeError("invalid hard RLIMIT_CORE")


@contextlib.contextmanager
def _inherited_solver_limits(cap: int) -> Iterator[None]:
    old_cpu = resource.getrlimit(resource.RLIMIT_CPU)
    old_fsize = resource.getrlimit(resource.RLIMIT_FSIZE)
    old_core = resource.getrlimit(resource.RLIMIT_CORE)
    if old_cpu[1] != resource.RLIM_INFINITY:
        raise AdaptiveChildResumeError("hard RLIMIT_CPU must be unlimited")
    if old_fsize[1] != resource.RLIM_INFINITY and old_fsize[1] < cap:
        raise AdaptiveChildResumeError("hard RLIMIT_FSIZE is below proof cap")
    try:
        resource.setrlimit(resource.RLIMIT_CPU, (resource.RLIM_INFINITY, resource.RLIM_INFINITY))
        resource.setrlimit(resource.RLIMIT_FSIZE, (cap, old_fsize[1]))
        resource.setrlimit(resource.RLIMIT_CORE, (0, old_core[1]))
        yield
    finally:
        resource.setrlimit(resource.RLIMIT_CPU, old_cpu)
        resource.setrlimit(resource.RLIMIT_FSIZE, old_fsize)
        resource.setrlimit(resource.RLIMIT_CORE, old_core)


def _rlimit_policy(cap: int) -> dict[str, Any]:
    return {
        "proof_fsize_soft_bytes": cap, "core_soft_bytes": 0,
        "cpu_soft_seconds": resource.RLIM_INFINITY,
        "cpu_hard_seconds": resource.RLIM_INFINITY,
        "must_be_inherited_by_live_solver": True,
    }


def _verify_live_peer_rlimits(pid: int, cap: int) -> dict[str, Any]:
    if not hasattr(resource, "prlimit"):
        raise AdaptiveChildResumeError("prlimit is unavailable")
    fsize = resource.prlimit(pid, resource.RLIMIT_FSIZE)
    core = resource.prlimit(pid, resource.RLIMIT_CORE)
    cpu = resource.prlimit(pid, resource.RLIMIT_CPU)
    if (
        fsize[0] != cap or (fsize[1] != resource.RLIM_INFINITY and fsize[1] < cap)
        or core[0] != 0 or cpu != (resource.RLIM_INFINITY, resource.RLIM_INFINITY)
    ):
        raise AdaptiveChildResumeError("live solver RLIMIT mismatch")
    return {
        "pid": pid, "proof_fsize_soft_bytes": fsize[0],
        "proof_fsize_hard_bytes": fsize[1], "core_soft_bytes": core[0],
        "core_hard_bytes": core[1], "cpu_soft_seconds": cpu[0],
        "cpu_hard_seconds": cpu[1], "verified": True,
    }


def _admit_live_peer(result: Mapping[str, Any], *, cpu: int, cap: int) -> dict[str, Any]:
    pid, ticks = result.get("pid"), result.get("proc_start_ticks")
    if (
        type(pid) is not int or type(ticks) is not int
        or not controller._pid_identity(pid, ticks) or os.sched_getaffinity(pid) != {cpu}
    ):
        raise AdaptiveChildResumeError("live solver identity/CPU mismatch")
    return _verify_live_peer_rlimits(pid, cap)


_PEER_RLIMIT_FIELDS = {
    "pid", "proof_fsize_soft_bytes", "proof_fsize_hard_bytes",
    "core_soft_bytes", "core_hard_bytes", "cpu_soft_seconds",
    "cpu_hard_seconds", "verified",
}


def _validate_peer_rlimits(
    value: Any, *, expected_pid: int, cap: int,
) -> dict[str, Any]:
    """Validate the complete historical live-peer admission record."""

    integer_fields = _PEER_RLIMIT_FIELDS - {"verified"}
    if (
        type(value) is not dict or set(value) != _PEER_RLIMIT_FIELDS
        or type(expected_pid) is not int or expected_pid <= 0
        or type(cap) is not int or not 1 <= cap <= MAX_PROOF_BYTES
        or any(type(value.get(field)) is not int for field in integer_fields)
        or value["pid"] != expected_pid
        or value["proof_fsize_soft_bytes"] != cap
        or (
            value["proof_fsize_hard_bytes"] != resource.RLIM_INFINITY
            and value["proof_fsize_hard_bytes"] < cap
        )
        or value["core_soft_bytes"] != 0
        or (
            value["core_hard_bytes"] != resource.RLIM_INFINITY
            and value["core_hard_bytes"] < 0
        )
        or value["cpu_soft_seconds"] != resource.RLIM_INFINITY
        or value["cpu_hard_seconds"] != resource.RLIM_INFINITY
        or value["verified"] is not True
    ):
        raise AdaptiveChildResumeError("peer RLIMIT admission record mismatch")
    return dict(value)


def _validate_inspection(value: Any, *, runtime: Path) -> dict[str, Any]:
    fields = {
        "authority", "config_manifest_sha256", "dmtcp_command_sha256",
        "generations", "hash_verification_requested", "root", "state",
    }
    if (
        type(value) is not dict or set(value) != fields
        or value.get("authority") != controller.AUTHORITY
        or value.get("hash_verification_requested") is not True
        or value.get("root") != str(runtime.resolve(strict=True))
        or value.get("state") not in {
            "INITIALIZED", "RUNNING", "CHECKPOINTED", "INACTIVE_UNCHECKPOINTED",
        }
        or type(value.get("generations")) is not list
        or not _is_sha256(value.get("config_manifest_sha256"))
        or not _is_sha256(value.get("dmtcp_command_sha256"))
    ):
        raise AdaptiveChildResumeError("controller inspect record mismatch")
    return value


def _inspect_controller(root: Path) -> dict[str, Any]:
    runtime = root / RUNTIME_ROOT
    with _fixed_environment():
        value = controller.inspect(runtime, verify_hashes=True)
    return _validate_inspection(value, runtime=runtime)


def _action_pairs(root: Path) -> list[tuple[dict[str, Any], dict[str, Any]]]:
    static = _read_json(root / STATIC_COMMIT, root=root)
    cap = static.get("resource_policy", {}).get("proof_max_bytes")
    if (
        not selfhash_valid(static) or static.get("kind") != STATIC_KIND
        or static.get("gate") != GATE or static.get("root") != str(root)
        or type(cap) is not int or not 1 <= cap <= MAX_PROOF_BYTES
    ):
        raise AdaptiveChildResumeError("action ledger static resource binding mismatch")
    entries = sorted((root / ACTIONS_DIR).iterdir(), key=lambda item: item.name)
    grouped: dict[tuple[int, str], dict[str, Path]] = {}
    for path in entries:
        match = ACTION_RE.fullmatch(path.name)
        if match is None:
            raise AdaptiveChildResumeError("unexpected action-ledger entry")
        key = (int(match.group("sequence")), match.group("action"))
        stages = grouped.setdefault(key, {})
        stage = match.group("stage")
        if stage in stages:
            raise AdaptiveChildResumeError("duplicate action-ledger stage")
        stages[stage] = path
    claim_fields = {
        "schema_version", "kind", "gate", "root", "root_identity",
        "root_lock_identity", "sequence", "action", "nonce_hex", "pid",
        "static_sha256", "session_sha256", "previous_commit_sha256",
        "terminal", "record_sha256",
    }
    commit_fields = {
        "schema_version", "kind", "gate", "root", "root_identity",
        "root_lock_identity", "sequence", "action", "claim_sha256",
        "static_sha256", "session_sha256", "previous_commit_sha256",
        "transition", "controller_result", "controller_inspection",
        "admitted_peer_rlimits", "transport_scientific_authority",
        "recovered_interrupted_claim", "record_sha256",
    }
    pairs: list[tuple[dict[str, Any], dict[str, Any]]] = []
    previous: str | None = None
    for expected_sequence, key in enumerate(sorted(grouped)):
        sequence, action = key
        stages = grouped[key]
        if sequence != expected_sequence or set(stages) != {"claim", "commit"}:
            raise AdaptiveChildResumeError("action ledger is noncontiguous or poisoned")
        claim = _read_json(stages["claim"], root=root)
        commit = _read_json(stages["commit"], root=root)
        if (
            set(claim) != claim_fields or set(commit) != commit_fields
            or not selfhash_valid(claim) or not selfhash_valid(commit)
            or claim["schema_version"] != SCHEMA_VERSION
            or type(claim["schema_version"]) is not int
            or commit["schema_version"] != SCHEMA_VERSION
            or type(commit["schema_version"]) is not int
            or claim["kind"] != ACTION_CLAIM_KIND
            or commit["kind"] != ACTION_COMMIT_KIND
            or claim["gate"] != GATE or commit["gate"] != GATE
            or claim["root"] != str(root) or commit["root"] != str(root)
            or not json_type_equal(claim["root_identity"], _directory_identity(root, require_mode_0700=True))
            or not json_type_equal(commit["root_identity"], claim["root_identity"])
            or not json_type_equal(claim["root_lock_identity"], _lock_identity(root))
            or not json_type_equal(commit["root_lock_identity"], claim["root_lock_identity"])
            or claim["sequence"] != sequence or type(claim["sequence"]) is not int
            or commit["sequence"] != sequence or type(commit["sequence"]) is not int
            or claim["action"] != action or commit["action"] != action
            or action not in {"start", "checkpoint-stop", "resume"}
            or type(claim["nonce_hex"]) is not str
            or re.fullmatch(r"[0-9a-f]{64}", claim["nonce_hex"]) is None
            or type(claim["pid"]) is not int or claim["pid"] <= 0
            or not _is_sha256(claim["static_sha256"])
            or claim["previous_commit_sha256"] != previous
            or commit["previous_commit_sha256"] != previous
            or commit["claim_sha256"] != claim["record_sha256"]
            or commit["static_sha256"] != claim["static_sha256"]
            or claim["terminal"] is not False
            or commit["transport_scientific_authority"] is not False
            or type(commit["recovered_interrupted_claim"]) is not bool
        ):
            raise AdaptiveChildResumeError("action ledger claim/commit mismatch")
        inspection = _validate_inspection(
            commit["controller_inspection"], runtime=root / RUNTIME_ROOT,
        )
        if commit["controller_result"] is not None and (
            type(commit["controller_result"]) is not dict
            or not controller.selfhash_valid(commit["controller_result"])
        ):
            raise AdaptiveChildResumeError("action controller result is malformed")
        if action == "start":
            if claim["session_sha256"] is not None or not _is_sha256(commit["session_sha256"]):
                raise AdaptiveChildResumeError("start action session transition mismatch")
        elif claim["session_sha256"] != commit["session_sha256"] or not _is_sha256(commit["session_sha256"]):
            raise AdaptiveChildResumeError("action session chain mismatch")
        normal_transition = {
            "start": ("STARTED_RUNNING", "RUNNING", True),
            "checkpoint-stop": ("CHECKPOINTED_STOPPED", "CHECKPOINTED", False),
            "resume": ("RESUMED_RUNNING", "RUNNING", True),
        }[action]
        transition, target_state, admits_peer = normal_transition
        generations = inspection["generations"]
        latest = (
            generations[-1]
            if generations and type(generations[-1]) is dict else None
        )
        if commit["recovered_interrupted_claim"] is True:
            recoverable_states = {
                "start": {"RUNNING"},
                "checkpoint-stop": {
                    "RUNNING", "CHECKPOINTED", "INACTIVE_UNCHECKPOINTED",
                },
                "resume": {
                    "RUNNING", "CHECKPOINTED", "INACTIVE_UNCHECKPOINTED",
                },
            }[action]
            expected_recovered = (
                f"RECOVERED_{action.upper().replace('-', '_')}_{inspection['state']}"
            )
            if (
                inspection["state"] not in recoverable_states
                or commit["transition"] != expected_recovered
                or commit["controller_result"] is not None
                or commit["admitted_peer_rlimits"] is not None
            ):
                raise AdaptiveChildResumeError("recovered action transition mismatch")
        else:
            result = commit["controller_result"]
            if (
                commit["transition"] != transition
                or inspection["state"] != target_state
                or type(result) is not dict
                or latest is None
            ):
                raise AdaptiveChildResumeError("normal action transition mismatch")
            if admits_peer:
                pid = result.get("pid")
                ticks = result.get("proc_start_ticks")
                if (
                    type(pid) is not int or type(ticks) is not int
                    or latest.get("active_manifest_sha256")
                    != result.get("self_sha256")
                ):
                    raise AdaptiveChildResumeError(
                        "running action/controller generation mismatch"
                    )
                _validate_peer_rlimits(
                    commit["admitted_peer_rlimits"],
                    expected_pid=pid, cap=cap,
                )
            elif (
                commit["admitted_peer_rlimits"] is not None
                or latest.get("checkpoint_manifest_sha256")
                != result.get("self_sha256")
                or latest.get("pid_identity_alive") is not False
            ):
                raise AdaptiveChildResumeError(
                    "checkpoint action/controller generation mismatch"
                )
        previous = commit["record_sha256"]
        pairs.append((claim, commit))
    return pairs


def _begin_action(
    root: Path, *, action: str, static_sha: str, session_sha: str | None,
) -> tuple[Path, dict[str, Any]]:
    if action not in {"start", "checkpoint-stop", "resume"}:
        raise AdaptiveChildResumeError("unsupported transport action")
    pairs = _action_pairs(root)
    sequence = len(pairs)
    previous = None if not pairs else pairs[-1][1]["record_sha256"]
    name = f"{sequence:06d}-{action}"
    claim_path = root / ACTIONS_DIR / f"{name}.claim.json"
    claim = seal({
        "schema_version": SCHEMA_VERSION, "kind": ACTION_CLAIM_KIND,
        "gate": GATE, "root": str(root),
        "root_identity": _directory_identity(root, require_mode_0700=True),
        "root_lock_identity": _lock_identity(root), "sequence": sequence,
        "action": action, "nonce_hex": os.urandom(32).hex(), "pid": os.getpid(),
        "static_sha256": static_sha, "session_sha256": session_sha,
        "previous_commit_sha256": previous, "terminal": False,
    })
    _publish_json(claim_path, claim)
    return claim_path, claim


def _finish_action(
    root: Path, claim_path: Path, claim: Mapping[str, Any], *,
    controller_result: Mapping[str, Any] | None, inspection: Mapping[str, Any],
    session_sha: str | None, transition: str,
    admitted_peer_rlimits: Mapping[str, Any] | None = None,
    recovered_interrupted_claim: bool = False,
) -> dict[str, Any]:
    if controller_result is not None and (
        type(controller_result) is not dict
        or not controller.selfhash_valid(controller_result)
    ):
        raise AdaptiveChildResumeError("controller action result self-hash mismatch")
    _validate_inspection(inspection, runtime=root / RUNTIME_ROOT)
    commit = seal({
        "schema_version": SCHEMA_VERSION, "kind": ACTION_COMMIT_KIND,
        "gate": GATE, "root": str(root),
        "root_identity": dict(claim["root_identity"]),
        "root_lock_identity": dict(claim["root_lock_identity"]),
        "sequence": claim["sequence"], "action": claim["action"],
        "claim_sha256": claim["record_sha256"],
        "static_sha256": claim["static_sha256"], "session_sha256": session_sha,
        "previous_commit_sha256": claim["previous_commit_sha256"],
        "transition": transition,
        "controller_result": None if controller_result is None else dict(controller_result),
        "controller_inspection": dict(inspection),
        "admitted_peer_rlimits": (
            None if admitted_peer_rlimits is None else dict(admitted_peer_rlimits)
        ),
        "transport_scientific_authority": False,
        "recovered_interrupted_claim": recovered_interrupted_claim,
    })
    commit_path = claim_path.with_name(
        claim_path.name.replace(".claim.json", ".commit.json")
    )
    _publish_json(commit_path, commit)
    return commit


def _session_value(
    root: Path, loaded: Mapping[str, Any], claim: Mapping[str, Any],
    config: Mapping[str, Any], started: Mapping[str, Any], inspection: Mapping[str, Any],
    cpu: int, peer_limits: Mapping[str, Any],
) -> dict[str, Any]:
    static = loaded["record"]
    return seal({
        "schema_version": SCHEMA_VERSION, "kind": SESSION_KIND, "gate": GATE,
        "state": "RUNNING", "root": str(root),
        "root_identity": _directory_identity(root, require_mode_0700=True),
        "root_lock_identity": _lock_identity(root),
        "static_sha256": static["record_sha256"],
        "overlay_manifest_sha256": static["overlay_manifest_sha256"],
        "switch_evidence_sha256": static["switch_evidence_sha256"],
        "descendant_sha256": static["selection"]["descendant_sha256"],
        "descendant_dimacs_sha256": static["descendant_cnf"]["dimacs_sha256"],
        "start_claim_sha256": claim["record_sha256"],
        "controller_root": str(root / RUNTIME_ROOT),
        "controller_config_sha256": config["self_sha256"],
        "controller_start_sha256": started["self_sha256"],
        "controller_start_pid": started["pid"],
        "controller_start_proc_start_ticks": started["proc_start_ticks"],
        "controller_initial_inspection": dict(inspection),
        "expected_single_cpu": cpu, "started_peer_rlimits": dict(peer_limits),
        "solver_args": list(SOLVER_ARGS),
        "proof_cap_bytes": static["resource_policy"]["proof_max_bytes"],
        "rlimit_policy": _rlimit_policy(static["resource_policy"]["proof_max_bytes"]),
        "source_binding_sha256": static["source_binding"]["source_binding_sha256"],
        "toolchain_sha256": static["toolchain_binding"]["toolchain_sha256"],
        "python_startup_sha256": static["python_startup"]["python_startup_sha256"],
        "transport_authority": "TEST_ONLY", "checkpoint_scientific_authority": False,
        "leaf_unsat_authenticated": False, "production_eligible": False,
    })


def _validate_session_value(
    root: Path, loaded: Mapping[str, Any], session: Mapping[str, Any],
) -> dict[str, Any]:
    fields = {
        "schema_version", "kind", "gate", "state", "root", "root_identity",
        "root_lock_identity", "static_sha256", "overlay_manifest_sha256",
        "switch_evidence_sha256", "descendant_sha256",
        "descendant_dimacs_sha256", "start_claim_sha256", "controller_root",
        "controller_config_sha256", "controller_start_sha256",
        "controller_start_pid", "controller_start_proc_start_ticks",
        "controller_initial_inspection", "expected_single_cpu",
        "started_peer_rlimits", "solver_args", "proof_cap_bytes",
        "rlimit_policy", "source_binding_sha256", "toolchain_sha256",
        "python_startup_sha256", "transport_authority",
        "checkpoint_scientific_authority",
        "leaf_unsat_authenticated", "production_eligible", "record_sha256",
    }
    static = loaded["record"]
    initial_generations = session.get("controller_initial_inspection", {}).get(
        "generations", [],
    ) if type(session) is dict else []
    initial_pid = (
        session.get("controller_start_pid")
        if type(session) is dict else None
    )
    if (
        type(session) is not dict or set(session) != fields
        or not selfhash_valid(session)
        or session["schema_version"] != SCHEMA_VERSION
        or type(session["schema_version"]) is not int
        or session["kind"] != SESSION_KIND or session["gate"] != GATE
        or session["state"] != "RUNNING" or session["root"] != str(root)
        or not json_type_equal(session["root_identity"], _directory_identity(root, require_mode_0700=True))
        or not json_type_equal(session["root_lock_identity"], _lock_identity(root))
        or session["static_sha256"] != static["record_sha256"]
        or session["overlay_manifest_sha256"] != static["overlay_manifest_sha256"]
        or session["switch_evidence_sha256"] != static["switch_evidence_sha256"]
        or session["descendant_sha256"] != static["selection"]["descendant_sha256"]
        or session["descendant_dimacs_sha256"] != static["descendant_cnf"]["dimacs_sha256"]
        or not _is_sha256(session["start_claim_sha256"])
        or session["controller_root"] != str(root / RUNTIME_ROOT)
        or not _is_sha256(session["controller_config_sha256"])
        or not _is_sha256(session["controller_start_sha256"])
        or type(session["controller_start_pid"]) is not int
        or session["controller_start_pid"] <= 0
        or type(session["controller_start_proc_start_ticks"]) is not int
        or session["controller_start_proc_start_ticks"] <= 0
        or type(session["expected_single_cpu"]) is not int
        or session["solver_args"] != list(SOLVER_ARGS)
        or session["proof_cap_bytes"] != static["resource_policy"]["proof_max_bytes"]
        or not json_type_equal(session["rlimit_policy"], _rlimit_policy(session["proof_cap_bytes"]))
        or session["source_binding_sha256"] != static["source_binding"]["source_binding_sha256"]
        or session["toolchain_sha256"] != static["toolchain_binding"]["toolchain_sha256"]
        or session["python_startup_sha256"] != static["python_startup"]["python_startup_sha256"]
        or session["transport_authority"] != "TEST_ONLY"
        or session["checkpoint_scientific_authority"] is not False
        or session["leaf_unsat_authenticated"] is not False
        or session["production_eligible"] is not False
    ):
        raise AdaptiveChildResumeError("session/static binding mismatch")
    initial = _validate_inspection(
        session["controller_initial_inspection"], runtime=root / RUNTIME_ROOT,
    )
    if (
        initial["state"] != "RUNNING"
        or initial["config_manifest_sha256"] != session["controller_config_sha256"]
        or not initial["generations"]
        or type(initial["generations"][-1]) is not dict
        or initial["generations"][-1].get("active_manifest_sha256")
        != session["controller_start_sha256"]
        or type(initial_pid) is not int
    ):
        raise AdaptiveChildResumeError("session initial controller binding mismatch")
    _validate_peer_rlimits(
        session["started_peer_rlimits"],
        expected_pid=initial_pid, cap=session["proof_cap_bytes"],
    )
    return dict(session)


def _load_session(root: Path, loaded: Mapping[str, Any]) -> dict[str, Any]:
    session = _validate_session_value(
        root, loaded, _read_json(root / SESSION_COMMIT, root=root),
    )
    pairs = _action_pairs(root)
    first_result = (
        None if not pairs else pairs[0][1]["controller_result"]
    )
    if (
        not pairs or pairs[0][0]["action"] != "start"
        or pairs[0][0]["record_sha256"] != session["start_claim_sha256"]
        or pairs[0][1]["session_sha256"] != session["record_sha256"]
        or pairs[0][1]["transition"] not in {
            "STARTED_RUNNING", "RECOVERED_START_RUNNING",
        }
        or (
            first_result is not None
            and (
                first_result.get("self_sha256")
                != session["controller_start_sha256"]
                or first_result.get("pid")
                != session["controller_start_pid"]
                or first_result.get("proc_start_ticks")
                != session["controller_start_proc_start_ticks"]
            )
        )
    ):
        raise AdaptiveChildResumeError("session lacks exact immutable start action")
    if any(
        claim["static_sha256"] != session["static_sha256"]
        or commit["static_sha256"] != session["static_sha256"]
        or (index > 0 and claim["session_sha256"] != session["record_sha256"])
        for index, (claim, commit) in enumerate(pairs)
    ):
        raise AdaptiveChildResumeError("action ledger breaks static/session chain")
    return session


def _action_kwargs(
    *, instance: Any | None, switch_verifier: Callable[..., Mapping[str, Any]] | None,
    science_modules: tuple[Any, Any, Any, Any] | None,
) -> dict[str, Any]:
    return {
        "instance": instance, "switch_verifier": switch_verifier,
        "science_modules": science_modules,
    }


@contextlib.contextmanager
def _temporary_cpu(cpu: int) -> Iterator[None]:
    if type(cpu) is not int:
        raise AdaptiveChildResumeError("CPU must be a strict integer")
    previous = os.sched_getaffinity(0)
    if cpu not in previous:
        raise AdaptiveChildResumeError(
            f"CPU {cpu} is outside caller affinity {sorted(previous)}"
        )
    os.sched_setaffinity(0, {cpu})
    try:
        yield
    finally:
        os.sched_setaffinity(0, previous)


def _preflight_cpu(cpu: int) -> None:
    if type(cpu) is not int or cpu not in os.sched_getaffinity(0):
        raise AdaptiveChildResumeError("CPU preflight failed")
    previous = os.sched_getaffinity(0)
    os.sched_setaffinity(0, {cpu})
    os.sched_setaffinity(0, previous)


class _PostSpawnFailure(AdaptiveChildResumeError):
    def __init__(self, message: str, quiescence: Mapping[str, Any]) -> None:
        super().__init__(message)
        self.quiescence = dict(quiescence)


def _start_locked(
    target: Path, loaded: Mapping[str, Any], *, cpu: int,
    pin_parent_cpu: bool, lane_index: int | None = None,
    descendant_index: int | None = None,
    started_hook: Callable[[Mapping[str, Any]], Any] | None = None,
) -> dict[str, Any]:
    if (target / SESSION_COMMIT).exists() or _terminal_bundle_present(target):
        raise AdaptiveChildResumeError("root was already started or terminally claimed")
    static = loaded["record"]
    cap = static["resource_policy"]["proof_max_bytes"]
    _preflight_solver_limits(cap)
    _preflight_cpu(cpu)
    tools = static["toolchain_binding"]["tools"]
    runtime_libs = [
        Path(item["path"])
        for item in static["toolchain_binding"]["runtime_libraries"]
    ]
    dmtcp_prefix = Path(static["toolchain_binding"]["dmtcp"]["prefix"])
    claim_path, claim = _begin_action(
        target, action="start", static_sha=static["record_sha256"],
        session_sha=None,
    )
    cpu_context = _temporary_cpu(cpu) if pin_parent_cpu else contextlib.nullcontext()
    started: dict[str, Any] | None = None
    started_worker: Any | None = None
    try:
        with cpu_context, _fixed_environment(), _inherited_solver_limits(cap):
            config = controller.initialize(
                target / RUNTIME_ROOT, cnf=target / STATIC_DESCENDANT_CNF,
                solver=Path(tools["cadical_solver"]["path"]),
                dmtcp_prefix=dmtcp_prefix, solver_args=list(SOLVER_ARGS),
                runtime_libs=runtime_libs, runtime_libs_complete=True,
            )
            started = controller.start(target / RUNTIME_ROOT)
            if started_hook is not None:  # first throwable call after start
                started_worker = started_hook(started)
        if not controller.selfhash_valid(config) or not controller.selfhash_valid(started):
            raise AdaptiveChildResumeError("controller init/start self-hash mismatch")
        peer_limits = _admit_live_peer(started, cpu=cpu, cap=cap)
        inspection = _inspect_controller(target)
        if (
            inspection["state"] != "RUNNING"
            or inspection["config_manifest_sha256"] != config["self_sha256"]
            or not inspection["generations"]
            or inspection["generations"][-1].get("active_manifest_sha256")
            != started["self_sha256"]
        ):
            raise AdaptiveChildResumeError("controller start/inspect binding mismatch")
        session = _session_value(
            target, loaded, claim, config, started, inspection, cpu, peer_limits,
        )
        _publish_json(target / SESSION_COMMIT, session)
        action_commit = _finish_action(
            target, claim_path, claim, controller_result=started,
            inspection=inspection, session_sha=session["record_sha256"],
            transition="STARTED_RUNNING", admitted_peer_rlimits=peer_limits,
        )
        return {
            "session": session, "action_commit": action_commit,
            "controller_start": dict(started), "started_worker": started_worker,
        }
    except BaseException as exc:
        if started is None:
            raise
        quiescence = _stop_failed_new_root(
            target, {"controller_start": dict(started)}, lane_index=lane_index,
            descendant_index=descendant_index,
        )
        failure = _PostSpawnFailure(
            f"post-spawn start failed: {type(exc).__name__}: {exc}", quiescence,
        )
        failure.__cause__ = exc
        raise failure


def start_root(
    root: Path, *, instance: Any | None = None,
    switch_verifier: Callable[..., Mapping[str, Any]] | None = None,
    science_modules: tuple[Any, Any, Any, Any] | None = None,
) -> dict[str, Any]:
    target = _existing_root(root)
    with _root_lock(target, exclusive=True):
        loaded = _load_static(target, **_action_kwargs(
            instance=instance, switch_verifier=switch_verifier,
            science_modules=science_modules,
        ))
        if loaded["record"]["strict_base"] is True:
            raise AdaptiveChildResumeError(
                "strict first start requires start-batch atomic switch-v4 lease"
            )
        cpu = _single_cpu()
        return _start_locked(target, loaded, cpu=cpu, pin_parent_cpu=False)["session"]


class _BatchTransportToken:
    """Process-local proof that all cover-root locks are held by one scheduler."""

    __slots__ = (
        "_owner_pid", "_owner_thread", "_roots", "_actions", "_used",
    )

    def __init__(
        self, roots: Sequence[Path], *, actions: Sequence[str],
    ) -> None:
        canonical = tuple(sorted(str(Path(root)) for root in roots))
        if (
            len(canonical) not in {COHORT_SIZE, COVER_ROOT_COUNT}
            or len(set(canonical)) != len(canonical)
            or type(actions) not in (list, tuple)
            or not actions
            or any(
                action not in {"checkpoint-stop", "resume"}
                for action in actions
            )
        ):
            raise AdaptiveChildResumeError("batch transport token scope malformed")
        self._owner_pid = os.getpid()
        self._owner_thread = threading.get_ident()
        self._roots = frozenset(canonical)
        self._actions = frozenset(actions)
        self._used: set[tuple[str, str]] = set()

    def consume(self, root: Path, action: str) -> None:
        key = (str(root), action)
        if (
            os.getpid() != self._owner_pid
            or threading.get_ident() != self._owner_thread
            or str(root) not in self._roots
            or action not in self._actions
            or key in self._used
        ):
            raise AdaptiveChildResumeError("batch transport token is stale/foreign")
        self._used.add(key)

    def __reduce__(self) -> Any:
        raise TypeError("batch transport token cannot be serialized")

    def __copy__(self) -> Any:
        raise TypeError("batch transport token cannot be copied")

    def __deepcopy__(self, memo: Any) -> Any:
        del memo
        raise TypeError("batch transport token cannot be copied")


def _checkpoint_stop_locked(
    target: Path, *, instance: Any | None = None,
    switch_verifier: Callable[..., Mapping[str, Any]] | None = None,
    science_modules: tuple[Any, Any, Any, Any] | None = None,
    batch_token: _BatchTransportToken | None = None,
) -> dict[str, Any]:
    loaded = _load_static(target, **_action_kwargs(
        instance=instance, switch_verifier=switch_verifier,
        science_modules=science_modules,
    ))
    session = _load_session(target, loaded)
    if loaded["record"]["strict_base"] is True:
        if batch_token is None:
            _verify_complete_handoff_links(target, loaded, session)
        else:
            batch_token.consume(target, "checkpoint-stop")
    elif batch_token is not None:
        raise AdaptiveChildResumeError("synthetic checkpoint rejects batch token")
    if _terminal_bundle_present(target):
        raise AdaptiveChildResumeError("terminal stage already claimed")
    if _single_cpu() != session["expected_single_cpu"]:
        raise AdaptiveChildResumeError("checkpoint CPU differs from session CPU")
    before = _inspect_controller(target)
    if before["state"] != "RUNNING":
        raise AdaptiveChildResumeError("checkpoint-stop requires RUNNING transport")
    claim_path, claim = _begin_action(
        target, action="checkpoint-stop", static_sha=loaded["record"]["record_sha256"],
        session_sha=session["record_sha256"],
    )
    with _fixed_environment():
        result = controller.checkpoint_stop(target / RUNTIME_ROOT)
    after = _inspect_controller(target)
    if (
        not controller.selfhash_valid(result) or after["state"] != "CHECKPOINTED"
        or not after["generations"]
        or after["generations"][-1].get("checkpoint_manifest_sha256") != result["self_sha256"]
        or after["generations"][-1].get("pid_identity_alive") is not False
    ):
        raise AdaptiveChildResumeError("checkpoint result/inspect binding mismatch")
    proof = _safe_root_path(target, RUNTIME_ROOT / "proof.drat")
    first = _stream_record(proof, cap=session["proof_cap_bytes"], root=target, role="checkpoint-stop-proof")
    holders = _writable_holders(proof)
    second = _stream_record(proof, cap=session["proof_cap_bytes"], root=target, role="checkpoint-stop-proof")
    if holders or not json_type_equal(first, second):
        raise AdaptiveChildResumeError("checkpoint proof is not stable/writer-free")
    return _finish_action(
        target, claim_path, claim, controller_result=result, inspection=after,
        session_sha=session["record_sha256"], transition="CHECKPOINTED_STOPPED",
    )


def checkpoint_stop_root(
    root: Path, *, instance: Any | None = None,
    switch_verifier: Callable[..., Mapping[str, Any]] | None = None,
    science_modules: tuple[Any, Any, Any, Any] | None = None,
) -> dict[str, Any]:
    target = _existing_root(root)
    with _root_lock(target, exclusive=True):
        return _checkpoint_stop_locked(
            target, instance=instance, switch_verifier=switch_verifier,
            science_modules=science_modules,
        )


def _resume_locked(
    target: Path, *, instance: Any | None = None,
    switch_verifier: Callable[..., Mapping[str, Any]] | None = None,
    science_modules: tuple[Any, Any, Any, Any] | None = None,
    batch_token: _BatchTransportToken | None = None,
) -> dict[str, Any]:
    loaded = _load_static(target, **_action_kwargs(
        instance=instance, switch_verifier=switch_verifier,
        science_modules=science_modules,
    ))
    session = _load_session(target, loaded)
    if loaded["record"]["strict_base"] is True:
        _verify_complete_handoff_links(target, loaded, session)
        if batch_token is None:
            raise AdaptiveChildResumeError(
                "strict resume requires the eight-root cohort scheduler"
            )
        batch_token.consume(target, "resume")
    elif batch_token is not None:
        raise AdaptiveChildResumeError("synthetic resume rejects batch token")
    if _terminal_bundle_present(target):
        raise AdaptiveChildResumeError("terminal stage already claimed")
    cpu = _single_cpu()
    if cpu != session["expected_single_cpu"]:
        raise AdaptiveChildResumeError("resume CPU differs from session CPU")
    before = _inspect_controller(target)
    if before["state"] != "CHECKPOINTED":
        raise AdaptiveChildResumeError("resume requires CHECKPOINTED transport")
    cap = session["proof_cap_bytes"]
    _preflight_solver_limits(cap)
    claim_path, claim = _begin_action(
        target, action="resume", static_sha=loaded["record"]["record_sha256"],
        session_sha=session["record_sha256"],
    )
    result: dict[str, Any] | None = None
    try:
        with _fixed_environment(), _inherited_solver_limits(cap):
            result = controller.resume(target / RUNTIME_ROOT)
        peer_limits = _admit_live_peer(result, cpu=cpu, cap=cap)
        after = _inspect_controller(target)
        if (
            not controller.selfhash_valid(result) or after["state"] != "RUNNING"
            or not after["generations"]
            or after["generations"][-1].get("active_manifest_sha256") != result["self_sha256"]
        ):
            raise AdaptiveChildResumeError("resume result/inspect binding mismatch")
        return _finish_action(
            target, claim_path, claim, controller_result=result, inspection=after,
            session_sha=session["record_sha256"], transition="RESUMED_RUNNING",
            admitted_peer_rlimits=peer_limits,
        )
    except BaseException as exc:
        if result is None:
            raise
        quiescence = _stop_failed_new_root(
            target, {"controller_start": dict(result)}, lane_index=None,
        )
        failure = _PostSpawnFailure(
            f"post-spawn resume failed: {type(exc).__name__}: {exc}", quiescence,
        )
        failure.__cause__ = exc
        raise failure


def resume_root(
    root: Path, *, instance: Any | None = None,
    switch_verifier: Callable[..., Mapping[str, Any]] | None = None,
    science_modules: tuple[Any, Any, Any, Any] | None = None,
) -> dict[str, Any]:
    target = _existing_root(root)
    with _root_lock(target, exclusive=True):
        return _resume_locked(
            target, instance=instance, switch_verifier=switch_verifier,
            science_modules=science_modules,
        )


def status_root(
    root: Path, *, instance: Any | None = None,
    switch_verifier: Callable[..., Mapping[str, Any]] | None = None,
    science_modules: tuple[Any, Any, Any, Any] | None = None,
) -> dict[str, Any]:
    target = _existing_root(root)
    with _root_lock(target, exclusive=False):
        loaded = _load_static(target, **_action_kwargs(
            instance=instance, switch_verifier=switch_verifier,
            science_modules=science_modules,
        ))
        session = _load_session(target, loaded)
        handoff = None
        if loaded["record"]["strict_base"] is True:
            handoff = _verify_complete_handoff_links(target, loaded, session)
        inspection = _inspect_controller(target)
        return seal({
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-dic5-adaptive-child-status-v5", "gate": GATE,
            "root": str(target), "static_sha256": loaded["record"]["record_sha256"],
            "session_sha256": session["record_sha256"],
            "controller_inspection": inspection,
            "handoff_verification_sha256": (
                None if handoff is None else handoff["record_sha256"]
            ),
            "read_only": True, "scientific_claim": False,
        })


def _recover_action_locked(
    target: Path, *, instance: Any | None = None,
    switch_verifier: Callable[..., Mapping[str, Any]] | None = None,
    science_modules: tuple[Any, Any, Any, Any] | None = None,
) -> dict[str, Any]:
    loaded = _load_static(target, **_action_kwargs(
        instance=instance, switch_verifier=switch_verifier,
        science_modules=science_modules,
    ))
    entries = sorted((target / ACTIONS_DIR).iterdir(), key=lambda item: item.name)
    grouped: dict[tuple[int, str], dict[str, Path]] = {}
    for path in entries:
        match = ACTION_RE.fullmatch(path.name)
        if match is None:
            raise AdaptiveChildResumeError("unexpected action-ledger entry")
        key = (int(match.group("sequence")), match.group("action"))
        grouped.setdefault(key, {})[match.group("stage")] = path
    incomplete = [key for key, stages in grouped.items() if set(stages) == {"claim"}]
    if len(incomplete) != 1 or incomplete[0] != max(grouped):
        raise AdaptiveChildResumeError("no unique last interrupted claim")
    sequence, action = incomplete[0]
    if sequence != len(grouped) - 1 or action not in {"start", "checkpoint-stop", "resume"}:
        raise AdaptiveChildResumeError("interrupted claim position/action mismatch")
    claim_path = grouped[incomplete[0]]["claim"]
    claim = _read_json(claim_path, root=target)
    claim_fields = {
        "schema_version", "kind", "gate", "root", "root_identity",
        "root_lock_identity", "sequence", "action", "nonce_hex", "pid",
        "static_sha256", "session_sha256", "previous_commit_sha256",
        "terminal", "record_sha256",
    }
    previous = None
    if sequence:
        previous_key = sorted(grouped)[sequence - 1]
        previous_stages = grouped[previous_key]
        if set(previous_stages) != {"claim", "commit"}:
            raise AdaptiveChildResumeError("earlier action stage is incomplete")
        previous_commit = _read_json(previous_stages["commit"], root=target)
        if not selfhash_valid(previous_commit):
            raise AdaptiveChildResumeError("earlier action commit is malformed")
        previous = previous_commit["record_sha256"]
    if (
        type(claim) is not dict or set(claim) != claim_fields
        or not selfhash_valid(claim) or claim["schema_version"] != SCHEMA_VERSION
        or type(claim["schema_version"]) is not int
        or claim["kind"] != ACTION_CLAIM_KIND or claim["gate"] != GATE
        or claim["root"] != str(target) or claim["sequence"] != sequence
        or type(claim["sequence"]) is not int or claim["action"] != action
        or claim["static_sha256"] != loaded["record"]["record_sha256"]
        or claim["previous_commit_sha256"] != previous
        or claim["terminal"] is not False
        or not json_type_equal(claim["root_identity"], _directory_identity(target, require_mode_0700=True))
        or not json_type_equal(claim["root_lock_identity"], _lock_identity(target))
    ):
        raise AdaptiveChildResumeError("interrupted claim is malformed")
    raw_session = _read_json(target / SESSION_COMMIT, root=target)
    session = _validate_session_value(target, loaded, raw_session)
    if (
        (action == "start" and (
            claim["session_sha256"] is not None
            or claim["record_sha256"] != session["start_claim_sha256"]
        ))
        or (action != "start" and claim["session_sha256"] != session["record_sha256"])
    ):
        raise AdaptiveChildResumeError("interrupted claim/session mismatch")
    inspection = _inspect_controller(target)
    if inspection["state"] not in {
        "RUNNING", "CHECKPOINTED", "INACTIVE_UNCHECKPOINTED",
    }:
        raise AdaptiveChildResumeError("interrupted action state is not recoverable")
    commit = _finish_action(
        target, claim_path, claim, controller_result=None,
        inspection=inspection, session_sha=session["record_sha256"],
        transition=f"RECOVERED_{action.upper().replace('-', '_')}_{inspection['state']}",
        recovered_interrupted_claim=True,
    )
    _action_pairs(target)
    return commit




def recover_action(
    root: Path, *, instance: Any | None = None,
    switch_verifier: Callable[..., Mapping[str, Any]] | None = None,
    science_modules: tuple[Any, Any, Any, Any] | None = None,
) -> dict[str, Any]:
    target = _existing_root(root)
    with _root_lock(target, exclusive=True):
        return _recover_action_locked(
            target, instance=instance, switch_verifier=switch_verifier,
            science_modules=science_modules,
        )


def _last_action_is_incomplete(root: Path) -> bool:
    grouped: dict[tuple[int, str], set[str]] = {}
    for path in sorted((root / ACTIONS_DIR).iterdir(), key=lambda item: item.name):
        match = ACTION_RE.fullmatch(path.name)
        if match is None:
            raise AdaptiveChildResumeError("unexpected action-ledger entry")
        key = (int(match.group("sequence")), match.group("action"))
        stage = match.group("stage")
        if stage in grouped.setdefault(key, set()):
            raise AdaptiveChildResumeError("duplicate action-ledger stage")
        grouped[key].add(stage)
    incomplete = [key for key, stages in grouped.items() if stages != {"claim", "commit"}]
    return (
        len(incomplete) == 1 and bool(grouped)
        and incomplete[0] == max(grouped)
        and grouped[incomplete[0]] == {"claim"}
    )


def _cover_roots_cpus(
    roots: Sequence[Path], cpus: Sequence[int],
) -> tuple[list[Path], list[int]]:
    """Admit exactly eight canonical root/CPU pairs with four live CPUs."""

    if type(roots) not in (list, tuple) or type(cpus) not in (list, tuple):
        raise AdaptiveChildResumeError("cover roots/CPUs must be list/tuple")
    resolved = [_existing_root(Path(item)) for item in roots]
    cpu_list = list(cpus)
    if (
        len(resolved) != COVER_ROOT_COUNT
        or len(cpu_list) != COVER_ROOT_COUNT
        or len(set(resolved)) != COVER_ROOT_COUNT
        or any(type(cpu) is not int for cpu in cpu_list)
        or cpu_list[:COHORT_SIZE] != cpu_list[COHORT_SIZE:]
        or len(set(cpu_list[:COHORT_SIZE])) != COHORT_SIZE
        or any(cpu_list.count(cpu) != DESCENDANTS_PER_LANE for cpu in set(cpu_list))
    ):
        raise AdaptiveChildResumeError(
            "cover requires eight unique roots and four CPUs repeated cohort-major"
        )
    available = os.sched_getaffinity(0)
    if any(cpu not in available for cpu in cpu_list):
        raise AdaptiveChildResumeError(
            f"cover CPU is outside caller affinity {sorted(available)}"
        )
    for cpu in sorted(set(cpu_list)):
        _preflight_cpu(cpu)
    return resolved, cpu_list


def _batch_common(loaded_items: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    if len(loaded_items) != COVER_ROOT_COUNT:
        raise AdaptiveChildResumeError(
            "atomic handoff requires the complete eight-root cover"
        )
    records = [item["record"] for item in loaded_items]
    fields = (
        "batch_root_identity", "switch_evidence_sha256", "switch_policy",
    )
    for field in fields:
        if any(
            not json_type_equal(record[field], records[0][field])
            for record in records[1:]
        ):
            raise AdaptiveChildResumeError(f"eight roots disagree on {field}")
    pins = [record["external_pins"] for record in records]
    for field in (
        "expected_switch_evidence_sha256",
        "expected_batch_manifest_sha256",
    ):
        if any(pin[field] != pins[0][field] for pin in pins[1:]):
            raise AdaptiveChildResumeError(f"eight roots disagree on {field}")
    switch_records = [item["switch_evidence"] for item in loaded_items]
    if any(
        not json_type_equal(value, switch_records[0])
        for value in switch_records[1:]
    ):
        raise AdaptiveChildResumeError("eight roots bind different switch records")
    lanes = switch_records[0].get("lanes")
    if type(lanes) is not list or len(lanes) != LANE_COUNT:
        raise AdaptiveChildResumeError("switch record lacks four exact lanes")
    lane_by_leaf: dict[int, dict[str, Any]] = {}
    hard_pins: list[str] = []
    for lane_index, lane in enumerate(lanes):
        if (
            type(lane) is not dict
            or type(lane.get("lane_index")) is not int
            or lane["lane_index"] != lane_index
            or type(lane.get("global_leaf_index")) is not int
            or lane["global_leaf_index"] in lane_by_leaf
            or not _is_sha256(lane.get("hard_evidence_sha256"))
        ):
            raise AdaptiveChildResumeError("switch lane layout/hard pin is malformed")
        lane_by_leaf[lane["global_leaf_index"]] = lane
        hard_pins.append(lane["hard_evidence_sha256"])
    observed_keys: list[tuple[int, int]] = []
    candidate_by_lane: dict[int, list[int]] = {}
    for record in records:
        selection = record["selection"]
        leaf = selection["global_leaf_index"]
        descendant = selection["descendant_index"]
        lane = lane_by_leaf.get(leaf)
        if (
            type(descendant) is not int
            or descendant not in range(DESCENDANTS_PER_LANE)
            or lane is None
            or record["external_pins"]["expected_hard_evidence_sha256"]
            != lane["hard_evidence_sha256"]
        ):
            raise AdaptiveChildResumeError(
                "prepared root misses an exact switch lane/descendant"
            )
        lane_index = lane["lane_index"]
        observed_keys.append((lane_index, descendant))
        candidates = selection["candidate_variables"]
        if lane_index in candidate_by_lane and not json_type_equal(
            candidate_by_lane[lane_index], candidates,
        ):
            raise AdaptiveChildResumeError(
                "sibling roots disagree on candidate-variable order"
            )
        candidate_by_lane[lane_index] = list(candidates)
    if (
        len(observed_keys) != len(set(observed_keys))
        or set(observed_keys) != set(TARGET_KEYS)
    ):
        raise AdaptiveChildResumeError(
            "prepared roots do not cover both descendants of all four lanes"
        )
    return {
        "batch_root": Path(records[0]["batch_root_identity"]["path"]),
        "expected_switch_evidence_sha256": pins[0][
            "expected_switch_evidence_sha256"
        ],
        "expected_batch_manifest_sha256": pins[0][
            "expected_batch_manifest_sha256"
        ],
        "expected_hard_evidence_sha256s": list(hard_pins),
        "timeout_seconds": records[0]["switch_policy"]["timeout_seconds"],
        "elapsed_seconds_by_lane": list(
            records[0]["switch_policy"]["elapsed_seconds_by_lane"]
        ),
        "lane_by_leaf": {
            str(leaf): lane["lane_index"]
            for leaf, lane in lane_by_leaf.items()
        },
        "target_keys": [list(key) for key in TARGET_KEYS],
    }


def _cover_entries(
    roots: Sequence[Path], cpus: Sequence[int],
    loaded_items: Sequence[Mapping[str, Any]],
) -> list[dict[str, Any]]:
    common = _batch_common(loaded_items)
    lane_by_leaf = {
        int(leaf): lane for leaf, lane in common["lane_by_leaf"].items()
    }
    entries: list[dict[str, Any]] = []
    for root, cpu, loaded in zip(roots, cpus, loaded_items, strict=True):
        selection = loaded["record"]["selection"]
        key = (
            lane_by_leaf.get(selection["global_leaf_index"]),
            selection["descendant_index"],
        )
        entries.append({
            "root": root, "cpu": cpu, "loaded": loaded,
            "lane_index": key[0], "descendant_index": key[1],
            "target_key": key,
        })
    keys = [entry["target_key"] for entry in entries]
    if keys != list(TARGET_KEYS):
        raise AdaptiveChildResumeError(
            "root arguments must be canonical cohort-major target order"
        )
    for lane_index in range(LANE_COUNT):
        first = entries[lane_index]
        second = entries[COHORT_SIZE + lane_index]
        if first["cpu"] != second["cpu"]:
            raise AdaptiveChildResumeError(
                "sibling roots must reuse their lane CPU"
            )
    return entries


def _permit_kwargs(loaded: Mapping[str, Any]) -> dict[str, Any]:
    static = loaded["record"]
    return {
        "overlay_manifest": loaded["overlay"],
        "expected_overlay_sha256": static["external_pins"][
            "expected_overlay_sha256"
        ],
        "global_leaf_index": static["selection"]["global_leaf_index"],
        "expected_hard_evidence_sha256": static["external_pins"][
            "expected_hard_evidence_sha256"
        ],
        "candidate_variables": list(
            static["selection"]["candidate_variables"]
        ),
        "descendant_index": static["selection"]["descendant_index"],
        "expected_descendant_sha256": static["selection"][
            "descendant_sha256"
        ],
    }


def _stop_failed_new_root(
    target: Path, started: Mapping[str, Any], *,
    lane_index: int | None, descendant_index: int | None = None,
) -> dict[str, Any]:
    result = started.get("controller_start")
    if type(result) is not dict:
        raise AdaptiveChildResumeError("cleanup lacks started process identity")
    pid = result.get("pid")
    ticks = result.get("proc_start_ticks")
    if type(pid) is not int or type(ticks) is not int:
        raise AdaptiveChildResumeError("cleanup process identity is malformed")
    try:
        with _fixed_environment():
            controller.checkpoint_stop(target / RUNTIME_ROOT)
    except BaseException:
        with contextlib.suppress(BaseException):
            controller._kill_spawned_group(pid, ticks)
        with contextlib.suppress(BaseException):
            controller._wait_pid_gone(pid, ticks)
    inspection = _inspect_controller(target)
    if (
        controller._pid_identity(pid, ticks)
        or inspection["state"] not in {
            "CHECKPOINTED", "INACTIVE_UNCHECKPOINTED",
        }
        or not inspection["generations"]
        or inspection["generations"][-1].get("pid_identity_alive") is not False
    ):
        raise AdaptiveChildResumeError(
            f"failed handoff cleanup left solver alive: {target}"
        )
    static = _read_json(target / STATIC_COMMIT, root=target)
    proof = _safe_root_path(target, RUNTIME_ROOT / "proof.drat")
    first = _stream_record(
        proof, cap=static["resource_policy"]["proof_max_bytes"],
        root=target, role="failed-start-proof",
    )
    holders = _writable_holders(proof)
    second = _stream_record(
        proof, cap=static["resource_policy"]["proof_max_bytes"],
        root=target, role="failed-start-proof",
    )
    if holders or not json_type_equal(first, second):
        raise AdaptiveChildResumeError(
            f"failed handoff proof is not writer-free/stable: {target}"
        )
    latest = inspection["generations"][-1]
    checkpoint_sha = latest.get("checkpoint_manifest_sha256")
    if (
        inspection["state"] == "CHECKPOINTED"
        and not _is_sha256(checkpoint_sha)
    ) or (
        inspection["state"] == "INACTIVE_UNCHECKPOINTED"
        and checkpoint_sha is not None
    ):
        raise AdaptiveChildResumeError(
            "failed-start checkpoint binding is inconsistent"
        )
    if lane_index is None:
        if descendant_index is not None:
            raise AdaptiveChildResumeError("local cleanup has descendant index")
        return seal({
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-adaptive-new-root-quiescence-local-v5",
            "root": str(target),
            "new_pid": pid,
            "new_proc_start_ticks": ticks,
            "state": inspection["state"],
            "pid_identity_alive": False,
            "proof_sha256": first["sha256"],
            "proof_bytes": first["bytes"],
            "writable_holders": [],
        })
    if (
        type(lane_index) is not int or not 0 <= lane_index < LANE_COUNT
        or type(descendant_index) is not int
        or descendant_index not in range(DESCENDANTS_PER_LANE)
    ):
        raise AdaptiveChildResumeError("cleanup target key is malformed")
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-adaptive-new-root-quiescence-observation-v5",
        "lane_index": lane_index,
        "descendant_index": descendant_index,
        "new_root_identity": _directory_identity(
            target, require_mode_0700=True,
        ),
        "new_pid": pid,
        "new_proc_start_ticks": ticks,
        "state": inspection["state"],
        "pid_identity_alive": False,
        "checkpoint_commit_sha256": checkpoint_sha,
        "proof_sha256": first["sha256"],
        "proof_bytes": first["bytes"],
        "writable_holders": [],
    })


def _target_key_from_quiescence(value: Mapping[str, Any]) -> tuple[int, int]:
    key = (value.get("lane_index"), value.get("descendant_index"))
    if (
        type(key[0]) is not int or type(key[1]) is not int
        or key not in TARGET_KEYS
    ):
        raise AdaptiveChildResumeError("quiescence target key is malformed")
    return key


def _atomic_handoff_start(
    lease: Any, entries: Sequence[dict[str, Any]], *,
    batch_commit_path: Path,
    outer_locks: Sequence[_TransferableRootLock],
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    """Atomically first-start the exact eight-root cover with <=4 live."""

    if (
        [entry.get("target_key") for entry in entries] != list(TARGET_KEYS)
        or type(outer_locks) not in (list, tuple)
        or len(outer_locks) != COVER_ROOT_COUNT
        or any(
            lock.root != entry["root"]
            for lock, entry in zip(outer_locks, entries, strict=True)
        )
    ):
        raise AdaptiveChildResumeError(
            "atomic entries/outer locks are not canonical cover"
        )
    exact_transferable_locks = all(
        type(lock) is _TransferableRootLock for lock in outer_locks
    )
    if not exact_transferable_locks and any(
        not callable(getattr(lock, "complete_transfer", None))
        for lock in outer_locks
    ):
        raise AdaptiveChildResumeError(
            "outer lock test seam lacks transfer operation"
        )
    permits: dict[tuple[int, int], Any] = {}
    started_entries: dict[tuple[int, int], dict[str, Any]] = {}
    spawn_attempts: set[tuple[int, int]] = set()
    early_quiescence: dict[tuple[int, int], dict[str, Any]] = {}
    fences: dict[tuple[int, int], Any] = {}
    committed = False
    outer_transferred = False
    try:
        outer_fds = tuple(
            (
                lock.validated_transfer_fd()
                if exact_transferable_locks else lock.fileno()
            )
            for lock in outer_locks
        )
        for entry in entries:
            permits[entry["target_key"]] = lease.verify_target(
                **_permit_kwargs(entry["loaded"])
            )
        prepared_targets = []
        for entry in entries:
            prepared_targets.append(lease.prepare_target(
                permit=permits[entry["target_key"]],
                new_root_identity=_directory_identity(
                    entry["root"], require_mode_0700=True,
                ),
            ))
        if (
            len(prepared_targets) != COVER_ROOT_COUNT
            or any(
                type(record) is not dict
                or not _is_sha256(record.get("record_sha256"))
                for record in prepared_targets
            )
        ):
            raise AdaptiveChildResumeError(
                "switch-v4 prepared-target journals malformed"
            )
        adoption = lease.adopt_prepared_outer_locks(
            outer_lock_fds=list(outer_fds),
        )
        # Successful return means switch-v4 owns duplicate references to all
        # eight OFDs. From this point the local ExitStack must never LOCK_UN.
        outer_transferred = True
        _relinquish_adopted_outer_locks(
            outer_locks, outer_fds,
            exact_transferable_locks=exact_transferable_locks,
        )
        if adoption is not None:
            raise AdaptiveChildResumeError(
                "switch-v4 outer-lock adoption must return None"
            )

        def start_entry(
            entry: dict[str, Any], cohort_transition_permit: Any | None,
        ) -> None:
            key = entry["target_key"]
            permit = permits[key]

            def note(active: Mapping[str, Any]) -> Any:
                # A solver exists at this boundary.  Mark the attempt before
                # the durable journal call; switch-v4 registers the key before
                # publishing so its process-local registry is authoritative.
                spawn_attempts.add(key)
                return lease.note_started_worker(
                    permit=permit,
                    new_root_identity=_directory_identity(
                        entry["root"], require_mode_0700=True,
                    ),
                    new_pid=active["pid"],
                    new_proc_start_ticks=active["proc_start_ticks"],
                    cohort_transition_permit=cohort_transition_permit,
                )

            try:
                started = _start_locked(
                    entry["root"], entry["loaded"], cpu=entry["cpu"],
                    pin_parent_cpu=True, lane_index=entry["lane_index"],
                    descendant_index=entry["descendant_index"],
                    started_hook=note,
                )
            except _PostSpawnFailure as exc:
                if key in spawn_attempts:
                    early_quiescence[key] = exc.quiescence
                raise
            entry["started"] = started
            started_entries[key] = entry
            fences[key] = lease.post_start_fence(
                permit=permit,
                started_worker=started["started_worker"],
                new_session_sha256=started["session"]["record_sha256"],
                new_start_commit_sha256=started[
                    "controller_start"
                ]["self_sha256"],
            )

        for entry in entries[:COHORT_SIZE]:
            start_entry(entry, None)

        checkpoint_token = _BatchTransportToken(
            [entry["root"] for entry in entries[:COHORT_SIZE]],
            actions=["checkpoint-stop"],
        )
        cohort_quiescence: list[dict[str, Any]] = []
        for entry in entries[:COHORT_SIZE]:
            with _temporary_cpu(entry["cpu"]):
                _checkpoint_stop_locked(
                    entry["root"], batch_token=checkpoint_token,
                )
            cohort_quiescence.append(_committed_quiescence_record(
                entry["root"], entry["lane_index"],
                entry["descendant_index"], entry["loaded"],
            ))
        transition = lease.note_cohort_checkpointed(
            quiescence_records=cohort_quiescence,
        )
        for entry in entries[COHORT_SIZE:]:
            start_entry(entry, transition)

        batch_commit = lease.commit_handoff(
            fences=[fences[key] for key in TARGET_KEYS],
            batch_commit_path=batch_commit_path,
        )
        committed = True
        if (
            type(batch_commit) is not dict
            or not _is_sha256(batch_commit.get("record_sha256"))
            or not _is_sha256(batch_commit.get("prepared_retirement_sha256"))
            or batch_commit.get("launch_authorized") is not False
            or type(batch_commit.get("root_bindings")) is not list
            or len(batch_commit["root_bindings"]) != COVER_ROOT_COUNT
        ):
            raise AdaptiveChildResumeError("switch-v4 cover commit schema mismatch")
        return dict(batch_commit), [
            started_entries[key] for key in TARGET_KEYS
        ]
    except BaseException as original:
        if committed:
            raise
        if not outer_transferred:
            raise AdaptiveChildResumeError(
                "handoff failed before continuous outer-lock adoption; "
                "PREPARED retirement retained"
            ) from original
        quiescence = dict(early_quiescence)
        cleanup_failures: list[str] = []
        for key in reversed(TARGET_KEYS):
            entry = started_entries.get(key)
            if entry is None or key in quiescence:
                continue
            try:
                quiescence[key] = _stop_failed_new_root(
                    entry["root"], entry["started"],
                    lane_index=entry["lane_index"],
                    descendant_index=entry["descendant_index"],
                )
            except BaseException as exc:
                cleanup_failures.append(f"{entry['root']}: {exc}")
        if cleanup_failures:
            raise AdaptiveChildResumeError(
                "cover cleanup failed; PREPARED retirement retained: "
                + "; ".join(cleanup_failures)
            )
        try:
            raw_registered = lease.started_target_keys()
            registered = set(raw_registered)
        except BaseException as exc:
            raise AdaptiveChildResumeError(
                "cannot obtain atomic started-target registry; "
                "PREPARED retirement retained"
            ) from exc
        if (
            any(
                type(key) is not tuple
                or len(key) != 2
                or type(key[0]) is not int
                or type(key[1]) is not int
                or key not in TARGET_KEYS
                for key in registered
            )
            or spawn_attempts != registered
            or set(quiescence) != registered
            or any(
                _target_key_from_quiescence(record) != key
                for key, record in quiescence.items()
            )
        ):
            raise AdaptiveChildResumeError(
                "cleanup partition differs from atomic registry; "
                "PREPARED retirement retained"
            )
        rollback = lease.rollback_after_new_quiescent(
            quiescence_records=[
                quiescence[key] for key in TARGET_KEYS if key in quiescence
            ],
            not_started_target_keys=[
                key for key in TARGET_KEYS if key not in registered
            ],
        )
        if (
            type(rollback) is not dict
            or rollback.get("launch_authorized") is not False
            or rollback.get("new_workers_quiescent") is not True
        ):
            raise AdaptiveChildResumeError(
                "switch-v4 explicit rollback attestation mismatch"
            )
        raise


_ROOT_BINDING_FIELDS = {
    "lane_index", "global_leaf_index", "descendant_index",
    "descendant_sha256", "new_root_identity", "new_session_sha256",
    "new_start_commit_sha256", "new_pid", "new_proc_start_ticks",
    "permit_binding_sha256", "prepared_target_sha256",
    "started_worker_journal_sha256", "fence_sha256", "cohort_index",
    "handoff_state", "cohort_quiescence_sha256",
}


def _binding_for_root(
    verification: Mapping[str, Any], root: Path,
) -> dict[str, Any]:
    bindings = verification.get("root_bindings")
    if type(bindings) is not list or len(bindings) != COVER_ROOT_COUNT:
        raise AdaptiveChildResumeError(
            "handoff has no exact eight-root cover binding"
        )
    matching = [
        item for item in bindings
        if type(item) is dict
        and item.get("new_root_identity", {}).get("path") == str(root)
    ]
    if len(matching) != 1:
        raise AdaptiveChildResumeError("handoff does not uniquely bind root")
    binding = dict(matching[0])
    descendant = binding.get("descendant_index")
    if (
        set(binding) != _ROOT_BINDING_FIELDS
        or type(binding.get("lane_index")) is not int
        or type(descendant) is not int
        or (binding["lane_index"], descendant) not in TARGET_KEYS
        or binding.get("cohort_index") != descendant
        or type(binding.get("cohort_index")) is not int
        or not all(_is_sha256(binding.get(field)) for field in (
            "descendant_sha256", "new_session_sha256",
            "new_start_commit_sha256", "permit_binding_sha256",
            "prepared_target_sha256", "started_worker_journal_sha256",
            "fence_sha256",
        ))
        or type(binding.get("global_leaf_index")) is not int
        or type(binding.get("new_root_identity")) is not dict
        or type(binding.get("new_pid")) is not int
        or type(binding.get("new_proc_start_ticks")) is not int
        or (
            descendant == 0
            and (
                binding.get("handoff_state") != "CHECKPOINTED"
                or not _is_sha256(
                    binding.get("cohort_quiescence_sha256")
                )
            )
        )
        or (
            descendant == 1
            and (
                binding.get("handoff_state") != "RUNNING"
                or binding.get("cohort_quiescence_sha256") is not None
            )
        )
    ):
        raise AdaptiveChildResumeError("handoff root binding schema mismatch")
    return binding


def _handoff_link_value(
    root: Path, static: Mapping[str, Any], session: Mapping[str, Any],
    batch_commit_path: Path, batch_commit: Mapping[str, Any],
    binding: Mapping[str, Any],
) -> dict[str, Any]:
    commit_sha = batch_commit.get("batch_commit_sha256")
    if commit_sha is None:
        commit_sha = batch_commit.get("record_sha256")
    attempt_id = batch_commit.get("attempt_id")
    incident_pin = batch_commit.get("incident_precondition_sha256")
    if (
        not _is_sha256(commit_sha)
        or not _is_sha256(attempt_id)
        or not _is_sha256(incident_pin)
    ):
        raise AdaptiveChildResumeError("handoff attempt/incident binding malformed")
    if (
        binding.get("new_session_sha256") != session["record_sha256"]
        or binding.get("new_start_commit_sha256")
        != session["controller_start_sha256"]
        or binding.get("descendant_index")
        != static["selection"]["descendant_index"]
        or binding.get("descendant_sha256")
        != static["selection"]["descendant_sha256"]
        or binding.get("global_leaf_index")
        != static["selection"]["global_leaf_index"]
        or not json_type_equal(
            binding.get("new_root_identity"), session["root_identity"]
        )
    ):
        raise AdaptiveChildResumeError("handoff binding/session mismatch")
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": HANDOFF_LINK_KIND,
        "gate": GATE,
        "root": str(root),
        "static_sha256": static["record_sha256"],
        "session_sha256": session["record_sha256"],
        "switch_evidence_sha256": static["switch_evidence_sha256"],
        "batch_manifest_sha256": static["external_pins"][
            "expected_batch_manifest_sha256"
        ],
        "batch_commit_path": str(batch_commit_path.resolve(strict=True)),
        "batch_commit_sha256": commit_sha,
        "attempt_id": attempt_id,
        "incident_precondition_sha256": incident_pin,
        "fence_sha256": binding["fence_sha256"],
        "prepared_target_sha256": binding["prepared_target_sha256"],
        "started_worker_journal_sha256": binding[
            "started_worker_journal_sha256"
        ],
        "cohort_index": binding["cohort_index"],
        "initial_handoff_state": binding["handoff_state"],
        "cohort_quiescence_sha256": binding[
            "cohort_quiescence_sha256"
        ],
        "root_binding": dict(binding),
        "launch_authorized": False,
        "resume_requires_fresh_durable_retirement_verification": True,
        "scientific_claim": False,
    })


def _write_handoff_links(
    entries: Sequence[Mapping[str, Any]], batch_commit_path: Path,
    batch_commit: Mapping[str, Any],
) -> list[dict[str, Any]]:
    links: list[dict[str, Any]] = []
    for entry in entries:
        root = entry["root"]
        session = entry["started"]["session"]
        binding = _binding_for_root(batch_commit, root)
        link = _handoff_link_value(
            root, entry["loaded"]["record"], session,
            batch_commit_path, batch_commit, binding,
        )
        _publish_json(root / HANDOFF_LINK, link)
        links.append(link)
    return links

def inspect_incident_batch(roots: Sequence[Path]) -> dict[str, Any]:
    """Build the sealed v4 incident precondition without launch authority."""

    if type(roots) not in (list, tuple) or len(roots) != COVER_ROOT_COUNT:
        raise AdaptiveChildResumeError(
            "incident inspection requires exactly eight roots"
        )
    root_list = [_existing_root(Path(root)) for root in roots]
    if len(set(root_list)) != COVER_ROOT_COUNT:
        raise AdaptiveChildResumeError("incident inspection roots are duplicated")
    loaded_items = [
        _load_static(
            root, instance=None, switch_verifier=None, science_modules=None,
        )
        for root in root_list
    ]
    if any(item["record"]["strict_base"] is not True for item in loaded_items):
        raise AdaptiveChildResumeError(
            "incident inspection is strict-production only"
        )
    common = _batch_common(loaded_items)
    entries = _cover_entries(
        root_list,
        list(range(COHORT_SIZE)) * DESCENDANTS_PER_LANE,
        loaded_items,
    )
    source_hashes = {
        item["record"]["execution_module_binding"]["switch_v4_source_sha256"]
        for item in loaded_items
    }
    if len(source_hashes) != 1:
        raise AdaptiveChildResumeError(
            "incident roots disagree on executed switch-v4 source"
        )
    switch = _switch_v4_module(next(iter(source_hashes)))
    record = switch.build_incident_precondition(
        common["batch_root"],
        target_roots=[entry["root"] for entry in entries],
        timeout_seconds=common["timeout_seconds"],
        elapsed_seconds_by_lane=common["elapsed_seconds_by_lane"],
        strict_base=True,
    )
    if (
        type(record) is not dict
        or not selfhash_valid(record)
        or record.get("attempt_id") != switch.ATTEMPT_ID
        or record.get("batch_root") != str(common["batch_root"])
        or record.get("batch_manifest_sha256")
            != common["expected_batch_manifest_sha256"]
        or record.get("switch_evidence_sha256")
            != common["expected_switch_evidence_sha256"]
        or type(record.get("target_roots")) is not list
        or len(record["target_roots"]) != COVER_ROOT_COUNT
        or record.get("authenticated") is not False
        or record.get("launch_authorized") is not False
        or record.get("scientific_claim") is not False
    ):
        raise AdaptiveChildResumeError(
            "switch-v4 incident precondition attestation mismatch"
        )
    return dict(record)



def start_batch(
    roots: Sequence[Path], cpus: Sequence[int], *, batch_commit_path: Path,
    expected_incident_precondition_sha256: str,
    instance: Any | None = None,
    switch_verifier: Callable[..., Mapping[str, Any]] | None = None,
    science_modules: tuple[Any, Any, Any, Any] | None = None,
    lease_factory: Callable[..., Any] | None = None,
) -> dict[str, Any]:
    """First-start all eight descendants under one atomic old-batch lease."""

    incident_pin = _require_sha256(
        expected_incident_precondition_sha256, "incident precondition pin",
    )
    commit_path = Path(batch_commit_path)
    _validate_new_output_path(commit_path, label="batch handoff commit")
    root_list, cpu_list = _cover_roots_cpus(roots, cpus)
    for root in root_list:
        _validate_new_output_path(
            root / HANDOFF_LINK, label="root handoff link",
        )
    with contextlib.ExitStack() as stack:
        locks_by_root: dict[Path, _TransferableRootLock] = {}
        for root in sorted(root_list, key=str):
            locks_by_root[root] = stack.enter_context(
                _TransferableRootLock(root)
            )
        loaded_items = [
            _load_static(root, **_action_kwargs(
                instance=instance, switch_verifier=switch_verifier,
                science_modules=science_modules,
            ))
            for root in root_list
        ]
        strict_values = [item["record"]["strict_base"] for item in loaded_items]
        if len(set(strict_values)) != 1:
            raise AdaptiveChildResumeError(
                "cover mixes strict and synthetic roots"
            )
        strict = strict_values[0]
        if strict and any(item is not None for item in (
            instance, switch_verifier, science_modules, lease_factory,
        )):
            raise AdaptiveChildResumeError(
                "strict start-batch forbids injected seams"
            )
        common = _batch_common(loaded_items)
        entries = _cover_entries(
            root_list, cpu_list, loaded_items,
        )
        for item in loaded_items:
            _preflight_solver_limits(
                item["record"]["resource_policy"]["proof_max_bytes"]
            )
        expected_attempt_id: str | None = None
        if lease_factory is None:
            source_hashes = {
                item["record"]["execution_module_binding"][
                    "switch_v4_source_sha256"
                ]
                for item in loaded_items
            }
            if len(source_hashes) != 1:
                raise AdaptiveChildResumeError(
                    "eight roots disagree on executed switch-v4 source"
                )
            switch_module = _switch_v4_module(next(iter(source_hashes)))
            expected_attempt_id = _require_sha256(
                switch_module.ATTEMPT_ID, "switch-v4 attempt id",
            )
            factory = switch_module.acquire_atomic_switch_lease
            expected_commit_path = (
                common["batch_root"] / switch_module.HANDOFF_COMMIT
            )
            if commit_path != expected_commit_path:
                raise AdaptiveChildResumeError(
                    "batch commit path is not switch-v4 canonical path"
                )
        else:
            factory = lease_factory
        with factory(
            common["batch_root"],
            target_roots=[entry["root"] for entry in entries],
            target_outer_lock_fds=[
                locks_by_root[entry["root"]].validated_transfer_fd()
                for entry in entries
            ],
            expected_incident_precondition_sha256=incident_pin,
            expected_batch_manifest_sha256=common[
                "expected_batch_manifest_sha256"
            ],
            expected_switch_evidence_sha256=common[
                "expected_switch_evidence_sha256"
            ],
            expected_hard_evidence_sha256s=common[
                "expected_hard_evidence_sha256s"
            ],
            timeout_seconds=common["timeout_seconds"],
            elapsed_seconds_by_lane=common["elapsed_seconds_by_lane"],
            strict_base=True if strict else False,
        ) as lease:
            batch_commit, started = _atomic_handoff_start(
                lease, entries, batch_commit_path=commit_path,
                outer_locks=[
                    locks_by_root[entry["root"]] for entry in entries
                ],
            )
            if (
                not _is_sha256(batch_commit.get("attempt_id"))
                or batch_commit.get("incident_precondition_sha256")
                    != incident_pin
                or (
                    expected_attempt_id is not None
                    and batch_commit["attempt_id"] != expected_attempt_id
                )
            ):
                raise AdaptiveChildResumeError(
                    "committed v4 handoff misses attempt/incident binding"
                )
            try:
                links = _write_handoff_links(
                    started, commit_path, batch_commit,
                )
            except BaseException as exc:
                raise AdaptiveChildResumeError(
                    "cover committed but root links incomplete; "
                    "run repair-handoff-links"
                ) from exc
    return seal({
        "schema_version": SCHEMA_VERSION, "kind": BATCH_SUMMARY_KIND,
        "gate": GATE, "action": "start-batch", "success": True,
        "complete_binary_cover": True,
        "target_keys": [list(key) for key in TARGET_KEYS],
        "roots": [str(root) for root in root_list], "cpus": cpu_list,
        "batch_commit_path": str(commit_path.resolve(strict=True)),
        "batch_commit_sha256": batch_commit["record_sha256"],
        "attempt_id": batch_commit["attempt_id"],
        "incident_precondition_sha256": incident_pin,
        "prepared_retirement_sha256": batch_commit[
            "prepared_retirement_sha256"
        ],
        "root_link_sha256s": [
            link["record_sha256"] for link in links
        ],
        "initial_handoff_states": [
            _binding_for_root(batch_commit, root)["handoff_state"]
            for root in root_list
        ],
        "max_live_workers": COHORT_SIZE,
        "launch_authorized": False, "scientific_claim": False,
    })


def _verify_complete_handoff_links(
    root: Path, loaded: Mapping[str, Any], session: Mapping[str, Any],
    handoff_verifier: Callable[..., Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    try:
        link = _read_json(root / HANDOFF_LINK, root=root)
    except OSError as exc:
        raise AdaptiveChildResumeError("root handoff link is absent") from exc
    link_fields = {
        "schema_version", "kind", "gate", "root", "static_sha256",
        "session_sha256", "switch_evidence_sha256", "batch_manifest_sha256",
        "batch_commit_path", "batch_commit_sha256", "fence_sha256",
        "attempt_id", "incident_precondition_sha256",
        "prepared_target_sha256", "started_worker_journal_sha256",
        "cohort_index", "initial_handoff_state",
        "cohort_quiescence_sha256", "root_binding", "launch_authorized",
        "resume_requires_fresh_durable_retirement_verification",
        "scientific_claim", "record_sha256",
    }
    if (
        type(link) is not dict or set(link) != link_fields
        or not selfhash_valid(link) or link["schema_version"] != SCHEMA_VERSION
        or type(link["schema_version"]) is not int
        or link["kind"] != HANDOFF_LINK_KIND or link["gate"] != GATE
        or link["root"] != str(root)
        or link["static_sha256"] != loaded["record"]["record_sha256"]
        or link["session_sha256"] != session["record_sha256"]
        or not _is_sha256(link["attempt_id"])
        or not _is_sha256(link["incident_precondition_sha256"])
        or link["launch_authorized"] is not False
        or link["resume_requires_fresh_durable_retirement_verification"] is not True
        or link["scientific_claim"] is not False
    ):
        raise AdaptiveChildResumeError("root handoff link mismatch")
    if handoff_verifier is None:
        source_sha = loaded["record"]["execution_module_binding"]["switch_v4_source_sha256"]
        verifier = _switch_v4_module(source_sha).verify_committed_handoff
    else:
        verifier = handoff_verifier
    verification = verifier(
        Path(link["batch_commit_path"]),
        expected_batch_commit_sha256=link["batch_commit_sha256"],
        expected_attempt_id=link["attempt_id"],
        expected_incident_precondition_sha256=link["incident_precondition_sha256"],
        expected_switch_evidence_sha256=link["switch_evidence_sha256"],
        expected_batch_manifest_sha256=link["batch_manifest_sha256"],
    )
    if (
        type(verification) is not dict
        or not selfhash_valid(verification)
        or verification.get("valid") is not True
        or verification.get("authenticated") is not False
        or verification.get("launch_authorized") is not False
        or verification.get("batch_commit_sha256") != link["batch_commit_sha256"]
        or verification.get("attempt_id") != link["attempt_id"]
        or verification.get("incident_precondition_sha256")
            != link["incident_precondition_sha256"]
        or verification.get("switch_evidence_sha256") != link["switch_evidence_sha256"]
        or verification.get("batch_manifest_sha256") != link["batch_manifest_sha256"]
        or not _is_sha256(verification.get("prepared_retirement_sha256"))
    ):
        raise AdaptiveChildResumeError("durable handoff verification mismatch")
    binding = _binding_for_root(verification, root)
    expected = _handoff_link_value(
        root, loaded["record"], session, Path(link["batch_commit_path"]),
        verification, binding,
    )
    if not json_type_equal(link, expected):
        raise AdaptiveChildResumeError("root handoff link differs from fresh replay")
    observed_links: list[dict[str, Any]] = []
    for peer in verification["root_bindings"]:
        peer_root = _existing_root(Path(peer["new_root_identity"]["path"]))
        peer_static = _load_static(
            peer_root, instance=None, switch_verifier=None, science_modules=None,
        )
        peer_session = _validate_session_value(
            peer_root, peer_static,
            _read_json(peer_root / SESSION_COMMIT, root=peer_root),
        )
        peer_link = _read_json(peer_root / HANDOFF_LINK, root=peer_root)
        peer_expected = _handoff_link_value(
            peer_root, peer_static["record"], peer_session,
            Path(link["batch_commit_path"]),
            verification, peer,
        )
        if not json_type_equal(peer_link, peer_expected):
            raise AdaptiveChildResumeError("eight-root handoff links incomplete")
        observed_links.append(peer_link)
    replay = verifier(
        Path(link["batch_commit_path"]),
        expected_batch_commit_sha256=link["batch_commit_sha256"],
        expected_attempt_id=link["attempt_id"],
        expected_incident_precondition_sha256=link["incident_precondition_sha256"],
        expected_switch_evidence_sha256=link["switch_evidence_sha256"],
        expected_batch_manifest_sha256=link["batch_manifest_sha256"],
    )
    if not json_type_equal(verification, replay):
        raise AdaptiveChildResumeError("handoff changed during eight-root replay")
    return dict(verification)


def _fresh_handoff_provenance(
    root: Path, loaded: Mapping[str, Any], session: Mapping[str, Any],
) -> dict[str, Any]:
    if loaded["record"]["strict_base"] is not True:
        return seal({
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-dic5-adaptive-handoff-provenance-v5",
            "strict_atomic_handoff": False,
            "batch_commit_sha256": None, "root_fence_sha256": None,
            "attempt_id": None,
            "incident_precondition_sha256": None,
            "prepared_retirement_sha256": None,
            "prepared_target_sha256": None,
            "started_worker_journal_sha256": None,
            "cohort_index": None, "initial_handoff_state": None,
            "cohort_quiescence_sha256": None,
            "switch_evidence_sha256": loaded["record"]["switch_evidence_sha256"],
            "batch_manifest_sha256": loaded["record"]["external_pins"]["expected_batch_manifest_sha256"],
            "handoff_link_sha256": None, "retired_locks_sha256": None,
            "handoff_verification_sha256": None,
        })
    verification = _verify_complete_handoff_links(root, loaded, session)
    binding = _binding_for_root(verification, root)
    link = _read_json(root / HANDOFF_LINK, root=root)
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-adaptive-handoff-provenance-v5",
        "strict_atomic_handoff": True,
        "batch_commit_sha256": verification["batch_commit_sha256"],
        "attempt_id": verification["attempt_id"],
        "incident_precondition_sha256":
            verification["incident_precondition_sha256"],
        "root_fence_sha256": binding["fence_sha256"],
        "prepared_retirement_sha256": verification["prepared_retirement_sha256"],
        "prepared_target_sha256": binding["prepared_target_sha256"],
        "started_worker_journal_sha256": binding[
            "started_worker_journal_sha256"
        ],
        "cohort_index": binding["cohort_index"],
        "initial_handoff_state": binding["handoff_state"],
        "cohort_quiescence_sha256": binding[
            "cohort_quiescence_sha256"
        ],
        "switch_evidence_sha256": verification["switch_evidence_sha256"],
        "batch_manifest_sha256": verification["batch_manifest_sha256"],
        "handoff_link_sha256": link["record_sha256"],
        "retired_locks_sha256": canonical_sha256(verification["retired_locks"]),
        "handoff_verification_sha256": verification["record_sha256"],
    })


def repair_handoff_links(
    roots: Sequence[Path], *, batch_commit_path: Path,
    expected_batch_commit_sha256: str,
    expected_attempt_id: str,
    expected_incident_precondition_sha256: str,
    handoff_verifier: Callable[..., Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    attempt_pin = _require_sha256(expected_attempt_id, "v4 attempt id")
    incident_pin = _require_sha256(
        expected_incident_precondition_sha256, "incident precondition pin",
    )
    if type(roots) not in (list, tuple) or len(roots) != COVER_ROOT_COUNT:
        raise AdaptiveChildResumeError("repair requires exactly eight roots")
    root_list = [_existing_root(Path(root)) for root in roots]
    if len(set(root_list)) != COVER_ROOT_COUNT:
        raise AdaptiveChildResumeError("repair roots are duplicated")
    loaded_items = [
        _load_static(
            root, instance=None, switch_verifier=None, science_modules=None,
        )
        for root in root_list
    ]
    if any(item["record"]["strict_base"] is not True for item in loaded_items):
        raise AdaptiveChildResumeError("repair is strict-production only")
    sessions = [
        _load_session(root, loaded)
        for root, loaded in zip(root_list, loaded_items, strict=True)
    ]
    common = _batch_common(loaded_items)
    if handoff_verifier is not None:
        raise AdaptiveChildResumeError("strict repair forbids injected verifier")
    source_hashes = {
        item["record"]["execution_module_binding"]["switch_v4_source_sha256"]
        for item in loaded_items
    }
    if len(source_hashes) != 1:
        raise AdaptiveChildResumeError("eight repair roots disagree on switch-v4 source")
    switch_module = _switch_v4_module(
        next(iter(source_hashes))
    )
    if attempt_pin != switch_module.ATTEMPT_ID:
        raise AdaptiveChildResumeError("repair attempt id misses frozen v4")
    verifier = switch_module.verify_committed_handoff
    verified = verifier(
        Path(batch_commit_path),
        expected_batch_commit_sha256=_require_sha256(
            expected_batch_commit_sha256, "batch commit pin"
        ),
        expected_attempt_id=attempt_pin,
        expected_incident_precondition_sha256=incident_pin,
        expected_switch_evidence_sha256=common[
            "expected_switch_evidence_sha256"
        ],
        expected_batch_manifest_sha256=common[
            "expected_batch_manifest_sha256"
        ],
    )
    written: list[str] = []
    for root, loaded, session in zip(
        root_list, loaded_items, sessions, strict=True,
    ):
        binding = _binding_for_root(verified, root)
        expected = _handoff_link_value(
            root, loaded["record"], session, Path(batch_commit_path),
            verified, binding,
        )
        path = root / HANDOFF_LINK
        if path.exists():
            if not json_type_equal(_read_json(path, root=root), expected):
                raise AdaptiveChildResumeError("existing handoff link mismatch")
        else:
            _publish_json(path, expected)
            written.append(str(root))
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": BATCH_SUMMARY_KIND,
        "gate": GATE,
        "action": "repair-handoff-links",
        "success": True,
        "batch_commit_sha256": expected_batch_commit_sha256,
        "attempt_id": attempt_pin,
        "incident_precondition_sha256": incident_pin,
        "written_roots": written,
        "launch_authorized": False,
        "scientific_claim": False,
    })


def _validate_new_output_path(path: Path, *, label: str) -> None:
    target = Path(path)
    if (
        not target.is_absolute()
        or str(target) != os.path.abspath(str(target))
        or target.exists() or target.is_symlink()
    ):
        raise AdaptiveChildResumeError(f"{label} path must be new normalized absolute")
    _directory_identity(target.parent, require_mode_0700=True)


def _publish_batch_summary(path: Path, value: Mapping[str, Any]) -> None:
    target = Path(path)
    _validate_new_output_path(target, label="batch summary")
    _publish_json(target, value)


def _active_identity_for_inspection(
    root: Path, inspection: Mapping[str, Any],
) -> tuple[int, int]:
    generations = inspection.get("generations")
    if (
        type(generations) is not list or not generations
        or type(generations[-1]) is not dict
        or type(generations[-1].get("generation")) is not int
        or not _is_sha256(generations[-1].get("active_manifest_sha256"))
    ):
        raise AdaptiveChildResumeError(
            "controller inspection lacks an exact active generation"
        )
    generation = generations[-1]["generation"]
    runtime = root / RUNTIME_ROOT
    with _fixed_environment(), controller.controller_lock(
        runtime, exclusive=False,
    ):
        active = controller._active_commit(
            controller._generation_dir(runtime, generation), generation,
        )
    pid = active.get("pid")
    ticks = active.get("proc_start_ticks")
    if (
        not controller.selfhash_valid(active)
        or active.get("self_sha256")
        != generations[-1]["active_manifest_sha256"]
        or type(pid) is not int or pid <= 0
        or type(ticks) is not int or ticks <= 0
    ):
        raise AdaptiveChildResumeError(
            "active manifest/inspection identity mismatch"
        )
    return pid, ticks


def _batch_preinspect(root: Path, cpu: int) -> dict[str, Any]:
    loaded = _load_static(
        root, instance=None, switch_verifier=None, science_modules=None,
    )
    session = _load_session(root, loaded)
    if loaded["record"]["strict_base"] is True:
        _verify_complete_handoff_links(root, loaded, session)
    inspection = _inspect_controller(root)
    if not inspection["generations"]:
        raise AdaptiveChildResumeError("batch root has no generation")
    latest = inspection["generations"][-1]
    state = inspection["state"]
    if state == "CHECKPOINTED":
        proof = _safe_root_path(root, RUNTIME_ROOT / "proof.drat")
        before = _stream_record(
            proof, cap=session["proof_cap_bytes"], root=root,
            role="batch-checkpoint-proof",
        )
        holders = _writable_holders(proof)
        after = _stream_record(
            proof, cap=session["proof_cap_bytes"], root=root,
            role="batch-checkpoint-proof",
        )
        if (
            latest.get("pid_identity_alive") is not False or holders
            or not json_type_equal(before, after)
        ):
            raise AdaptiveChildResumeError("checkpoint goal is not quiescent")
    elif state == "RUNNING":
        pid, ticks = _active_identity_for_inspection(root, inspection)
        if (
            latest.get("pid_identity_alive") is not True
            or not controller._pid_identity(pid, ticks)
            or os.sched_getaffinity(pid) != {cpu}
        ):
            raise AdaptiveChildResumeError("running goal identity/CPU mismatch")
        _verify_live_peer_rlimits(pid, session["proof_cap_bytes"])
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-batch-preinspect-v5",
        "root": str(root), "cpu": cpu, "state": state,
        "inspection_sha256": canonical_sha256(inspection),
        "session_sha256": session["record_sha256"],
        "scientific_claim": False,
    })


def _verify_links_before_batch_mutation(
    roots: Sequence[Path], loaded_items: Sequence[Mapping[str, Any]],
) -> None:
    for root, loaded in zip(roots, loaded_items, strict=True):
        if loaded["record"]["strict_base"] is not True:
            raise AdaptiveChildResumeError(
                "cover scheduler requires strict roots"
            )
        session = _validate_session_value(
            root, loaded, _read_json(root / SESSION_COMMIT, root=root),
        )
        _verify_complete_handoff_links(root, loaded, session)


def _batch_action(
    action: str, roots: Sequence[Path], cpus: Sequence[int], *,
    summary_path: Path,
) -> dict[str, Any]:
    """Read all eight roots or monotonically reduce the live-worker set."""

    if action not in {"checkpoint-stop-batch", "status-batch"}:
        raise AdaptiveChildResumeError(
            "increasing liveness requires switch-cohort-batch"
        )
    _validate_new_output_path(Path(summary_path), label="batch summary")
    root_list, cpu_list = _cover_roots_cpus(roots, cpus)
    outcomes: list[dict[str, Any]] = []
    with contextlib.ExitStack() as stack:
        for root in sorted(root_list, key=str):
            stack.enter_context(_root_lock(root, exclusive=True))
        loaded_items = [
            _load_static(
                root, instance=None, switch_verifier=None,
                science_modules=None,
            )
            for root in root_list
        ]
        _batch_common(loaded_items)
        _cover_entries(root_list, cpu_list, loaded_items)
        _verify_links_before_batch_mutation(root_list, loaded_items)
        token = _BatchTransportToken(
            root_list, actions=["checkpoint-stop"],
        )
        for root, cpu in zip(root_list, cpu_list, strict=True):
            recovery_sha: str | None = None
            before: dict[str, Any] | None = None
            try:
                if _last_action_is_incomplete(root):
                    if action == "status-batch":
                        raise AdaptiveChildResumeError(
                            "read-only status refuses interrupted action recovery"
                        )
                    recovered = _recover_action_locked(root)
                    recovery_sha = recovered["record_sha256"]
                before = _batch_preinspect(root, cpu)
                if action == "status-batch":
                    after = before
                    disposition = "OBSERVED"
                    action_sha = None
                elif before["state"] in {
                    "CHECKPOINTED", "INACTIVE_UNCHECKPOINTED",
                }:
                    after = before
                    disposition = "SKIPPED_GOAL_ALREADY_QUIESCENT"
                    action_sha = None
                elif before["state"] == "RUNNING":
                    with _temporary_cpu(cpu):
                        value = _checkpoint_stop_locked(
                            root, batch_token=token,
                        )
                    after = _batch_preinspect(root, cpu)
                    if after["state"] not in {
                        "CHECKPOINTED", "INACTIVE_UNCHECKPOINTED",
                    }:
                        raise AdaptiveChildResumeError(
                            "checkpoint-stop did not quiesce root"
                        )
                    disposition = "APPLIED"
                    action_sha = value["record_sha256"]
                else:
                    raise AdaptiveChildResumeError(
                        f"checkpoint source state is {before['state']}"
                    )
                outcomes.append({
                    "root": str(root), "cpu": cpu, "success": True,
                    "disposition": disposition,
                    "before_sha256": before["record_sha256"],
                    "after_sha256": after["record_sha256"],
                    "result_sha256": action_sha,
                    "recovery_sha256": recovery_sha, "error": None,
                })
            except BaseException as exc:
                outcomes.append({
                    "root": str(root), "cpu": cpu, "success": False,
                    "disposition": "FAILED",
                    "before_sha256": (
                        None if before is None else before["record_sha256"]
                    ),
                    "after_sha256": None, "result_sha256": None,
                    "recovery_sha256": recovery_sha,
                    "error": f"{type(exc).__name__}: {exc}",
                })
    result = seal({
        "schema_version": SCHEMA_VERSION, "kind": BATCH_SUMMARY_KIND,
        "gate": GATE, "action": action,
        "success": all(item["success"] for item in outcomes),
        "complete_binary_cover": True,
        "target_keys": [list(key) for key in TARGET_KEYS],
        "goal_oriented_retry": True,
        "status_is_read_only_no_action_ledger": action == "status-batch",
        "outcomes": outcomes, "launch_authorized": False,
        "scientific_claim": False,
    })
    _publish_batch_summary(Path(summary_path), result)
    if result["success"] is not True:
        raise AdaptiveChildResumeError(
            f"{action} failed; immutable summary: {summary_path}"
        )
    return result


def checkpoint_stop_batch(
    roots: Sequence[Path], cpus: Sequence[int], *, summary_path: Path,
) -> dict[str, Any]:
    return _batch_action(
        "checkpoint-stop-batch", roots, cpus, summary_path=summary_path,
    )


def resume_batch(
    roots: Sequence[Path], cpus: Sequence[int], *, summary_path: Path,
) -> dict[str, Any]:
    del roots, cpus, summary_path
    raise AdaptiveChildResumeError(
        "resume-batch is disabled; use switch-cohort-batch with all eight roots"
    )


def status_batch(
    roots: Sequence[Path], cpus: Sequence[int], *, summary_path: Path,
) -> dict[str, Any]:
    return _batch_action(
        "status-batch", roots, cpus, summary_path=summary_path,
    )


def switch_cohort_batch(
    roots: Sequence[Path], cpus: Sequence[int], *,
    descendant_index: int, summary_path: Path,
) -> dict[str, Any]:
    """Stop every live worker, prove global quiescence, then resume one cohort."""

    if (
        type(descendant_index) is not int
        or descendant_index not in range(DESCENDANTS_PER_LANE)
    ):
        raise AdaptiveChildResumeError("target cohort descendant index is invalid")
    _validate_new_output_path(Path(summary_path), label="batch summary")
    root_list, cpu_list = _cover_roots_cpus(roots, cpus)
    outcomes: list[dict[str, Any]] = []
    resumed: list[tuple[dict[str, Any], dict[str, Any]]] = []
    failure: BaseException | None = None
    with contextlib.ExitStack() as stack:
        for root in sorted(root_list, key=str):
            stack.enter_context(_root_lock(root, exclusive=True))
        loaded_items = [
            _load_static(
                root, instance=None, switch_verifier=None,
                science_modules=None,
            )
            for root in root_list
        ]
        _batch_common(loaded_items)
        entries = _cover_entries(root_list, cpu_list, loaded_items)
        _verify_links_before_batch_mutation(root_list, loaded_items)
        for entry in entries:
            if _last_action_is_incomplete(entry["root"]):
                _recover_action_locked(entry["root"])
        stop_token = _BatchTransportToken(
            root_list, actions=["checkpoint-stop"],
        )
        for entry in entries:
            try:
                before = _batch_preinspect(entry["root"], entry["cpu"])
                if before["state"] == "RUNNING":
                    with _temporary_cpu(entry["cpu"]):
                        value = _checkpoint_stop_locked(
                            entry["root"], batch_token=stop_token,
                        )
                    disposition = "CHECKPOINTED_FOR_GLOBAL_ZERO"
                    result_sha = value["record_sha256"]
                elif before["state"] in {
                    "CHECKPOINTED", "INACTIVE_UNCHECKPOINTED",
                }:
                    disposition = "ALREADY_QUIESCENT"
                    result_sha = None
                else:
                    raise AdaptiveChildResumeError(
                        f"cannot quiesce state {before['state']}"
                    )
                outcomes.append({
                    "phase": "quiesce", "target_key": list(entry["target_key"]),
                    "root": str(entry["root"]), "cpu": entry["cpu"],
                    "success": True, "disposition": disposition,
                    "result_sha256": result_sha, "error": None,
                })
            except BaseException as exc:
                outcomes.append({
                    "phase": "quiesce", "target_key": list(entry["target_key"]),
                    "root": str(entry["root"]), "cpu": entry["cpu"],
                    "success": False, "disposition": "FAILED",
                    "result_sha256": None,
                    "error": f"{type(exc).__name__}: {exc}",
                })
                if failure is None:
                    failure = exc

        quiescence: list[dict[str, Any]] = []
        if failure is None:
            try:
                quiescence = [
                    _global_zero_quiescence_record(
                        entry["root"], entry["lane_index"],
                        entry["descendant_index"], entry["loaded"],
                    )
                    for entry in entries
                ]
            except BaseException as exc:
                failure = exc
        target_entries = [
            entry for entry in entries
            if entry["descendant_index"] == descendant_index
        ]
        if failure is None:
            resume_token = _BatchTransportToken(
                [entry["root"] for entry in target_entries],
                actions=["resume"],
            )
            for entry in target_entries:
                if _terminal_bundle_present(entry["root"]):
                    outcomes.append({
                        "phase": "resume", "target_key": list(entry["target_key"]),
                        "root": str(entry["root"]), "cpu": entry["cpu"],
                        "success": True,
                        "disposition": "SKIPPED_TERMINAL_FAIL_CLOSED",
                        "result_sha256": None, "error": None,
                    })
                    continue
                try:
                    with _temporary_cpu(entry["cpu"]):
                        value = _resume_locked(
                            entry["root"], batch_token=resume_token,
                        )
                    resumed.append((entry, value))
                    outcomes.append({
                        "phase": "resume", "target_key": list(entry["target_key"]),
                        "root": str(entry["root"]), "cpu": entry["cpu"],
                        "success": True, "disposition": "RESUMED",
                        "result_sha256": value["record_sha256"],
                        "error": None,
                    })
                except BaseException as exc:
                    outcomes.append({
                        "phase": "resume", "target_key": list(entry["target_key"]),
                        "root": str(entry["root"]), "cpu": entry["cpu"],
                        "success": False, "disposition": "FAILED",
                        "result_sha256": None,
                        "error": f"{type(exc).__name__}: {exc}",
                    })
                    failure = exc
                    break

        final_states: list[dict[str, Any]] = []
        if failure is None:
            try:
                for entry in entries:
                    observed = _batch_preinspect(
                        entry["root"], entry["cpu"],
                    )
                    is_target = (
                        entry["descendant_index"] == descendant_index
                    )
                    terminal = _terminal_bundle_present(
                        entry["root"]
                    )
                    expected_running = is_target and not terminal
                    if (
                        (expected_running and observed["state"] != "RUNNING")
                        or (
                            not expected_running
                            and observed["state"] not in {
                                "CHECKPOINTED",
                                "INACTIVE_UNCHECKPOINTED",
                            }
                        )
                    ):
                        raise AdaptiveChildResumeError(
                            "cohort switch final state mismatch"
                        )
                    final_states.append({
                        "target_key": list(entry["target_key"]),
                        "state": observed["state"],
                        "terminal_fail_closed": terminal,
                        "inspection_sha256": observed["record_sha256"],
                    })
                if sum(
                    item["state"] == "RUNNING" for item in final_states
                ) > COHORT_SIZE:
                    raise AdaptiveChildResumeError(
                        "cohort switch exceeded four live workers"
                    )
            except BaseException as exc:
                failure = exc

        post_failure_quiescence: list[dict[str, Any]] = []
        if failure is not None and resumed:
            cleanup_failures: list[str] = []
            for entry, action_commit in reversed(resumed):
                try:
                    _stop_failed_new_root(
                        entry["root"],
                        {
                            "controller_start":
                                action_commit["controller_result"]
                        },
                        lane_index=None,
                    )
                except BaseException as exc:
                    cleanup_failures.append(f"{entry['root']}: {exc}")
            if not cleanup_failures:
                try:
                    post_failure_quiescence = [
                        _global_zero_quiescence_record(
                            entry["root"], entry["lane_index"],
                            entry["descendant_index"], entry["loaded"],
                        )
                        for entry in entries
                    ]
                except BaseException as exc:
                    cleanup_failures.append(str(exc))
            if cleanup_failures:
                failure = AdaptiveChildResumeError(
                    "cohort-switch cleanup did not prove global zero: "
                    + "; ".join(cleanup_failures)
                )
        # Bind the fresh all-root quiescence fence that preceded any resume.
        zero_fence_sha256 = (
            canonical_sha256(quiescence) if quiescence else None
        )
        post_failure_zero_sha256 = (
            canonical_sha256(post_failure_quiescence)
            if post_failure_quiescence else None
        )

    result = seal({
        "schema_version": SCHEMA_VERSION, "kind": BATCH_SUMMARY_KIND,
        "gate": GATE, "action": "switch-cohort-batch",
        "success": failure is None,
        "complete_binary_cover": True,
        "target_descendant_index": descendant_index,
        "target_keys": [list(key) for key in TARGET_KEYS],
        "global_zero_quiescence_sha256": zero_fence_sha256,
        "post_failure_global_zero_sha256": post_failure_zero_sha256,
        "post_failure_quiescence_record_sha256s": [
            record["record_sha256"]
            for record in post_failure_quiescence
        ],
        "max_live_workers": COHORT_SIZE,
        "outcomes": outcomes, "final_states": final_states,
        "launch_authorized": False, "scientific_claim": False,
        "error": (
            None if failure is None
            else f"{type(failure).__name__}: {failure}"
        ),
    })
    _publish_batch_summary(Path(summary_path), result)
    if failure is not None:
        raise AdaptiveChildResumeError(
            f"switch-cohort-batch failed; immutable summary: {summary_path}"
        )
    return result


def _global_zero_quiescence_record(
    root: Path, lane_index: int, descendant_index: int,
    loaded: Mapping[str, Any],
) -> dict[str, Any]:
    """Bind any stopped transport without pretending it has a checkpoint."""

    inspection = _inspect_controller(root)
    if (
        inspection["state"] not in {
            "CHECKPOINTED", "INACTIVE_UNCHECKPOINTED",
        }
        or not inspection["generations"]
        or type(inspection["generations"][-1]) is not dict
        or (lane_index, descendant_index) not in TARGET_KEYS
    ):
        raise AdaptiveChildResumeError("global-zero transport state mismatch")
    latest = inspection["generations"][-1]
    pid, ticks = _active_identity_for_inspection(root, inspection)
    if (
        latest.get("pid_identity_alive") is not False
        or controller._pid_identity(pid, ticks)
    ):
        raise AdaptiveChildResumeError("global-zero worker remains alive")
    proof = _safe_root_path(root, RUNTIME_ROOT / "proof.drat")
    cap = loaded["record"]["resource_policy"]["proof_max_bytes"]
    first = _stream_record(
        proof, cap=cap, root=root, role="global-zero-proof",
    )
    holders = _writable_holders(proof)
    second = _stream_record(
        proof, cap=cap, root=root, role="global-zero-proof",
    )
    if holders or not json_type_equal(first, second):
        raise AdaptiveChildResumeError(
            "global-zero proof is not stable/writer-free"
        )
    checkpoint_sha = latest.get("checkpoint_manifest_sha256")
    if (
        inspection["state"] == "CHECKPOINTED"
        and not _is_sha256(checkpoint_sha)
    ):
        raise AdaptiveChildResumeError(
            "checkpointed global-zero root lacks checkpoint commit"
        )
    if (
        inspection["state"] == "INACTIVE_UNCHECKPOINTED"
        and checkpoint_sha is not None
    ):
        raise AdaptiveChildResumeError(
            "inactive global-zero root unexpectedly has checkpoint"
        )
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-adaptive-global-zero-quiescence-v5",
        "lane_index": lane_index,
        "descendant_index": descendant_index,
        "new_root_identity": _directory_identity(
            root, require_mode_0700=True,
        ),
        "new_pid": pid, "new_proc_start_ticks": ticks,
        "state": inspection["state"], "pid_identity_alive": False,
        "checkpoint_commit_sha256": checkpoint_sha,
        "proof_sha256": first["sha256"], "proof_bytes": first["bytes"],
        "writable_holders": [],
    })


def _committed_quiescence_record(
    root: Path, lane_index: int, descendant_index: int,
    loaded: Mapping[str, Any],
) -> dict[str, Any]:
    inspection = _inspect_controller(root)
    if inspection["state"] not in {"CHECKPOINTED", "INACTIVE_UNCHECKPOINTED"}:
        raise AdaptiveChildResumeError("committed rollback requires stopped root")
    if not inspection["generations"]:
        raise AdaptiveChildResumeError("committed rollback root has no generation")
    latest = inspection["generations"][-1]
    pid, ticks = _active_identity_for_inspection(root, inspection)
    if (
        type(lane_index) is not int or type(descendant_index) is not int
        or (lane_index, descendant_index) not in TARGET_KEYS
        or latest.get("pid_identity_alive") is not False
        or controller._pid_identity(pid, ticks)
    ):
        raise AdaptiveChildResumeError("committed rollback solver is not dead")
    proof = _safe_root_path(root, RUNTIME_ROOT / "proof.drat")
    cap = loaded["record"]["resource_policy"]["proof_max_bytes"]
    first = _stream_record(
        proof, cap=cap, root=root, role="committed-rollback-proof",
    )
    holders = _writable_holders(proof)
    second = _stream_record(
        proof, cap=cap, root=root, role="committed-rollback-proof",
    )
    if holders or not json_type_equal(first, second):
        raise AdaptiveChildResumeError(
            "committed rollback proof is not quiescent"
        )
    checkpoint_sha = latest.get("checkpoint_manifest_sha256")
    if (
        inspection["state"] == "CHECKPOINTED"
        and not _is_sha256(checkpoint_sha)
    ) or (
        inspection["state"] == "INACTIVE_UNCHECKPOINTED"
        and checkpoint_sha is not None
    ):
        raise AdaptiveChildResumeError(
            "committed rollback checkpoint binding is inconsistent"
        )
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-adaptive-new-root-quiescence-observation-v5",
        "lane_index": lane_index,
        "descendant_index": descendant_index,
        "new_root_identity": _directory_identity(
            root, require_mode_0700=True,
        ),
        "new_pid": pid, "new_proc_start_ticks": ticks,
        "state": inspection["state"], "pid_identity_alive": False,
        "checkpoint_commit_sha256": checkpoint_sha,
        "proof_sha256": first["sha256"], "proof_bytes": first["bytes"],
        "writable_holders": [],
    })


def rollback_handoff_batch(
    roots: Sequence[Path], cpus: Sequence[int], *,
    batch_commit_path: Path, expected_batch_commit_sha256: str,
    checkpoint_summary_path: Path,
) -> dict[str, Any]:
    commit_pin = _require_sha256(
        expected_batch_commit_sha256, "batch handoff commit pin",
    )
    stopped = checkpoint_stop_batch(
        roots, cpus, summary_path=checkpoint_summary_path,
    )
    root_list, cpu_list = _cover_roots_cpus(roots, cpus)
    loaded_items: list[dict[str, Any]] = []
    verifications: list[dict[str, Any]] = []
    with contextlib.ExitStack() as stack:
        for root in sorted(root_list, key=str):
            stack.enter_context(_root_lock(root, exclusive=True))
        for root in root_list:
            loaded = _load_static(
                root, instance=None, switch_verifier=None,
                science_modules=None,
            )
            if loaded["record"]["strict_base"] is not True:
                raise AdaptiveChildResumeError(
                    "committed rollback requires strict roots"
                )
            session = _load_session(root, loaded)
            verification = _verify_complete_handoff_links(
                root, loaded, session,
            )
            if verification["batch_commit_sha256"] != commit_pin:
                raise AdaptiveChildResumeError(
                    "rollback root binds another batch commit"
                )
            loaded_items.append(loaded)
            verifications.append(verification)
        attempt_ids = {item["attempt_id"] for item in verifications}
        incident_pins = {
            item["incident_precondition_sha256"] for item in verifications
        }
        if len(attempt_ids) != 1 or len(incident_pins) != 1:
            raise AdaptiveChildResumeError("rollback roots disagree on v4 incident")
        attempt_pin, incident_pin = next(iter(attempt_ids)), next(iter(incident_pins))
        common = _batch_common(loaded_items)
        expected_switch_record = loaded_items[0]["switch_evidence"]
        if any(
            not json_type_equal(
                item["switch_evidence"], expected_switch_record,
            )
            for item in loaded_items[1:]
        ):
            raise AdaptiveChildResumeError(
                "rollback roots disagree on exact switch record"
            )
        entries = _cover_entries(root_list, cpu_list, loaded_items)
        keys = [
            (
                _binding_for_root(verification, root)["lane_index"],
                _binding_for_root(
                    verification, root,
                )["descendant_index"],
            )
            for root, verification in zip(
                root_list, verifications, strict=True,
            )
        ]
        if keys != list(TARGET_KEYS):
            raise AdaptiveChildResumeError(
                "rollback roots do not cover canonical eight targets"
            )
        quiescence = [
            _committed_quiescence_record(
                entry["root"], entry["lane_index"],
                entry["descendant_index"], entry["loaded"],
            )
            for entry in entries
        ]
        source_hashes = {
            item["record"]["execution_module_binding"][
                "switch_v4_source_sha256"
            ]
            for item in loaded_items
        }
        if len(source_hashes) != 1:
            raise AdaptiveChildResumeError(
                "rollback roots disagree on switch-v4 source"
            )
        switch = _switch_v4_module(next(iter(source_hashes)))
        if attempt_pin != switch.ATTEMPT_ID:
            raise AdaptiveChildResumeError("rollback attempt id misses frozen v4")
    # The runner releases all new-root locks.  switch-v4 is the unique owner
    # that reacquires and independently rechecks all sixteen new entrypoints.
    rollback_record = switch.rollback_committed_handoff(
        Path(batch_commit_path),
        expected_batch_commit_sha256=commit_pin,
        expected_attempt_id=attempt_pin,
        expected_incident_precondition_sha256=incident_pin,
        expected_switch_evidence_sha256=common[
            "expected_switch_evidence_sha256"
        ],
        expected_batch_manifest_sha256=common[
            "expected_batch_manifest_sha256"
        ],
        expected_switch_record=expected_switch_record,
        quiescence_records=quiescence,
    )
    if (
        type(rollback_record) is not dict
        or not _is_sha256(rollback_record.get("record_sha256"))
        or rollback_record.get("committed_handoff_sha256") != commit_pin
        or rollback_record.get("attempt_id") != attempt_pin
        or rollback_record.get("incident_precondition_sha256")
            != incident_pin
        or rollback_record.get("new_workers_quiescent") is not True
        or rollback_record.get("old_checkpoint_replayed") is not True
        or rollback_record.get("authenticated") is not False
        or rollback_record.get("launch_authorized") is not False
    ):
        raise AdaptiveChildResumeError(
            "committed rollback attestation mismatch"
        )
    return seal({
        "schema_version": SCHEMA_VERSION, "kind": BATCH_SUMMARY_KIND,
        "gate": GATE, "action": "rollback-handoff-batch",
        "success": True, "complete_binary_cover": True,
        "checkpoint_summary_sha256": stopped["record_sha256"],
        "batch_commit_sha256": commit_pin,
        "attempt_id": attempt_pin,
        "incident_precondition_sha256": incident_pin,
        "rollback_record_sha256": rollback_record["record_sha256"],
        "old_checkpoint_replayed": True, "new_workers_quiescent": True,
        "new_resume_entrypoints_retired": True,
        "launch_authorized": False, "scientific_claim": False,
    })


def _writable_holders(path: Path) -> list[int]:
    wanted = os.stat(path, follow_symlinks=False)
    if not stat.S_ISREG(wanted.st_mode):
        raise AdaptiveChildResumeError("proof holder target is not regular")
    identity = lambda item: (
        item.st_dev, item.st_ino, item.st_mode, item.st_uid, item.st_nlink,
        item.st_size, item.st_mtime_ns, item.st_ctime_ns,
    )
    holders: set[int] = set()
    for process in Path("/proc").iterdir():
        if not process.name.isdigit():
            continue
        try:
            status_lines = (process / "status").read_text(encoding="ascii").splitlines()
            uid_line = [line for line in status_lines if line.startswith("Uid:")]
            if len(uid_line) != 1 or int(uid_line[0].split()[2]) != wanted.st_uid:
                continue
            descriptors = list((process / "fd").iterdir())
        except (FileNotFoundError, ProcessLookupError):
            continue
        except (PermissionError, ValueError, IndexError) as exc:
            raise AdaptiveChildResumeError(
                "cannot inspect process descriptor table"
            ) from exc
        for descriptor in descriptors:
            try:
                observed = os.stat(descriptor)
                if (observed.st_dev, observed.st_ino) != (wanted.st_dev, wanted.st_ino):
                    continue
                flags = [
                    line for line in (process / "fdinfo" / descriptor.name).read_text(
                        encoding="ascii"
                    ).splitlines() if line.startswith("flags:")
                ]
                if len(flags) != 1:
                    raise AdaptiveChildResumeError("ambiguous fd flags")
                if int(flags[0].split(":", 1)[1].strip(), 8) & os.O_ACCMODE != os.O_RDONLY:
                    holders.add(int(process.name))
            except (FileNotFoundError, ProcessLookupError):
                continue
            except (PermissionError, ValueError) as exc:
                raise AdaptiveChildResumeError(
                    "cannot inspect descriptor flags"
                ) from exc
    if identity(wanted) != identity(os.stat(path, follow_symlinks=False)):
        raise AdaptiveChildResumeError("proof changed during writer scan")
    return sorted(holders)


def _contains_line(payload: bytes, marker: bytes) -> bool:
    return marker in [line.strip() for line in payload.splitlines()]


def _checker_preexec(cap: int, timeout_seconds: int) -> Callable[[], None]:
    def apply() -> None:
        fsize_hard = resource.getrlimit(resource.RLIMIT_FSIZE)[1]
        selected = cap if fsize_hard == resource.RLIM_INFINITY else min(cap, fsize_hard)
        resource.setrlimit(resource.RLIMIT_FSIZE, (selected, selected))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        cpu_hard = max(1, int(math.ceil(timeout_seconds)))
        resource.setrlimit(resource.RLIMIT_CPU, (cpu_hard, cpu_hard))
    return apply


def _run_checker(
    argv: Sequence[str], *, cwd: Path, timeout_seconds: int, file_cap: int,
    marker: bytes,
) -> dict[str, Any]:
    stdout_path = cwd / f"checker-{uuid.uuid4().hex}.stdout"
    stderr_path = cwd / f"checker-{uuid.uuid4().hex}.stderr"
    stdout_fd = os.open(stdout_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC, 0o600)
    stderr_fd = os.open(stderr_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC, 0o600)
    started = time.monotonic_ns()
    try:
        process = subprocess.Popen(
            [str(item) for item in argv], cwd=cwd,
            env={"LANG": "C", "LC_ALL": "C", "PATH": "/usr/bin:/bin", "TZ": "UTC"},
            stdin=subprocess.DEVNULL, stdout=stdout_fd, stderr=stderr_fd,
            close_fds=True, start_new_session=True,
            preexec_fn=_checker_preexec(file_cap, timeout_seconds),
        )
        timed_out = False
        try:
            returncode = process.wait(timeout=timeout_seconds)
        except subprocess.TimeoutExpired:
            timed_out = True
            process.kill()
            returncode = process.wait()
    finally:
        os.close(stdout_fd)
        os.close(stderr_fd)
    ended = time.monotonic_ns()
    stdout = _read_bounded(stdout_path, cap=MAX_LOG_BYTES, root=None, role="checker-stdout")
    stderr = _read_bounded(stderr_path, cap=MAX_LOG_BYTES, root=None, role="checker-stderr")
    stdout_record = _stream_record(stdout_path, cap=MAX_LOG_BYTES, root=None, role="checker-stdout")
    stderr_record = _stream_record(stderr_path, cap=MAX_LOG_BYTES, root=None, role="checker-stderr")
    stdout_path.unlink()
    stderr_path.unlink()
    if timed_out or returncode != 0 or stderr != b"" or not _contains_line(stdout, marker):
        raise AdaptiveChildResumeError(f"checker failed required marker {marker.decode('ascii')}")
    command = [str(item) for item in argv]
    return {
        "argv": command, "argv_sha256": canonical_sha256(command),
        "started_monotonic_ns": started, "ended_monotonic_ns": ended,
        "exit_code": returncode, "timed_out": timed_out,
        "stdout": {"sha256": stdout_record["sha256"], "bytes": stdout_record["bytes"]},
        "stderr": {"sha256": stderr_record["sha256"], "bytes": stderr_record["bytes"]},
        "semantic_marker": marker.decode("ascii"), "verified": True,
    }


def _dead_quiescent(root: Path, loaded: Mapping[str, Any]) -> dict[str, Any]:
    inspection = _inspect_controller(root)
    if inspection["state"] not in {"CHECKPOINTED", "INACTIVE_UNCHECKPOINTED"}:
        raise AdaptiveChildResumeError("proof harvest requires stopped transport")
    if not inspection["generations"]:
        raise AdaptiveChildResumeError("stopped transport has no generation")
    latest = inspection["generations"][-1]
    if latest.get("pid_identity_alive") is not False or latest.get("poison_claim") is not None:
        raise AdaptiveChildResumeError("latest solver identity is not cleanly dead")
    proof = root / RUNTIME_ROOT / "proof.drat"
    stdout = root / RUNTIME_ROOT / "solver.stdout"
    cap = loaded["record"]["resource_policy"]["proof_max_bytes"]
    proof_record = _stream_record(proof, cap=cap, root=root, role="stopped-binary-drat")
    if proof_record["bytes"] <= 0:
        raise AdaptiveChildResumeError("stopped DRAT is empty")
    holders = _writable_holders(proof)
    if holders:
        raise AdaptiveChildResumeError(f"stopped DRAT still has writers: {holders}")
    stdout_payload = _read_bounded(stdout, cap=MAX_LOG_BYTES, root=root, role="solver-stdout")
    stdout_record = _stream_record(stdout, cap=MAX_LOG_BYTES, root=root, role="solver-stdout")
    if not _contains_line(stdout_payload, SOLVER_MARKER):
        raise AdaptiveChildResumeError("solver stdout lacks exact UNSAT marker")
    return {
        "inspection": inspection, "transport_state": inspection["state"],
        "latest_generation": latest.get("generation"),
        "latest_pid": latest.get("pid"),
        "latest_proc_start_ticks": latest.get("proc_start_ticks"),
        "latest_pid_identity_alive": False, "writable_holders": [],
        "proof": proof_record, "solver_stdout": stdout_record,
        "solver_unsat_marker": SOLVER_MARKER.decode("ascii"),
        "solver_exit_code_observed": None,
    }


def _checker_paths(static: Mapping[str, Any]) -> tuple[Path, Path]:
    tools = static["toolchain_binding"]["tools"]
    return Path(tools["drat_checker"]["path"]), Path(tools["lrat_checker"]["path"])


def _proof_sequence(
    *, cnf: Path, drat: Path, lrat: Path, static: Mapping[str, Any],
    work: Path,
) -> dict[str, Any]:
    drat_checker, lrat_checker = _checker_paths(static)
    cap = static["resource_policy"]["proof_max_bytes"]
    timeout = static["resource_policy"]["checker_timeout_seconds"]
    seconds = str(timeout)

    def checked(operation: str, argv: Sequence[str], marker: bytes) -> dict[str, Any]:
        raw = _run_checker(
            argv, cwd=work, timeout_seconds=timeout, file_cap=cap,
            marker=marker,
        )
        public = dict(raw)
        # Private paths, logs, and monotonic timestamps are ephemeral.
        # Removing them makes the public result reproducible by a later
        # fresh replay.
        for field in (
            "argv", "argv_sha256", "started_monotonic_ns",
            "ended_monotonic_ns", "stdout", "stderr",
        ):
            public.pop(field, None)
        public["operation"] = operation
        return public

    first_drat = checked(
        "drat-verify",
        [str(drat_checker), str(cnf), str(drat), "-t", seconds],
        DRAT_MARKER,
    )
    conversion = checked(
        "drat-to-lrat",
        [str(drat_checker), str(cnf), str(drat), "-L", str(lrat), "-t", seconds],
        DRAT_MARKER,
    )
    private_lrat = _stream_record(
        lrat, cap=cap, root=None, role="converted-lrat",
    )
    if private_lrat["bytes"] <= 0:
        raise AdaptiveChildResumeError("DRAT conversion emitted empty LRAT")
    first_lrat = checked(
        "lrat-check", [str(lrat_checker), str(cnf), str(lrat)], LRAT_MARKER,
    )
    fresh_drat = checked(
        "fresh-drat-replay",
        [str(drat_checker), str(cnf), str(drat), "-t", seconds],
        DRAT_MARKER,
    )
    fresh_lrat = checked(
        "fresh-lrat-replay",
        [str(lrat_checker), str(cnf), str(lrat)], LRAT_MARKER,
    )
    return {
        "drat_verify": first_drat,
        "drat_to_lrat": conversion,
        "lrat_check": first_lrat,
        "fresh_drat_replay": fresh_drat,
        "fresh_lrat_replay": fresh_lrat,
        "drat_independently_verified": True,
        "lrat_independently_verified": True,
        "fresh_both_replayed": True,
        "lrat_private": {
            "role": "converted-lrat",
            "sha256": private_lrat["sha256"],
            "bytes": private_lrat["bytes"],
        },
    }

def _proof_payload_binding(
    value: Mapping[str, Any], *, role: str,
) -> dict[str, Any]:
    if (
        type(value) is not dict
        or not _is_sha256(value.get("sha256"))
        or type(value.get("bytes")) is not int
        or value["bytes"] <= 0
    ):
        raise AdaptiveChildResumeError(
            f"malformed {role} proof binding"
        )
    return {
        "role": role,
        "sha256": value["sha256"],
        "bytes": value["bytes"],
    }


def _terminal_claim_value(
    target: Path, static: Mapping[str, Any], session: Mapping[str, Any],
    handoff_provenance: Mapping[str, Any],
    quiescence: Mapping[str, Any],
    drat_payload: Mapping[str, Any], lrat_payload: Mapping[str, Any],
    *, nonce_hex: str,
) -> dict[str, Any]:
    if (
        type(nonce_hex) is not str
        or re.fullmatch(r"[0-9a-f]{64}", nonce_hex) is None
    ):
        raise AdaptiveChildResumeError("terminal nonce is malformed")
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": TERMINAL_CLAIM_KIND,
        "gate": GATE,
        "authority": AUTHORITY,
        "test_only": True,
        "production_eligible": False,
        "root": str(target),
        "static_sha256": static["record_sha256"],
        "session_sha256": session["record_sha256"],
        "handoff_provenance": dict(handoff_provenance),
        "overlay_manifest_sha256": static["overlay_manifest_sha256"],
        "hard_evidence_sha256": static["hard_evidence_sha256"],
        "switch_evidence_sha256": static["switch_evidence_sha256"],
        "switch_structure_validation_sha256":
            static["switch_structure_validation"]["record_sha256"],
        "global_leaf_index": static["selection"]["global_leaf_index"],
        "descendant_index": static["selection"]["descendant_index"],
        "descendant_sha256": static["selection"]["descendant_sha256"],
        "relative_assignment_literals": list(
            static["selection"]["relative_assignment_literals"]
        ),
        "descendant_cnf": dict(static["descendant_cnf"]),
        "descendant_cnf_artifact": dict(
            static["material_files"]["descendant_cnf"]
        ),
        "source_binding_sha256":
            static["source_binding"]["source_binding_sha256"],
        "execution_module_binding_sha256":
            static["execution_module_binding"][
                "execution_module_binding_sha256"
            ],
        "toolchain_sha256":
            static["toolchain_binding"]["toolchain_sha256"],
        "claim_scope": dict(static["claim_scope"]),
        "quiescence": dict(quiescence),
        "prospective_drat_artifact": _proof_payload_binding(
            drat_payload, role="binary-drat",
        ),
        "prospective_lrat_artifact": _proof_payload_binding(
            lrat_payload, role="converted-lrat",
        ),
        "all_proof_preflight_passed": True,
        "leaf_unsat_authenticated": False,
        "nonce_hex": nonce_hex,
    })


def _certificate_value(
    target: Path, static: Mapping[str, Any], session: Mapping[str, Any],
    claim: Mapping[str, Any],
    handoff_provenance: Mapping[str, Any],
    quiescence: Mapping[str, Any],
    proof_sequence: Mapping[str, Any],
    drat_artifact: Mapping[str, Any],
    lrat_artifact: Mapping[str, Any],
) -> dict[str, Any]:
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": CERTIFICATE_KIND,
        "gate": GATE,
        "authority": AUTHORITY,
        "test_only": True,
        "production_eligible": False,
        "root": str(target),
        "static_sha256": static["record_sha256"],
        "session_sha256": session["record_sha256"],
        "terminal_claim_sha256": claim["record_sha256"],
        "handoff_provenance": dict(handoff_provenance),
        "overlay_manifest_sha256": static["overlay_manifest_sha256"],
        "hard_evidence_sha256": static["hard_evidence_sha256"],
        "switch_evidence_sha256": static["switch_evidence_sha256"],
        "switch_structure_validation_sha256":
            static["switch_structure_validation"]["record_sha256"],
        "global_leaf_index": static["selection"]["global_leaf_index"],
        "descendant_index": static["selection"]["descendant_index"],
        "descendant_sha256": static["selection"]["descendant_sha256"],
        "relative_assignment_literals": list(
            static["selection"]["relative_assignment_literals"]
        ),
        "descendant_cnf": dict(static["descendant_cnf"]),
        "descendant_cnf_artifact": dict(
            static["material_files"]["descendant_cnf"]
        ),
        "source_binding_sha256":
            static["source_binding"]["source_binding_sha256"],
        "execution_module_binding_sha256":
            static["execution_module_binding"][
                "execution_module_binding_sha256"
            ],
        "toolchain_sha256":
            static["toolchain_binding"]["toolchain_sha256"],
        "claim_scope": dict(static["claim_scope"]),
        "quiescence": dict(quiescence),
        "proof_sequence": dict(proof_sequence),
        "drat_artifact": dict(drat_artifact),
        "lrat_artifact": dict(lrat_artifact),
        "solver_stdout_unsat_marker_observed": True,
        "solver_exit_code_observed": None,
        "detached_solver_exit_code_not_invented": True,
        "leaf_unsat_authenticated": True,
        "parent_leaf_unsat_claim": False,
        "distance_lower_bound_claim": False,
        "checkpoint_scientific_authority": False,
        "publication_certificate": False,
    })


def _final_value(
    target: Path, static: Mapping[str, Any], session: Mapping[str, Any],
    claim: Mapping[str, Any], certificate: Mapping[str, Any],
    handoff_provenance: Mapping[str, Any],
    drat_artifact: Mapping[str, Any],
    lrat_artifact: Mapping[str, Any],
) -> dict[str, Any]:
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": FINAL_KIND,
        "gate": GATE,
        "authority": AUTHORITY,
        "test_only": True,
        "state": "PROOF_CARRYING_DESCENDANT_UNSAT",
        "root": str(target),
        "static_sha256": static["record_sha256"],
        "session_sha256": session["record_sha256"],
        "terminal_claim_sha256": claim["record_sha256"],
        "certificate_sha256": certificate["record_sha256"],
        "handoff_provenance": dict(handoff_provenance),
        "overlay_manifest_sha256": static["overlay_manifest_sha256"],
        "hard_evidence_sha256": static["hard_evidence_sha256"],
        "switch_evidence_sha256": static["switch_evidence_sha256"],
        "global_leaf_index": static["selection"]["global_leaf_index"],
        "descendant_index": static["selection"]["descendant_index"],
        "descendant_sha256": static["selection"]["descendant_sha256"],
        "relative_assignment_literals": list(
            static["selection"]["relative_assignment_literals"]
        ),
        "descendant_cnf": dict(static["descendant_cnf"]),
        "descendant_cnf_artifact": dict(
            static["material_files"]["descendant_cnf"]
        ),
        "source_binding_sha256":
            static["source_binding"]["source_binding_sha256"],
        "execution_module_binding_sha256":
            static["execution_module_binding"][
                "execution_module_binding_sha256"
            ],
        "toolchain_sha256":
            static["toolchain_binding"]["toolchain_sha256"],
        "claim_scope": dict(static["claim_scope"]),
        "drat_artifact": _proof_payload_binding(
            drat_artifact, role="binary-drat",
        ),
        "lrat_artifact": _proof_payload_binding(
            lrat_artifact, role="converted-lrat",
        ),
        "leaf_unsat_authenticated": True,
        "no_parent_or_distance_claim": True,
        "checkpoint_scientific_authority": False,
        "production_eligible": False,
    })


def harvest_root(
    root: Path, *, instance: Any | None = None,
    switch_verifier: Callable[..., Mapping[str, Any]] | None = None,
    science_modules: tuple[Any, Any, Any, Any] | None = None,
) -> dict[str, Any]:
    target = _existing_root(root)
    with _root_lock(target, exclusive=True):
        action_kwargs = _action_kwargs(
            instance=instance, switch_verifier=switch_verifier,
            science_modules=science_modules,
        )
        loaded = _load_static(target, **action_kwargs)
        session = _load_session(target, loaded)
        handoff_provenance = _fresh_handoff_provenance(
            target, loaded, session,
        )
        _validate_new_output_path(
            target / TERMINAL_BUNDLE, label="terminal bundle",
        )
        before = _dead_quiescent(target, loaded)
        static = loaded["record"]
        cap = static["resource_policy"]["proof_max_bytes"]
        with tempfile.TemporaryDirectory(
            prefix="adaptive-child-proof-"
        ) as temporary:
            work = Path(temporary)
            private_drat = work / "proof.drat"
            private_lrat = work / "proof.lrat"
            copied = _stream_copy(
                _safe_root_path(
                    target, RUNTIME_ROOT / "proof.drat"
                ),
                private_drat, cap=cap, expected=before["proof"],
            )
            private_drat_record = {
                "role": "binary-drat",
                "sha256": copied["sha256"],
                "bytes": copied["bytes"],
            }
            sequence = _proof_sequence(
                cnf=target / STATIC_DESCENDANT_CNF,
                drat=private_drat, lrat=private_lrat,
                static=static, work=work,
            )
            private_lrat_record = {
                "role": "converted-lrat",
                "sha256": sequence["lrat_private"]["sha256"],
                "bytes": sequence["lrat_private"]["bytes"],
            }
            after = _dead_quiescent(target, loaded)
            if not json_type_equal(before, after):
                raise AdaptiveChildResumeError(
                    "transport/proof changed during proof replay"
                )

            staging = _new_terminal_staging(target)
            try:
                staged_drat = _publish_stream(
                    private_drat,
                    staging / DRAT_ARTIFACT.name,
                    cap=cap, expected=private_drat_record,
                    root=target,
                )
                staged_lrat = _publish_stream(
                    private_lrat,
                    staging / LRAT_ARTIFACT.name,
                    cap=cap, expected=private_lrat_record,
                    root=target,
                )
                drat_artifact = _rebased_terminal_artifact(
                    staged_drat,
                    staged_relative=Path(staging.name)
                        / DRAT_ARTIFACT.name,
                    final_relative=DRAT_ARTIFACT,
                    role="binary-drat",
                )
                lrat_artifact = _rebased_terminal_artifact(
                    staged_lrat,
                    staged_relative=Path(staging.name)
                        / LRAT_ARTIFACT.name,
                    final_relative=LRAT_ARTIFACT,
                    role="converted-lrat",
                )
                claim = _terminal_claim_value(
                    target, static, session, handoff_provenance,
                    before, drat_artifact, lrat_artifact,
                    nonce_hex=os.urandom(32).hex(),
                )
                certificate = _certificate_value(
                    target, static, session, claim,
                    handoff_provenance, before, sequence,
                    drat_artifact, lrat_artifact,
                )
                commit = _final_value(
                    target, static, session, claim, certificate,
                    handoff_provenance, drat_artifact, lrat_artifact,
                )
                _publish_json(
                    staging / TERMINAL_CLAIM.name, claim,
                )
                _publish_json(
                    staging / CERTIFICATE.name, certificate,
                )
                _publish_json(
                    staging / FINAL_COMMIT.name, commit,
                )
                final_quiescence = _dead_quiescent(
                    target, loaded,
                )
                final_loaded = _load_static(
                    target, **action_kwargs,
                )
                final_session = _load_session(
                    target, final_loaded,
                )
                final_handoff = _fresh_handoff_provenance(
                    target, final_loaded, final_session,
                )
                if (
                    not json_type_equal(before, final_quiescence)
                    or final_loaded["record"]["record_sha256"]
                    != static["record_sha256"]
                    or final_session["record_sha256"]
                    != session["record_sha256"]
                    or not json_type_equal(
                        handoff_provenance, final_handoff,
                    )
                ):
                    raise AdaptiveChildResumeError(
                        "static/session/handoff/proof changed before "
                        "terminal bundle commit"
                    )
                staged_drat_now = _rebased_terminal_artifact(
                    _stream_record(
                        staging / DRAT_ARTIFACT.name,
                        cap=cap, root=target, role="binary-drat",
                    ),
                    staged_relative=Path(staging.name)
                        / DRAT_ARTIFACT.name,
                    final_relative=DRAT_ARTIFACT,
                    role="binary-drat",
                )
                staged_lrat_now = _rebased_terminal_artifact(
                    _stream_record(
                        staging / LRAT_ARTIFACT.name,
                        cap=cap, root=target,
                        role="converted-lrat",
                    ),
                    staged_relative=Path(staging.name)
                        / LRAT_ARTIFACT.name,
                    final_relative=LRAT_ARTIFACT,
                    role="converted-lrat",
                )
                if (
                    not json_type_equal(
                        staged_drat_now, drat_artifact,
                    )
                    or not json_type_equal(
                        staged_lrat_now, lrat_artifact,
                    )
                    or not json_type_equal(
                        _read_json(
                            staging / TERMINAL_CLAIM.name,
                            root=target,
                        ), claim,
                    )
                    or not json_type_equal(
                        _read_json(
                            staging / CERTIFICATE.name,
                            root=target,
                        ), certificate,
                    )
                    or not json_type_equal(
                        _read_json(
                            staging / FINAL_COMMIT.name,
                            root=target,
                        ), commit,
                    )
                ):
                    raise AdaptiveChildResumeError(
                        "terminal staging changed before atomic commit"
                    )
                _commit_terminal_bundle(target, staging)
            except BaseException:
                # After rename, staging is absent and the complete fixed bundle
                # remains fail-closed for verify. Before rename, discard only
                # this exact non-authoritative random staging child.
                try:
                    staging_info = os.stat(
                        staging, follow_symlinks=False,
                    )
                except FileNotFoundError:
                    staging_info = None
                if (
                    staging_info is not None
                    and stat.S_ISDIR(staging_info.st_mode)
                ):
                    _discard_terminal_staging(target, staging)
                raise

        published_drat = _stream_record(
            target / DRAT_ARTIFACT, cap=cap, root=target,
            role="binary-drat",
        )
        published_lrat = _stream_record(
            target / LRAT_ARTIFACT, cap=cap, root=target,
            role="converted-lrat",
        )
        published_claim = _read_json(
            target / TERMINAL_CLAIM, root=target,
        )
        published_certificate = _read_json(
            target / CERTIFICATE, root=target,
        )
        published_commit = _read_json(
            target / FINAL_COMMIT, root=target,
        )
        if (
            not json_type_equal(published_drat, drat_artifact)
            or not json_type_equal(published_lrat, lrat_artifact)
            or not json_type_equal(published_claim, claim)
            or not json_type_equal(
                published_certificate, certificate,
            )
            or not json_type_equal(published_commit, commit)
        ):
            raise AdaptiveChildResumeError(
                "atomic terminal bundle post-commit mismatch"
            )
        return commit


def verify_root(
    root: Path, *, instance: Any | None = None,
    switch_verifier: Callable[..., Mapping[str, Any]] | None = None,
    science_modules: tuple[Any, Any, Any, Any] | None = None,
) -> dict[str, Any]:
    target = _existing_root(root)
    with _root_lock(target, exclusive=False):
        action_kwargs = _action_kwargs(
            instance=instance, switch_verifier=switch_verifier,
            science_modules=science_modules,
        )
        loaded = _load_static(target, **action_kwargs)
        session = _load_session(target, loaded)
        static = loaded["record"]
        handoff_provenance = _fresh_handoff_provenance(
            target, loaded, session,
        )
        claim = _read_json(target / TERMINAL_CLAIM, root=target)
        certificate = _read_json(target / CERTIFICATE, root=target)
        commit = _read_json(target / FINAL_COMMIT, root=target)
        if not all(
            selfhash_valid(item) for item in (claim, certificate, commit)
        ):
            raise AdaptiveChildResumeError(
                "terminal record self-hash mismatch"
            )

        quiescence = _dead_quiescent(target, loaded)
        cap = static["resource_policy"]["proof_max_bytes"]
        drat = _stream_record(
            target / DRAT_ARTIFACT, cap=cap, root=target,
            role="binary-drat",
        )
        lrat = _stream_record(
            target / LRAT_ARTIFACT, cap=cap, root=target,
            role="converted-lrat",
        )
        if (
            not json_type_equal(
                drat, certificate.get("drat_artifact")
            )
            or not json_type_equal(
                lrat, certificate.get("lrat_artifact")
            )
        ):
            raise AdaptiveChildResumeError(
                "terminal proof artifact binding mismatch"
            )
        expected_claim = _terminal_claim_value(
            target, static, session, handoff_provenance, quiescence,
            drat, lrat, nonce_hex=claim.get("nonce_hex"),
        )
        if not json_type_equal(claim, expected_claim):
            raise AdaptiveChildResumeError(
                "terminal claim canonical binding mismatch"
            )

        with tempfile.TemporaryDirectory(
            prefix="adaptive-child-verify-"
        ) as temporary:
            work = Path(temporary)
            converted_lrat = work / "fresh-converted.lrat"
            fresh_sequence = _proof_sequence(
                cnf=target / STATIC_DESCENDANT_CNF,
                drat=target / DRAT_ARTIFACT,
                lrat=converted_lrat,
                static=static,
                work=work,
            )
            converted_record = _stream_record(
                converted_lrat, cap=cap, root=None,
                role="converted-lrat",
            )
        if not json_type_equal(
            _proof_payload_binding(
                converted_record, role="converted-lrat",
            ),
            _proof_payload_binding(lrat, role="converted-lrat"),
        ):
            raise AdaptiveChildResumeError(
                "fresh DRAT conversion differs from published LRAT"
            )
        final_drat = _stream_record(
            target / DRAT_ARTIFACT, cap=cap, root=target,
            role="binary-drat",
        )
        final_lrat = _stream_record(
            target / LRAT_ARTIFACT, cap=cap, root=target,
            role="converted-lrat",
        )
        if (
            not json_type_equal(drat, final_drat)
            or not json_type_equal(lrat, final_lrat)
        ):
            raise AdaptiveChildResumeError(
                "published proof changed during final fresh replay"
            )
        after = _dead_quiescent(target, loaded)
        if not json_type_equal(quiescence, after):
            raise AdaptiveChildResumeError(
                "transport/proof changed during final fresh replay"
            )

        expected_certificate = _certificate_value(
            target, static, session, expected_claim,
            handoff_provenance, quiescence, fresh_sequence, drat, lrat,
        )
        if not json_type_equal(certificate, expected_certificate):
            raise AdaptiveChildResumeError(
                "terminal certificate canonical binding mismatch"
            )
        expected_commit = _final_value(
            target, static, session, expected_claim,
            expected_certificate, handoff_provenance, drat, lrat,
        )
        if not json_type_equal(commit, expected_commit):
            raise AdaptiveChildResumeError(
                "terminal final record canonical binding mismatch"
            )

        final_loaded = _load_static(target, **action_kwargs)
        final_session = _load_session(target, final_loaded)
        final_handoff = _fresh_handoff_provenance(
            target, final_loaded, final_session,
        )
        if (
            final_loaded["record"]["record_sha256"]
            != static["record_sha256"]
            or final_session["record_sha256"]
            != session["record_sha256"]
            or not json_type_equal(
                handoff_provenance, final_handoff,
            )
        ):
            raise AdaptiveChildResumeError(
                "static/session/handoff changed during final fresh replay"
            )
        return seal({
            "schema_version": SCHEMA_VERSION,
            "kind": VERIFICATION_KIND,
            "gate": GATE,
            "authority": AUTHORITY,
            "test_only": True,
            "production_eligible": False,
            "root": str(target),
            "valid": True,
            "authenticated": True,
            "static_sha256": static["record_sha256"],
            "session_sha256": session["record_sha256"],
            "terminal_claim_sha256": expected_claim["record_sha256"],
            "certificate_sha256": expected_certificate["record_sha256"],
            "final_sha256": expected_commit["record_sha256"],
            "handoff_provenance": handoff_provenance,
            "overlay_manifest_sha256":
                static["overlay_manifest_sha256"],
            "hard_evidence_sha256": static["hard_evidence_sha256"],
            "switch_evidence_sha256":
                static["switch_evidence_sha256"],
            "global_leaf_index":
                static["selection"]["global_leaf_index"],
            "descendant_index":
                static["selection"]["descendant_index"],
            "descendant_sha256":
                static["selection"]["descendant_sha256"],
            "relative_assignment_literals": list(
                static["selection"]["relative_assignment_literals"]
            ),
            "descendant_cnf": dict(static["descendant_cnf"]),
            "source_binding_sha256":
                static["source_binding"]["source_binding_sha256"],
            "execution_module_binding_sha256":
                static["execution_module_binding"][
                    "execution_module_binding_sha256"
                ],
            "toolchain_sha256":
                static["toolchain_binding"]["toolchain_sha256"],
            "claim_scope": dict(static["claim_scope"]),
            "drat_artifact": dict(drat),
            "lrat_artifact": dict(lrat),
            "fresh_proof_sequence": fresh_sequence,
            "leaf_unsat_authenticated": True,
            "checkpoint_scientific_authority": False,
            "parent_or_distance_claim": False,
        })


def _read_cli_json(path: Path) -> dict[str, Any]:
    candidate = Path(path)
    if (
        not candidate.is_absolute()
        or str(candidate) != os.path.abspath(str(candidate))
    ):
        raise AdaptiveChildResumeError("CLI JSON path must be normalized absolute")
    lexical = os.stat(candidate, follow_symlinks=False)
    if (
        stat.S_ISLNK(lexical.st_mode) or not stat.S_ISREG(lexical.st_mode)
        or candidate.resolve(strict=True) != candidate
    ):
        raise AdaptiveChildResumeError("CLI JSON path is symlinked or aliased")
    payload = _read_bounded(
        candidate, cap=MAX_JSON_BYTES, root=None, role="cli-json-input",
    )

    def object_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise AdaptiveChildResumeError(
                    f"duplicate input JSON key: {key}"
                )
            result[key] = value
        return result

    try:
        value = json.loads(
            payload.decode("ascii"), object_pairs_hook=object_pairs,
            parse_constant=lambda item: (_ for _ in ()).throw(
                AdaptiveChildResumeError(f"non-finite input JSON: {item}")
            ),
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise AdaptiveChildResumeError(f"invalid input JSON: {path}") from exc
    if type(value) is not dict:
        raise AdaptiveChildResumeError(f"input JSON is not an object: {path}")
    return value

def _read_cli_float_list(path: Path) -> list[float]:
    candidate = Path(path)
    if (
        not candidate.is_absolute()
        or str(candidate) != os.path.abspath(str(candidate))
    ):
        raise AdaptiveChildResumeError("CLI list path must be normalized absolute")
    lexical = os.stat(candidate, follow_symlinks=False)
    if (
        stat.S_ISLNK(lexical.st_mode) or not stat.S_ISREG(lexical.st_mode)
        or candidate.resolve(strict=True) != candidate
    ):
        raise AdaptiveChildResumeError("CLI list path is symlinked or aliased")
    payload = _read_bounded(
        candidate, cap=MAX_JSON_BYTES, root=None, role="cli-list-input",
    )
    try:
        value = json.loads(
            payload.decode("ascii"),
            parse_constant=lambda item: (_ for _ in ()).throw(
                AdaptiveChildResumeError(f"non-finite input JSON: {item}")
            ),
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise AdaptiveChildResumeError("invalid CLI list JSON") from exc
    if (
        type(value) is not list or len(value) != LANE_COUNT
        or any(type(item) is not float or not math.isfinite(item) or item < 0 for item in value)
    ):
        raise AdaptiveChildResumeError("CLI list must be four finite floats")
    return value


def _caps_from_args(args: argparse.Namespace) -> dict[str, int]:
    return {"proof_max_bytes": args.proof_max_bytes}


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    sub = parser.add_subparsers(dest="action", required=True)
    prepare = sub.add_parser("prepare", allow_abbrev=False)
    for name in (
        "root", "batch-root", "parent-manifest", "width6-campaign",
        "width10-campaign", "overlay-manifest", "hard-evidence",
        "switch-evidence", "elapsed-seconds-by-lane-json",
    ):
        prepare.add_argument(f"--{name}", type=Path, required=True)
    for name in (
        "expected-overlay-sha256", "expected-hard-evidence-sha256",
        "expected-switch-evidence-sha256", "expected-batch-manifest-sha256",
    ):
        prepare.add_argument(f"--{name}", required=True)
    prepare.add_argument("--descendant-index", type=int, required=True)
    prepare.add_argument(
        "--candidate-variable", type=int, action="append", required=True,
    )
    prepare.add_argument("--timeout-seconds", type=float, required=True)
    prepare.add_argument("--proof-max-bytes", type=int, required=True)
    for action in (
        "start", "checkpoint-stop", "resume", "status", "harvest", "verify",
    ):
        command = sub.add_parser(action, allow_abbrev=False)
        command.add_argument("--root", type=Path, required=True)
    start_batch_parser = sub.add_parser("start-batch", allow_abbrev=False)
    start_batch_parser.add_argument(
        "--root", type=Path, action="append", required=True,
    )
    start_batch_parser.add_argument(
        "--cpu", type=int, action="append", required=True,
    )
    start_batch_parser.add_argument(
        "--batch-commit-path", type=Path, required=True,
    )
    start_batch_parser.add_argument(
        "--expected-incident-precondition-sha256", required=True,
    )
    inspect_incident = sub.add_parser(
        "inspect-incident-batch", allow_abbrev=False,
    )
    inspect_incident.add_argument("--root", type=Path, action="append", required=True)
    for action in (
        "checkpoint-stop-batch", "resume-batch", "status-batch",
    ):
        command = sub.add_parser(action, allow_abbrev=False)
        command.add_argument("--root", type=Path, action="append", required=True)
        command.add_argument("--cpu", type=int, action="append", required=True)
        command.add_argument("--summary-path", type=Path, required=True)
    switch_cohort = sub.add_parser(
        "switch-cohort-batch", allow_abbrev=False,
    )
    switch_cohort.add_argument(
        "--root", type=Path, action="append", required=True,
    )
    switch_cohort.add_argument(
        "--cpu", type=int, action="append", required=True,
    )
    switch_cohort.add_argument(
        "--descendant-index", type=int, required=True,
    )
    switch_cohort.add_argument(
        "--summary-path", type=Path, required=True,
    )
    recover = sub.add_parser("recover-action", allow_abbrev=False)
    recover.add_argument("--root", type=Path, required=True)
    rollback = sub.add_parser("rollback-handoff-batch", allow_abbrev=False)
    rollback.add_argument("--root", type=Path, action="append", required=True)
    rollback.add_argument("--cpu", type=int, action="append", required=True)
    rollback.add_argument("--batch-commit-path", type=Path, required=True)
    rollback.add_argument("--expected-batch-commit-sha256", required=True)
    rollback.add_argument("--checkpoint-summary-path", type=Path, required=True)
    repair = sub.add_parser("repair-handoff-links", allow_abbrev=False)
    repair.add_argument("--root", type=Path, action="append", required=True)
    repair.add_argument("--batch-commit-path", type=Path, required=True)
    repair.add_argument("--expected-batch-commit-sha256", required=True)
    repair.add_argument("--expected-attempt-id", required=True)
    repair.add_argument("--expected-incident-precondition-sha256", required=True)
    return parser

def _main_in_cli_replay_scope(argv: Sequence[str] | None = None) -> int:
    _python_startup_binding(True)
    args = build_parser().parse_args(argv)
    if args.action == "prepare":
        elapsed_value = _read_cli_float_list(
            args.elapsed_seconds_by_lane_json,
        )
        result = prepare_root_from_material(
            args.root, batch_root=args.batch_root,
            parent_manifest=_read_cli_json(args.parent_manifest),
            width6_campaign=_read_cli_json(args.width6_campaign),
            width10_campaign=_read_cli_json(args.width10_campaign),
            overlay_manifest=_read_cli_json(args.overlay_manifest),
            hard_evidence=_read_cli_json(args.hard_evidence),
            switch_evidence=_read_cli_json(args.switch_evidence),
            expected_overlay_sha256=args.expected_overlay_sha256,
            expected_hard_evidence_sha256=args.expected_hard_evidence_sha256,
            expected_switch_evidence_sha256=args.expected_switch_evidence_sha256,
            expected_batch_manifest_sha256=args.expected_batch_manifest_sha256,
            descendant_index=args.descendant_index,
            candidate_variables=args.candidate_variable,
            timeout_seconds=args.timeout_seconds,
            elapsed_seconds_by_lane=elapsed_value,
            resource_caps=_caps_from_args(args), strict_base=True,
        )
    elif args.action == "start":
        result = start_root(args.root)
    elif args.action == "inspect-incident-batch":
        result = inspect_incident_batch(args.root)
    elif args.action == "start-batch":
        result = start_batch(
            args.root, args.cpu, batch_commit_path=args.batch_commit_path,
            expected_incident_precondition_sha256=(
                args.expected_incident_precondition_sha256
            ),
        )
    elif args.action in {
        "checkpoint-stop-batch", "status-batch",
    }:
        result = _batch_action(
            args.action, args.root, args.cpu, summary_path=args.summary_path,
        )
    elif args.action == "resume-batch":
        result = resume_batch(
            args.root, args.cpu, summary_path=args.summary_path,
        )
    elif args.action == "switch-cohort-batch":
        result = switch_cohort_batch(
            args.root, args.cpu,
            descendant_index=args.descendant_index,
            summary_path=args.summary_path,
        )
    elif args.action == "recover-action":
        result = recover_action(args.root)
    elif args.action == "rollback-handoff-batch":
        result = rollback_handoff_batch(
            args.root, args.cpu,
            batch_commit_path=args.batch_commit_path,
            expected_batch_commit_sha256=args.expected_batch_commit_sha256,
            checkpoint_summary_path=args.checkpoint_summary_path,
        )
    elif args.action == "repair-handoff-links":
        result = repair_handoff_links(
            args.root, batch_commit_path=args.batch_commit_path,
            expected_attempt_id=args.expected_attempt_id,
            expected_incident_precondition_sha256=args.expected_incident_precondition_sha256,
            expected_batch_commit_sha256=(
                args.expected_batch_commit_sha256
            ),
        )
    elif args.action == "checkpoint-stop":
        result = checkpoint_stop_root(args.root)
    elif args.action == "resume":
        result = resume_root(args.root)
    elif args.action == "status":
        result = status_root(args.root)
    elif args.action == "harvest":
        result = harvest_root(args.root)
    elif args.action == "verify":
        result = verify_root(args.root)
    else:  # pragma: no cover
        raise AdaptiveChildResumeError("unreachable action")
    sys.stdout.buffer.write(canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    return 0



def main(argv: Sequence[str] | None = None) -> int:
    with _strict_dependency_context():
        with _cli_replay_scope():
            return _main_in_cli_replay_scope(argv)


if __name__ == "__main__":
    try:
        _exit = main()
    except (
        AdaptiveChildResumeError, controller.ResumeControllerError,
        OSError, ValueError, TypeError, subprocess.SubprocessError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        _exit = 2
    raise SystemExit(_exit)


__all__ = [
    "AdaptiveChildResumeError", "checkpoint_stop_batch",
    "checkpoint_stop_root", "harvest_root", "prepare_root_from_material",
    "inspect_incident_batch",
    "recover_action", "repair_handoff_links", "resume_batch", "resume_root",
    "rollback_handoff_batch", "start_batch", "start_root", "status_batch",
    "switch_cohort_batch",
    "status_root", "verify_root",
]
