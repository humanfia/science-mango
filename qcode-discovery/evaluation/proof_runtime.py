"""Canonical runtime identity for every proof-producing code path.

The pipeline controller is not necessarily executed by the same Python
interpreter as the proof CLIs.  This module therefore supports both a local
fingerprint and a fail-closed probe of the configured proof interpreter.
"""

from __future__ import annotations

import base64
import hashlib
import importlib.metadata
import importlib.util
import json
import math
import os
import platform
import secrets
import select
import signal
import stat
import struct
import subprocess
import sys
import sysconfig
import time
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Any, Mapping


PROOF_RUNTIME_SCHEMA_VERSION = 2
PROOF_INTERPRETER_SCHEMA_VERSION = 1
PROOF_RUNTIME_PROBE_PROTOCOL = "qcode-proof-runtime-probe-v2"
PROOF_RUNTIME_PROBE_TIMEOUT_SECONDS = 30.0
PROOF_RUNTIME_PROBE_MAX_OUTPUT_BYTES = 64 * 1024
PROOF_RUNTIME_PROBE_TERMINATION_GRACE_SECONDS = 0.25
PROOF_RUNTIME_MAX_FILES_PER_DISTRIBUTION = 5_000
PROOF_RUNTIME_MAX_BYTES_PER_DISTRIBUTION = 512 * 1024 * 1024
PROOF_RUNTIME_MAX_TOTAL_FILES = 20_000
PROOF_RUNTIME_MAX_TOTAL_BYTES = 2 * 1024 * 1024 * 1024

# Keys are distribution names understood by importlib.metadata.  This is a
# fixed, audited closure of the production proof imports and their active
# runtime requirements:
#
# * qldpc imports galois/ldpc/stim/pymatching/cvxpy while constructing BB codes;
# * galois executes numba/llvmlite for finite-field operations;
# * numba imports PyYAML for its runtime configuration;
# * NumPy's imported F2PY stack imports charset-normalizer;
# * OR-Tools CP-SAT imports protobuf and its Python support stack;
# * python-sat supplies the CNF cardinality encoders and bundled native SAT
#   engines used by the optional exact threshold backend;
# * cvxpy imports its installed solver interfaces even though qcode's final MILP
#   is implemented with scipy/HiGHS; and
# * the remaining entries close the non-extra metadata requirements of those
#   packages on the supported Linux runtime.
#
# ``igraph`` contains the imported implementation, while ``python-igraph`` is
# its separately versioned meta distribution.
PROOF_RUNTIME_ROOT_PACKAGES = (
    "numpy",
    "ortools",
    "python-sat",
    "qldpc",
    "scipy",
    "highspy",
    "sympy",
    "igraph",
    "python-igraph",
    "ldpc",
    "galois",
    "networkx",
)
PROOF_RUNTIME_TRANSITIVE_PACKAGES = (
    "absl-py",
    "clarabel",
    "cffi",
    "charset-normalizer",
    "contourpy",
    "cvxpy",
    "cycler",
    "diskcache",
    "fonttools",
    "immutabledict",
    "jinja2",
    "joblib",
    "kiwisolver",
    "llvmlite",
    "markupsafe",
    "matplotlib",
    "mpmath",
    "numba",
    "osqp",
    "packaging",
    "pandas",
    "pillow",
    "platformdirs",
    "protobuf",
    "pycparser",
    "pymatching",
    "pyparsing",
    "python-dateutil",
    "pyyaml",
    "pytz",
    "scs",
    "setuptools",
    "sinter",
    "six",
    "stim",
    "texttable",
    "tqdm",
    "typing-extensions",
)
SOLVER_RUNTIME_PACKAGES = (
    *PROOF_RUNTIME_ROOT_PACKAGES,
    *PROOF_RUNTIME_TRANSITIVE_PACKAGES,
)
KNOWN_ANSWER_RUNTIME_PACKAGES = ("numpy", "scipy", "qldpc")
PACKAGE_IMPORT_NAMES = {
    "numpy": "numpy",
    "ortools": "ortools",
    "python-sat": "pysat",
    "qldpc": "qldpc",
    "scipy": "scipy",
    "highspy": "highspy",
    "sympy": "sympy",
    "igraph": "igraph",
    "python-igraph": "igraph",
    "ldpc": "ldpc",
    "galois": "galois",
    "networkx": "networkx",
    "absl-py": "absl",
    "clarabel": "clarabel",
    "cffi": "cffi",
    "charset-normalizer": "charset_normalizer",
    "contourpy": "contourpy",
    "cvxpy": "cvxpy",
    "cycler": "cycler",
    "diskcache": "diskcache",
    "fonttools": "fontTools",
    "immutabledict": "immutabledict",
    "jinja2": "jinja2",
    "joblib": "joblib",
    "kiwisolver": "kiwisolver",
    "llvmlite": "llvmlite",
    "markupsafe": "markupsafe",
    "matplotlib": "matplotlib",
    "mpmath": "mpmath",
    "numba": "numba",
    "osqp": "osqp",
    "packaging": "packaging",
    "pandas": "pandas",
    "pillow": "PIL",
    "platformdirs": "platformdirs",
    "protobuf": "google.protobuf",
    "pycparser": "pycparser",
    "pymatching": "pymatching",
    "pyparsing": "pyparsing",
    "python-dateutil": "dateutil",
    "pyyaml": "yaml",
    "pytz": "pytz",
    "scs": "scs",
    "setuptools": "setuptools",
    "sinter": "sinter",
    "six": "six",
    "stim": "stim",
    "texttable": "texttable",
    "tqdm": "tqdm",
    "typing-extensions": "typing_extensions",
}

_RUNTIME_KEYS = frozenset(
    {
        "schema_version",
        "python",
        "packages",
        "package_artifacts",
        "interpreter",
    }
)
_RUNTIME_CORE_KEYS = frozenset(
    {"schema_version", "python", "packages", "package_artifacts"}
)
_PYTHON_KEYS = frozenset(
    {
        "implementation",
        "version",
        "version_info",
        "cache_tag",
        "soabi",
        "platform",
        "machine",
    }
)
_INTERPRETER_KEYS = frozenset(
    {
        "schema_version",
        "invocation_path",
        "realpath",
        "reported_sys_executable",
        "prefix",
        "base_prefix",
        "invocation_lstat",
        "executable_file",
        "pyvenv_cfg",
    }
)
_FILE_IDENTITY_KEYS = frozenset(
    {
        "sha256",
        "bytes",
        "mode",
        "device",
        "inode",
        "mtime_ns",
        "ctime_ns",
    }
)
_INVOCATION_LSTAT_KEYS = frozenset(
    {
        "kind",
        "link_target",
        "mode",
        "device",
        "inode",
        "mtime_ns",
        "ctime_ns",
    }
)
_PROBE_RESPONSE_KEYS = frozenset(
    {
        "protocol",
        "nonce",
        "runtime",
        "reported_sys_executable",
        "reported_realpath",
        "reported_prefix",
        "reported_base_prefix",
    }
)
_PACKAGE_ARTIFACT_KEYS = frozenset(
    {
        "distribution",
        "import_name",
        "installed",
        "version",
        "record_sha256",
        "metadata_sha256",
        "direct_url_sha256",
        "files",
        "bytes",
        "files_sha256",
        "import_origin",
    }
)
_IMPORT_ORIGIN_KEYS = frozenset(
    {
        "name",
        "origin",
        "realpath",
        "file_identity",
        "search_locations",
    }
)

# The immutable bootstrap completes an isolated-session identity handshake
# before it executes the replaceable payload used by the probe tests.  Keeping
# the handshake outside ``_PROBE_PROGRAM`` means even an early-exiting payload
# cannot bypass the process-group identity that cleanup relies on.
_PROBE_HANDSHAKE_MAGIC = b"QPR2"
_PROBE_HANDSHAKE_STRUCT = struct.Struct(">4sQQQ")
_PROBE_BOOTSTRAP_PROGRAM = r"""
import base64
import os
import struct
import sys

handshake_fd = int(sys.argv[1])
protocol_fd = int(sys.argv[2])
payload = base64.b64decode(
    sys.argv[3].encode("ascii"),
    validate=True,
).decode("utf-8", errors="strict")
handshake = struct.pack(
    ">4sQQQ",
    b"QPR2",
    os.getpid(),
    os.getpgrp(),
    os.getsid(0),
)
offset = 0
while offset < len(handshake):
    written = os.write(handshake_fd, handshake[offset:])
    if written <= 0:
        raise RuntimeError("proof runtime handshake pipe closed")
    offset += written
os.close(handshake_fd)
sys.argv = [sys.argv[0], str(protocol_fd), *sys.argv[4:]]
exec(
    compile(payload, "<qcode-proof-runtime-probe>", "exec"),
    {"__name__": "__main__"},
)
""".strip()

# This payload writes one length-prefixed canonical frame to a parent-created
# pipe. stdout and stderr are deliberately not protocol channels, so site
# diagnostics or wrapper noise cannot inject a fingerprint.
_PROBE_PROGRAM = r"""
import importlib.util
import json
import os
import struct
import sys

fd = int(sys.argv[1])
protocol = sys.argv[2]
nonce = sys.argv[3]
module_path = sys.argv[4]
project_root = sys.argv[5]
spec = importlib.util.spec_from_file_location(
    "_qcode_proof_runtime_probe",
    module_path,
)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load proof runtime implementation")
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)
sys.path.insert(0, project_root)
runtime = module._runtime_core()
payload = {
    "protocol": protocol,
    "nonce": nonce,
    "runtime": runtime,
    "reported_sys_executable": sys.executable,
    "reported_realpath": os.path.realpath(sys.executable),
    "reported_prefix": sys.prefix,
    "reported_base_prefix": sys.base_prefix,
}
encoded = json.dumps(
    payload,
    sort_keys=True,
    separators=(",", ":"),
    ensure_ascii=True,
    allow_nan=False,
).encode("ascii")
frame = struct.pack(">I", len(encoded)) + encoded
offset = 0
while offset < len(frame):
    written = os.write(fd, frame[offset:])
    if written <= 0:
        raise RuntimeError("proof runtime probe pipe closed")
    offset += written
os.close(fd)
""".strip()


class RuntimeProbeError(RuntimeError):
    """The configured proof interpreter could not be identified safely."""


def _package_version(name: str) -> str | None:
    try:
        return importlib.metadata.version(name)
    except importlib.metadata.PackageNotFoundError:
        return None


def _optional_metadata_sha256(
    distribution: importlib.metadata.Distribution,
    filename: str,
) -> str | None:
    try:
        text = distribution.read_text(filename)
    except (OSError, UnicodeError) as exc:
        raise RuntimeProbeError(
            f"cannot read {filename} for {distribution.metadata.get('Name')}: "
            f"{exc}",
        ) from exc
    if text is None:
        return None
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _is_ignored_runtime_file(path: importlib.metadata.PackagePath) -> bool:
    parts = tuple(str(part) for part in path.parts)
    return (
        path.suffix.lower() in {".pyc", ".pyo"}
        or "__pycache__" in parts
    )


def _require_runtime_file_beneath_prefix(path: Path) -> Path:
    try:
        realpath = path.resolve(strict=True)
    except OSError as exc:
        raise RuntimeProbeError(
            f"installed proof dependency is unavailable: {path}: {exc}",
        ) from exc
    allowed_roots = {
        Path(sys.prefix).resolve(),
        Path(sys.base_prefix).resolve(),
    }
    if not any(
        realpath == root or realpath.is_relative_to(root)
        for root in allowed_roots
    ):
        raise RuntimeProbeError(
            f"installed proof dependency escapes Python prefixes: {path}",
        )
    return realpath


def _import_origin_identity(import_name: str) -> dict[str, Any]:
    try:
        spec = importlib.util.find_spec(import_name)
    except ModuleNotFoundError:
        # ``find_spec("parent.child")`` raises rather than returning ``None``
        # when the parent is absent.  The distribution lookup below still
        # fails closed if metadata claims that this import should be installed.
        spec = None
    except (ImportError, AttributeError, ValueError) as exc:
        raise RuntimeProbeError(
            f"cannot resolve proof import {import_name}: {exc}",
        ) from exc
    if spec is None:
        return {
            "name": import_name,
            "origin": None,
            "realpath": None,
            "file_identity": None,
            "search_locations": [],
        }
    locations = [
        str(Path(value).absolute())
        for value in (spec.submodule_search_locations or ())
    ]
    if any(not Path(value).is_absolute() for value in locations):
        raise RuntimeProbeError(
            f"proof import {import_name} has a relative search location",
        )
    raw_origin = spec.origin
    if raw_origin in {None, "built-in", "frozen"}:
        return {
            "name": import_name,
            "origin": raw_origin,
            "realpath": None,
            "file_identity": None,
            "search_locations": locations,
        }
    origin = Path(raw_origin)
    if not origin.is_absolute():
        raise RuntimeProbeError(
            f"proof import {import_name} has a relative origin: {origin}",
        )
    try:
        metadata = origin.lstat()
    except OSError as exc:
        raise RuntimeProbeError(
            f"proof import {import_name} origin is unavailable: {origin}: {exc}",
        ) from exc
    if not stat.S_ISREG(metadata.st_mode):
        raise RuntimeProbeError(
            f"proof import {import_name} origin is not a regular file: {origin}",
        )
    realpath = origin.resolve(strict=True)
    return {
        "name": import_name,
        "origin": str(origin),
        "realpath": str(realpath),
        "file_identity": _regular_file_identity(
            realpath,
            require_executable=False,
        ),
        "search_locations": locations,
    }


def _package_artifact_identity(
    distribution_name: str,
    import_name: str,
) -> dict[str, Any]:
    """Hash actual installed files, not only mutable version metadata."""

    origin = _import_origin_identity(import_name)
    try:
        distribution = importlib.metadata.distribution(distribution_name)
    except importlib.metadata.PackageNotFoundError:
        return {
            "distribution": distribution_name,
            "import_name": import_name,
            "installed": False,
            "version": None,
            "record_sha256": None,
            "metadata_sha256": None,
            "direct_url_sha256": None,
            "files": 0,
            "bytes": 0,
            "files_sha256": None,
            "import_origin": origin,
        }
    version = distribution.version
    if not isinstance(version, str) or not version:
        raise RuntimeProbeError(
            f"proof distribution {distribution_name} has no version",
        )
    record_sha256 = _optional_metadata_sha256(distribution, "RECORD")
    if record_sha256 is None:
        raise RuntimeProbeError(
            f"proof distribution {distribution_name} has no RECORD",
        )
    files = [
        item
        for item in (distribution.files or ())
        if not _is_ignored_runtime_file(item)
    ]
    if not files:
        raise RuntimeProbeError(
            f"proof distribution {distribution_name} has no bound files",
        )
    if len(files) > PROOF_RUNTIME_MAX_FILES_PER_DISTRIBUTION:
        raise RuntimeProbeError(
            f"proof distribution {distribution_name} exceeds the file limit",
        )
    manifest: list[dict[str, Any]] = []
    total_bytes = 0
    for item in sorted(files, key=str):
        lexical = Path(distribution.locate_file(item))
        try:
            lexical_metadata = lexical.lstat()
        except OSError as exc:
            raise RuntimeProbeError(
                f"proof distribution {distribution_name} file is unavailable: "
                f"{item}: {exc}",
            ) from exc
        if not stat.S_ISREG(lexical_metadata.st_mode):
            raise RuntimeProbeError(
                f"proof distribution {distribution_name} contains a "
                f"non-regular file: {item}",
            )
        realpath = _require_runtime_file_beneath_prefix(lexical)
        identity = _regular_file_identity(
            realpath,
            require_executable=False,
        )
        total_bytes += int(identity["bytes"])
        if total_bytes > PROOF_RUNTIME_MAX_BYTES_PER_DISTRIBUTION:
            raise RuntimeProbeError(
                f"proof distribution {distribution_name} exceeds the byte limit",
            )
        declared_size = item.size
        if declared_size is not None and declared_size != identity["bytes"]:
            raise RuntimeProbeError(
                f"proof distribution {distribution_name} RECORD size mismatch: "
                f"{item}",
            )
        declared_hash = item.hash
        declared_hash_text: str | None = None
        if declared_hash is not None:
            if declared_hash.mode != "sha256":
                raise RuntimeProbeError(
                    f"proof distribution {distribution_name} uses unsupported "
                    f"RECORD hash {declared_hash.mode}: {item}",
                )
            actual_record_hash = base64.urlsafe_b64encode(
                bytes.fromhex(str(identity["sha256"])),
            ).rstrip(b"=").decode("ascii")
            if actual_record_hash != declared_hash.value:
                raise RuntimeProbeError(
                    f"proof distribution {distribution_name} RECORD hash "
                    f"mismatch: {item}",
                )
            declared_hash_text = (
                f"{declared_hash.mode}={declared_hash.value}"
            )
        manifest.append(
            {
                "path": str(item),
                "realpath": str(realpath),
                "sha256": identity["sha256"],
                "bytes": identity["bytes"],
                "mode": identity["mode"],
                "device": identity["device"],
                "inode": identity["inode"],
                "mtime_ns": identity["mtime_ns"],
                "ctime_ns": identity["ctime_ns"],
                "record_hash": declared_hash_text,
                "record_bytes": declared_size,
            }
        )
    return {
        "distribution": distribution_name,
        "import_name": import_name,
        "installed": True,
        "version": version,
        "record_sha256": record_sha256,
        "metadata_sha256": _optional_metadata_sha256(
            distribution,
            "METADATA",
        ),
        "direct_url_sha256": _optional_metadata_sha256(
            distribution,
            "direct_url.json",
        ),
        "files": len(manifest),
        "bytes": total_bytes,
        "files_sha256": hashlib.sha256(
            _canonical_json_bytes(manifest),
        ).hexdigest(),
        "import_origin": origin,
    }


def _python_identity() -> dict[str, Any]:
    return {
        "implementation": platform.python_implementation(),
        "version": platform.python_version(),
        "version_info": [
            sys.version_info.major,
            sys.version_info.minor,
            sys.version_info.micro,
            sys.version_info.releaselevel,
            sys.version_info.serial,
        ],
        "cache_tag": sys.implementation.cache_tag,
        "soabi": sysconfig.get_config_var("SOABI"),
        "platform": platform.platform(),
        "machine": platform.machine(),
    }


def _runtime_core() -> dict[str, Any]:
    artifacts = {
        name: _package_artifact_identity(
            name,
            PACKAGE_IMPORT_NAMES[name],
        )
        for name in SOLVER_RUNTIME_PACKAGES
    }
    total_files = sum(int(item["files"]) for item in artifacts.values())
    total_bytes = sum(int(item["bytes"]) for item in artifacts.values())
    if total_files > PROOF_RUNTIME_MAX_TOTAL_FILES:
        raise RuntimeProbeError(
            "proof runtime distributions exceed the total file limit",
        )
    if total_bytes > PROOF_RUNTIME_MAX_TOTAL_BYTES:
        raise RuntimeProbeError(
            "proof runtime distributions exceed the total byte limit",
        )
    versions = {
        name: _package_version(name)
        for name in SOLVER_RUNTIME_PACKAGES
    }
    if any(
        artifacts[name]["version"] != versions[name]
        for name in SOLVER_RUNTIME_PACKAGES
    ):
        raise RuntimeProbeError(
            "proof distribution versions changed during fingerprinting",
        )
    return {
        "schema_version": PROOF_RUNTIME_SCHEMA_VERSION,
        "python": _python_identity(),
        "packages": versions,
        "package_artifacts": artifacts,
    }


def _canonical_json_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    ).encode("ascii")


def resolve_python_executable(
    python_executable: str,
    *,
    cwd: Path | str,
) -> tuple[Path, Path]:
    """Resolve one explicit invocation path without changing venv semantics."""

    if (
        not isinstance(python_executable, str)
        or not python_executable
        or "\x00" in python_executable
    ):
        raise RuntimeProbeError(
            "configured proof interpreter must be a non-empty path",
        )
    if os.path.sep not in python_executable and (
        os.path.altsep is None or os.path.altsep not in python_executable
    ):
        raise RuntimeProbeError(
            "configured proof interpreter must be an explicit path, not a "
            "PATH-resolved command",
        )
    base = Path(cwd)
    configured = Path(python_executable)
    lexical = configured if configured.is_absolute() else base / configured
    lexical = Path(os.path.abspath(lexical))
    try:
        realpath = lexical.resolve(strict=True)
        metadata = realpath.lstat()
    except OSError as exc:
        raise RuntimeProbeError(
            f"cannot resolve configured proof interpreter "
            f"{python_executable}: {exc}",
        ) from exc
    if not stat.S_ISREG(metadata.st_mode) or not os.access(realpath, os.X_OK):
        raise RuntimeProbeError(
            f"configured proof interpreter is not an executable regular file: "
            f"{realpath}",
        )
    return lexical, realpath


def _stat_fields(metadata: os.stat_result) -> dict[str, int]:
    return {
        "mode": metadata.st_mode & 0o7777,
        "device": metadata.st_dev,
        "inode": metadata.st_ino,
        "mtime_ns": metadata.st_mtime_ns,
        "ctime_ns": metadata.st_ctime_ns,
    }


def _invocation_lstat_identity(path: Path) -> dict[str, Any]:
    try:
        metadata = path.lstat()
        if stat.S_ISLNK(metadata.st_mode):
            kind = "symlink"
            link_target: str | None = os.readlink(path)
        elif stat.S_ISREG(metadata.st_mode):
            kind = "regular"
            link_target = None
        else:
            raise RuntimeProbeError(
                f"proof interpreter invocation is not a file or symlink: {path}",
            )
    except RuntimeProbeError:
        raise
    except OSError as exc:
        raise RuntimeProbeError(
            f"cannot inspect proof interpreter invocation {path}: {exc}",
        ) from exc
    return {
        "kind": kind,
        "link_target": link_target,
        **_stat_fields(metadata),
    }


@lru_cache(maxsize=25_000)
def _hash_regular_file_for_stat(
    path_text: str,
    device: int,
    inode: int,
    mode: int,
    size: int,
    mtime_ns: int,
    ctime_ns: int,
) -> dict[str, int | str]:
    path = Path(path_text)
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0)
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = -1
    try:
        descriptor = os.open(path, flags)
        before = os.fstat(descriptor)
        expected = (
            device,
            inode,
            mode,
            size,
            mtime_ns,
            ctime_ns,
        )
        observed_before = (
            before.st_dev,
            before.st_ino,
            before.st_mode,
            before.st_size,
            before.st_mtime_ns,
            before.st_ctime_ns,
        )
        if not stat.S_ISREG(before.st_mode) or observed_before != expected:
            raise RuntimeProbeError(
                f"runtime dependency changed before it was hashed: {path}",
            )
        digest = hashlib.sha256()
        total = 0
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            total += len(chunk)
            digest.update(chunk)
        after = os.fstat(descriptor)
        stable_fields = (
            "st_dev",
            "st_ino",
            "st_mode",
            "st_size",
            "st_mtime_ns",
            "st_ctime_ns",
        )
        if (
            total != before.st_size
            or any(
                getattr(before, name) != getattr(after, name)
                for name in stable_fields
            )
        ):
            raise RuntimeProbeError(
                f"runtime dependency changed while it was hashed: {path}",
            )
        return {
            "sha256": digest.hexdigest(),
            "bytes": after.st_size,
            **_stat_fields(after),
        }
    except RuntimeProbeError:
        raise
    except OSError as exc:
        raise RuntimeProbeError(
            f"cannot hash runtime dependency {path}: {exc}",
        ) from exc
    finally:
        if descriptor >= 0:
            os.close(descriptor)


def _regular_file_identity(
    path: Path,
    *,
    require_executable: bool,
) -> dict[str, int | str]:
    try:
        before = path.lstat()
    except OSError as exc:
        raise RuntimeProbeError(
            f"cannot inspect runtime dependency {path}: {exc}",
        ) from exc
    if not stat.S_ISREG(before.st_mode):
        raise RuntimeProbeError(f"runtime dependency is not regular: {path}")
    if require_executable and not os.access(path, os.X_OK):
        raise RuntimeProbeError(f"proof interpreter is not executable: {path}")
    identity = _hash_regular_file_for_stat(
        str(path),
        before.st_dev,
        before.st_ino,
        before.st_mode,
        before.st_size,
        before.st_mtime_ns,
        before.st_ctime_ns,
    )
    try:
        after = path.lstat()
    except OSError as exc:
        raise RuntimeProbeError(
            f"cannot recheck runtime dependency {path}: {exc}",
        ) from exc
    if (
        before.st_dev,
        before.st_ino,
        before.st_mode,
        before.st_size,
        before.st_mtime_ns,
        before.st_ctime_ns,
    ) != (
        after.st_dev,
        after.st_ino,
        after.st_mode,
        after.st_size,
        after.st_mtime_ns,
        after.st_ctime_ns,
    ):
        raise RuntimeProbeError(
            f"runtime dependency changed during identity lookup: {path}",
        )
    return dict(identity)


def _pyvenv_identity(prefix: str) -> dict[str, Any] | None:
    path = Path(prefix) / "pyvenv.cfg"
    try:
        metadata = path.lstat()
    except FileNotFoundError:
        return None
    except OSError as exc:
        raise RuntimeProbeError(f"cannot inspect {path}: {exc}") from exc
    if not stat.S_ISREG(metadata.st_mode):
        raise RuntimeProbeError(f"pyvenv.cfg is not a regular file: {path}")
    return {
        "path": str(path),
        "file_identity": _regular_file_identity(
            path,
            require_executable=False,
        ),
    }


def _build_interpreter_identity(
    *,
    lexical: Path,
    realpath: Path,
    reported_sys_executable: str,
    prefix: str,
    base_prefix: str,
) -> dict[str, Any]:
    if any(
        not isinstance(value, str)
        or not value
        or not Path(value).is_absolute()
        for value in (reported_sys_executable, prefix, base_prefix)
    ):
        raise RuntimeProbeError(
            "proof runtime reported invalid absolute interpreter paths",
        )
    if os.path.realpath(reported_sys_executable) != str(realpath):
        raise RuntimeProbeError(
            "proof runtime ran a different interpreter than configured",
        )
    return {
        "schema_version": PROOF_INTERPRETER_SCHEMA_VERSION,
        "invocation_path": str(lexical),
        "realpath": str(realpath),
        "reported_sys_executable": reported_sys_executable,
        "prefix": prefix,
        "base_prefix": base_prefix,
        "invocation_lstat": _invocation_lstat_identity(lexical),
        "executable_file": _regular_file_identity(
            realpath,
            require_executable=True,
        ),
        "pyvenv_cfg": _pyvenv_identity(prefix),
    }


def proof_runtime_fingerprint() -> dict[str, Any]:
    """Return the full canonical identity for this proof process."""

    if not sys.executable or not Path(sys.executable).is_absolute():
        raise RuntimeProbeError(
            "current Python interpreter has no absolute sys.executable",
        )
    lexical, realpath = resolve_python_executable(
        sys.executable,
        cwd=Path(sys.executable).parent,
    )
    runtime = _runtime_core()
    runtime["interpreter"] = _build_interpreter_identity(
        lexical=lexical,
        realpath=realpath,
        reported_sys_executable=sys.executable,
        prefix=sys.prefix,
        base_prefix=sys.base_prefix,
    )
    return runtime


def _validate_file_identity(
    value: Any,
    *,
    label: str,
) -> dict[str, int | str]:
    if not isinstance(value, Mapping) or set(value) != _FILE_IDENTITY_KEYS:
        raise ValueError(f"{label} file identity is malformed")
    sha256 = value.get("sha256")
    if (
        not isinstance(sha256, str)
        or len(sha256) != 64
        or any(character not in "0123456789abcdef" for character in sha256)
    ):
        raise ValueError(f"{label} SHA-256 is malformed")
    normalized: dict[str, int | str] = {"sha256": sha256}
    for name in _FILE_IDENTITY_KEYS - {"sha256"}:
        item = value.get(name)
        if isinstance(item, bool) or not isinstance(item, int) or item < 0:
            raise ValueError(f"{label} {name} is malformed")
        normalized[name] = item
    return normalized


def _validate_interpreter_identity(value: Any) -> dict[str, Any]:
    if not isinstance(value, Mapping) or set(value) != _INTERPRETER_KEYS:
        raise ValueError("proof interpreter identity is malformed")
    if (
        isinstance(value.get("schema_version"), bool)
        or value.get("schema_version") != PROOF_INTERPRETER_SCHEMA_VERSION
    ):
        raise ValueError("proof interpreter identity schema is unsupported")
    paths: dict[str, str] = {}
    for name in (
        "invocation_path",
        "realpath",
        "reported_sys_executable",
        "prefix",
        "base_prefix",
    ):
        item = value.get(name)
        if (
            not isinstance(item, str)
            or not item
            or not Path(item).is_absolute()
        ):
            raise ValueError(f"proof interpreter {name} is malformed")
        paths[name] = item
    invocation = value.get("invocation_lstat")
    if (
        not isinstance(invocation, Mapping)
        or set(invocation) != _INVOCATION_LSTAT_KEYS
        or invocation.get("kind") not in {"regular", "symlink"}
    ):
        raise ValueError("proof interpreter invocation identity is malformed")
    link_target = invocation.get("link_target")
    if (
        invocation["kind"] == "regular"
        and link_target is not None
    ) or (
        invocation["kind"] == "symlink"
        and (not isinstance(link_target, str) or not link_target)
    ):
        raise ValueError("proof interpreter symlink identity is malformed")
    normalized_invocation: dict[str, Any] = {
        "kind": invocation["kind"],
        "link_target": link_target,
    }
    for name in _INVOCATION_LSTAT_KEYS - {"kind", "link_target"}:
        item = invocation.get(name)
        if isinstance(item, bool) or not isinstance(item, int) or item < 0:
            raise ValueError(
                f"proof interpreter invocation {name} is malformed",
            )
        normalized_invocation[name] = item
    pyvenv = value.get("pyvenv_cfg")
    normalized_pyvenv: dict[str, Any] | None
    if pyvenv is None:
        normalized_pyvenv = None
    elif (
        isinstance(pyvenv, Mapping)
        and set(pyvenv) == {"path", "file_identity"}
        and isinstance(pyvenv.get("path"), str)
        and Path(pyvenv["path"]).is_absolute()
    ):
        normalized_pyvenv = {
            "path": pyvenv["path"],
            "file_identity": _validate_file_identity(
                pyvenv["file_identity"],
                label="pyvenv.cfg",
            ),
        }
    else:
        raise ValueError("proof interpreter pyvenv.cfg identity is malformed")
    return {
        "schema_version": PROOF_INTERPRETER_SCHEMA_VERSION,
        **paths,
        "invocation_lstat": normalized_invocation,
        "executable_file": _validate_file_identity(
            value["executable_file"],
            label="proof interpreter",
        ),
        "pyvenv_cfg": normalized_pyvenv,
    }


def _validate_sha256_or_none(value: Any, *, label: str) -> str | None:
    if value is None:
        return None
    if (
        not isinstance(value, str)
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise ValueError(f"{label} SHA-256 is malformed")
    return value


def _validate_import_origin(
    value: Any,
    *,
    expected_name: str,
) -> dict[str, Any]:
    if not isinstance(value, Mapping) or set(value) != _IMPORT_ORIGIN_KEYS:
        raise ValueError(
            f"proof import {expected_name} origin identity is malformed",
        )
    if value.get("name") != expected_name:
        raise ValueError(f"proof import {expected_name} name is malformed")
    locations = value.get("search_locations")
    if (
        not isinstance(locations, list)
        or any(
            not isinstance(item, str) or not Path(item).is_absolute()
            for item in locations
        )
    ):
        raise ValueError(
            f"proof import {expected_name} search locations are malformed",
        )
    origin = value.get("origin")
    realpath = value.get("realpath")
    file_identity = value.get("file_identity")
    if origin in {None, "built-in", "frozen"}:
        if realpath is not None or file_identity is not None:
            raise ValueError(
                f"proof import {expected_name} special origin is malformed",
            )
        normalized_file = None
    else:
        if (
            not isinstance(origin, str)
            or not Path(origin).is_absolute()
            or not isinstance(realpath, str)
            or not Path(realpath).is_absolute()
        ):
            raise ValueError(
                f"proof import {expected_name} file origin is malformed",
            )
        normalized_file = _validate_file_identity(
            file_identity,
            label=f"proof import {expected_name}",
        )
    return {
        "name": expected_name,
        "origin": origin,
        "realpath": realpath,
        "file_identity": normalized_file,
        "search_locations": list(locations),
    }


def _validate_package_artifact(
    value: Any,
    *,
    distribution: str,
    expected_version: str | None,
) -> dict[str, Any]:
    if not isinstance(value, Mapping) or set(value) != _PACKAGE_ARTIFACT_KEYS:
        raise ValueError(
            f"proof distribution {distribution} identity is malformed",
        )
    import_name = PACKAGE_IMPORT_NAMES[distribution]
    if (
        value.get("distribution") != distribution
        or value.get("import_name") != import_name
        or not isinstance(value.get("installed"), bool)
        or value.get("version") != expected_version
    ):
        raise ValueError(
            f"proof distribution {distribution} binding is malformed",
        )
    installed = value["installed"]
    files = value.get("files")
    byte_count = value.get("bytes")
    if (
        isinstance(files, bool)
        or not isinstance(files, int)
        or files < 0
        or files > PROOF_RUNTIME_MAX_FILES_PER_DISTRIBUTION
        or isinstance(byte_count, bool)
        or not isinstance(byte_count, int)
        or byte_count < 0
        or byte_count > PROOF_RUNTIME_MAX_BYTES_PER_DISTRIBUTION
    ):
        raise ValueError(
            f"proof distribution {distribution} bounds are malformed",
        )
    hashes = {
        name: _validate_sha256_or_none(
            value.get(name),
            label=f"proof distribution {distribution} {name}",
        )
        for name in (
            "record_sha256",
            "metadata_sha256",
            "direct_url_sha256",
            "files_sha256",
        )
    }
    if installed:
        if (
            expected_version is None
            or files <= 0
            or hashes["record_sha256"] is None
            or hashes["metadata_sha256"] is None
            or hashes["files_sha256"] is None
        ):
            raise ValueError(
                f"proof distribution {distribution} installed identity "
                "is incomplete",
            )
    elif (
        expected_version is not None
        or files != 0
        or byte_count != 0
        or any(item is not None for item in hashes.values())
    ):
        raise ValueError(
            f"proof distribution {distribution} missing identity is malformed",
        )
    normalized_origin = _validate_import_origin(
        value.get("import_origin"),
        expected_name=import_name,
    )
    if installed and normalized_origin["file_identity"] is None:
        raise ValueError(
            f"proof distribution {distribution} import origin is unbound",
        )
    return {
        "distribution": distribution,
        "import_name": import_name,
        "installed": installed,
        "version": expected_version,
        **hashes,
        "files": files,
        "bytes": byte_count,
        "import_origin": normalized_origin,
    }


def _validate_runtime_core(runtime: Mapping[str, Any]) -> dict[str, Any]:
    if set(runtime) != _RUNTIME_CORE_KEYS:
        raise ValueError("proof runtime fingerprint has unexpected fields")
    if (
        isinstance(runtime.get("schema_version"), bool)
        or runtime.get("schema_version") != PROOF_RUNTIME_SCHEMA_VERSION
    ):
        raise ValueError("proof runtime fingerprint schema is unsupported")
    python = runtime.get("python")
    packages = runtime.get("packages")
    if not isinstance(python, Mapping) or set(python) != _PYTHON_KEYS:
        raise ValueError("proof runtime Python identity is malformed")
    for name in ("implementation", "version", "platform", "machine"):
        if not isinstance(python.get(name), str) or not python[name]:
            raise ValueError("proof runtime Python identity is malformed")
    version_info = python.get("version_info")
    if (
        not isinstance(version_info, list)
        or len(version_info) != 5
        or any(
            isinstance(item, bool)
            or not isinstance(item, (int, str))
            for item in version_info
        )
    ):
        raise ValueError("proof runtime Python version_info is malformed")
    for name in ("cache_tag", "soabi"):
        item = python.get(name)
        if item is not None and (not isinstance(item, str) or not item):
            raise ValueError(f"proof runtime Python {name} is malformed")
    if (
        not isinstance(packages, Mapping)
        or set(packages) != set(SOLVER_RUNTIME_PACKAGES)
    ):
        raise ValueError("proof runtime package identity is incomplete")
    normalized_packages: dict[str, str | None] = {}
    for name in SOLVER_RUNTIME_PACKAGES:
        item = packages.get(name)
        if item is not None and (not isinstance(item, str) or not item):
            raise ValueError(
                f"proof runtime package version for {name} is malformed",
            )
        normalized_packages[name] = item
    raw_artifacts = runtime.get("package_artifacts")
    if (
        not isinstance(raw_artifacts, Mapping)
        or set(raw_artifacts) != set(SOLVER_RUNTIME_PACKAGES)
    ):
        raise ValueError("proof runtime package artifact identity is incomplete")
    normalized_artifacts = {
        name: _validate_package_artifact(
            raw_artifacts[name],
            distribution=name,
            expected_version=normalized_packages[name],
        )
        for name in SOLVER_RUNTIME_PACKAGES
    }
    if (
        sum(item["files"] for item in normalized_artifacts.values())
        > PROOF_RUNTIME_MAX_TOTAL_FILES
        or sum(item["bytes"] for item in normalized_artifacts.values())
        > PROOF_RUNTIME_MAX_TOTAL_BYTES
    ):
        raise ValueError("proof runtime package artifact bounds are exceeded")
    return {
        "schema_version": PROOF_RUNTIME_SCHEMA_VERSION,
        "python": {
            name: (
                list(python[name])
                if name == "version_info"
                else python[name]
            )
            for name in _PYTHON_KEYS
        },
        "packages": normalized_packages,
        "package_artifacts": normalized_artifacts,
    }


def validate_proof_runtime_fingerprint(
    runtime: Mapping[str, Any],
) -> dict[str, Any]:
    """Validate and normalize a runtime without accepting legacy/extra data."""

    if set(runtime) != _RUNTIME_KEYS:
        raise ValueError("proof runtime fingerprint has unexpected fields")
    core = _validate_runtime_core(
        {name: runtime[name] for name in _RUNTIME_CORE_KEYS},
    )
    core["interpreter"] = _validate_interpreter_identity(
        runtime.get("interpreter"),
    )
    return core


def proof_runtime_fingerprints_equivalent(
    first: Mapping[str, Any],
    second: Mapping[str, Any],
) -> bool:
    """Compare validated runtimes while ignoring only executable ctime.

    Copying or restoring the same interpreter executable can change its inode
    change timestamp without changing the executable, its invocation, or any
    proof dependency.  That timestamp is therefore unsuitable as a cache
    invalidator.  Every other field remains part of the exact comparison,
    including ``invocation_lstat.ctime_ns`` and all package file identities.
    """

    normalized_first = validate_proof_runtime_fingerprint(first)
    normalized_second = validate_proof_runtime_fingerprint(second)
    normalized_first["interpreter"]["executable_file"]["ctime_ns"] = 0
    normalized_second["interpreter"]["executable_file"]["ctime_ns"] = 0
    return normalized_first == normalized_second


@dataclass(frozen=True)
class _ProbeProcessIdentity:
    pid: int
    pgid: int
    session_id: int
    uid: int
    starttime: int


def _read_probe_process_identity(pid: int) -> tuple[str, _ProbeProcessIdentity]:
    """Read the Linux process identity without trusting a reusable PID alone."""

    try:
        stat_text = (Path("/proc") / str(pid) / "stat").read_text()
        proc_metadata = (Path("/proc") / str(pid)).stat()
    except (OSError, UnicodeError) as exc:
        raise RuntimeProbeError(
            f"cannot establish proof runtime probe process identity: {exc}",
        ) from exc
    closing_parenthesis = stat_text.rfind(")")
    if closing_parenthesis < 0:
        raise RuntimeProbeError(
            "proof runtime probe process identity is malformed",
        )
    fields = stat_text[closing_parenthesis + 2 :].split()
    try:
        state = fields[0]
        pgid = int(fields[2])
        session_id = int(fields[3])
        starttime = int(fields[19])
    except (IndexError, TypeError, ValueError) as exc:
        raise RuntimeProbeError(
            "proof runtime probe process identity is malformed",
        ) from exc
    return state, _ProbeProcessIdentity(
        pid=pid,
        pgid=pgid,
        session_id=session_id,
        uid=int(proc_metadata.st_uid),
        starttime=starttime,
    )


def _validate_isolated_probe_identity(
    identity: _ProbeProcessIdentity,
    *,
    expected_pid: int,
) -> None:
    current_pgid = os.getpgrp()
    current_session = os.getsid(0)
    if (
        identity.pgid == current_pgid
        or identity.session_id == current_session
    ):
        raise RuntimeProbeError(
            "refusing to signal the current proof controller process group",
        )
    if (
        identity.pid != expected_pid
        or identity.pgid != expected_pid
        or identity.session_id != expected_pid
        or identity.pid <= 1
        or identity.uid != os.getuid()
        or identity.starttime <= 0
    ):
        raise RuntimeProbeError(
            "proof runtime probe did not establish a private process group",
        )


def _read_probe_handshake(
    descriptor: int,
    process: subprocess.Popen[Any],
    observed: _ProbeProcessIdentity,
    *,
    timeout: float,
) -> _ProbeProcessIdentity:
    os.set_blocking(descriptor, False)
    frame = bytearray()
    deadline = time.monotonic() + timeout
    while len(frame) < _PROBE_HANDSHAKE_STRUCT.size:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            _terminate_probe(process, observed)
            raise RuntimeProbeError(
                f"proof runtime probe handshake timed out after {timeout} seconds",
            )
        readable, _, _ = select.select(
            [descriptor],
            [],
            [],
            min(remaining, 0.1),
        )
        if not readable:
            continue
        try:
            chunk = os.read(
                descriptor,
                _PROBE_HANDSHAKE_STRUCT.size - len(frame),
            )
        except BlockingIOError:
            continue
        if not chunk:
            _terminate_probe(process, observed)
            raise RuntimeProbeError(
                "proof runtime probe returned an incomplete process handshake",
            )
        frame.extend(chunk)
    magic, pid, pgid, session_id = _PROBE_HANDSHAKE_STRUCT.unpack(frame)
    if (
        magic != _PROBE_HANDSHAKE_MAGIC
        or pid != observed.pid
        or pgid != observed.pgid
        or session_id != observed.session_id
    ):
        _terminate_probe(process, observed)
        raise RuntimeProbeError(
            "proof runtime probe process handshake identity is invalid",
        )
    _validate_isolated_probe_identity(observed, expected_pid=process.pid)
    return observed


def _probe_identity_is_pinned(identity: _ProbeProcessIdentity) -> bool:
    """The unreaped leader pins its PID, PGID, and SID against numeric reuse."""

    try:
        _state, current = _read_probe_process_identity(identity.pid)
    except RuntimeProbeError:
        return False
    return current == identity


def _live_probe_group_members(
    identity: _ProbeProcessIdentity,
) -> list[int]:
    """Return live members of exactly the handshaken session and group."""

    members: list[int] = []
    try:
        entries = list(Path("/proc").iterdir())
    except OSError as exc:
        raise RuntimeProbeError(
            f"cannot inspect proof runtime probe process group: {exc}",
        ) from exc
    for entry in entries:
        if not entry.name.isdigit():
            continue
        pid = int(entry.name)
        try:
            state, member = _read_probe_process_identity(pid)
        except RuntimeProbeError:
            continue
        if (
            member.pgid == identity.pgid
            and member.session_id == identity.session_id
        ):
            if member.uid != identity.uid or member.starttime < identity.starttime:
                raise RuntimeProbeError(
                    "proof runtime probe process group identity became unsafe",
                )
            if state != "Z":
                members.append(pid)
    return members


def _wait_for_probe_leader_zombie(
    identity: _ProbeProcessIdentity,
    *,
    deadline: float,
) -> bool:
    """Observe exit without waitpid so the leader keeps the PGID pinned."""

    while time.monotonic() < deadline:
        try:
            state, current = _read_probe_process_identity(identity.pid)
        except RuntimeProbeError:
            return False
        if current != identity:
            return False
        if state == "Z":
            return True
        time.sleep(0.01)
    return False


def _signal_probe_group(
    identity: _ProbeProcessIdentity,
    signal_number: int,
) -> None:
    _validate_isolated_probe_identity(identity, expected_pid=identity.pid)
    if not _probe_identity_is_pinned(identity):
        raise RuntimeProbeError(
            "refusing to signal an unpinned proof runtime probe process group",
        )
    # A live or zombie, unreaped leader pins the numeric PGID and SID through
    # this exact killpg call, so neither can be recycled between validation and
    # signalling.
    try:
        os.killpg(identity.pgid, signal_number)
    except ProcessLookupError:
        return
    except OSError as exc:
        raise RuntimeProbeError(
            f"cannot terminate proof runtime probe process group: {exc}",
        ) from exc


def _terminate_probe(
    process: subprocess.Popen[Any],
    identity: _ProbeProcessIdentity,
) -> None:
    """Terminate the whole verified probe group before reaping its leader."""

    _validate_isolated_probe_identity(identity, expected_pid=process.pid)
    if process.returncode is not None:
        # Reaping the leader releases the numeric PID/PGID pin.  At that point
        # killpg would risk signalling an unrelated, recycled group.
        if _live_probe_group_members(identity):
            raise RuntimeProbeError(
                "proof runtime probe leader was reaped before group cleanup",
            )
        return
    _signal_probe_group(identity, signal.SIGTERM)
    grace_deadline = (
        time.monotonic() + PROOF_RUNTIME_PROBE_TERMINATION_GRACE_SECONDS
    )
    members = _live_probe_group_members(identity)
    while members and time.monotonic() < grace_deadline:
        time.sleep(0.01)
        members = _live_probe_group_members(identity)
    if members:
        _signal_probe_group(identity, signal.SIGKILL)
        kill_deadline = time.monotonic() + 5.0
        while (
            _live_probe_group_members(identity)
            and time.monotonic() < kill_deadline
        ):
            time.sleep(0.01)
    try:
        process.wait(timeout=5)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise RuntimeProbeError(
            "proof runtime probe leader could not be reaped after termination",
        ) from exc
    if _live_probe_group_members(identity):
        raise RuntimeProbeError(
            "proof runtime probe process group survived forced termination",
        )


def _read_probe_frame(
    descriptor: int,
    process: subprocess.Popen[Any],
    identity: _ProbeProcessIdentity,
    *,
    timeout: float,
) -> tuple[bytes, bytes, bytes]:
    if process.stdout is None or process.stderr is None:
        raise RuntimeProbeError("proof runtime probe diagnostics are unavailable")
    stdout_fd = process.stdout.fileno()
    stderr_fd = process.stderr.fileno()
    open_descriptors = {
        descriptor: "protocol",
        stdout_fd: "stdout",
        stderr_fd: "stderr",
    }
    buffers = {
        "protocol": bytearray(),
        "stdout": bytearray(),
        "stderr": bytearray(),
    }
    for item in open_descriptors:
        os.set_blocking(item, False)
    deadline = time.monotonic() + timeout
    while open_descriptors:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            _terminate_probe(process, identity)
            raise RuntimeProbeError(
                f"proof runtime probe timed out after {timeout} seconds",
            )
        readable, _, _ = select.select(
            list(open_descriptors),
            [],
            [],
            min(remaining, 0.1),
        )
        if not readable:
            continue
        for readable_fd in readable:
            channel = open_descriptors[readable_fd]
            limit = (
                4 + PROOF_RUNTIME_PROBE_MAX_OUTPUT_BYTES
                if channel == "protocol"
                else PROOF_RUNTIME_PROBE_MAX_OUTPUT_BYTES
            )
            try:
                chunk = os.read(
                    readable_fd,
                    min(65536, limit + 1 - len(buffers[channel])),
                )
            except BlockingIOError:
                continue
            if not chunk:
                del open_descriptors[readable_fd]
                continue
            buffers[channel].extend(chunk)
            if len(buffers[channel]) > limit:
                _terminate_probe(process, identity)
                raise RuntimeProbeError(
                    f"proof runtime probe {channel} exceeded the limit",
                )
    if not _wait_for_probe_leader_zombie(identity, deadline=deadline):
        _terminate_probe(process, identity)
        raise RuntimeProbeError(
            f"proof runtime probe timed out after {timeout} seconds",
        )
    live_members = _live_probe_group_members(identity)
    if live_members:
        _terminate_probe(process, identity)
        raise RuntimeProbeError(
            "proof runtime probe left unexpected child processes",
        )
    try:
        returncode = process.wait(timeout=max(0.001, deadline - time.monotonic()))
    except subprocess.TimeoutExpired as exc:
        # This is not expected after observing the exact leader as a zombie,
        # but fail closed without ever signalling a potentially recycled PGID.
        raise RuntimeProbeError(
            f"proof runtime probe could not reap its exited leader: {exc}",
        ) from exc
    if returncode != 0:
        raise RuntimeProbeError(
            f"proof runtime probe exited with status {returncode}",
        )
    frame = buffers["protocol"]
    if buffers["stdout"] or buffers["stderr"]:
        raise RuntimeProbeError(
            "proof runtime probe emitted unexpected stdout or stderr",
        )
    if len(frame) < 4:
        raise RuntimeProbeError("proof runtime probe returned no complete frame")
    declared = struct.unpack(">I", frame[:4])[0]
    if declared > PROOF_RUNTIME_PROBE_MAX_OUTPUT_BYTES:
        raise RuntimeProbeError("proof runtime probe frame exceeded the limit")
    if len(frame) != 4 + declared:
        raise RuntimeProbeError(
            "proof runtime probe returned a truncated or trailing frame",
        )
    return (
        bytes(frame[4:]),
        bytes(buffers["stdout"]),
        bytes(buffers["stderr"]),
    )


def probe_python_runtime(
    python_executable: str,
    *,
    cwd: Path | str | None = None,
    timeout: float = PROOF_RUNTIME_PROBE_TIMEOUT_SECONDS,
) -> dict[str, Any]:
    """Probe and bind the exact interpreter used by proof subprocesses."""

    working_directory = Path.cwd() if cwd is None else Path(cwd)
    try:
        working_directory = working_directory.resolve(strict=True)
    except OSError as exc:
        raise RuntimeProbeError(
            f"proof runtime probe cwd is unavailable: {working_directory}: {exc}",
        ) from exc
    if (
        isinstance(timeout, bool)
        or not isinstance(timeout, (int, float))
        or not math.isfinite(float(timeout))
        or timeout <= 0
    ):
        raise RuntimeProbeError("proof runtime probe timeout must be finite and positive")
    lexical, realpath = resolve_python_executable(
        python_executable,
        cwd=working_directory,
    )
    invocation_before = _invocation_lstat_identity(lexical)
    executable_before = _regular_file_identity(
        realpath,
        require_executable=True,
    )
    nonce = secrets.token_hex(32)
    read_fd, write_fd = os.pipe()
    handshake_read_fd, handshake_write_fd = os.pipe()
    process: subprocess.Popen[Any] | None = None
    process_identity: _ProbeProcessIdentity | None = None
    try:
        process = subprocess.Popen(
            [
                str(lexical),
                "-I",
                "-c",
                _PROBE_BOOTSTRAP_PROGRAM,
                str(handshake_write_fd),
                str(write_fd),
                base64.b64encode(
                    _PROBE_PROGRAM.encode("utf-8"),
                ).decode("ascii"),
                PROOF_RUNTIME_PROBE_PROTOCOL,
                nonce,
                str(Path(__file__).resolve()),
                str(working_directory),
            ],
            cwd=working_directory,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            close_fds=True,
            pass_fds=(write_fd, handshake_write_fd),
            start_new_session=True,
        )
        _state, process_identity = _read_probe_process_identity(process.pid)
        _validate_isolated_probe_identity(
            process_identity,
            expected_pid=process.pid,
        )
    except OSError as exc:
        os.close(read_fd)
        os.close(write_fd)
        os.close(handshake_read_fd)
        os.close(handshake_write_fd)
        raise RuntimeProbeError(
            f"proof runtime probe could not start: {exc}",
        ) from exc
    except RuntimeProbeError:
        os.close(read_fd)
        os.close(write_fd)
        os.close(handshake_read_fd)
        os.close(handshake_write_fd)
        if process is not None:
            try:
                process.kill()
                process.wait(timeout=5)
            except (OSError, subprocess.TimeoutExpired):
                pass
        raise
    os.close(write_fd)
    os.close(handshake_write_fd)
    assert process_identity is not None
    try:
        process_identity = _read_probe_handshake(
            handshake_read_fd,
            process,
            process_identity,
            timeout=float(timeout),
        )
        encoded, _stdout, _stderr = _read_probe_frame(
            read_fd,
            process,
            process_identity,
            timeout=float(timeout),
        )
    finally:
        os.close(read_fd)
        os.close(handshake_read_fd)
        if process.returncode is None:
            _terminate_probe(process, process_identity)
        if process.stdout is not None:
            process.stdout.close()
        if process.stderr is not None:
            process.stderr.close()

    def object_without_duplicates(
        pairs: list[tuple[str, Any]],
    ) -> dict[str, Any]:
        value: dict[str, Any] = {}
        for key, item in pairs:
            if key in value:
                raise ValueError(f"duplicate key: {key}")
            value[key] = item
        return value

    try:
        response = json.loads(
            encoded.decode("ascii", errors="strict"),
            object_pairs_hook=object_without_duplicates,
            parse_constant=lambda value: (_ for _ in ()).throw(
                ValueError(f"invalid JSON constant: {value}")
            ),
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        raise RuntimeProbeError(
            f"proof runtime probe returned invalid canonical JSON: {exc}",
        ) from exc
    if (
        not isinstance(response, Mapping)
        or set(response) != _PROBE_RESPONSE_KEYS
        or response.get("protocol") != PROOF_RUNTIME_PROBE_PROTOCOL
        or response.get("nonce") != nonce
    ):
        raise RuntimeProbeError("proof runtime probe response identity is invalid")
    if _canonical_json_bytes(response) != encoded:
        raise RuntimeProbeError(
            "proof runtime probe response is not canonical JSON",
        )
    raw_core = response.get("runtime")
    if not isinstance(raw_core, Mapping):
        raise RuntimeProbeError("proof runtime probe fingerprint is malformed")
    try:
        runtime = _validate_runtime_core(raw_core)
    except ValueError as exc:
        raise RuntimeProbeError(
            f"proof runtime probe fingerprint is malformed: {exc}",
        ) from exc
    reported_executable = response.get("reported_sys_executable")
    reported_realpath = response.get("reported_realpath")
    prefix = response.get("reported_prefix")
    base_prefix = response.get("reported_base_prefix")
    if (
        not isinstance(reported_executable, str)
        or not isinstance(reported_realpath, str)
        or not isinstance(prefix, str)
        or not isinstance(base_prefix, str)
        or os.path.realpath(reported_realpath) != str(realpath)
    ):
        raise RuntimeProbeError(
            "proof runtime probe reported invalid interpreter paths",
        )
    runtime["interpreter"] = _build_interpreter_identity(
        lexical=lexical,
        realpath=realpath,
        reported_sys_executable=reported_executable,
        prefix=prefix,
        base_prefix=base_prefix,
    )
    try:
        runtime = validate_proof_runtime_fingerprint(runtime)
    except ValueError as exc:
        raise RuntimeProbeError(
            f"proof runtime probe provenance is malformed: {exc}",
        ) from exc

    final_lexical, final_realpath = resolve_python_executable(
        python_executable,
        cwd=working_directory,
    )
    if (
        final_lexical != lexical
        or final_realpath != realpath
        or _invocation_lstat_identity(final_lexical) != invocation_before
        or _regular_file_identity(
            final_realpath,
            require_executable=True,
        )
        != executable_before
        or runtime["interpreter"]["invocation_lstat"] != invocation_before
        or runtime["interpreter"]["executable_file"] != executable_before
    ):
        raise RuntimeProbeError(
            "configured proof interpreter changed during the runtime probe",
        )
    return {
        "runtime": runtime,
        # Kept as a top-level convenience for stage/release manifests. It is
        # exactly the same canonical object already embedded in runtime, so
        # worker-local caches cannot accidentally use a weaker identity.
        "interpreter": dict(runtime["interpreter"]),
    }


def known_answer_environment(
    runtime: Mapping[str, Any] | None = None,
) -> dict[str, str | None]:
    """Project the proof runtime onto the frozen known-answer schema."""

    raw_runtime = proof_runtime_fingerprint() if runtime is None else runtime
    normalized = validate_proof_runtime_fingerprint(raw_runtime)
    python = normalized["python"]
    packages = normalized["packages"]
    environment: dict[str, str | None] = {"python": python["version"]}
    for name in KNOWN_ANSWER_RUNTIME_PACKAGES:
        environment[name] = packages[name]
    return environment


__all__ = [
    "KNOWN_ANSWER_RUNTIME_PACKAGES",
    "PROOF_INTERPRETER_SCHEMA_VERSION",
    "PROOF_RUNTIME_ROOT_PACKAGES",
    "PROOF_RUNTIME_PROBE_PROTOCOL",
    "PROOF_RUNTIME_SCHEMA_VERSION",
    "PROOF_RUNTIME_TRANSITIVE_PACKAGES",
    "RuntimeProbeError",
    "SOLVER_RUNTIME_PACKAGES",
    "known_answer_environment",
    "probe_python_runtime",
    "proof_runtime_fingerprint",
    "proof_runtime_fingerprints_equivalent",
    "resolve_python_executable",
    "validate_proof_runtime_fingerprint",
]
