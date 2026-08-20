"""Portable, fail-closed exporter for typed DistQLDPC release evidence.

This is a standalone release type because the generic certificate dispatcher
does not yet register the typed DistQLDPC certificate.  Export performs strict
static replay only: it never invokes a solver or a subprocess.  Publication is
immutable and uses Linux ``renameat2(RENAME_NOREPLACE)`` after inode checks.
"""

from __future__ import annotations

import ctypes
import errno
import json
import os
import re
import stat
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping

from evaluation import distqldpc_release_replay_v4 as _replay
from evaluation import known_answer_integrity as _known_integrity
from evaluation import proof_runtime as _proof_runtime
from evaluation import release_gate as _release_gate


canonical_sha256 = _release_gate.canonical_sha256
SCHEMA_VERSION = 1
RELEASE_GATE = "qldpc-challenge-release-distqldpc-typed-portable-final"
RELEASE_TYPE = "qldpc-typed-distqldpc-standalone-portable-final-v1"
PIPELINE_REGISTRATION = "standalone-unregistered"
MANIFEST_FILENAME = "typed_distqldpc_release_manifest.json"
EXPORTER_SOURCE = "humanize/distqldpc_release_export_final5.py"
CLI_SOURCE = "scripts/export_distqldpc_release_final5.py"
REQUIRED_SOURCE_FILES = (
    EXPORTER_SOURCE,
    CLI_SOURCE,
    "evaluation/distqldpc_release_replay_v4.py",
    "evaluation/distqldpc_release_replay_v3.py",
    "evaluation/distqldpc_release_replay_v2.py",
    "scripts/check_known_answer_integrity.py",
    "evaluation/known_answer_integrity.py",
    "tests/verify_known_answer_gate.py",
)
_CRITICAL_MODULE_PATHS = {
    "exporter": EXPORTER_SOURCE,
    "replay_v4": "evaluation/distqldpc_release_replay_v4.py",
    "replay_v3": "evaluation/distqldpc_release_replay_v3.py",
    "replay_v2": "evaluation/distqldpc_release_replay_v2.py",
    "adapter": "evaluation/distqldpc_sector_adapter.py",
    "certificate": "evaluation/distqldpc_sector_certificate.py",
    "distance": "evaluation/distance_distqldpc.py",
    "sector": "evaluation/sector_certificate.py",
    "known_integrity": "evaluation/known_answer_integrity.py",
    "proof_runtime": "evaluation/proof_runtime.py",
    "release_gate": "evaluation/release_gate.py",
}
_RUN_ID_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,127}")
_CHECKS = {
    "certificate_passed": True,
    "stage3_physical_selfhash": True,
    "stage3_production_claim_import": True,
    "stage4_zero_solver_exact_rebuild": True,
    "zero_solver_static_replay": True,
    "certificate_bound_distqldpc_rerun": True,
    "official_exact_evidence_replay": True,
    "official_lower_evidence_replay": True,
    "typed_decision_count_1_of_1": True,
    "logical_partition_count_1_of_1": True,
    "anchored_upper_replay": True,
    "final_gate": True,
    "novelty": True,
    "fom_target": True,
    "known_answer_fast_semantic_replay": True,
    "known_answer_strict_rerun": True,
    "known_answer_runner_source_binding": True,
    "four_explicit_physical_sha256_pins": True,
    "loaded_project_modules_execute_from_bound_repo": True,
    "all_loaded_project_source_hashes": True,
    "portable_normalized_invocation": True,
    "known_answer_path_only_normalization": True,
}


class TypedDistQLDPCFinal5ReleaseError(RuntimeError):
    """A classified fail-closed release error."""

    def __init__(self, classification: str, message: str):
        super().__init__(message)
        self.classification = classification


def _fail(classification: str, message: str) -> None:
    raise TypedDistQLDPCFinal5ReleaseError(classification, message)


def _run_id(value: Any) -> str:
    if not isinstance(value, str) or _RUN_ID_RE.fullmatch(value) is None:
        _fail("RUN_ID_INVALID", "run_id has an unsafe or invalid form")
    return value


def _sha(value: Any, label: str) -> str:
    try:
        return _replay.require_sha256(value, label)
    except _replay.DistQLDPCReleaseReplayError as exc:
        _fail(exc.classification, str(exc))


def _physical_pins(
    *,
    expected_stage3_file_sha256: str,
    expected_certificate_file_sha256: str,
    expected_verification_file_sha256: str,
    expected_known_answer_integrity_file_sha256: str,
) -> dict[str, str]:
    return {
        "stage3_file_sha256": _sha(
            expected_stage3_file_sha256, "expected_stage3_file_sha256",
        ),
        "certificate_file_sha256": _sha(
            expected_certificate_file_sha256, "expected_certificate_file_sha256",
        ),
        "verification_file_sha256": _sha(
            expected_verification_file_sha256, "expected_verification_file_sha256",
        ),
        "known_answer_integrity_file_sha256": _sha(
            expected_known_answer_integrity_file_sha256,
            "expected_known_answer_integrity_file_sha256",
        ),
    }


def _read_json(path: Path | str, *, label: str) -> tuple[dict[str, Any], bytes]:
    try:
        return _replay.read_json_object(path, label=label)
    except _replay.DistQLDPCReleaseReplayError as exc:
        _fail(exc.classification, str(exc))


def _read_regular(path: Path | str, *, label: str) -> bytes:
    try:
        return _replay.read_regular(path, label=label)
    except _replay.DistQLDPCReleaseReplayError as exc:
        _fail(exc.classification, str(exc))


def _no_symlink_components(path: Path, *, allow_missing_leaf: bool = False) -> None:
    if not path.is_absolute():
        _fail("UNSAFE_PATH", f"path must be absolute: {path}")
    parts = path.parts
    cursor = Path(parts[0])
    for index, part in enumerate(parts[1:], start=1):
        cursor /= part
        try:
            metadata = cursor.lstat()
        except FileNotFoundError:
            if allow_missing_leaf and index == len(parts) - 1:
                return
            _fail("UNSAFE_PATH", f"path component is unavailable: {cursor}")
        except OSError as exc:
            _fail("UNSAFE_PATH", f"cannot inspect path component {cursor}: {exc}")
        if stat.S_ISLNK(metadata.st_mode):
            _fail("UNSAFE_PATH", f"path contains a symlink: {cursor}")


def _existing_file(path: Path | str, *, label: str) -> Path:
    candidate = Path(path)
    _no_symlink_components(candidate)
    try:
        resolved = candidate.resolve(strict=True)
        metadata = resolved.lstat()
    except OSError as exc:
        _fail("SOURCE_INVALID", f"{label} is unavailable: {exc}")
    if not stat.S_ISREG(metadata.st_mode) or stat.S_ISLNK(metadata.st_mode):
        _fail("SOURCE_INVALID", f"{label} is not a regular non-symlink file")
    return resolved


def _repo_file(repo: Path, relative: str, *, label: str) -> Path:
    candidate = repo / relative
    _no_symlink_components(candidate)
    try:
        resolved = candidate.resolve(strict=True)
        resolved.relative_to(repo)
    except (OSError, ValueError) as exc:
        _fail("SOURCE_INVALID", f"{label} is unavailable or escapes repo: {exc}")
    if resolved.suffix != ".py" or not resolved.is_file():
        _fail("SOURCE_INVALID", f"{label} is not one Python source file")
    return resolved


def _critical_modules() -> dict[str, Any]:
    v2 = _replay._v2
    return {
        "exporter": sys.modules[__name__],
        "replay_v4": _replay,
        "replay_v3": _replay._v3,
        "replay_v2": v2,
        "adapter": v2._adapter,
        "certificate": v2._certificate,
        "distance": v2._distance,
        "sector": v2._sector,
        "known_integrity": _known_integrity,
        "proof_runtime": _proof_runtime,
        "release_gate": _release_gate,
    }


def _bound_repo(repo_dir: Path | str) -> Path:
    candidate = Path(repo_dir)
    _no_symlink_components(candidate)
    try:
        repo = candidate.resolve(strict=True)
        metadata = repo.lstat()
    except OSError as exc:
        _fail("SOURCE_INVALID", f"repository is unavailable: {exc}")
    if not stat.S_ISDIR(metadata.st_mode):
        _fail("SOURCE_INVALID", "repository is not a directory")
    modules = _critical_modules()
    for name, relative in _CRITICAL_MODULE_PATHS.items():
        raw = getattr(modules[name], "__file__", None)
        if not isinstance(raw, str):
            _fail("SOURCE_INVALID", f"critical module {name} lacks __file__")
        actual = _existing_file(raw, label=f"loaded critical source {name}")
        expected = _repo_file(repo, relative, label=f"critical source {name}")
        if actual != expected:
            _fail(
                "SOURCE_REPOSITORY_MISMATCH",
                f"critical module {name} was not executed from bound repo",
            )
    return repo


def _source_hashes(repo_dir: Path | str) -> dict[str, Any]:
    """Hash all loaded project Python plus explicit non-imported producers."""

    repo = _bound_repo(repo_dir)
    paths: set[Path] = set()
    for relative in REQUIRED_SOURCE_FILES:
        paths.add(_repo_file(repo, relative, label=f"required source {relative}"))
    for name, module in tuple(sys.modules.items()):
        project_named = bool(
            name in {"evaluation", "humanize"}
            or name.startswith("evaluation.")
            or name.startswith("humanize.")
        )
        raw = getattr(module, "__file__", None)
        if raw is None:
            if project_named:
                spec = getattr(module, "__spec__", None)
                if spec is None or spec.submodule_search_locations is None:
                    _fail("SOURCE_INVALID", f"project module {name} lacks source")
            continue
        if not isinstance(raw, str):
            if project_named:
                _fail("SOURCE_INVALID", f"project module {name} has invalid __file__")
            continue
        try:
            path = _existing_file(raw, label=f"loaded module {name}")
            relative = path.relative_to(repo)
        except (TypedDistQLDPCFinal5ReleaseError, ValueError):
            if project_named:
                _fail(
                    "SOURCE_REPOSITORY_MISMATCH",
                    f"loaded project module {name} is outside bound repo",
                )
            continue
        if path.suffix == ".py":
            paths.add(path)
        elif project_named:
            _fail("SOURCE_INVALID", f"project module {name} is not loaded from .py")
    files: dict[str, str] = {}
    for path in sorted(paths):
        relative = path.relative_to(repo).as_posix()
        raw = _read_regular(path, label=f"loaded source {relative}")
        files[relative] = _replay.sha256_bytes(raw)
    if any(relative not in files for relative in REQUIRED_SOURCE_FILES):
        _fail("SOURCE_INVALID", "release source set is incomplete")
    return {
        "schema_version": 1,
        "mode": "portable-relative-all-loaded-project-plus-entrypoints",
        "files": files,
        "fingerprint_sha256": canonical_sha256(files),
    }


def _input_paths(
    *,
    repo_dir: Path | str,
    stage3_artifact: Path | str,
    certificate_path: Path | str,
    verification_path: Path | str,
    known_answer_artifact: Path | str,
    known_answer_trust: Path | str,
    known_answer_integrity: Path | str,
) -> dict[str, Path]:
    return {
        "repo_dir": _bound_repo(repo_dir),
        "stage3_artifact": _existing_file(stage3_artifact, label="source Stage-3"),
        "certificate": _existing_file(certificate_path, label="Stage-4 certificate"),
        "verification": _existing_file(verification_path, label="verification sidecar"),
        "known_answer_artifact": _existing_file(
            known_answer_artifact, label="known-answer artifact",
        ),
        "known_answer_trust": _existing_file(
            known_answer_trust, label="known-answer trust",
        ),
        "known_answer_integrity": _existing_file(
            known_answer_integrity, label="strict known-answer sidecar",
        ),
    }


def _output_path(value: Path | str) -> tuple[Path, tuple[int, int]]:
    output = Path(value)
    _no_symlink_components(output, allow_missing_leaf=True)
    if output.name in {"", ".", ".."}:
        _fail("OUTPUT_INVALID", "output leaf is invalid")
    try:
        parent = output.parent.resolve(strict=True)
        metadata = parent.lstat()
        existing = output.exists() or output.is_symlink()
    except OSError as exc:
        _fail("OUTPUT_INVALID", f"output path is unavailable: {exc}")
    if not stat.S_ISDIR(metadata.st_mode) or existing:
        _fail("OUTPUT_EXISTS", f"immutable destination exists or parent is invalid: {output}")
    return parent / output.name, (metadata.st_dev, metadata.st_ino)


def _provenance_raw(paths: Mapping[str, Path]) -> dict[str, bytes]:
    labels = {
        "stage3_artifact": "source Stage-3",
        "certificate": "Stage-4 certificate",
        "verification": "verification sidecar",
        "known_answer_artifact": "known-answer artifact",
        "known_answer_trust": "known-answer trust",
        "known_answer_integrity": "strict known-answer sidecar",
    }
    return {
        name: _read_regular(paths[name], label=label)
        for name, label in labels.items()
    }


def _replay_inputs(
    certificate: Mapping[str, Any],
    verification: Mapping[str, Any],
    *,
    paths: Mapping[str, Path],
    expected_candidate_digest: str,
    expected_certificate_sha256: str,
    expected_stage3_artifact_sha256: str,
    before: Mapping[str, bytes],
    phase: str,
    expected_runner_sha256: str | None,
) -> dict[str, Any]:
    try:
        pair = _replay.validate_release_inputs(
            certificate,
            verification,
            repo_dir=paths["repo_dir"],
            stage3_artifact=paths["stage3_artifact"],
            known_answer_artifact=paths["known_answer_artifact"],
            known_answer_trust=paths["known_answer_trust"],
            known_answer_integrity=paths["known_answer_integrity"],
            expected_candidate_digest=expected_candidate_digest,
            expected_certificate_sha256=expected_certificate_sha256,
            expected_stage3_artifact_sha256=expected_stage3_artifact_sha256,
            phase=phase,
            expected_runner_sha256=expected_runner_sha256,
        )
    except _replay.DistQLDPCReleaseReplayError as exc:
        _fail(exc.classification, str(exc))
    try:
        fast = _known_integrity.check_fast(
            paths["known_answer_artifact"], paths["known_answer_trust"],
        )
    except (OSError, TypeError, ValueError, json.JSONDecodeError) as exc:
        _fail("KNOWN_ANSWER_INVALID", f"official fast replay raised: {exc}")
    after = _provenance_raw(paths)
    if dict(before) != after:
        _fail("SOURCE_CHANGED", "a provenance input changed during replay")
    known = dict(pair["known_answer_integrity"])
    sidecar = known.get("sidecar")
    command = known.get("rerun_command")
    runner = known.get("runner_source")
    if (
        not isinstance(sidecar, Mapping)
        or not isinstance(command, list)
        or not isinstance(runner, Mapping)
    ):
        _fail("KNOWN_ANSWER_INVALID", "strict provenance is missing")
    try:
        logical_timeout = int(command[7])
        total_timeout = int(command[9])
    except (IndexError, TypeError, ValueError) as exc:
        _fail("KNOWN_ANSWER_INVALID", f"strict timeout command is invalid: {exc}")
    expected_wall = 3 * total_timeout + max(60, (total_timeout + 19) // 20)
    if (
        logical_timeout <= 0
        or total_timeout <= 0
        or str(logical_timeout) != command[7]
        or str(total_timeout) != command[9]
        or fast.get("passed") is not True
        or fast.get("mode") != "fast"
        or fast.get("failures") != []
        or fast.get("artifact_sha256") != known.get("artifact_sha256")
        or fast.get("semantic_sha256") != known.get("semantic_sha256")
        or fast.get("environment") != known.get("environment")
        or sidecar.get("passed") is not True
        or sidecar.get("mode") != "strict"
        or sidecar.get("failures") != []
        or sidecar.get("semantic_sha256") != sidecar.get("rerun_semantic_sha256")
        or sidecar.get("rerun_wall_timeout_s") != expected_wall
        or not isinstance(sidecar.get("rerun_output_tail"), str)
        or runner.get("path") != _replay.KNOWN_ANSWER_RUNNER
        or _replay.sha256_bytes(before["stage3_artifact"])
        != pair["stage3"]["file_sha256"]
        or _replay.sha256_bytes(before["known_answer_integrity"])
        != known["sidecar_file_sha256"]
        or _replay.sha256_bytes(before["known_answer_artifact"])
        != known["artifact_sha256"]
        or _replay.sha256_bytes(before["known_answer_trust"])
        != known["trust_file_sha256"]
    ):
        _fail("KNOWN_ANSWER_INVALID", "fast/strict semantic or runtime replay differs")
    known["fast_replay"] = dict(fast)
    known["rerun_wall_timeout_s"] = expected_wall
    result = dict(pair)
    result["known_answer_integrity"] = known
    return result


def _parse_export_argv(
    argv: Any,
    *,
    repo: Path,
    paths: Mapping[str, Path],
    output: Path,
    run_id: str,
    expected_candidate_digest: str,
    expected_certificate_sha256: str,
    expected_stage3_artifact_sha256: str,
    physical: Mapping[str, str],
) -> None:
    if not isinstance(argv, list) or any(not isinstance(item, str) for item in argv):
        _fail("INVOCATION_INVALID", "release argv is malformed")
    if len(argv) < 2 or argv[1] != "export":
        _fail("INVOCATION_INVALID", "release argv must select export")
    try:
        actual_cli = _existing_file(argv[0], label="release CLI")
        expected_cli = _repo_file(repo, CLI_SOURCE, label="release CLI source")
    except TypedDistQLDPCFinal5ReleaseError:
        raise
    if actual_cli != expected_cli:
        _fail("INVOCATION_INVALID", "argv[0] is not the bound release CLI")
    expected = {
        "--repo-dir": str(repo),
        "--stage3-artifact": str(paths["stage3_artifact"]),
        "--certificate": str(paths["certificate"]),
        "--verification": str(paths["verification"]),
        "--output-dir": str(output),
        "--known-answer-artifact": str(paths["known_answer_artifact"]),
        "--known-answer-trust": str(paths["known_answer_trust"]),
        "--known-answer-integrity": str(paths["known_answer_integrity"]),
        "--run-id": run_id,
        "--expected-candidate-digest": expected_candidate_digest,
        "--expected-certificate-sha256": expected_certificate_sha256,
        "--expected-stage3-artifact-sha256": expected_stage3_artifact_sha256,
        "--expected-stage3-file-sha256": physical["stage3_file_sha256"],
        "--expected-certificate-file-sha256": physical["certificate_file_sha256"],
        "--expected-verification-file-sha256": physical["verification_file_sha256"],
        "--expected-known-answer-integrity-file-sha256": (
            physical["known_answer_integrity_file_sha256"]
        ),
    }
    seen: dict[str, str] = {}
    index = 2
    while index < len(argv):
        token = argv[index]
        if not token.startswith("--"):
            _fail("INVOCATION_INVALID", f"unexpected positional argument: {token}")
        if "=" in token:
            flag, value = token.split("=", 1)
            index += 1
        else:
            flag = token
            if index + 1 >= len(argv):
                _fail("INVOCATION_INVALID", f"missing value for {flag}")
            value = argv[index + 1]
            index += 2
        if flag not in expected or flag in seen or not value:
            _fail("INVOCATION_INVALID", f"unknown, duplicate, or empty flag: {flag}")
        seen[flag] = value
    if seen != expected:
        _fail("INVOCATION_INVALID", "export flags are incomplete or differ from inputs")


def _normalized_invocation(
    *,
    run_id: str,
    expected_candidate_digest: str,
    expected_certificate_sha256: str,
    expected_stage3_artifact_sha256: str,
    physical: Mapping[str, str],
    pair: Mapping[str, Any],
) -> dict[str, Any]:
    known = pair["known_answer_integrity"]
    value = {
        "schema_version": 1,
        "mode": "portable-content-role-normalization",
        "cli_source": CLI_SOURCE,
        "command": "export",
        "path_roles": {
            "repo_dir": "BOUND_REPOSITORY",
            "stage3_artifact": "EXTERNAL_STAGE3_BY_FILE_SHA256",
            "certificate": "EXTERNAL_CERTIFICATE_BY_FILE_SHA256",
            "verification": "EXTERNAL_VERIFICATION_BY_FILE_SHA256",
            "output_dir": "RELEASE_ROOT",
            "known_answer_artifact": "KNOWN_ANSWER_BY_ARTIFACT_SHA256",
            "known_answer_trust": "KNOWN_ANSWER_TRUST_BY_FILE_SHA256",
            "known_answer_integrity": "STRICT_INTEGRITY_BY_FILE_SHA256",
        },
        "run_id": run_id,
        "expected_bindings": {
            "candidate_digest": expected_candidate_digest,
            "certificate_sha256": expected_certificate_sha256,
            "stage3_artifact_sha256": expected_stage3_artifact_sha256,
        },
        "expected_physical_bindings": dict(physical),
        "known_answer_artifact_sha256": known["artifact_sha256"],
        "known_answer_trust_file_sha256": known["trust_file_sha256"],
        "known_answer_runner_source_sha256": known["runner_source"]["sha256"],
    }
    value["normalized_sha256"] = canonical_sha256(
        value, omit="normalized_sha256",
    )
    return value


def _json_bytes(value: Mapping[str, Any]) -> bytes:
    try:
        return (
            json.dumps(
                dict(value), indent=2, sort_keys=True, ensure_ascii=False,
                allow_nan=False,
            )
            + "\n"
        ).encode("utf-8")
    except (TypeError, ValueError) as exc:
        _fail("MANIFEST_INVALID", f"release JSON is not strict: {exc}")


def _write_new(path: Path, raw: bytes) -> None:
    flags = (
        os.O_WRONLY | os.O_CREAT | os.O_EXCL
        | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    )
    descriptor = -1
    try:
        descriptor = os.open(path, flags, 0o600)
        with os.fdopen(descriptor, "wb") as stream:
            descriptor = -1
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
    except OSError as exc:
        _fail("OUTPUT_INVALID", f"cannot create immutable file {path}: {exc}")
    finally:
        if descriptor >= 0:
            os.close(descriptor)


def _fsync_dir(path: Path) -> None:
    flags = (
        os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
        | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    )
    try:
        descriptor = os.open(path, flags)
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
    except OSError as exc:
        _fail("OUTPUT_INVALID", f"cannot fsync directory {path}: {exc}")


def _inode(metadata: os.stat_result) -> tuple[int, int]:
    return metadata.st_dev, metadata.st_ino


def _rename_noreplace(
    source: Path,
    destination: Path,
    *,
    expected_parent_identity: tuple[int, int],
    expected_source_identity: tuple[int, int],
) -> bool:
    """Atomically rename only while the owned source/parent inodes remain."""

    flags = (
        os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
        | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    )
    parent_fd = source_fd = -1
    try:
        if source.parent != destination.parent:
            _fail("UNSAFE_PATH", "staging and destination must share one parent")
        parent_fd = os.open(source.parent, flags)
        source_fd = os.open(source.name, flags, dir_fd=parent_fd)
        if (
            _inode(os.fstat(parent_fd)) != expected_parent_identity
            or _inode(os.fstat(source_fd)) != expected_source_identity
        ):
            _fail("UNSAFE_PATH", "staging/parent identity changed before publish")
        current = os.stat(source.name, dir_fd=parent_fd, follow_symlinks=False)
        if _inode(current) != expected_source_identity or not stat.S_ISDIR(current.st_mode):
            _fail("UNSAFE_PATH", "staging name no longer identifies owned directory")
        libc = ctypes.CDLL(None, use_errno=True)
        renameat2 = getattr(libc, "renameat2", None)
        if renameat2 is None:
            _fail(
                "ATOMIC_NOREPLACE_UNAVAILABLE",
                "renameat2 is required for immutable publication",
            )
        renameat2.argtypes = [
            ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p,
            ctypes.c_uint,
        ]
        renameat2.restype = ctypes.c_int
        result = renameat2(
            parent_fd, os.fsencode(source.name), parent_fd,
            os.fsencode(destination.name), 1,
        )
        if result == 0:
            return True
        failure_errno = ctypes.get_errno()
        if failure_errno in {errno.EEXIST, errno.ENOTEMPTY}:
            return False
        if failure_errno in {errno.ENOSYS, errno.EINVAL}:
            _fail(
                "ATOMIC_NOREPLACE_UNAVAILABLE",
                "kernel does not support atomic no-replace publication",
            )
        _fail(
            "DESTINATION_CONFLICT",
            f"atomic publication failed: {os.strerror(failure_errno)}",
        )
    except OSError as exc:
        _fail("UNSAFE_PATH", f"cannot recheck publication identity: {exc}")
    finally:
        for descriptor in (source_fd, parent_fd):
            if descriptor >= 0:
                os.close(descriptor)


def _safe_cleanup(
    *,
    staging: Path,
    parent: Path,
    parent_identity: tuple[int, int],
    staging_identity: tuple[int, int],
    directories: Mapping[str, tuple[tuple[int, int], tuple[str, ...]]],
) -> None:
    flags = (
        os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
        | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    )
    parent_fd = staging_fd = child_fd = -1
    try:
        parent_fd = os.open(parent, flags)
        if _inode(os.fstat(parent_fd)) != parent_identity:
            return
        staging_fd = os.open(staging.name, flags, dir_fd=parent_fd)
        if _inode(os.fstat(staging_fd)) != staging_identity:
            return
        for directory, (identity, filenames) in directories.items():
            try:
                child_fd = os.open(directory, flags, dir_fd=staging_fd)
            except OSError:
                child_fd = -1
                continue
            if _inode(os.fstat(child_fd)) != identity:
                os.close(child_fd)
                child_fd = -1
                continue
            for filename in filenames:
                try:
                    os.unlink(filename, dir_fd=child_fd)
                except OSError:
                    pass
            os.close(child_fd)
            child_fd = -1
            try:
                current = os.stat(directory, dir_fd=staging_fd, follow_symlinks=False)
                if _inode(current) == identity:
                    os.rmdir(directory, dir_fd=staging_fd)
            except OSError:
                pass
        try:
            os.unlink(MANIFEST_FILENAME, dir_fd=staging_fd)
        except OSError:
            pass
        try:
            current = os.stat(staging.name, dir_fd=parent_fd, follow_symlinks=False)
            if _inode(current) == staging_identity:
                os.close(staging_fd)
                staging_fd = -1
                os.rmdir(staging.name, dir_fd=parent_fd)
        except OSError:
            pass
    except OSError:
        pass
    finally:
        for descriptor in (child_fd, staging_fd, parent_fd):
            if descriptor >= 0:
                os.close(descriptor)


def _release_file(root: Path, value: Any, *, label: str) -> Path:
    if not isinstance(value, str) or not value:
        _fail("MANIFEST_INVALID", f"{label} path is invalid")
    relative = Path(value)
    if relative.is_absolute() or ".." in relative.parts:
        _fail("MANIFEST_INVALID", f"{label} path is unsafe")
    cursor = root
    for part in relative.parts:
        cursor /= part
        try:
            metadata = cursor.lstat()
        except OSError as exc:
            _fail("MANIFEST_INVALID", f"{label} path is unavailable: {exc}")
        if stat.S_ISLNK(metadata.st_mode):
            _fail("MANIFEST_INVALID", f"{label} path contains a symlink")
    try:
        cursor.resolve(strict=True).relative_to(root.resolve(strict=True))
    except (OSError, ValueError) as exc:
        _fail("MANIFEST_INVALID", f"{label} escapes release root: {exc}")
    return cursor


def _snapshot_bindings(pair: Mapping[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    known = dict(pair["known_answer_integrity"])
    known["sidecar_file"] = f"integrity/{known['sidecar_file_sha256']}.json"
    stage3 = dict(pair["stage3"])
    stage3["file"] = f"stage3/{stage3['file_sha256']}.json"
    return known, stage3


def _build_manifest(
    *,
    run_id: str,
    generated_at: str,
    certificate: Mapping[str, Any],
    certificate_raw: bytes,
    verification: Mapping[str, Any],
    verification_raw: bytes,
    pair: Mapping[str, Any],
    sources: Mapping[str, Any],
    expected_candidate_digest: str,
    expected_certificate_sha256: str,
    expected_stage3_artifact_sha256: str,
    physical: Mapping[str, str],
) -> dict[str, Any]:
    known, stage3 = _snapshot_bindings(pair)
    context = pair["context"]
    upper = context["proof"]["upper_witness"]
    certificate_sha = certificate["certificate_sha256"]
    verification_payload_sha = canonical_sha256(verification)
    invocation = _normalized_invocation(
        run_id=run_id,
        expected_candidate_digest=expected_candidate_digest,
        expected_certificate_sha256=expected_certificate_sha256,
        expected_stage3_artifact_sha256=expected_stage3_artifact_sha256,
        physical=physical,
        pair=pair,
    )
    entry = {
        "file": f"certificates/{certificate_sha}.json",
        "certificate_sha256": certificate_sha,
        "certificate_payload_sha256": canonical_sha256(certificate),
        "certificate_file_sha256": _replay.sha256_bytes(certificate_raw),
        "verification_file": f"verifications/{verification_payload_sha}.json",
        "verification_payload_sha256": verification_payload_sha,
        "verification_file_sha256": _replay.sha256_bytes(verification_raw),
        "candidate": {
            "canonical_digest": context["claim"]["canonical_digest"],
            "n": context["claim"]["n"],
            "k": context["claim"]["k"],
            "d": context["distance"],
            "required_distance": context["required_distance"],
            "fom": context["fom"],
        },
        "anchored_upper": {
            "sector": upper["sector"],
            "objective": upper["solver_evidence"]["objective"],
            "anchor_indices": list(context["anchors"]),
        },
        "verification": {
            "passed": True,
            "replay_complete": True,
            "lower_bound_backend": "distqldpc",
            "distqldpc_rerun": True,
            "decisions_verified": 1,
            "decisions_total": 1,
            "logical_partitions_verified": 1,
            "logical_partitions_total": 1,
            "fresh_checkpoint_identity_sha256": (
                pair["fresh"]["checkpoint_identity_sha256"]
            ),
            "fresh_solver_evidence_sha256": pair["fresh"]["solver_evidence_sha256"],
        },
    }
    manifest: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "gate": RELEASE_GATE,
        "release_type": RELEASE_TYPE,
        "generic_pipeline_registration": {
            "registered": False,
            "mode": PIPELINE_REGISTRATION,
            "reason": (
                "typed DistQLDPC is not registered in the generic five-stage "
                "certificate dispatch/release schema"
            ),
        },
        "run_id": run_id,
        "generated_at": generated_at,
        "passed": True,
        "scientific_checks": dict(_CHECKS),
        "known_answer_integrity": known,
        "source_stage3": stage3,
        "source_evaluations": 1,
        "source_total": 1,
        "accepted": 1,
        "rejected": 0,
        "incomplete": 0,
        "eligible_candidates": 1,
        "stage5_artifact_sha256": _replay.sha256_bytes(verification_raw),
        "expected_bindings": {
            "candidate_digest": expected_candidate_digest,
            "certificate_sha256": expected_certificate_sha256,
            "stage3_artifact_sha256": expected_stage3_artifact_sha256,
        },
        "expected_physical_bindings": dict(physical),
        "normalized_invocation": invocation,
        "nonsemantic_path_normalization": dict(pair["path_normalization"]),
        "source_pipeline": {
            "schema_version": 1,
            "gate": "qldpc-typed-distqldpc-portable-final-release-source",
            "registration": PIPELINE_REGISTRATION,
            "stage3": stage3,
            "stage4": {
                "certificate_type": certificate["certificate_type"],
                "certificate_sha256": certificate_sha,
                "certificate_payload_sha256": canonical_sha256(certificate),
                "certificate_file_sha256": _replay.sha256_bytes(certificate_raw),
            },
            "stage5": {
                "kind": "typed-distqldpc-final-verification-sidecar",
                "verification_file_sha256": _replay.sha256_bytes(verification_raw),
                "verification_payload_sha256": verification_payload_sha,
                "known_answer_integrity_file_sha256": known["sidecar_file_sha256"],
                "proof_runtime": dict(pair["proof_runtime"]),
            },
            "loaded_project_source": dict(sources),
            "nonsemantic_path_normalization": dict(pair["path_normalization"]),
        },
        "release_seal": {
            "schema_version": 1,
            "mode": "portable-path-normalized-four-physical-sha256-final-v1",
            "exporter_source": EXPORTER_SOURCE,
            "cli_source": CLI_SOURCE,
            "raw_invocation_stored": False,
            "solver_invocations": 0,
        },
        "certificates": [entry],
    }
    manifest["manifest_sha256"] = canonical_sha256(
        manifest, omit="manifest_sha256",
    )
    return manifest


def _failure(expected_run_id: Any, exc: BaseException) -> dict[str, Any]:
    return {
        "passed": False,
        "run_id": expected_run_id,
        "certificates": 0,
        "verified": 0,
        "classification": getattr(exc, "classification", "MANIFEST_INVALID"),
        "failures": [str(exc)],
    }


def validate_typed_distqldpc_release(
    manifest_path: Path | str,
    *,
    repo_dir: Path | str,
    stage3_artifact: Path | str,
    certificate_path: Path | str,
    verification_path: Path | str,
    known_answer_artifact: Path | str,
    known_answer_trust: Path | str,
    known_answer_integrity: Path | str,
    expected_run_id: str,
    expected_candidate_digest: str,
    expected_certificate_sha256: str,
    expected_stage3_artifact_sha256: str,
    expected_stage3_file_sha256: str,
    expected_certificate_file_sha256: str,
    expected_verification_file_sha256: str,
    expected_known_answer_integrity_file_sha256: str,
) -> dict[str, Any]:
    """Validate and completely rebuild a release without writes or solver calls."""

    try:
        run_id = _run_id(expected_run_id)
        paths = _input_paths(
            repo_dir=repo_dir,
            stage3_artifact=stage3_artifact,
            certificate_path=certificate_path,
            verification_path=verification_path,
            known_answer_artifact=known_answer_artifact,
            known_answer_trust=known_answer_trust,
            known_answer_integrity=known_answer_integrity,
        )
        physical = _physical_pins(
            expected_stage3_file_sha256=expected_stage3_file_sha256,
            expected_certificate_file_sha256=expected_certificate_file_sha256,
            expected_verification_file_sha256=expected_verification_file_sha256,
            expected_known_answer_integrity_file_sha256=(
                expected_known_answer_integrity_file_sha256
            ),
        )
        manifest_file = _existing_file(manifest_path, label="release manifest")
        manifest, _manifest_raw = _read_json(manifest_file, label="release manifest")
        if (
            manifest.get("schema_version") != SCHEMA_VERSION
            or manifest.get("gate") != RELEASE_GATE
            or manifest.get("release_type") != RELEASE_TYPE
            or manifest.get("run_id") != run_id
            or manifest.get("passed") is not True
            or manifest.get("manifest_sha256")
            != canonical_sha256(manifest, omit="manifest_sha256")
            or not isinstance(manifest.get("generated_at"), str)
            or manifest.get("expected_bindings") != {
                "candidate_digest": expected_candidate_digest,
                "certificate_sha256": expected_certificate_sha256,
                "stage3_artifact_sha256": expected_stage3_artifact_sha256,
            }
            or manifest.get("expected_physical_bindings") != physical
        ):
            _fail("MANIFEST_INVALID", "release header/selfhash/bindings are invalid")
        invocation = manifest.get("normalized_invocation")
        known_binding = manifest.get("known_answer_integrity")
        runner_binding = (
            known_binding.get("runner_source")
            if isinstance(known_binding, Mapping) else None
        )
        if (
            not isinstance(invocation, Mapping)
            or invocation.get("normalized_sha256")
            != canonical_sha256(invocation, omit="normalized_sha256")
            or not isinstance(runner_binding, Mapping)
        ):
            _fail("MANIFEST_INVALID", "normalized invocation/runner seal is invalid")
        entries = manifest.get("certificates")
        stage3_binding = manifest.get("source_stage3")
        if (
            not isinstance(entries, list)
            or len(entries) != 1
            or not isinstance(entries[0], Mapping)
            or not isinstance(stage3_binding, Mapping)
        ):
            _fail("MANIFEST_INVALID", "release artifact entries are malformed")
        root = manifest_file.parent
        entry = entries[0]
        packaged_certificate, packaged_certificate_raw = _read_json(
            _release_file(root, entry.get("file"), label="certificate"),
            label="packaged certificate",
        )
        packaged_verification, packaged_verification_raw = _read_json(
            _release_file(root, entry.get("verification_file"), label="verification"),
            label="packaged verification",
        )
        packaged_stage3, packaged_stage3_raw = _read_json(
            _release_file(root, stage3_binding.get("file"), label="Stage-3"),
            label="packaged Stage-3",
        )
        packaged_integrity, packaged_integrity_raw = _read_json(
            _release_file(root, known_binding.get("sidecar_file"), label="integrity"),
            label="packaged strict integrity",
        )
        external_certificate, external_certificate_raw = _read_json(
            paths["certificate"], label="external certificate",
        )
        external_verification, external_verification_raw = _read_json(
            paths["verification"], label="external verification",
        )
        external_stage3, external_stage3_raw = _read_json(
            paths["stage3_artifact"], label="external Stage-3",
        )
        external_integrity, external_integrity_raw = _read_json(
            paths["known_answer_integrity"], label="external strict integrity",
        )
        if (
            _replay.sha256_bytes(external_stage3_raw) != physical["stage3_file_sha256"]
            or _replay.sha256_bytes(external_certificate_raw)
            != physical["certificate_file_sha256"]
            or _replay.sha256_bytes(external_verification_raw)
            != physical["verification_file_sha256"]
            or _replay.sha256_bytes(external_integrity_raw)
            != physical["known_answer_integrity_file_sha256"]
            or external_certificate_raw != packaged_certificate_raw
            or external_verification_raw != packaged_verification_raw
            or external_stage3_raw != packaged_stage3_raw
            or external_integrity_raw != packaged_integrity_raw
            or external_certificate != packaged_certificate
            or external_verification != packaged_verification
            or external_stage3 != packaged_stage3
            or external_integrity != packaged_integrity
        ):
            _fail("MANIFEST_INVALID", "packaged/external physical binding failed")
        before = _provenance_raw(paths)
        pair = _replay_inputs(
            external_certificate,
            external_verification,
            paths=paths,
            expected_candidate_digest=expected_candidate_digest,
            expected_certificate_sha256=expected_certificate_sha256,
            expected_stage3_artifact_sha256=expected_stage3_artifact_sha256,
            before=before,
            phase="relocated-validate",
            expected_runner_sha256=runner_binding.get("sha256"),
        )
        sources = _source_hashes(paths["repo_dir"])
        rebuilt = _build_manifest(
            run_id=run_id,
            generated_at=manifest["generated_at"],
            certificate=external_certificate,
            certificate_raw=external_certificate_raw,
            verification=external_verification,
            verification_raw=external_verification_raw,
            pair=pair,
            sources=sources,
            expected_candidate_digest=expected_candidate_digest,
            expected_certificate_sha256=expected_certificate_sha256,
            expected_stage3_artifact_sha256=expected_stage3_artifact_sha256,
            physical=physical,
        )
        if manifest != rebuilt:
            _fail("MANIFEST_INVALID", "release differs from complete static rebuild")
        return {
            "passed": True,
            "run_id": run_id,
            "certificates": 1,
            "verified": 1,
            "manifest_sha256": manifest["manifest_sha256"],
            "failures": [],
        }
    except (
        TypedDistQLDPCFinal5ReleaseError,
        _replay.DistQLDPCReleaseReplayError,
        KeyError,
        IndexError,
        OSError,
        TypeError,
        ValueError,
    ) as exc:
        return _failure(expected_run_id, exc)


def export_typed_distqldpc_release(
    *,
    repo_dir: Path | str,
    stage3_artifact: Path | str,
    certificate_path: Path | str,
    verification_path: Path | str,
    output_dir: Path | str,
    run_id: str,
    known_answer_artifact: Path | str,
    known_answer_trust: Path | str,
    known_answer_integrity: Path | str,
    expected_candidate_digest: str,
    expected_certificate_sha256: str,
    expected_stage3_artifact_sha256: str,
    expected_stage3_file_sha256: str,
    expected_certificate_file_sha256: str,
    expected_verification_file_sha256: str,
    expected_known_answer_integrity_file_sha256: str,
    invocation_argv: list[str],
) -> dict[str, Any]:
    """Publish one immutable, portable, self-validating release snapshot."""

    run_id = _run_id(run_id)
    paths = _input_paths(
        repo_dir=repo_dir,
        stage3_artifact=stage3_artifact,
        certificate_path=certificate_path,
        verification_path=verification_path,
        known_answer_artifact=known_answer_artifact,
        known_answer_trust=known_answer_trust,
        known_answer_integrity=known_answer_integrity,
    )
    output, parent_identity = _output_path(output_dir)
    physical = _physical_pins(
        expected_stage3_file_sha256=expected_stage3_file_sha256,
        expected_certificate_file_sha256=expected_certificate_file_sha256,
        expected_verification_file_sha256=expected_verification_file_sha256,
        expected_known_answer_integrity_file_sha256=(
            expected_known_answer_integrity_file_sha256
        ),
    )
    _parse_export_argv(
        invocation_argv,
        repo=paths["repo_dir"],
        paths=paths,
        output=output,
        run_id=run_id,
        expected_candidate_digest=expected_candidate_digest,
        expected_certificate_sha256=expected_certificate_sha256,
        expected_stage3_artifact_sha256=expected_stage3_artifact_sha256,
        physical=physical,
    )
    stage3, stage3_raw = _read_json(paths["stage3_artifact"], label="source Stage-3")
    certificate, certificate_raw = _read_json(
        paths["certificate"], label="Stage-4 certificate",
    )
    verification, verification_raw = _read_json(
        paths["verification"], label="verification sidecar",
    )
    integrity, integrity_raw = _read_json(
        paths["known_answer_integrity"], label="strict known-answer sidecar",
    )
    before = _provenance_raw(paths)
    if (
        stage3_raw != before["stage3_artifact"]
        or certificate_raw != before["certificate"]
        or verification_raw != before["verification"]
        or integrity_raw != before["known_answer_integrity"]
        or _replay.sha256_bytes(stage3_raw) != physical["stage3_file_sha256"]
        or _replay.sha256_bytes(certificate_raw)
        != physical["certificate_file_sha256"]
        or _replay.sha256_bytes(verification_raw)
        != physical["verification_file_sha256"]
        or _replay.sha256_bytes(integrity_raw)
        != physical["known_answer_integrity_file_sha256"]
    ):
        _fail("PHYSICAL_SHA256_MISMATCH", "an explicitly pinned input differs")
    pair = _replay_inputs(
        certificate,
        verification,
        paths=paths,
        expected_candidate_digest=expected_candidate_digest,
        expected_certificate_sha256=expected_certificate_sha256,
        expected_stage3_artifact_sha256=expected_stage3_artifact_sha256,
        before=before,
        phase="export",
        expected_runner_sha256=None,
    )
    if (
        integrity != pair["known_answer_integrity"]["sidecar"]
        or canonical_sha256(stage3) != pair["stage3"]["payload_sha256"]
    ):
        _fail("SOURCE_CHANGED", "Stage-3/integrity changed during replay")
    sources = _source_hashes(paths["repo_dir"])
    generated_at = datetime.now(timezone.utc).isoformat()
    manifest = _build_manifest(
        run_id=run_id,
        generated_at=generated_at,
        certificate=certificate,
        certificate_raw=certificate_raw,
        verification=verification,
        verification_raw=verification_raw,
        pair=pair,
        sources=sources,
        expected_candidate_digest=expected_candidate_digest,
        expected_certificate_sha256=expected_certificate_sha256,
        expected_stage3_artifact_sha256=expected_stage3_artifact_sha256,
        physical=physical,
    )
    parent = output.parent
    try:
        staging = Path(tempfile.mkdtemp(prefix=f".{output.name}.staging-", dir=parent))
        staging_identity = _inode(staging.lstat())
    except OSError as exc:
        _fail("OUTPUT_INVALID", f"cannot create private staging: {exc}")
    directories: dict[str, tuple[tuple[int, int], tuple[str, ...]]] = {}
    published = False
    try:
        known, stage3_binding = _snapshot_bindings(pair)
        layouts = {
            "certificates": f"{certificate['certificate_sha256']}.json",
            "verifications": f"{canonical_sha256(verification)}.json",
            "stage3": f"{stage3_binding['file_sha256']}.json",
            "integrity": f"{known['sidecar_file_sha256']}.json",
        }
        for directory, filename in layouts.items():
            path = staging / directory
            path.mkdir(mode=0o700)
            directories[directory] = (_inode(path.lstat()), (filename,))
        _write_new(staging / "certificates" / layouts["certificates"], certificate_raw)
        _write_new(staging / "verifications" / layouts["verifications"], verification_raw)
        _write_new(staging / "stage3" / layouts["stage3"], stage3_raw)
        _write_new(staging / "integrity" / layouts["integrity"], integrity_raw)
        manifest_path = staging / MANIFEST_FILENAME
        _write_new(manifest_path, _json_bytes(manifest))
        for directory in layouts:
            _fsync_dir(staging / directory)
        _fsync_dir(staging)
        validation = validate_typed_distqldpc_release(
            manifest_path,
            repo_dir=paths["repo_dir"],
            stage3_artifact=paths["stage3_artifact"],
            certificate_path=paths["certificate"],
            verification_path=paths["verification"],
            known_answer_artifact=paths["known_answer_artifact"],
            known_answer_trust=paths["known_answer_trust"],
            known_answer_integrity=paths["known_answer_integrity"],
            expected_run_id=run_id,
            expected_candidate_digest=expected_candidate_digest,
            expected_certificate_sha256=expected_certificate_sha256,
            expected_stage3_artifact_sha256=expected_stage3_artifact_sha256,
            expected_stage3_file_sha256=expected_stage3_file_sha256,
            expected_certificate_file_sha256=expected_certificate_file_sha256,
            expected_verification_file_sha256=expected_verification_file_sha256,
            expected_known_answer_integrity_file_sha256=(
                expected_known_answer_integrity_file_sha256
            ),
        )
        if validation.get("passed") is not True:
            _fail("SELF_VALIDATION_FAILED", "; ".join(validation["failures"]))
        if not _rename_noreplace(
            staging,
            output,
            expected_parent_identity=parent_identity,
            expected_source_identity=staging_identity,
        ):
            _fail("OUTPUT_EXISTS", f"immutable destination raced: {output}")
        published = True
        _fsync_dir(parent)
    finally:
        if not published:
            _safe_cleanup(
                staging=staging,
                parent=parent,
                parent_identity=parent_identity,
                staging_identity=staging_identity,
                directories=directories,
            )
    return {
        "status": "EXPORTED",
        "run_id": run_id,
        "manifest": str(output / MANIFEST_FILENAME),
        "manifest_sha256": manifest["manifest_sha256"],
        "certificates": 1,
        "generic_pipeline_registration": False,
        "known_answer_integrity": "official-fast-plus-strict-portable-runner",
        "physical_source_pins": 4,
        "solver_invocations": 0,
    }


__all__ = [
    "CLI_SOURCE",
    "EXPORTER_SOURCE",
    "MANIFEST_FILENAME",
    "RELEASE_GATE",
    "RELEASE_TYPE",
    "REQUIRED_SOURCE_FILES",
    "TypedDistQLDPCFinal5ReleaseError",
    "export_typed_distqldpc_release",
    "validate_typed_distqldpc_release",
]




