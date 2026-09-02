#!/usr/bin/env python3
"""Resumable proof runner for one exact paper400 hierarchical child.

DMTCP is used only to preserve the live CaDiCaL process and its append-only
DRAT stream.  A checkpoint has no scientific authority.  This runner emits a
child UNSAT envelope only after checking a *complete* quiescent DRAT,
converting it to LRAT, checking the LRAT, and freshly replaying both proofs.
The quiescent source is explicitly either DMTCP checkpoint-stopped or a latest
generation whose committed PID identity is dead and whose proof has no writer.
Neither path invents a clean solver exit or exit code.

The retry boundary is deliberate: ``verify-checkpoint`` and
``harvest-inactive`` perform the first complete DRAT check before creating a
terminal claim.  A failed checkpoint proof stays resumable; a failed inactive
proof stays unclaimed and may be checked again, but cannot resume search.
"""

from __future__ import annotations

import argparse
import contextlib
import fcntl
import hashlib
import importlib.util
import os
import re
import resource
import stat
import subprocess
import sys
import threading
from pathlib import Path
from typing import Any, Iterator, Mapping, Sequence


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from investigations import paper400_dic5_nested_width10_campaign_v1 as nested
from investigations import paper400_dic5_nested_width10_proof_records_v1 as proof_v1
from scripts import paper400_dic5_nested_width10_resume_static_v1 as static_v1


CONTROLLER_RELATIVE = Path("scripts/run_cadical_dmtcp_resume_v1.py")
PROOF_HELPER_RELATIVE = Path(
    "scripts/run_paper400_dic5_cube16_standalone_proof_v1.py"
)
FOUR_LANE_RELATIVE = Path(
    "scripts/run_paper400_dic5_nested_width10_four_lane_v1.py"
)
EXPECTED_CONTROLLER_SHA256 = (
    "9e57ea9b99a4b041c73a97939f997671790b77b6cb5c7b3d7fe04e1d925f47d2"
)
EXPECTED_PROOF_HELPER_SHA256 = (
    "2d1c2e0240a7eacb5e07695fc55028860ec1a23eb15681af9f1e49fbb42d2a38"
)
EXPECTED_FOUR_LANE_SHA256 = (
    "595fc59c65ab7d5b2de628b4c6d55d5adfc110d28386a811a235c847db57b60d"
)

SOLVER = Path("/home/jing/paper400-toolchain/cadical-1.9.5/bin/cadical")
DMTCP_PREFIX = Path("/home/jing/paper400-toolchain/dmtcp-4.2.0")
DRAT_CHECKER = Path(
    "/home/jing/paper400-toolchain/proof-checkers/bin/drat-trim"
)
LRAT_CHECKER = Path(
    "/home/jing/paper400-toolchain/proof-checkers/bin/lrat-check"
)
SUDO = Path("/usr/bin/sudo")
LSOF = Path("/usr/bin/lsof")

EXPECTED_SOLVER_SHA256 = (
    "6e7d53fa447d13fb962de78c7bd6a6354711151529754a5684170bd9a6a36a21"
)
EXPECTED_DMTCP_LAUNCH_SHA256 = (
    "2036e98a96ca701425a4d47d86b82d0b4657cf39cbac90cd22770dc9d65480ab"
)
EXPECTED_DMTCP_COMMAND_SHA256 = (
    "aa4eebcbdaa62abde9af5e849f93423de22ce4415871c678095613598d3c4c98"
)
EXPECTED_DMTCP_RESTART_SHA256 = (
    "b1e72dd345660cdcb3688accb4888542df3c8d1ed97e08ebbbfc46e783da32ae"
)
EXPECTED_DRAT_SHA256 = (
    "8d25091073e9295028dd4aec85acca4d9b3381d2cfcc145a5b0e14ae909ce394"
)
EXPECTED_LRAT_SHA256 = (
    "c523189a2c4c121bc1e6d284347cbbbec0d3ebf6a1deccb99cb4752548a3ee79"
)
EXPECTED_SUDO_SHA256 = (
    "1e000f41739201f030cdc588fbe50d5438570f5386104c9521543824827fb985"
)
EXPECTED_LSOF_SHA256 = (
    "2484863a7bfda7f97b90bfd5dfceed4ec9f27dd51f9c5158c8daabbf4309b1df"
)

SCHEMA_VERSION = 1
GATE = "paper400-dic5-nested-width10-child-resume-proof-v1"
SOLVER_ARGS = ["-q"]
FINAL_ROOT_ATTESTATION_SCHEMA_VERSION = 1
FINAL_ROOT_ATTESTATION_KIND = "paper400-dic5-nested-width10-final-root-attestation-v1"
FINAL_ROOT_ATTESTATION_FIELDS = frozenset({
    "schema_version", "kind", "gate", "root", "root_identity",
    "resume_static_sha256", "session_sha256", "transport_chain_sha256",
    "terminal_claim_sha256", "drat_commit_sha256", "lrat_commit_sha256",
    "final_commit_sha256", "certificate_sha256", "validation_sha256",
    "cnf_artifact", "drat_artifact", "lrat_artifact",
    "source_binding_sha256", "toolchain_binding_sha256",
    "fresh_drat_checker", "fresh_lrat_checker",
    "proof_source_state", "proof_replay_decision_complete",
    "strict_proof_unsat", "valid",
    "failures", "record_sha256",
}) | frozenset(proof_v1.IDENTITY_FIELDS)
TRANSPORT_PRUNE_SCHEMA_VERSION = 1
TRANSPORT_PRUNE_CLAIM_KIND = (
    "paper400-dic5-nested-width10-transport-prune-claim-v1"
)
TRANSPORT_PRUNE_COMMIT_KIND = (
    "paper400-dic5-nested-width10-transport-prune-commit-v1"
)
TRANSPORT_PRUNE_STATUS_KIND = (
    "paper400-dic5-nested-width10-transport-prune-status-v1"
)
TRANSPORT_PRUNE_MAX_ENTRIES = 100_000

STATIC_PARENT = Path("static/parent-manifest.json")
STATIC_WIDTH6_CAMPAIGN = Path("static/width6-campaign.json")
STATIC_WIDTH10_CAMPAIGN = Path("static/width10-campaign.json")
STATIC_DIMACS = Path("static/cube.cnf")
STATIC_COMMIT = Path("state/00-resume-static.json")
START_CLAIM = Path("state/10-start.claim")
SESSION_COMMIT = Path("state/11-session.json")
RESUME_ADMISSIONS = Path("state/resume-admissions")
TERMINAL_CLAIM = Path("state/20-proof-harvest.claim")
DRAT_COMMIT = Path("state/21-drat.json")
LRAT_COMMIT = Path("state/22-lrat.json")
CERTIFICATE = Path("certificate.json")
VALIDATION = Path("validation.json")
FINAL_COMMIT = Path("COMMIT.json")
RUNTIME_ROOT = Path("runtime/dmtcp")
ROOT_LOCK = Path(".hierarchical-resume.lock")
_HELD_ROOT_LOCKS: set[tuple[int, int, int]] = set()
_HELD_ROOT_LOCKS_GUARD = threading.Lock()
DRAT_ARTIFACT = Path("artifacts/child.drat")
LRAT_ARTIFACT = Path("artifacts/child.lrat")
TRANSPORT_PRUNE_CLAIM = Path("state/30-transport-prune.claim.json")
TRANSPORT_PRUNE_COMMIT = Path("state/31-transport-prune.json")
CHAIN_REQUIRE_STATUS = "STATUS"
CHAIN_REQUIRE_CHECKPOINTED = "CHECKPOINTED_ONLY"
CHAIN_REQUIRE_INACTIVE = "INACTIVE_ONLY"
CHAIN_REQUIRE_STOPPED = "STOPPED_ONLY"
CHAIN_REQUIREMENTS = frozenset({
    CHAIN_REQUIRE_STATUS,
    CHAIN_REQUIRE_CHECKPOINTED,
    CHAIN_REQUIRE_INACTIVE,
    CHAIN_REQUIRE_STOPPED,
})


class HierarchicalResumeRunnerError(RuntimeError):
    """A static, transport, resource, or proof-chain invariant failed."""


def _stable_source(path: Path, expected_sha256: str) -> bytes:
    fd = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        before = os.fstat(fd)
        if not stat.S_ISREG(before.st_mode) or before.st_size > (16 << 20):
            raise HierarchicalResumeRunnerError("pinned source is not bounded/plain")
        payload = bytearray()
        while True:
            chunk = os.read(fd, 1 << 20)
            if not chunk:
                break
            payload.extend(chunk)
            if len(payload) > (16 << 20):
                raise HierarchicalResumeRunnerError("pinned source exceeds cap")
        after = os.fstat(fd)
    finally:
        os.close(fd)
    identity = lambda item: (
        item.st_dev, item.st_ino, item.st_mode, item.st_uid, item.st_size,
        item.st_mtime_ns, item.st_ctime_ns,
    )
    if identity(before) != identity(after) or len(payload) != before.st_size:
        raise HierarchicalResumeRunnerError("pinned source changed while reading")
    result = bytes(payload)
    if hashlib.sha256(result).hexdigest() != expected_sha256:
        raise HierarchicalResumeRunnerError(f"pinned source hash mismatch: {path}")
    return result


def _load_pinned_module(name: str, relative: Path, digest: str) -> Any:
    path = (PROJECT / relative).resolve(strict=True)
    payload = _stable_source(path, digest)
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise HierarchicalResumeRunnerError(f"cannot load pinned module {relative}")
    module = importlib.util.module_from_spec(spec)
    exec(compile(payload, str(path), "exec"), module.__dict__)
    return module


controller = _load_pinned_module(
    "_paper400_hierarchical_dmtcp_v1", CONTROLLER_RELATIVE,
    EXPECTED_CONTROLLER_SHA256,
)
proof_helper = _load_pinned_module(
    "_paper400_hierarchical_proof_helper_v1", PROOF_HELPER_RELATIVE,
    EXPECTED_PROOF_HELPER_SHA256,
)
v2 = proof_helper.v2


def canonical_bytes(value: Any) -> bytes:
    return static_v1.canonical_bytes(value)


def seal(value: Mapping[str, Any]) -> dict[str, Any]:
    return static_v1.seal(value)


def _default_tool_paths() -> dict[str, Path]:
    return {
        "cadical_solver": SOLVER,
        "dmtcp_controller_source": PROJECT / CONTROLLER_RELATIVE,
        "four_lane_coordinator_source": PROJECT / FOUR_LANE_RELATIVE,
        "dmtcp_launch": DMTCP_PREFIX / "bin/dmtcp_launch",
        "dmtcp_command": DMTCP_PREFIX / "bin/dmtcp_command",
        "dmtcp_restart": DMTCP_PREFIX / "bin/dmtcp_restart",
        "drat_checker": DRAT_CHECKER,
        "drat_to_lrat": DRAT_CHECKER,
        "lrat_checker": LRAT_CHECKER,
    }


def _default_tool_hashes() -> dict[str, str]:
    return {
        "cadical_solver": EXPECTED_SOLVER_SHA256,
        "dmtcp_controller_source": EXPECTED_CONTROLLER_SHA256,
        "four_lane_coordinator_source": EXPECTED_FOUR_LANE_SHA256,
        "dmtcp_launch": EXPECTED_DMTCP_LAUNCH_SHA256,
        "dmtcp_command": EXPECTED_DMTCP_COMMAND_SHA256,
        "dmtcp_restart": EXPECTED_DMTCP_RESTART_SHA256,
        "drat_checker": EXPECTED_DRAT_SHA256,
        "drat_to_lrat": EXPECTED_DRAT_SHA256,
        "lrat_checker": EXPECTED_LRAT_SHA256,
    }


def _read_json(path: Path) -> dict[str, Any]:
    try:
        return v2._strict_json(path)
    except (OSError, ValueError, TypeError, v2.ProofRunnerError) as exc:
        raise HierarchicalResumeRunnerError(f"invalid strict JSON: {path}") from exc


def _root_identity(root: Path) -> dict[str, Any]:
    target = root.resolve(strict=True)
    lexical = os.stat(root, follow_symlinks=False)
    if (
        target != root or root.is_symlink() or not stat.S_ISDIR(lexical.st_mode)
        or stat.S_IMODE(lexical.st_mode) != 0o700
        or lexical.st_uid != os.geteuid()
    ):
        raise HierarchicalResumeRunnerError("root is not canonical owned mode-0700")
    return {
        "path": str(root), "device": lexical.st_dev, "inode": lexical.st_ino,
        "uid": lexical.st_uid, "mode": stat.S_IMODE(lexical.st_mode),
    }


def _lock_file_identity(root: Path) -> dict[str, Any]:
    path = root / ROOT_LOCK
    info = os.stat(path, follow_symlinks=False)
    if (
        path.is_symlink() or not stat.S_ISREG(info.st_mode)
        or stat.S_IMODE(info.st_mode) != 0o600
        or info.st_uid != os.geteuid() or info.st_nlink != 1
        or info.st_size != 0
    ):
        raise HierarchicalResumeRunnerError("root lock file identity is invalid")
    return {
        "relative_path": ROOT_LOCK.as_posix(),
        "device": info.st_dev, "inode": info.st_ino, "uid": info.st_uid,
        "mode": stat.S_IMODE(info.st_mode), "links": info.st_nlink,
        "bytes": info.st_size, "sha256": hashlib.sha256(b"").hexdigest(),
    }


def _initialize_root_lock(root: Path) -> dict[str, Any]:
    directory = os.open(root, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    descriptor = -1
    try:
        descriptor = os.open(
            ROOT_LOCK.name,
            os.O_RDWR | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW,
            0o600, dir_fd=directory,
        )
        os.fchmod(descriptor, 0o600)
        os.fsync(descriptor)
        os.fsync(directory)
    finally:
        if descriptor >= 0:
            os.close(descriptor)
        os.close(directory)
    return _lock_file_identity(root)


def _acquire_root_lock(
    root: Path, *, exclusive: bool,
) -> tuple[int, tuple[int, int, int], dict[str, Any], dict[str, Any]]:
    root_before = _root_identity(root)
    key = (os.getpid(), root_before["device"], root_before["inode"])
    with _HELD_ROOT_LOCKS_GUARD:
        if key in _HELD_ROOT_LOCKS:
            raise HierarchicalResumeRunnerError(
                "nested root lock acquisition rejected"
            )
        _HELD_ROOT_LOCKS.add(key)
    descriptor = -1
    try:
        expected = _lock_file_identity(root)
        descriptor = os.open(
            root / ROOT_LOCK, os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW,
        )
        observed = os.fstat(descriptor)
        if (
            observed.st_dev != expected["device"]
            or observed.st_ino != expected["inode"]
            or not stat.S_ISREG(observed.st_mode)
            or stat.S_IMODE(observed.st_mode) != 0o600
            or observed.st_uid != os.geteuid() or observed.st_nlink != 1
            or observed.st_size != 0
        ):
            raise HierarchicalResumeRunnerError("root lock changed before acquire")
        operation = fcntl.LOCK_EX if exclusive else fcntl.LOCK_SH
        try:
            fcntl.flock(descriptor, operation | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise HierarchicalResumeRunnerError("root lock is busy") from exc
        if (
            not static_v1.json_type_equal(root_before, _root_identity(root))
            or not static_v1.json_type_equal(expected, _lock_file_identity(root))
        ):
            raise HierarchicalResumeRunnerError("root or lock changed during acquire")
        return descriptor, key, root_before, expected
    except BaseException:
        with _HELD_ROOT_LOCKS_GUARD:
            _HELD_ROOT_LOCKS.discard(key)
        if descriptor >= 0:
            with contextlib.suppress(OSError):
                fcntl.flock(descriptor, fcntl.LOCK_UN)
            os.close(descriptor)
        raise


def _release_root_lock(
    descriptor: int, key: tuple[int, int, int], root: Path,
    root_before: Mapping[str, Any], lock_before: Mapping[str, Any],
) -> None:
    release_error: BaseException | None = None
    try:
        observed = os.fstat(descriptor)
        if (
            not static_v1.json_type_equal(root_before, _root_identity(root))
            or not static_v1.json_type_equal(lock_before, _lock_file_identity(root))
            or observed.st_dev != lock_before["device"]
            or observed.st_ino != lock_before["inode"]
        ):
            raise HierarchicalResumeRunnerError("root or lock changed while held")
    except BaseException as exc:
        release_error = exc
    finally:
        with _HELD_ROOT_LOCKS_GUARD:
            _HELD_ROOT_LOCKS.discard(key)
        with contextlib.suppress(OSError):
            fcntl.flock(descriptor, fcntl.LOCK_UN)
        os.close(descriptor)
    if release_error is not None:
        raise release_error


@contextlib.contextmanager
def _root_lock(root: Path, *, exclusive: bool) -> Iterator[dict[str, Any]]:
    descriptor, key, root_before, lock_before = _acquire_root_lock(
        root, exclusive=exclusive,
    )
    try:
        yield lock_before
    finally:
        _release_root_lock(descriptor, key, root, root_before, lock_before)


def _new_root(root: Path) -> Path:
    target = Path(root)
    if not target.is_absolute() or str(target) != os.path.abspath(str(target)):
        raise HierarchicalResumeRunnerError("root must be normalized absolute")
    if target.exists() or target.is_symlink():
        raise HierarchicalResumeRunnerError("new root already exists")
    parent = target.parent.resolve(strict=True)
    if parent != target.parent or target.parent.is_symlink():
        raise HierarchicalResumeRunnerError("root parent is aliased")
    os.mkdir(target, 0o700)
    os.chmod(target, 0o700, follow_symlinks=False)
    directory = os.open(parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)
    _root_identity(target)
    return target


def _existing_root(root: Path) -> Path:
    target = Path(root)
    if not target.is_absolute() or str(target) != os.path.abspath(str(target)):
        raise HierarchicalResumeRunnerError("root must be normalized absolute")
    _root_identity(target)
    return target


def _mkdir(parent: Path, name: str) -> None:
    v2._mkdir_new(parent, name)


def _publish_json(path: Path, value: Mapping[str, Any]) -> None:
    v2._atomic_publish_json(path.parent, path.name, value)


def _publish_bytes(path: Path, value: bytes) -> None:
    v2._atomic_publish_bytes(path.parent, path.name, value)


def _claim(path: Path, *, root: Path, action: str) -> dict[str, Any]:
    value = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-nested-width10-resume-stage-claim-v1",
        "gate": GATE,
        "root": str(root),
        "root_identity": _root_identity(root),
        "root_lock_identity": _lock_file_identity(root),
        "action": action,
        "nonce_hex": os.urandom(32).hex(),
        "pid": os.getpid(),
        "terminal": action in {"verify-checkpoint", "harvest-inactive"},
    })
    _publish_json(path, value)
    return value


def _caps_from_static(record: Mapping[str, Any]) -> dict[str, int]:
    policy = record.get("resource_policy")
    if type(policy) is not dict:
        raise HierarchicalResumeRunnerError("static resource policy missing")
    result = {key: policy.get(key) for key in static_v1.CAP_INPUT_FIELDS}
    if any(type(value) is not int for value in result.values()):
        raise HierarchicalResumeRunnerError("static resource inputs malformed")
    return result  # type: ignore[return-value]


def _tool_inputs_from_static(
    record: Mapping[str, Any],
) -> tuple[dict[str, Path], dict[str, str]]:
    tools = record.get("toolchain_binding", {}).get("tools")
    if type(tools) is not dict or set(tools) != static_v1.TOOL_ROLES:
        raise HierarchicalResumeRunnerError("static toolchain roles malformed")
    paths: dict[str, Path] = {}
    hashes: dict[str, str] = {}
    for role in static_v1.TOOL_ROLES:
        item = tools.get(role)
        if type(item) is not dict or type(item.get("path")) is not str:
            raise HierarchicalResumeRunnerError("static tool path malformed")
        paths[role] = Path(item["path"])
        hashes[role] = item.get("sha256")
    return paths, hashes


def _load_static(
    root: Path,
    *,
    instance: Any | None = None,
    strict_base: bool | None = None,
    tool_paths: Mapping[str, Path] | None = None,
    expected_tool_sha256: Mapping[str, str] | None = None,
    resource_caps: Mapping[str, Any] | None = None,
    campaign_verification_record: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    target = _existing_root(root)
    record = _read_json(target / STATIC_COMMIT)
    parent = _read_json(target / STATIC_PARENT)
    width6_campaign = _read_json(target / STATIC_WIDTH6_CAMPAIGN)
    campaign = _read_json(target / STATIC_WIDTH10_CAMPAIGN)
    if strict_base is None:
        strict_base = record.get("test_only") is False
    if type(strict_base) is not bool:
        raise HierarchicalResumeRunnerError("strict_base is malformed")
    if strict_base:
        if instance is not None:
            raise HierarchicalResumeRunnerError(
                "production replay must build the current instance"
            )
        instance = nested.cube16.optimized.build_optimized_instance()
    elif instance is None:
        raise HierarchicalResumeRunnerError("test-only root needs caller instance")
    if campaign_verification_record is None:
        caller_verification = nested.verify_campaign_manifest(
            campaign,
            width6_campaign,
            parent,
            instance,
            parent_cube_index=record.get("child", {}).get(
                "parent_cube_index"
            ),
            strict_base=strict_base,
        )
        if caller_verification.get("valid") is not True:
            raise HierarchicalResumeRunnerError(
                "direct child action failed full width-ten campaign replay: "
                f"{caller_verification.get('binding_failures')}"
            )
    else:
        caller_verification = static_v1._require_campaign_verification_record(
            campaign_verification_record,
            campaign_manifest_sha256=campaign.get("manifest_sha256"),
        )
    stored_paths, stored_hashes = _tool_inputs_from_static(record)
    if tool_paths is None:
        tool_paths = _default_tool_paths() if strict_base else stored_paths
    if expected_tool_sha256 is None:
        expected_tool_sha256 = (
            _default_tool_hashes() if strict_base else stored_hashes
        )
    if strict_base and (
        {key: str(Path(value)) for key, value in tool_paths.items()}
        != {key: str(value) for key, value in _default_tool_paths().items()}
        or dict(expected_tool_sha256) != _default_tool_hashes()
    ):
        raise HierarchicalResumeRunnerError("production tool policy mismatch")
    if resource_caps is None:
        resource_caps = _caps_from_static(record)
    global_leaf_index = record.get("child", {}).get("global_leaf_index")
    parent_index = record.get("child", {}).get("parent_cube_index")
    report = static_v1.verify_resume_static_record(
        record,
        root=target,
        parent_manifest=parent,
        width6_campaign_manifest=width6_campaign,
        width10_campaign_manifest=campaign,
        instance=instance,
        parent_cube_index=parent_index,
        global_leaf_index=global_leaf_index,
        campaign_verification_record=caller_verification,
        child_cnf_path=target / STATIC_DIMACS,
        tool_paths=dict(tool_paths),
        expected_tool_sha256=dict(expected_tool_sha256),
        resource_caps=dict(resource_caps),
        strict_base=strict_base,
    )
    if report.get("valid") is not True:
        raise HierarchicalResumeRunnerError(
            f"resume-static replay failed: {report.get('binding_failures')}"
        )
    return {
        "record": record,
        "parent": parent,
        "width6_campaign": width6_campaign,
        "campaign": campaign,
        "instance": instance,
        "strict_base": strict_base,
        "tool_paths": dict(tool_paths),
        "tool_hashes": dict(expected_tool_sha256),
        "resource_caps": dict(resource_caps),
        "static_report": report,
    }


def prepare_root_from_material(
    root: Path,
    *,
    parent_manifest: Mapping[str, Any],
    width6_campaign_manifest: Mapping[str, Any],
    width10_campaign_manifest: Mapping[str, Any],
    instance: Any | None = None,
    parent_cube_index: int,
    global_leaf_index: int,
    campaign_verification_record: Mapping[str, Any],
    verified_child_dimacs: bytes,
    resource_caps: Mapping[str, Any],
    strict_base: bool,
    tool_paths: Mapping[str, Path] | None = None,
    expected_tool_sha256: Mapping[str, str] | None = None,
) -> dict[str, Any]:
    if type(strict_base) is not bool:
        raise HierarchicalResumeRunnerError("strict_base is malformed")
    static_v1._require_width10_request(
        parent_cube_index=parent_cube_index,
        global_leaf_index=global_leaf_index,
    )
    if strict_base:
        if instance is not None:
            raise HierarchicalResumeRunnerError(
                "production replay must build the current instance"
            )
        current_instance = nested.cube16.optimized.build_optimized_instance()
    else:
        if instance is None:
            raise HierarchicalResumeRunnerError(
                "test-only prepare needs caller instance"
            )
        current_instance = instance
    if tool_paths is None:
        tool_paths = _default_tool_paths()
    if expected_tool_sha256 is None:
        expected_tool_sha256 = _default_tool_hashes()
    verification = static_v1._require_campaign_verification_record(
        campaign_verification_record,
        campaign_manifest_sha256=width10_campaign_manifest.get(
            "manifest_sha256"
        ),
    )
    leaves = width10_campaign_manifest.get("leaves")
    if (
        type(leaves) is not list
        or len(leaves) != nested.LEAF_COUNT
        or type(leaves[global_leaf_index]) is not dict
    ):
        raise HierarchicalResumeRunnerError("width-ten campaign leaf list malformed")
    child_dimacs = static_v1._verified_payload_for_leaf(
        verified_child_dimacs, leaves[global_leaf_index]
    )
    target = _new_root(root)
    _initialize_root_lock(target)
    descriptor, key, root_before, lock_before = _acquire_root_lock(
        target, exclusive=True,
    )
    try:
        for name in ("static", "state", "artifacts", "logs", "runtime"):
            _mkdir(target, name)
        _mkdir(target / "state", RESUME_ADMISSIONS.name)
        _publish_bytes(
            target / STATIC_PARENT,
            canonical_bytes(dict(parent_manifest)) + b"\n",
        )
        _publish_bytes(
            target / STATIC_WIDTH6_CAMPAIGN,
            canonical_bytes(dict(width6_campaign_manifest)) + b"\n",
        )
        _publish_bytes(
            target / STATIC_WIDTH10_CAMPAIGN,
            canonical_bytes(dict(width10_campaign_manifest)) + b"\n",
        )
        _publish_bytes(target / STATIC_DIMACS, child_dimacs)
        record = static_v1.build_resume_static_record(
            root=target,
            parent_manifest=parent_manifest,
            width6_campaign_manifest=width6_campaign_manifest,
            width10_campaign_manifest=width10_campaign_manifest,
            instance=current_instance,
            parent_cube_index=parent_cube_index,
            global_leaf_index=global_leaf_index,
            campaign_verification_record=verification,
            verified_child_dimacs=child_dimacs,
            child_cnf_path=target / STATIC_DIMACS,
            tool_paths=dict(tool_paths),
            expected_tool_sha256=dict(expected_tool_sha256),
            resource_caps=dict(resource_caps),
            strict_base=strict_base,
        )
        _publish_json(target / STATIC_COMMIT, record)
        post_report = static_v1.verify_resume_static_record(
            record,
            root=target,
            parent_manifest=parent_manifest,
            width6_campaign_manifest=width6_campaign_manifest,
            width10_campaign_manifest=width10_campaign_manifest,
            instance=current_instance,
            parent_cube_index=parent_cube_index,
            global_leaf_index=global_leaf_index,
            campaign_verification_record=verification,
            child_cnf_path=target / STATIC_DIMACS,
            tool_paths=dict(tool_paths),
            expected_tool_sha256=dict(expected_tool_sha256),
            resource_caps=dict(resource_caps),
            strict_base=strict_base,
            verified_child_dimacs=child_dimacs,
        )
        if post_report.get("valid") is not True:
            raise HierarchicalResumeRunnerError(
                f"post-prepare static mismatch: {post_report.get('binding_failures')}"
            )
        return record
    finally:
        _release_root_lock(
            descriptor, key, target, root_before, lock_before,
        )


@contextlib.contextmanager
def _fixed_environment() -> Iterator[None]:
    previous = dict(os.environ)
    os.environ.clear()
    os.environ.update(controller._clean_dmtcp_environment())
    try:
        yield
    finally:
        os.environ.clear()
        os.environ.update(previous)


def _require_unlimited_cpu_hard() -> None:
    _soft, hard = resource.getrlimit(resource.RLIMIT_CPU)
    if hard != resource.RLIM_INFINITY:
        raise HierarchicalResumeRunnerError(
            "hard RLIMIT_CPU must be unlimited for resumable solver"
        )


@contextlib.contextmanager
def _inherited_solver_limits(cap: int) -> Iterator[None]:
    old_fsize = resource.getrlimit(resource.RLIMIT_FSIZE)
    old_core = resource.getrlimit(resource.RLIMIT_CORE)
    old_cpu = resource.getrlimit(resource.RLIMIT_CPU)
    hard = old_fsize[1]
    if hard != resource.RLIM_INFINITY and hard < cap:
        raise HierarchicalResumeRunnerError("hard RLIMIT_FSIZE below proof cap")
    if old_cpu[1] != resource.RLIM_INFINITY:
        raise HierarchicalResumeRunnerError(
            "hard RLIMIT_CPU must be unlimited for resumable solver"
        )
    try:
        resource.setrlimit(resource.RLIMIT_FSIZE, (cap, hard))
        resource.setrlimit(resource.RLIMIT_CORE, (0, old_core[1]))
        resource.setrlimit(
            resource.RLIMIT_CPU,
            (resource.RLIM_INFINITY, resource.RLIM_INFINITY),
        )
        yield
    finally:
        try:
            resource.setrlimit(resource.RLIMIT_CPU, old_cpu)
        finally:
            try:
                resource.setrlimit(resource.RLIMIT_FSIZE, old_fsize)
            finally:
                resource.setrlimit(resource.RLIMIT_CORE, old_core)


def _rlimit_policy(cap: int) -> dict[str, Any]:
    if type(cap) is not int or cap <= 0:
        raise HierarchicalResumeRunnerError("invalid proof RLIMIT cap")
    return {
        "proof_fsize_soft_bytes": cap,
        "core_soft_bytes": 0,
        "cpu_soft_seconds": resource.RLIM_INFINITY,
        "cpu_hard_seconds": resource.RLIM_INFINITY,
        "must_be_inherited_by_live_solver": True,
    }


def _verify_live_peer_rlimits(pid: int, cap: int) -> dict[str, Any]:
    if type(pid) is not int or pid <= 0 or not hasattr(resource, "prlimit"):
        raise HierarchicalResumeRunnerError("cannot inspect live peer RLIMITs")
    try:
        fsize = resource.prlimit(pid, resource.RLIMIT_FSIZE)
        core = resource.prlimit(pid, resource.RLIMIT_CORE)
        cpu = resource.prlimit(pid, resource.RLIMIT_CPU)
    except (OSError, ProcessLookupError, PermissionError) as exc:
        raise HierarchicalResumeRunnerError("cannot inspect live peer RLIMITs") from exc
    if (
        type(fsize) is not tuple or len(fsize) != 2
        or type(core) is not tuple or len(core) != 2
        or type(cpu) is not tuple or len(cpu) != 2
        or fsize[0] != cap
        or (fsize[1] != resource.RLIM_INFINITY and fsize[1] < cap)
        or core[0] != 0
        or cpu != (resource.RLIM_INFINITY, resource.RLIM_INFINITY)
    ):
        raise HierarchicalResumeRunnerError("live peer RLIMIT policy mismatch")
    return {
        "pid": pid,
        "proof_fsize_soft_bytes": fsize[0],
        "proof_fsize_hard_bytes": fsize[1],
        "core_soft_bytes": core[0],
        "core_hard_bytes": core[1],
        "cpu_soft_seconds": cpu[0],
        "cpu_hard_seconds": cpu[1],
        "verified": True,
    }


def _peer_rlimit_record_valid(
    value: Any, *, pid: int, cap: int,
) -> bool:
    fields = {
        "pid", "proof_fsize_soft_bytes", "proof_fsize_hard_bytes",
        "core_soft_bytes", "core_hard_bytes", "cpu_soft_seconds",
        "cpu_hard_seconds", "verified",
    }
    return bool(
        type(value) is dict and set(value) == fields
        and type(value.get("pid")) is int and value.get("pid") == pid
        and type(value.get("proof_fsize_soft_bytes")) is int
        and value.get("proof_fsize_soft_bytes") == cap
        and type(value.get("proof_fsize_hard_bytes")) is int
        and (
            value.get("proof_fsize_hard_bytes") == resource.RLIM_INFINITY
            or value.get("proof_fsize_hard_bytes") >= cap
        )
        and type(value.get("core_soft_bytes")) is int
        and value.get("core_soft_bytes") == 0
        and type(value.get("core_hard_bytes")) is int
        and type(value.get("cpu_soft_seconds")) is int
        and value.get("cpu_soft_seconds") == resource.RLIM_INFINITY
        and type(value.get("cpu_hard_seconds")) is int
        and value.get("cpu_hard_seconds") == resource.RLIM_INFINITY
        and value.get("verified") is True
    )


def _single_cpu() -> int:
    cpus = os.sched_getaffinity(0)
    if len(cpus) != 1:
        raise HierarchicalResumeRunnerError(
            f"action requires singleton CPU affinity, got {sorted(cpus)}"
        )
    return next(iter(cpus))


def _runtime_libraries() -> list[Path]:
    binding = proof_helper._toolchain_binding()
    objects = binding.get("dynamic_elf_tcb", {}).get("objects")
    if type(objects) is not list or not objects:
        raise HierarchicalResumeRunnerError("pinned runtime closure missing")
    result: list[Path] = []
    for item in objects:
        path = item.get("physical", {}).get("realpath") if type(item) is dict else None
        if type(path) is not str or not Path(path).is_absolute():
            raise HierarchicalResumeRunnerError("runtime closure path malformed")
        result.append(Path(path))
    return result


def _execution_source_binding() -> dict[str, str]:
    """Bind execution/aggregation code not already covered by static-v2."""

    return {
        "runner_source_sha256": v2.file_sha256(Path(__file__).resolve()),
        "proof_v1_source_sha256": v2.file_sha256(
            Path(proof_v1.__file__).resolve()
        ),
        "proof_helper_source_sha256": EXPECTED_PROOF_HELPER_SHA256,
        "dmtcp_controller_source_sha256": EXPECTED_CONTROLLER_SHA256,
    }


def _session_value(
    root: Path, loaded: Mapping[str, Any], claim: Mapping[str, Any],
    config: Mapping[str, Any], started: Mapping[str, Any], cpu: int,
    started_peer_rlimits: Mapping[str, Any],
) -> dict[str, Any]:
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-nested-width10-dmtcp-session-v1",
        "gate": GATE,
        "state": "RUNNING",
        "root": str(root),
        "root_identity": _root_identity(root),
        "root_lock_identity": _lock_file_identity(root),
        "resume_static_sha256": loaded["record"]["record_sha256"],
        "child_index": loaded["record"]["child"]["child_index"],
        "child_dimacs_sha256": loaded["record"]["child"]["child_dimacs_sha256"],
        "start_claim_sha256": claim["record_sha256"],
        "controller_root": str(root / RUNTIME_ROOT),
        "controller_config_sha256": config["self_sha256"],
        "controller_start_sha256": started["self_sha256"],
        "expected_single_cpu": cpu,
        "started_peer_rlimits": dict(started_peer_rlimits),
        "solver_args": list(SOLVER_ARGS),
        "proof_cap_bytes": loaded["resource_caps"]["proof_max_bytes"],
        "resource_policy_sha256": static_v1.canonical_sha256(
            loaded["record"]["resource_policy"]
        ),
        "rlimit_policy": _rlimit_policy(
            loaded["resource_caps"]["proof_max_bytes"]
        ),
        "execution_source_binding": _execution_source_binding(),
        "transport_authority": "TEST_ONLY",
        "transport_trusted_for_scientific_proof": False,
        "production_eligible": False,
    })


def _load_session(
    root: Path, **static_kwargs: Any,
) -> tuple[dict[str, Any], dict[str, Any]]:
    loaded = _load_static(root, **static_kwargs)
    session = _read_json(root / SESSION_COMMIT)
    expected_fields = {
        "schema_version", "kind", "gate", "state", "root",
        "root_identity", "root_lock_identity", "resume_static_sha256", "child_index",
        "child_dimacs_sha256", "start_claim_sha256", "controller_root",
        "controller_config_sha256", "controller_start_sha256",
        "expected_single_cpu", "started_peer_rlimits", "solver_args",
        "proof_cap_bytes",
        "resource_policy_sha256", "rlimit_policy",
        "execution_source_binding", "transport_authority",
        "transport_trusted_for_scientific_proof", "production_eligible",
        "record_sha256",
    }
    if (
        set(session) != expected_fields
        or not static_v1.selfhash_valid(session)
        or type(session.get("schema_version")) is not int
        or session.get("schema_version") != SCHEMA_VERSION
        or session.get("kind") != "paper400-nested-width10-dmtcp-session-v1"
        or session.get("gate") != GATE
        or session.get("state") != "RUNNING"
        or session.get("root") != str(root)
        or not static_v1.json_type_equal(session.get("root_identity"), _root_identity(root))
        or not static_v1.json_type_equal(
            session.get("root_lock_identity"), _lock_file_identity(root)
        )
        or session.get("resume_static_sha256") != loaded["record"]["record_sha256"]
        or session.get("child_index") != loaded["record"]["child"]["child_index"]
        or session.get("child_dimacs_sha256") != loaded["record"]["child"]["child_dimacs_sha256"]
        or session.get("controller_root") != str(root / RUNTIME_ROOT)
        or type(session.get("expected_single_cpu")) is not int
        or session.get("expected_single_cpu") < 0
        or session.get("solver_args") != SOLVER_ARGS
        or type(session.get("proof_cap_bytes")) is not int
        or session.get("proof_cap_bytes") != loaded["resource_caps"]["proof_max_bytes"]
        or session.get("resource_policy_sha256") != static_v1.canonical_sha256(
            loaded["record"]["resource_policy"]
        )
        or not static_v1.json_type_equal(
            session.get("rlimit_policy"),
            _rlimit_policy(loaded["resource_caps"]["proof_max_bytes"]),
        )
        or not static_v1.json_type_equal(
            session.get("execution_source_binding"), _execution_source_binding()
        )
        or session.get("transport_authority") != "TEST_ONLY"
        or session.get("transport_trusted_for_scientific_proof") is not False
        or session.get("production_eligible") is not False
    ):
        raise HierarchicalResumeRunnerError("session schema/static binding mismatch")
    start_claim = _read_json(root / START_CLAIM)
    expected_claim_fields = {
        "schema_version", "kind", "gate", "root", "root_identity",
        "root_lock_identity", "action", "nonce_hex", "pid", "terminal",
        "record_sha256",
    }
    nonce = start_claim.get("nonce_hex")
    if (
        set(start_claim) != expected_claim_fields
        or not static_v1.selfhash_valid(start_claim)
        or type(start_claim.get("schema_version")) is not int
        or start_claim.get("schema_version") != SCHEMA_VERSION
        or start_claim.get("kind") != "paper400-nested-width10-resume-stage-claim-v1"
        or start_claim.get("gate") != GATE
        or start_claim.get("root") != str(root)
        or not static_v1.json_type_equal(
            start_claim.get("root_identity"), _root_identity(root)
        )
        or not static_v1.json_type_equal(
            start_claim.get("root_lock_identity"), _lock_file_identity(root)
        )
        or type(nonce) is not str or len(nonce) != 64
        or any(character not in "0123456789abcdef" for character in nonce)
        or type(start_claim.get("pid")) is not int or start_claim.get("pid") <= 0
        or start_claim.get("action") != "start"
        or start_claim.get("terminal") is not False
        or start_claim.get("record_sha256") != session.get("start_claim_sha256")
    ):
        raise HierarchicalResumeRunnerError("start claim/session binding mismatch")
    with _fixed_environment():
        config, _ = controller._load_and_verify_config(root / RUNTIME_ROOT)
    expected_cnf = controller.stable_file_record(root / STATIC_DIMACS)
    if (
        config.get("self_sha256") != session.get("controller_config_sha256")
        or config.get("root") != str((root / RUNTIME_ROOT).resolve(strict=True))
        or config.get("cnf") != expected_cnf
        or config.get("controller_source", {}).get("sha256") != EXPECTED_CONTROLLER_SHA256
        or config.get("solver", {}).get("sha256") != EXPECTED_SOLVER_SHA256
        or config.get("solver_args") != session.get("solver_args")
        or config.get("proof_relative_path") != "proof.drat"
        or config.get("runtime_libraries_complete_attestation") is not True
    ):
        raise HierarchicalResumeRunnerError("DMTCP config/session binding mismatch")
    generation_zero = controller._generation_dir(root / RUNTIME_ROOT, 0)
    start = controller._active_commit(generation_zero, 0)
    if (
        start.get("kind") != "start.commit"
        or start.get("self_sha256") != session.get("controller_start_sha256")
        or not _peer_rlimit_record_valid(
            session.get("started_peer_rlimits"),
            pid=start.get("pid"),
            cap=session.get("proof_cap_bytes"),
        )
    ):
        raise HierarchicalResumeRunnerError("controller start/session mismatch")
    return loaded, session


def _action_static_kwargs(
    root: Path, static_kwargs: Mapping[str, Any],
) -> dict[str, Any]:
    checked = dict(static_kwargs)
    supplied = checked.get("campaign_verification_record")
    if supplied is not None:
        campaign = _read_json(root / STATIC_WIDTH10_CAMPAIGN)
        checked["campaign_verification_record"] = (
            static_v1._require_campaign_verification_record(
                supplied,
                campaign_manifest_sha256=campaign.get("manifest_sha256"),
            )
        )
        return checked

    record = _read_json(root / STATIC_COMMIT)
    parent = _read_json(root / STATIC_PARENT)
    width6_campaign = _read_json(root / STATIC_WIDTH6_CAMPAIGN)
    campaign = _read_json(root / STATIC_WIDTH10_CAMPAIGN)
    strict_base = checked.get("strict_base")
    if strict_base is None:
        strict_base = record.get("test_only") is False
    if type(strict_base) is not bool:
        raise HierarchicalResumeRunnerError("direct action strict-base mode malformed")
    caller_instance = checked.get("instance")
    if strict_base:
        if caller_instance is not None:
            raise HierarchicalResumeRunnerError(
                "production direct action cannot inject an instance"
            )
        replay_instance = nested.cube16.optimized.build_optimized_instance()
    else:
        if caller_instance is None:
            raise HierarchicalResumeRunnerError(
                "synthetic direct action requires an explicit instance"
            )
        replay_instance = caller_instance
    parent_cube_index = record.get("child", {}).get("parent_cube_index")
    verification = nested.verify_campaign_manifest(
        campaign,
        width6_campaign,
        parent,
        replay_instance,
        parent_cube_index=parent_cube_index,
        strict_base=strict_base,
    )
    if verification.get("valid") is not True:
        raise HierarchicalResumeRunnerError(
            "direct action failed full width-ten campaign replay: "
            f"{verification.get('binding_failures')}"
        )
    checked["campaign_verification_record"] = verification
    return checked


def start_root(root: Path, **static_kwargs: Any) -> dict[str, Any]:
    target = _existing_root(root)
    with _root_lock(target, exclusive=True):
        checked_static_kwargs = _action_static_kwargs(target, static_kwargs)
        return _start_root_locked(target, **checked_static_kwargs)


def _start_root_locked(root: Path, **static_kwargs: Any) -> dict[str, Any]:
    target = _existing_root(root)
    loaded = _load_static(target, **static_kwargs)
    if any((target / item).exists() for item in (
        START_CLAIM, SESSION_COMMIT, TERMINAL_CLAIM, FINAL_COMMIT,
    )):
        raise HierarchicalResumeRunnerError("root was already started or claimed")
    cpu = _single_cpu()
    cap = loaded["resource_caps"]["proof_max_bytes"]
    _require_unlimited_cpu_hard()
    claim = _claim(target / START_CLAIM, root=target, action="start")
    try:
        with _fixed_environment(), _inherited_solver_limits(cap):
            config = controller.initialize(
                target / RUNTIME_ROOT,
                cnf=target / STATIC_DIMACS,
                solver=SOLVER,
                dmtcp_prefix=DMTCP_PREFIX,
                solver_args=list(SOLVER_ARGS),
                runtime_libs=_runtime_libraries(),
                runtime_libs_complete=True,
            )
            started = controller.start(target / RUNTIME_ROOT)
        pid, ticks = started.get("pid"), started.get("proc_start_ticks")
        if (
            type(pid) is not int or type(ticks) is not int
            or not controller._pid_identity(pid, ticks)
            or os.sched_getaffinity(pid) != {cpu}
        ):
            raise HierarchicalResumeRunnerError("started peer identity/CPU mismatch")
        started_peer_rlimits = _verify_live_peer_rlimits(pid, cap)
        session = _session_value(
            target, loaded, claim, config, started, cpu,
            started_peer_rlimits,
        )
        _publish_json(target / SESSION_COMMIT, session)
        _load_session(target, **static_kwargs)
        return session
    except BaseException:
        if (target / RUNTIME_ROOT).exists():
            with contextlib.suppress(Exception), _fixed_environment():
                controller.checkpoint_stop(target / RUNTIME_ROOT)
        raise


def _manifest_claim_matches(
    directory: Path, claim_name: str, claim_kind: str,
    commit: Mapping[str, Any],
) -> dict[str, Any]:
    claim = controller.read_manifest(directory / claim_name, expected_kind=claim_kind)
    if commit.get("claim_sha256") != claim.get("self_sha256"):
        raise HierarchicalResumeRunnerError("controller claim/commit mismatch")
    return claim


RESTART_ALIAS_NAME = "dmtcp_restart_script.sh"
RESTART_TARGET_RE = re.compile(
    r"dmtcp_restart_script_([0-9a-f]+)-([0-9]+)-([0-9a-f]+)\.sh",
    re.ASCII,
)
GIVEN_CKPT_ASSIGNMENT_RE = re.compile(
    r"^[ \t]*given_ckpt_files[ \t]*=", re.ASCII,
)
RESTART_SCRIPT_MAX_BYTES = 16 << 20


def _stat_identity(info: os.stat_result) -> tuple[int, ...]:
    return (
        info.st_dev, info.st_ino, info.st_mode, info.st_uid, info.st_nlink,
        info.st_size, info.st_mtime_ns, info.st_ctime_ns,
    )


def _stable_restart_target(path: Path) -> tuple[str, os.stat_result]:
    try:
        fd = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    except OSError as exc:
        raise HierarchicalResumeRunnerError(
            "missing or unsafe DMTCP restart alias target"
        ) from exc
    try:
        before = os.fstat(fd)
        if (
            not stat.S_ISREG(before.st_mode)
            or stat.S_IMODE(before.st_mode) != 0o744
            or before.st_uid != os.geteuid()
            or before.st_nlink != 1
            or before.st_size > RESTART_SCRIPT_MAX_BYTES
        ):
            raise HierarchicalResumeRunnerError(
                "invalid DMTCP restart alias target inode"
            )
        payload = bytearray()
        while True:
            chunk = os.read(fd, 1 << 20)
            if not chunk:
                break
            payload.extend(chunk)
            if len(payload) > RESTART_SCRIPT_MAX_BYTES:
                raise HierarchicalResumeRunnerError(
                    "DMTCP restart target exceeds cap"
                )
        after = os.fstat(fd)
    finally:
        os.close(fd)
    if (
        _stat_identity(before) != _stat_identity(after)
        or len(payload) != before.st_size
    ):
        raise HierarchicalResumeRunnerError(
            "DMTCP restart target changed while reading"
        )
    try:
        text = bytes(payload).decode("ascii", "strict")
    except UnicodeDecodeError as exc:
        raise HierarchicalResumeRunnerError(
            "non-ASCII DMTCP restart target"
        ) from exc
    return text, before


def _validate_restart_pair(
    alias: Path, expected_image: Path,
) -> tuple[Path, int]:
    if alias.name != RESTART_ALIAS_NAME or not expected_image.is_absolute():
        raise HierarchicalResumeRunnerError(
            "invalid DMTCP restart-pair binding"
        )
    try:
        before = os.stat(alias, follow_symlinks=False)
    except FileNotFoundError as exc:
        raise HierarchicalResumeRunnerError(
            "missing DMTCP restart alias"
        ) from exc
    if (
        not stat.S_ISLNK(before.st_mode)
        or stat.S_IMODE(before.st_mode) != 0o777
        or before.st_uid != os.geteuid()
        or before.st_nlink != 1
    ):
        raise HierarchicalResumeRunnerError(
            "invalid DMTCP restart alias inode"
        )
    try:
        target_name = os.readlink(alias)
        after = os.stat(alias, follow_symlinks=False)
    except OSError as exc:
        raise HierarchicalResumeRunnerError(
            "unstable DMTCP restart alias"
        ) from exc
    if _stat_identity(before) != _stat_identity(after):
        raise HierarchicalResumeRunnerError(
            "DMTCP restart alias changed while reading"
        )
    try:
        target_name.encode("ascii", "strict")
    except UnicodeEncodeError as exc:
        raise HierarchicalResumeRunnerError(
            "non-ASCII DMTCP restart alias target"
        ) from exc
    if (
        Path(target_name).name != target_name
        or RESTART_TARGET_RE.fullmatch(target_name) is None
    ):
        raise HierarchicalResumeRunnerError(
            "invalid DMTCP restart alias target token"
        )
    target = alias.parent / target_name
    script, target_info = _stable_restart_target(target)
    try:
        expected_image_text = str(expected_image)
        expected_image_text.encode("ascii", "strict")
    except UnicodeEncodeError as exc:
        raise HierarchicalResumeRunnerError(
            "non-ASCII committed checkpoint image path"
        ) from exc
    assignments = [
        line for line in script.splitlines()
        if GIVEN_CKPT_ASSIGNMENT_RE.match(line) is not None
    ]
    expected_assignment = f'given_ckpt_files=" {expected_image_text}"'
    if assignments != [expected_assignment]:
        raise HierarchicalResumeRunnerError(
            "DMTCP restart target given_ckpt_files mismatch"
        )
    return target, target_info.st_size


def _generation_metadata_bytes(
    directory: Path, image_paths: set[Path], *, generation: int,
) -> int:
    if type(generation) is not int or not 0 <= generation <= 999999:
        raise HierarchicalResumeRunnerError("checkpoint generation is invalid")
    images_dir = directory / "images"
    try:
        images_info = os.stat(images_dir, follow_symlinks=False)
    except FileNotFoundError as exc:
        raise HierarchicalResumeRunnerError(
            "checkpoint images directory is missing"
        ) from exc
    if (
        not stat.S_ISDIR(images_info.st_mode)
        or stat.S_IMODE(images_info.st_mode) != 0o700
        or images_info.st_uid != os.geteuid()
    ):
        raise HierarchicalResumeRunnerError(
            "checkpoint images directory identity is invalid"
        )
    if len(image_paths) not in {0, 1}:
        raise HierarchicalResumeRunnerError(
            "single-process checkpoint image layout is invalid"
        )
    for image in image_paths:
        if (
            image.parent != images_dir
            or Path(image.name).name != image.name
            or not image.name.startswith("ckpt_")
            or not image.name.endswith(".dmtcp")
        ):
            raise HierarchicalResumeRunnerError(
                "committed checkpoint image escaped its generation"
            )
    expected_entries = set(image_paths)
    allowed_alias: Path | None = None
    if generation == 0 and image_paths:
        allowed_alias = images_dir / RESTART_ALIAS_NAME
        target, _ = _validate_restart_pair(
            allowed_alias, next(iter(image_paths)),
        )
        expected_entries.update({allowed_alias, target})
    actual_entries = set(images_dir.iterdir())
    if actual_entries != expected_entries:
        label = "generation-zero alias pair" if generation == 0 else "resumed image-only"
        raise HierarchicalResumeRunnerError(
            f"checkpoint {label} layout mismatch"
        )
    total = 0
    for candidate in directory.rglob("*"):
        info = os.stat(candidate, follow_symlinks=False)
        if stat.S_ISLNK(info.st_mode):
            if candidate != allowed_alias:
                raise HierarchicalResumeRunnerError(
                    "unexpected symlink in checkpoint generation"
                )
            continue
        if stat.S_ISREG(info.st_mode) and candidate not in image_paths:
            total += info.st_size
    return total


def _runtime_restart_pair(
    runtime: Path, expected_image: Path | None,
) -> tuple[Path | None, int]:
    entries = list(runtime.iterdir())
    restart_entries = {
        candidate for candidate in entries
        if candidate.name.startswith("dmtcp_restart_script")
    }
    symlinks = {
        candidate for candidate in entries
        if stat.S_ISLNK(os.stat(candidate, follow_symlinks=False).st_mode)
    }
    if expected_image is None:
        if restart_entries or symlinks:
            raise HierarchicalResumeRunnerError(
                "runtime restart pair exists without a resumed checkpoint"
            )
        return None, 0
    alias = runtime / RESTART_ALIAS_NAME
    target, target_bytes = _validate_restart_pair(alias, expected_image)
    if restart_entries != {alias, target} or symlinks != {alias}:
        raise HierarchicalResumeRunnerError(
            "runtime latest restart pair is not unique"
        )
    return target, target_bytes


def _writable_holders(path: Path) -> list[int]:
    wanted = os.stat(path, follow_symlinks=False)
    if not stat.S_ISREG(wanted.st_mode):
        raise HierarchicalResumeRunnerError("proof holder target is not regular")
    identity = lambda item: (
        item.st_dev, item.st_ino, item.st_mode, item.st_uid, item.st_nlink,
        item.st_size, item.st_mtime_ns, item.st_ctime_ns,
    )
    holders: set[int] = set()
    needs_privileged_scan = False
    for process in Path("/proc").iterdir():
        if not process.name.isdigit():
            continue
        try:
            status_lines = (process / "status").read_text(
                encoding="ascii",
            ).splitlines()
            uid_lines = [
                line for line in status_lines if line.startswith("Uid:")
            ]
            if len(uid_lines) != 1:
                raise HierarchicalResumeRunnerError(
                    "ambiguous process UID status"
                )
            uid_fields = uid_lines[0].split()[1:]
            if len(uid_fields) != 4:
                raise HierarchicalResumeRunnerError(
                    "malformed process UID status"
                )
            process_effective_uid = int(uid_fields[1])
        except (FileNotFoundError, ProcessLookupError):
            continue
        except PermissionError as exc:
            raise HierarchicalResumeRunnerError(
                "cannot inspect process UID status"
            ) from exc
        except ValueError as exc:
            raise HierarchicalResumeRunnerError(
                "non-integer process UID status"
            ) from exc
        if process_effective_uid != wanted.st_uid:
            # A different-euid process cannot acquire this mode-0600 inode
            # inside the canonical mode-0700 result root.  Same-euid
            # descriptor visibility remains fail-closed below.
            continue
        try:
            descriptors = list((process / "fd").iterdir())
        except (FileNotFoundError, ProcessLookupError):
            continue
        except PermissionError:
            needs_privileged_scan = True
            continue
        for descriptor in descriptors:
            try:
                observed = os.stat(descriptor)
                if (observed.st_dev, observed.st_ino) != (wanted.st_dev, wanted.st_ino):
                    continue
                lines = (process / "fdinfo" / descriptor.name).read_text(
                    encoding="ascii",
                ).splitlines()
                flags = [line for line in lines if line.startswith("flags:")]
                if len(flags) != 1:
                    raise HierarchicalResumeRunnerError("ambiguous /proc fd flags")
                value = int(flags[0].split(":", 1)[1].strip(), 8)
                if value & os.O_ACCMODE != os.O_RDONLY:
                    holders.add(int(process.name))
            except (FileNotFoundError, ProcessLookupError):
                continue
            except PermissionError:
                needs_privileged_scan = True
                continue
    if needs_privileged_scan:
        # Some login/session processes are deliberately non-dumpable, so a
        # same-UID caller cannot inspect their /proc/<pid>/fd directories.
        # A pinned root lsof pass over the exact inode closes that visibility
        # gap.  Treating every open descriptor as writable is conservative.
        holders.update(_privileged_open_holders(path))
    after = os.stat(path, follow_symlinks=False)
    if identity(wanted) != identity(after):
        raise HierarchicalResumeRunnerError(
            "proof changed during writable-holder scan"
        )
    return sorted(holders)


def _verify_privileged_scanner_binary(
    path: Path, expected_sha256: str, *, require_setuid: bool,
) -> None:
    descriptor = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        before = os.fstat(descriptor)
        if (
            not stat.S_ISREG(before.st_mode)
            or before.st_uid != 0
            or before.st_nlink != 1
            or before.st_mode & 0o022
            or not before.st_mode & stat.S_IXUSR
            or require_setuid is not bool(before.st_mode & stat.S_ISUID)
            or before.st_size > (16 << 20)
        ):
            raise HierarchicalResumeRunnerError(
                "privileged descriptor scanner binary is unsafe"
            )
        digest = hashlib.sha256()
        observed = 0
        while True:
            chunk = os.read(descriptor, 1 << 20)
            if not chunk:
                break
            observed += len(chunk)
            digest.update(chunk)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    if (
        _stat_identity(before) != _stat_identity(after)
        or observed != before.st_size
        or digest.hexdigest() != expected_sha256
    ):
        raise HierarchicalResumeRunnerError(
            "privileged descriptor scanner binary binding mismatch"
        )


def _privileged_open_holders(path: Path) -> list[int]:
    _verify_privileged_scanner_binary(
        SUDO, EXPECTED_SUDO_SHA256, require_setuid=True,
    )
    _verify_privileged_scanner_binary(
        LSOF, EXPECTED_LSOF_SHA256, require_setuid=False,
    )
    argv = [
        str(SUDO), "-n", "--", str(LSOF),
        "-nP", "-w", "-t", "--", str(path),
    ]
    try:
        result = subprocess.run(
            argv,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=30,
            check=False,
            env={"LANG": "C", "LC_ALL": "C", "PATH": "/usr/bin:/bin"},
        )
    except (OSError, subprocess.SubprocessError) as exc:
        raise HierarchicalResumeRunnerError(
            "privileged descriptor scan failed"
        ) from exc
    if result.returncode == 1 and result.stdout == b"" and result.stderr == b"":
        return []
    if result.returncode != 0 or result.stderr:
        raise HierarchicalResumeRunnerError(
            "privileged descriptor scan returned an error"
        )
    try:
        lines = result.stdout.decode("ascii", "strict").splitlines()
        holders = sorted({int(line) for line in lines})
    except (UnicodeDecodeError, ValueError) as exc:
        raise HierarchicalResumeRunnerError(
            "privileged descriptor scan output is malformed"
        ) from exc
    if (
        not lines or len(result.stdout) > (1 << 20)
        or any(not line or not line.isdecimal() for line in lines)
        or any(pid <= 0 for pid in holders)
    ):
        raise HierarchicalResumeRunnerError(
            "privileged descriptor scan output is malformed"
        )
    return holders


def validate_transport_chain(
    root: Path, session: Mapping[str, Any], caps: Mapping[str, Any],
    *, requirement: str,
) -> dict[str, Any]:
    if requirement not in CHAIN_REQUIREMENTS:
        raise HierarchicalResumeRunnerError("unknown transport-chain requirement")
    runtime = root / RUNTIME_ROOT
    with _fixed_environment():
        config, _ = controller._load_and_verify_config(runtime)
        numbers = controller._generation_numbers(runtime)
        if not numbers or numbers != list(range(len(numbers))):
            raise HierarchicalResumeRunnerError("generation chain is not contiguous")
        if len(numbers) > caps["checkpoint_generation_max_count"]:
            raise HierarchicalResumeRunnerError("generation count exceeds cap")
        generations: list[dict[str, Any]] = []
        previous_checkpoint: Mapping[str, Any] | None = None
        total_images = 0
        total_metadata = 0
        latest_checkpoint: Mapping[str, Any] | None = None
        latest_resumed_checkpoint_image: Path | None = None
        latest_resumed_checkpoint_generation: int | None = None
        for generation in numbers:
            directory = controller._generation_dir(runtime, generation)
            poison = controller._claim_without_commit(directory)
            if poison is not None:
                raise HierarchicalResumeRunnerError(
                    f"generation {generation} poisoned by {poison}"
                )
            if (directory / "stale-tail.commit.json").exists():
                raise HierarchicalResumeRunnerError("stale-tail injection forbidden")
            active = controller._active_commit(directory, generation)
            if generation == 0:
                if active.get("kind") != "start.commit":
                    raise HierarchicalResumeRunnerError("generation zero is not start")
                start_claim = _manifest_claim_matches(
                    directory, "start.claim.json", "start.claim", active,
                )
                if (
                    start_claim.get("init_manifest_sha256")
                    != config.get("self_sha256")
                    or not _peer_rlimit_record_valid(
                        session.get("started_peer_rlimits"),
                        pid=active.get("pid"),
                        cap=session.get("proof_cap_bytes"),
                    )
                ):
                    raise HierarchicalResumeRunnerError("start/config mismatch")
            else:
                if active.get("kind") != "resume.commit" or previous_checkpoint is None:
                    raise HierarchicalResumeRunnerError("resume predecessor missing")
                _manifest_claim_matches(directory, "resume.claim.json", "resume.claim", active)
                if (
                    active.get("source_generation") != generation - 1
                    or active.get("source_checkpoint_manifest_sha256")
                    != previous_checkpoint.get("self_sha256")
                    or active.get("proof_prefix_revalidated") is not True
                ):
                    raise HierarchicalResumeRunnerError("resume/checkpoint mismatch")
                admission_claim = _read_json(
                    root / _resume_claim_path(generation)
                )
                admission = _read_json(
                    root / _resume_commit_path(generation)
                )
                claim_fields = {
                    "schema_version", "kind", "gate", "root",
                    "root_identity", "root_lock_identity", "action",
                    "nonce_hex", "pid", "terminal", "record_sha256",
                }
                admission_fields = {
                    "schema_version", "kind", "gate", "root", "generation",
                    "session_sha256", "source_checkpoint_sha256",
                    "source_proof_prefix", "claim_sha256",
                    "resume_manifest_sha256", "expected_single_cpu",
                    "resumed_peer_rlimits", "transport_authority",
                    "production_eligible", "record_sha256",
                }
                nonce = admission_claim.get("nonce_hex")
                if (
                    set(admission_claim) != claim_fields
                    or not static_v1.selfhash_valid(admission_claim)
                    or admission_claim.get("schema_version") != SCHEMA_VERSION
                    or admission_claim.get("kind")
                    != "paper400-nested-width10-resume-stage-claim-v1"
                    or admission_claim.get("gate") != GATE
                    or admission_claim.get("root") != str(root)
                    or not static_v1.json_type_equal(
                        admission_claim.get("root_identity"), _root_identity(root)
                    )
                    or not static_v1.json_type_equal(
                        admission_claim.get("root_lock_identity"),
                        _lock_file_identity(root),
                    )
                    or admission_claim.get("action")
                    != f"resume-{generation:06d}"
                    or admission_claim.get("terminal") is not False
                    or type(admission_claim.get("pid")) is not int
                    or admission_claim.get("pid") <= 0
                    or type(nonce) is not str or len(nonce) != 64
                    or any(character not in "0123456789abcdef" for character in nonce)
                    or set(admission) != admission_fields
                    or not static_v1.selfhash_valid(admission)
                    or admission.get("schema_version") != SCHEMA_VERSION
                    or admission.get("kind")
                    != "paper400-nested-width10-resume-admission-v1"
                    or admission.get("gate") != GATE
                    or admission.get("root") != str(root)
                    or admission.get("generation") != generation
                    or admission.get("session_sha256")
                    != session.get("record_sha256")
                    or admission.get("source_checkpoint_sha256")
                    != previous_checkpoint.get("self_sha256")
                    or not static_v1.json_type_equal(
                        admission.get("source_proof_prefix"),
                        previous_checkpoint.get("proof_prefix"),
                    )
                    or admission.get("claim_sha256")
                    != admission_claim.get("record_sha256")
                    or admission.get("resume_manifest_sha256")
                    != active.get("self_sha256")
                    or admission.get("expected_single_cpu")
                    != session.get("expected_single_cpu")
                    or not _peer_rlimit_record_valid(
                        admission.get("resumed_peer_rlimits"),
                        pid=active.get("pid"), cap=session.get("proof_cap_bytes"),
                    )
                    or admission.get("transport_authority") != "TEST_ONLY"
                    or admission.get("production_eligible") is not False
                ):
                    raise HierarchicalResumeRunnerError(
                        "resume admission/generation mismatch"
                    )
            pid, ticks = active.get("pid"), active.get("proc_start_ticks")
            port = active.get("coordinator_port")
            if (
                type(pid) is not int or pid <= 0
                or type(ticks) is not int or ticks <= 0
                or type(port) is not int or not 1 <= port <= 65535
            ):
                raise HierarchicalResumeRunnerError(
                    "active process/coordinator identity is invalid"
                )
            alive = controller._pid_identity(pid, ticks)
            if alive:
                if os.sched_getaffinity(pid) != {session["expected_single_cpu"]}:
                    raise HierarchicalResumeRunnerError("live solver escaped singleton CPU")
                _verify_live_peer_rlimits(pid, session["proof_cap_bytes"])
            checkpoint: Mapping[str, Any] | None = None
            path = directory / "checkpoint.commit.json"
            image_paths: set[Path] = set()
            if path.exists():
                checkpoint = controller._checkpoint_commit(directory, generation)
                checkpoint_claim = _manifest_claim_matches(
                    directory, "checkpoint.claim.json", "checkpoint.claim", checkpoint,
                )
                checkpoint_claim_fields = {
                    "schema_version", "kind", "authority", "controller",
                    "created_utc", "generation", "active_manifest_sha256",
                    "method", "self_sha256",
                }
                checkpoint_fields = {
                    "schema_version", "kind", "authority", "controller",
                    "created_utc", "generation", "claim_sha256",
                    "command_returncode", "command_stderr", "command_stdout",
                    "images", "proof_prefix", "single_writer_stopped",
                    "self_sha256",
                }
                if (
                    set(checkpoint_claim) != checkpoint_claim_fields
                    or set(checkpoint) != checkpoint_fields
                    or type(checkpoint_claim.get("generation")) is not int
                    or checkpoint_claim.get("generation") != generation
                    or checkpoint_claim.get("method")
                    != "dmtcp_command --kcheckpoint"
                    or checkpoint_claim.get("active_manifest_sha256")
                    != active.get("self_sha256")
                    or type(checkpoint.get("generation")) is not int
                    or checkpoint.get("generation") != generation
                    or type(checkpoint.get("command_returncode")) is not int
                    or checkpoint.get("command_returncode") not in {0, 2}
                    or checkpoint.get("single_writer_stopped") is not True
                ):
                    raise HierarchicalResumeRunnerError(
                        "checkpoint schema/active binding mismatch"
                    )
                stdout_path = controller.verify_file_record(
                    checkpoint["command_stdout"], root=runtime,
                )
                stderr_path = controller.verify_file_record(
                    checkpoint["command_stderr"], root=runtime,
                )
                stdout_bytes, stderr_bytes = (
                    stdout_path.read_bytes(), stderr_path.read_bytes(),
                )
                if (
                    len(stdout_bytes) > 4096
                    or len(stderr_bytes) > 4096
                    or not controller._kc_semantics(
                        checkpoint["command_returncode"],
                        stdout_bytes,
                        stderr_bytes,
                    )
                ):
                    raise HierarchicalResumeRunnerError(
                        "checkpoint command semantics mismatch"
                    )
                image_paths = set(controller._verify_checkpoint_images(runtime, checkpoint))
                if len(image_paths) > caps["checkpoint_images_per_generation_max"]:
                    raise HierarchicalResumeRunnerError("checkpoint image count exceeds cap")
                for image in image_paths:
                    size = image.stat().st_size
                    if size > caps["checkpoint_image_max_bytes"]:
                        raise HierarchicalResumeRunnerError("checkpoint image exceeds cap")
                    total_images += size
                if generation >= 1:
                    latest_resumed_checkpoint_image = next(iter(image_paths))
                    latest_resumed_checkpoint_generation = generation
            metadata = _generation_metadata_bytes(
                directory, image_paths, generation=generation,
            )
            if metadata > caps["checkpoint_generation_metadata_max_bytes"]:
                raise HierarchicalResumeRunnerError("generation metadata exceeds cap")
            total_metadata += metadata
            if generation != numbers[-1] and checkpoint is None:
                raise HierarchicalResumeRunnerError("consumed generation lacks checkpoint")
            generations.append({
                "generation": generation,
                "active_kind": active.get("kind"),
                "active_manifest_sha256": active.get("self_sha256"),
                "checkpoint_manifest_sha256": (
                    None if checkpoint is None else checkpoint.get("self_sha256")
                ),
                "pid": pid,
                "proc_start_ticks": ticks,
                "coordinator_port": port,
                "pid_identity_alive": alive,
                "metadata_bytes": metadata,
                "image_bytes": sum(path.stat().st_size for path in image_paths),
            })
            previous_checkpoint = checkpoint
            latest_checkpoint = checkpoint
        _, runtime_restart_metadata = _runtime_restart_pair(
            runtime, latest_resumed_checkpoint_image,
        )
        if latest_resumed_checkpoint_generation is not None:
            generation_record = generations[latest_resumed_checkpoint_generation]
            combined_metadata = (
                generation_record["metadata_bytes"] + runtime_restart_metadata
            )
            if combined_metadata > caps["checkpoint_generation_metadata_max_bytes"]:
                raise HierarchicalResumeRunnerError(
                    "resumed generation metadata plus runtime restart target exceeds cap"
                )
            generation_record["metadata_bytes"] = combined_metadata
            total_metadata += runtime_restart_metadata
        elif runtime_restart_metadata != 0:
            raise HierarchicalResumeRunnerError(
                "unbound runtime restart target metadata"
            )
        latest = generations[-1]
        state = (
            "CHECKPOINTED" if latest_checkpoint is not None
            else "RUNNING" if latest["pid_identity_alive"]
            else "INACTIVE_UNCHECKPOINTED"
        )
        allowed_states = {
            CHAIN_REQUIRE_STATUS: {"RUNNING", "CHECKPOINTED", "INACTIVE_UNCHECKPOINTED"},
            CHAIN_REQUIRE_CHECKPOINTED: {"CHECKPOINTED"},
            CHAIN_REQUIRE_INACTIVE: {"INACTIVE_UNCHECKPOINTED"},
            CHAIN_REQUIRE_STOPPED: {"CHECKPOINTED", "INACTIVE_UNCHECKPOINTED"},
        }[requirement]
        if state not in allowed_states:
            raise HierarchicalResumeRunnerError(
                f"transport state {state} rejected by {requirement}"
            )
        proof_record = None
        proof_physical = None
        holders: list[int] | None = None
        if requirement != CHAIN_REQUIRE_STATUS:
            if state == "CHECKPOINTED":
                assert latest_checkpoint is not None
                controller._validate_proof_before_resume(
                    runtime, latest_checkpoint, None,
                )
            proof_record = controller.stable_file_record(
                runtime / "proof.drat", relative_to=runtime,
            )
            if (
                state == "CHECKPOINTED"
                and proof_record != latest_checkpoint.get("proof_prefix")
            ):
                raise HierarchicalResumeRunnerError(
                    "checkpoint proof prefix mismatch"
                )
            if proof_record["bytes"] > caps["proof_max_bytes"]:
                raise HierarchicalResumeRunnerError("stopped proof exceeds cap")
            proof_physical = v2._physical_record(
                runtime / "proof.drat", root, "raw-binary-drat",
                cap=caps["proof_max_bytes"],
            )
            proof_info = os.stat(runtime / "proof.drat", follow_symlinks=False)
            if (
                proof_physical.get("relative_path")
                != (RUNTIME_ROOT / "proof.drat").as_posix()
                or proof_physical.get("file_sha256") != proof_record["sha256"]
                or proof_physical.get("bytes") != proof_record["bytes"]
                or proof_physical.get("mode") != 0o600
                or proof_physical.get("links") != 1
                or proof_physical.get("device") != proof_info.st_dev
                or proof_physical.get("inode") != proof_info.st_ino
                or proof_info.st_nlink != 1
                or proof_info.st_uid != os.geteuid()
            ):
                raise HierarchicalResumeRunnerError(
                    "stopped proof physical binding mismatch"
                )
            proof_physical = {
                **proof_physical,
                "uid": int(proof_info.st_uid),
            }
            holders = _writable_holders(runtime / "proof.drat")
            if holders:
                raise HierarchicalResumeRunnerError(
                    f"stopped proof still has writable holders: {holders}"
                )
        if total_images > caps["checkpoint_image_budget_max_bytes"]:
            raise HierarchicalResumeRunnerError("cumulative images exceed cap")
        if total_metadata > caps["checkpoint_metadata_budget_max_bytes"]:
            raise HierarchicalResumeRunnerError("cumulative metadata exceeds cap")
        return seal({
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-nested-width10-dmtcp-chain-replay-v1",
            "gate": GATE,
            "root": str(root),
            "controller_config_sha256": config["self_sha256"],
            "generations": generations,
            "state": state,
            "latest_checkpoint_sha256": (
                None if latest_checkpoint is None else latest_checkpoint["self_sha256"]
            ),
            "latest_proof_prefix": proof_record,
            "latest_proof_physical": proof_physical,
            "writable_holders": holders,
            "total_checkpoint_image_bytes": total_images,
            "total_generation_metadata_bytes": total_metadata,
            "transport_authority": "TEST_ONLY",
            "transport_trusted_for_scientific_proof": False,
        })


def checkpoint_stop_root(root: Path, **static_kwargs: Any) -> dict[str, Any]:
    target = _existing_root(root)
    with _root_lock(target, exclusive=True):
        checked_static_kwargs = _action_static_kwargs(target, static_kwargs)
        return _checkpoint_stop_root_locked(target, **checked_static_kwargs)


def _checkpoint_stop_root_locked(root: Path, **static_kwargs: Any) -> dict[str, Any]:
    target = _existing_root(root)
    loaded, session = _load_session(target, **static_kwargs)
    if (target / TERMINAL_CLAIM).exists():
        raise HierarchicalResumeRunnerError("terminal stage already claimed")
    if _single_cpu() != session["expected_single_cpu"]:
        raise HierarchicalResumeRunnerError("checkpoint CPU differs from session CPU")
    with _fixed_environment():
        checkpoint = controller.checkpoint_stop(target / RUNTIME_ROOT)
    chain = validate_transport_chain(
        target, session, loaded["record"]["resource_policy"],
        requirement=CHAIN_REQUIRE_CHECKPOINTED,
    )
    if checkpoint.get("self_sha256") != chain["latest_checkpoint_sha256"]:
        raise HierarchicalResumeRunnerError("checkpoint result/chain mismatch")
    return chain


def _resume_claim_path(generation: int) -> Path:
    if type(generation) is not int or not 1 <= generation <= 999999:
        raise HierarchicalResumeRunnerError("resume generation out of range")
    return RESUME_ADMISSIONS / f"{generation:06d}.claim"


def _resume_commit_path(generation: int) -> Path:
    return RESUME_ADMISSIONS / f"{generation:06d}.json"


def resume_root(root: Path, **static_kwargs: Any) -> dict[str, Any]:
    target = _existing_root(root)
    with _root_lock(target, exclusive=True):
        checked_static_kwargs = _action_static_kwargs(target, static_kwargs)
        return _resume_root_locked(target, **checked_static_kwargs)


def _resume_root_locked(root: Path, **static_kwargs: Any) -> dict[str, Any]:
    target = _existing_root(root)
    loaded, session = _load_session(target, **static_kwargs)
    if (target / TERMINAL_CLAIM).exists():
        raise HierarchicalResumeRunnerError("terminal stage already claimed")
    cpu = _single_cpu()
    if cpu != session["expected_single_cpu"]:
        raise HierarchicalResumeRunnerError("resume CPU differs from session CPU")
    before = validate_transport_chain(
        target, session, loaded["record"]["resource_policy"],
        requirement=CHAIN_REQUIRE_CHECKPOINTED,
    )
    generation = before["generations"][-1]["generation"] + 1
    if generation >= loaded["resource_caps"]["checkpoint_generation_max_count"]:
        raise HierarchicalResumeRunnerError("resume would exceed generation cap")
    claim_path = target / _resume_claim_path(generation)
    commit_path = target / _resume_commit_path(generation)
    if claim_path.exists() or commit_path.exists():
        raise HierarchicalResumeRunnerError("checkpoint resume already claimed")
    cap = loaded["resource_caps"]["proof_max_bytes"]
    _require_unlimited_cpu_hard()
    claim = _claim(claim_path, root=target, action=f"resume-{generation:06d}")
    with _fixed_environment(), _inherited_solver_limits(cap):
        resumed = controller.resume(target / RUNTIME_ROOT)
    pid, ticks = resumed.get("pid"), resumed.get("proc_start_ticks")
    if (
        type(pid) is not int or type(ticks) is not int
        or not controller._pid_identity(pid, ticks)
        or os.sched_getaffinity(pid) != {cpu}
    ):
        raise HierarchicalResumeRunnerError("resumed peer identity/CPU mismatch")
    peer_limits = _verify_live_peer_rlimits(pid, cap)
    record = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-nested-width10-resume-admission-v1",
        "gate": GATE,
        "root": str(target),
        "generation": generation,
        "session_sha256": session["record_sha256"],
        "source_checkpoint_sha256": before["latest_checkpoint_sha256"],
        "source_proof_prefix": before["latest_proof_prefix"],
        "claim_sha256": claim["record_sha256"],
        "resume_manifest_sha256": resumed["self_sha256"],
        "expected_single_cpu": cpu,
        "resumed_peer_rlimits": peer_limits,
        "transport_authority": "TEST_ONLY",
        "production_eligible": False,
    })
    _publish_json(commit_path, record)
    return record


def status_root(root: Path, **static_kwargs: Any) -> dict[str, Any]:
    target = _existing_root(root)
    with _root_lock(target, exclusive=False):
        checked_static_kwargs = _action_static_kwargs(target, static_kwargs)
        if (target / TRANSPORT_PRUNE_COMMIT).exists():
            return _pruned_status_locked(target, **checked_static_kwargs)
        if (target / TRANSPORT_PRUNE_CLAIM).exists():
            raise HierarchicalResumeRunnerError(
                "transport prune is incomplete; rerun prune-transport"
            )
        return _status_root_locked(target, **checked_static_kwargs)


def _status_root_locked(root: Path, **static_kwargs: Any) -> dict[str, Any]:
    target = _existing_root(root)
    loaded, session = _load_session(target, **static_kwargs)
    chain = validate_transport_chain(
        target, session, loaded["record"]["resource_policy"],
        requirement=CHAIN_REQUIRE_STATUS,
    )
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-nested-width10-resume-status-v1",
        "gate": GATE,
        "root": str(target),
        "resume_static_sha256": loaded["record"]["record_sha256"],
        "session_sha256": session["record_sha256"],
        "chain": chain,
        "terminal_claimed": (target / TERMINAL_CLAIM).exists(),
        "terminal_committed": (target / FINAL_COMMIT).exists(),
        "production_eligible": False,
    })


def _artifact_reference(record: Mapping[str, Any]) -> dict[str, Any]:
    return {
        key: record[key] for key in (
            "role", "relative_path", "file_sha256", "bytes",
        )
    }


def _copy_once(
    source: Path, destination: Path, *, root: Path, expected: Mapping[str, Any],
    cap: int,
) -> dict[str, Any]:
    """Copy a stopped proof into an inode DMTCP can no longer mutate."""

    source_fd = os.open(source, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    output_fd = -1
    private_name = ""
    try:
        before = os.fstat(source_fd)
        if (
            not stat.S_ISREG(before.st_mode) or before.st_size > cap
            or before.st_size != expected.get("bytes")
        ):
            raise HierarchicalResumeRunnerError("DRAT handoff source invalid")
        output_fd, private_name = v2._create_private_output(
            destination.parent, destination.name,
        )
        digest = hashlib.sha256()
        total = 0
        while True:
            chunk = os.read(source_fd, 8 << 20)
            if not chunk:
                break
            total += len(chunk)
            if total > cap:
                raise HierarchicalResumeRunnerError("DRAT handoff exceeds cap")
            digest.update(chunk)
            v2._write_all(output_fd, chunk)
        os.fsync(output_fd)
        after = os.fstat(source_fd)
        identity = lambda item: (
            item.st_dev, item.st_ino, item.st_mode, item.st_uid, item.st_size,
            item.st_mtime_ns, item.st_ctime_ns,
        )
        if (
            identity(before) != identity(after)
            or total != expected.get("bytes")
            or digest.hexdigest() != expected.get("file_sha256")
        ):
            raise HierarchicalResumeRunnerError("DRAT changed during checked copy")
        v2._publish_private_output(
            destination.parent, private_name, output_fd, destination.name,
            expected_sha256=digest.hexdigest(), expected_bytes=total,
        )
        output_fd = -1
        record = v2._physical_record(
            destination, root, "raw-binary-drat", cap=cap,
        )
        if (
            record["file_sha256"] != expected.get("file_sha256")
            or record["bytes"] != expected.get("bytes")
            or record["links"] != 1
        ):
            raise HierarchicalResumeRunnerError("copied DRAT binding mismatch")
        return record
    finally:
        os.close(source_fd)
        if output_fd >= 0:
            v2._discard_private(destination.parent, private_name, output_fd)


def _child_checker_view(loaded: Mapping[str, Any]) -> dict[str, Any]:
    child = loaded["record"]["child"]
    return {
        "cube_index": child["child_index"],
        "cube_dimacs_sha256": child["child_dimacs_sha256"],
        "cube_dimacs_bytes": child["child_dimacs_bytes"],
    }


def _run_checker(
    *, root: Path, loaded: Mapping[str, Any], role: str,
    proof_path: Path, proof_record: Mapping[str, Any], proof_cap: int,
    output_fd: int | None = None,
) -> tuple[dict[str, Any], bytes, bytes, dict[str, Any]]:
    if role in {"drat-verify", "drat-to-lrat", "final-drat-replay"}:
        checker_path = DRAT_CHECKER
        checker_sha = EXPECTED_DRAT_SHA256
        marker = b"s VERIFIED"
    elif role in {"lrat-check", "final-lrat-replay"}:
        checker_path = LRAT_CHECKER
        checker_sha = EXPECTED_LRAT_SHA256
        marker = b"c VERIFIED"
    else:
        raise HierarchicalResumeRunnerError("unknown checker role")
    return proof_helper._run_checker(
        target=root, cube=_child_checker_view(loaded), role=role,
        checker_path=checker_path, checker_sha256=checker_sha,
        proof_path=proof_path, proof_record=proof_record,
        proof_cap=proof_cap, marker=marker, output_fd=output_fd,
    )


def _proof_identity(loaded: Mapping[str, Any]) -> dict[str, Any]:
    identity = proof_v1.expected_identity(
        loaded["campaign"],
        loaded["record"]["child"]["global_leaf_index"],
    )
    static_child = loaded["record"]["child"]
    for key in (
        "global_leaf_index", "global_leaf_id", "leaf_sha256",
        "width6_leaf_index", "width6_leaf_sha256", "local_child_index",
        "child_index", "child_id", "child_sha256", "child_cnf_sha256",
        "child_dimacs_sha256", "combined_unit_clauses",
        "combined_unit_clauses_sha256",
    ):
        if not static_v1.json_type_equal(static_child.get(key), identity.get(key)):
            raise HierarchicalResumeRunnerError(
                f"static/proof identity mismatch for {key}"
            )
    return identity


def _coordinator_observation(chain: Mapping[str, Any]) -> dict[str, Any]:
    state = chain.get("state")
    if state == proof_v1.TRANSPORT_STATE_CHECKPOINTED:
        return {
            "attempted": False,
            "reachable": None,
            "peer_count": None,
            "running": None,
        }
    if state != proof_v1.TRANSPORT_STATE_INACTIVE:
        raise HierarchicalResumeRunnerError(
            "coordinator observation requires a stopped transport"
        )
    latest = chain.get("generations", [])[-1]
    if latest.get("pid_identity_alive") is not False:
        raise HierarchicalResumeRunnerError(
            "inactive transport PID identity is still alive"
        )
    try:
        with _fixed_environment():
            peers, running = controller._query_status(
                DMTCP_PREFIX / "bin/dmtcp_command",
                latest["coordinator_port"],
                timeout=2.0,
            )
    except (
        controller.ResumeControllerError,
        subprocess.SubprocessError,
        OSError,
    ):
        return {
            "attempted": True,
            "reachable": False,
            "peer_count": None,
            "running": None,
        }
    if peers != 0 or running:
        raise HierarchicalResumeRunnerError(
            "inactive coordinator still reports an active peer"
        )
    return {
        "attempted": True,
        "reachable": True,
        "peer_count": peers,
        "running": running,
    }


def _transport_quiescence(
    before: Mapping[str, Any], after: Mapping[str, Any],
    observation_before: Mapping[str, Any],
    observation_after: Mapping[str, Any],
) -> dict[str, Any]:
    if not static_v1.json_type_equal(before, after):
        raise HierarchicalResumeRunnerError(
            "transport chain changed during DRAT preflight"
        )
    state = before.get("state")
    if state not in proof_v1.TRANSPORT_STATES:
        raise HierarchicalResumeRunnerError("proof source is not quiescent")
    latest = before["generations"][-1]
    proof_before = before.get("latest_proof_physical")
    proof_after = after.get("latest_proof_physical")
    if (
        latest.get("pid_identity_alive") is not False
        or before.get("writable_holders") != []
        or after.get("writable_holders") != []
        or type(proof_before) is not dict
        or not static_v1.json_type_equal(proof_before, proof_after)
    ):
        raise HierarchicalResumeRunnerError(
            "stopped proof quiescence binding mismatch"
        )
    return {
        "method": (
            "dmtcp-checkpoint-stop-v1"
            if state == proof_v1.TRANSPORT_STATE_CHECKPOINTED
            else "dmtcp-inactive-exit-harvest-v1"
        ),
        "transport_state": state,
        "latest_generation": latest["generation"],
        "latest_pid": latest["pid"],
        "latest_proc_start_ticks": latest["proc_start_ticks"],
        "latest_pid_identity_alive": False,
        "coordinator_observations": [
            dict(observation_before), dict(observation_after),
        ],
        "writable_holders_before": [],
        "writable_holders_after": [],
        "proof_before": dict(proof_before),
        "proof_after": dict(proof_after),
    }


def _proof_envelopes(
    root: Path, loaded: Mapping[str, Any], session: Mapping[str, Any],
    chain: Mapping[str, Any], quiescence: Mapping[str, Any],
    drat_record: Mapping[str, Any], lrat_record: Mapping[str, Any],
    fresh_record: Mapping[str, Any],
    drat_artifact: Mapping[str, Any], lrat_artifact: Mapping[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    test_only = loaded["record"]["test_only"]
    authority = "TEST_ONLY" if test_only else "PRODUCTION"
    identity = _proof_identity(loaded)
    proof_chain = proof_v1.seal({
        "format": "binary-drat+converted-lrat-v1",
        "binary_drat": _artifact_reference(drat_artifact),
        "converted_lrat": _artifact_reference(lrat_artifact),
        "drat_checker_sha256": EXPECTED_DRAT_SHA256,
        "lrat_checker_sha256": EXPECTED_LRAT_SHA256,
        "trusted_policy_sha256": v2.EXPECTED_POLICY_CANONICAL_SHA256,
        "drat_independently_verified": True,
        "lrat_independently_verified": True,
        "fresh_drat_replay": True,
        "fresh_lrat_replay": True,
        "drat_record_sha256": drat_record["record_sha256"],
        "lrat_record_sha256": lrat_record["record_sha256"],
        "fresh_replay_record_sha256": fresh_record["record_sha256"],
    }, "chain_sha256")
    source_hash = static_v1.canonical_sha256({
        "resume_static_source_binding": loaded["record"]["source_binding"],
        "execution_source_binding": session["execution_source_binding"],
    })
    tool_hash = static_v1.canonical_sha256(loaded["record"]["toolchain_binding"])
    predecessor = static_v1.canonical_sha256([
        loaded["record"]["record_sha256"], session["record_sha256"],
        chain["record_sha256"], drat_record["record_sha256"],
        lrat_record["record_sha256"], fresh_record["record_sha256"],
    ])
    decision = proof_v1.expected_unsat_decision(chain["state"])
    transport_provenance = proof_v1.native_transport_provenance()
    certificate = proof_v1.seal({
        "schema_version": proof_v1.SCHEMA_VERSION,
        "kind": proof_v1.CHILD_CERTIFICATE_KIND,
        "gate": proof_v1.RUNNER_GATE,
        "state": proof_v1.STATE_PROOF_UNSAT,
        "authority": authority,
        "test_only": test_only,
        "production_eligible": not test_only,
        **identity,
        "child_num_variables": loaded["record"]["child"]["child_num_variables"],
        "child_num_clauses": loaded["record"]["child"]["child_num_clauses"],
        "child_dimacs_bytes": loaded["record"]["child"]["child_dimacs_bytes"],
        "solver": {
            "name": proof_v1.v4.v1.root_aggregate.EXPECTED_SOLVER_NAME,
            "version": proof_v1.v4.v1.root_aggregate.EXPECTED_SOLVER_VERSION,
            "executable_sha256": EXPECTED_SOLVER_SHA256,
        },
        "decision": decision,
        "proof_chain": proof_chain,
        "resume_static_sha256": loaded["record"]["record_sha256"],
        "transport_chain_sha256": chain["record_sha256"],
        "transport_quiescence": dict(quiescence),
        "transport_provenance": dict(transport_provenance),
        "source_binding_sha256": source_hash,
        "toolchain_binding_sha256": tool_hash,
        "predecessor_chain_sha256": predecessor,
        "parent_cube_unsat_claim": False,
        "global_distance_claim": None,
        "publication_certificate": False,
        "upload_authorized": False,
    }, "certificate_sha256")
    validation = proof_v1.seal({
        "schema_version": proof_v1.SCHEMA_VERSION,
        "kind": proof_v1.CHILD_VALIDATION_KIND,
        "gate": proof_v1.RUNNER_GATE,
        "root": str(root),
        **identity,
        "state": proof_v1.STATE_PROOF_UNSAT,
        "authority": authority,
        "test_only": test_only,
        "valid": True,
        "strict_proof_unsat": True,
        "fresh_proof_replay": True,
        "source_toolchain_fresh": True,
        "certificate": certificate,
        "transport_provenance": dict(transport_provenance),
        "failures": [],
        "global_distance_claim": None,
        "publication_certificate": False,
        "upload_authorized": False,
    }, "validation_sha256")
    return certificate, validation


def verify_checkpoint_root(root: Path, **static_kwargs: Any) -> dict[str, Any]:
    """Verify only a DMTCP checkpoint-stopped proof source."""

    target = _existing_root(root)
    with _root_lock(target, exclusive=True):
        checked_static_kwargs = _action_static_kwargs(target, static_kwargs)
        return _verify_stopped_proof_locked(
            target,
            requirement=CHAIN_REQUIRE_CHECKPOINTED,
            terminal_action="verify-checkpoint",
            **checked_static_kwargs,
        )


def harvest_inactive_root(root: Path, **static_kwargs: Any) -> dict[str, Any]:
    """Verify only a dead-identity, uncheckpointed DMTCP proof source."""

    target = _existing_root(root)
    with _root_lock(target, exclusive=True):
        checked_static_kwargs = _action_static_kwargs(target, static_kwargs)
        return _verify_stopped_proof_locked(
            target,
            requirement=CHAIN_REQUIRE_INACTIVE,
            terminal_action="harvest-inactive",
            **checked_static_kwargs,
        )


def _verify_stopped_proof_locked(
    root: Path, *, requirement: str, terminal_action: str,
    **static_kwargs: Any,
) -> dict[str, Any]:
    """Verify one explicitly selected stopped transport profile."""

    expected_action = {
        CHAIN_REQUIRE_CHECKPOINTED: "verify-checkpoint",
        CHAIN_REQUIRE_INACTIVE: "harvest-inactive",
    }.get(requirement)
    if terminal_action != expected_action:
        raise HierarchicalResumeRunnerError(
            "proof harvest action/transport requirement mismatch"
        )

    target = _existing_root(root)
    loaded, session = _load_session(target, **static_kwargs)
    if any((target / item).exists() for item in (
        TERMINAL_CLAIM, DRAT_COMMIT, LRAT_COMMIT, FINAL_COMMIT,
    )):
        raise HierarchicalResumeRunnerError("terminal stage already claimed")
    chain = validate_transport_chain(
        target, session, loaded["record"]["resource_policy"],
        requirement=requirement,
    )
    observation_before = _coordinator_observation(chain)
    prefix = chain["latest_proof_prefix"]
    if type(prefix) is not dict or prefix.get("bytes", 0) <= 0:
        return seal({
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-nested-width10-stopped-drat-preflight-v1",
            "gate": GATE,
            "root": str(target),
            "transport_chain_sha256": chain["record_sha256"],
            "drat_verified": False,
            "terminal_claim_created": False,
            "resumable": requirement == CHAIN_REQUIRE_CHECKPOINTED,
            "solver_resume_available": requirement == CHAIN_REQUIRE_CHECKPOINTED,
            "verification_retry_allowed": True,
            "transport_state": chain["state"],
            "failure": "stopped DRAT source is empty",
            "production_eligible": False,
        })
    proof_record = v2._physical_record(
        target / RUNTIME_ROOT / "proof.drat", target,
        "raw-binary-drat", cap=loaded["resource_caps"]["proof_max_bytes"],
    )
    drat, drat_stdout, drat_stderr, bound_drat = _run_checker(
        root=target, loaded=loaded, role="drat-verify",
        proof_path=target / RUNTIME_ROOT / "proof.drat",
        proof_record=proof_record,
        proof_cap=loaded["resource_caps"]["proof_max_bytes"],
    )
    if drat.get("verified") is not True:
        # Absolutely no terminal claim or durable checker artifact before here.
        return seal({
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-nested-width10-stopped-drat-preflight-v1",
            "gate": GATE,
            "root": str(target),
            "transport_chain_sha256": chain["record_sha256"],
            "bound_drat": bound_drat,
            "checker": drat,
            "checker_stdout": v2._hash_record(drat_stdout),
            "checker_stderr": v2._hash_record(drat_stderr),
            "drat_verified": False,
            "terminal_claim_created": False,
            "resumable": requirement == CHAIN_REQUIRE_CHECKPOINTED,
            "solver_resume_available": requirement == CHAIN_REQUIRE_CHECKPOINTED,
            "verification_retry_allowed": True,
            "transport_state": chain["state"],
            "failure": "complete pinned DRAT verification failed",
            "production_eligible": False,
        })
    # Close the race between successful checking and claiming the terminal.
    chain_after = validate_transport_chain(
        target, session, loaded["record"]["resource_policy"],
        requirement=requirement,
    )
    observation_after = _coordinator_observation(chain_after)
    quiescence = _transport_quiescence(
        chain, chain_after, observation_before, observation_after,
    )
    claim = _claim(
        target / TERMINAL_CLAIM, root=target, action=terminal_action,
    )
    _publish_bytes(target / "logs/drat-verify.stdout", drat_stdout)
    _publish_bytes(target / "logs/drat-verify.stderr", drat_stderr)
    drat_artifact = _copy_once(
        target / RUNTIME_ROOT / "proof.drat", target / DRAT_ARTIFACT,
        root=target, expected=proof_record,
        cap=loaded["resource_caps"]["proof_max_bytes"],
    )
    if (
        drat_artifact["file_sha256"] != proof_record["file_sha256"]
        or drat_artifact["bytes"] != proof_record["bytes"]
    ):
        raise HierarchicalResumeRunnerError("DRAT changed during handoff")
    drat_record = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-nested-width10-drat-verification-v1",
        "gate": GATE,
        "root": str(target),
        "resume_static_sha256": loaded["record"]["record_sha256"],
        "transport_chain_sha256": chain["record_sha256"],
        "terminal_claim_sha256": claim["record_sha256"],
        "proof": drat_artifact,
        "bound_drat": bound_drat,
        "checker": drat,
        "verified": True,
        "transport_trusted_for_scientific_proof": False,
    })
    _publish_json(target / DRAT_COMMIT, drat_record)

    lrat_fd, private_name = v2._create_private_output(
        target / "artifacts", LRAT_ARTIFACT.name,
    )
    try:
        conversion, conversion_out, conversion_err, conversion_bound = _run_checker(
            root=target, loaded=loaded, role="drat-to-lrat",
            proof_path=target / DRAT_ARTIFACT, proof_record=drat_artifact,
            proof_cap=loaded["resource_caps"]["proof_max_bytes"],
            output_fd=lrat_fd,
        )
        os.fsync(lrat_fd)
        lrat_sha, lrat_bytes, _ = v2._hash_fd_stable(
            lrat_fd, cap=proof_helper.LRAT_MAX_BYTES,
        )
        if (
            conversion.get("verified") is not True
            or not 0 < lrat_bytes <= proof_helper.LRAT_MAX_BYTES
        ):
            raise HierarchicalResumeRunnerError("DRAT-to-LRAT conversion failed")
        v2._publish_private_output(
            target / "artifacts", private_name, lrat_fd, LRAT_ARTIFACT.name,
            expected_sha256=lrat_sha, expected_bytes=lrat_bytes,
        )
        lrat_fd = -1
    finally:
        if lrat_fd >= 0:
            v2._discard_private(target / "artifacts", private_name, lrat_fd)
    _publish_bytes(target / "logs/drat-to-lrat.stdout", conversion_out)
    _publish_bytes(target / "logs/drat-to-lrat.stderr", conversion_err)
    lrat_artifact = v2._physical_record(
        target / LRAT_ARTIFACT, target, "converted-lrat",
        cap=proof_helper.LRAT_MAX_BYTES,
    )
    lrat_check, lrat_out, lrat_err, bound_lrat = _run_checker(
        root=target, loaded=loaded, role="lrat-check",
        proof_path=target / LRAT_ARTIFACT, proof_record=lrat_artifact,
        proof_cap=proof_helper.LRAT_MAX_BYTES,
    )
    if lrat_check.get("verified") is not True:
        raise HierarchicalResumeRunnerError("converted LRAT verification failed")
    _publish_bytes(target / "logs/lrat-check.stdout", lrat_out)
    _publish_bytes(target / "logs/lrat-check.stderr", lrat_err)
    lrat_record = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-nested-width10-lrat-verification-v1",
        "gate": GATE,
        "root": str(target),
        "drat_predecessor_sha256": drat_record["record_sha256"],
        "conversion": conversion,
        "conversion_bound_drat": conversion_bound,
        "lrat_artifact": lrat_artifact,
        "bound_lrat": bound_lrat,
        "lrat_checker": lrat_check,
        "verified": True,
    })
    _publish_json(target / LRAT_COMMIT, lrat_record)

    fresh_drat, fresh_drat_out, fresh_drat_err, fresh_bound_drat = _run_checker(
        root=target, loaded=loaded, role="final-drat-replay",
        proof_path=target / DRAT_ARTIFACT, proof_record=drat_artifact,
        proof_cap=loaded["resource_caps"]["proof_max_bytes"],
    )
    fresh_lrat, fresh_lrat_out, fresh_lrat_err, fresh_bound_lrat = _run_checker(
        root=target, loaded=loaded, role="final-lrat-replay",
        proof_path=target / LRAT_ARTIFACT, proof_record=lrat_artifact,
        proof_cap=proof_helper.LRAT_MAX_BYTES,
    )
    if fresh_drat.get("verified") is not True or fresh_lrat.get("verified") is not True:
        raise HierarchicalResumeRunnerError("fresh DRAT/LRAT replay failed")
    # Replay exact static/source/tool material once more immediately before seal.
    final_loaded, final_session = _load_session(target, **static_kwargs)
    if (
        final_loaded["record"]["record_sha256"] != loaded["record"]["record_sha256"]
        or final_session["record_sha256"] != session["record_sha256"]
    ):
        raise HierarchicalResumeRunnerError("static binding changed before final seal")
    final_chain = validate_transport_chain(
        target, final_session, final_loaded["record"]["resource_policy"],
        requirement=requirement,
    )
    _coordinator_observation(final_chain)
    if not static_v1.json_type_equal(final_chain, chain):
        raise HierarchicalResumeRunnerError(
            "stopped transport changed before final seal"
        )
    fresh_record = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-nested-width10-fresh-proof-replay-v1",
        "gate": GATE,
        "root": str(target),
        "bound_drat": fresh_bound_drat,
        "bound_lrat": fresh_bound_lrat,
        "drat_checker": fresh_drat,
        "lrat_checker": fresh_lrat,
        "drat_stdout": v2._hash_record(fresh_drat_out),
        "drat_stderr": v2._hash_record(fresh_drat_err),
        "lrat_stdout": v2._hash_record(fresh_lrat_out),
        "lrat_stderr": v2._hash_record(fresh_lrat_err),
        "all_fresh_replay_passed": True,
    })
    certificate, validation = _proof_envelopes(
        target, loaded, session, chain, quiescence,
        drat_record, lrat_record, fresh_record,
        drat_artifact, lrat_artifact,
    )
    aggregate_failures = proof_v1.validate_child_run_record(
        validation, loaded["campaign"],
    )
    if not static_v1.json_type_equal(
        session["execution_source_binding"], _execution_source_binding()
    ):
        raise HierarchicalResumeRunnerError(
            "execution source changed before final publication"
        )
    if aggregate_failures:
        raise HierarchicalResumeRunnerError(
            f"aggregate-v4 rejected final child envelope: {aggregate_failures}"
        )
    _publish_json(target / CERTIFICATE, certificate)
    _publish_json(target / VALIDATION, validation)
    commit = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-nested-width10-child-proof-final-v1",
        "gate": GATE,
        "state": proof_v1.STATE_PROOF_UNSAT,
        "root": str(target),
        "resume_static_sha256": loaded["record"]["record_sha256"],
        "transport_chain_sha256": chain["record_sha256"],
        "drat_predecessor_sha256": drat_record["record_sha256"],
        "lrat_predecessor_sha256": lrat_record["record_sha256"],
        "fresh_replay": fresh_record,
        "certificate_sha256": certificate["certificate_sha256"],
        "validation_sha256": validation["validation_sha256"],
        "strict_proof_unsat": True,
        "solver_clean_exit_observed": False,
        "solver_terminal_status_observed": False,
        "solver_exit_code_observed": None,
        "proof_replay_decision_complete": True,
        "proof_source_state": chain["state"],
        "proof_source_quiescent": True,
        "proof_v1_compatible": aggregate_failures == [],
        "proof_v1_failures": aggregate_failures,
        "global_distance_claim": None,
        "publication_certificate": False,
        "upload_authorized": False,
        "production_eligible_child_terminal": not loaded["record"]["test_only"],
        "no_further_scientific_artifact_writes_after_this_commit": True,
    })
    _publish_json(target / FINAL_COMMIT, commit)
    return commit


def verify_checkpoint_only(root: Path, **static_kwargs: Any) -> dict[str, Any]:
    """Read-only checkpoint replay under the shared root lock."""

    target = _existing_root(root)
    with _root_lock(target, exclusive=False):
        checked_static_kwargs = _action_static_kwargs(target, static_kwargs)
        return _verify_checkpoint_only_locked(target, **checked_static_kwargs)


def _verify_checkpoint_only_locked(
    root: Path, **static_kwargs: Any,
) -> dict[str, Any]:
    """Read-only checkpoint/prefix replay without invoking proof checkers."""

    target = _existing_root(root)
    loaded, session = _load_session(target, **static_kwargs)
    chain = validate_transport_chain(
        target, session, loaded["record"]["resource_policy"],
        requirement=CHAIN_REQUIRE_CHECKPOINTED,
    )
    return chain


def _require_record_sha256(
    value: Mapping[str, Any], expected_fields: set[str], *, label: str,
) -> None:
    if set(value) != expected_fields or not static_v1.selfhash_valid(value):
        raise HierarchicalResumeRunnerError(f"{label} schema or self-hash mismatch")


def _require_terminal_claim(
    root: Path, claim: Mapping[str, Any], *, expected_action: str,
) -> None:
    if expected_action not in {"verify-checkpoint", "harvest-inactive"}:
        raise HierarchicalResumeRunnerError("terminal claim action is invalid")
    fields = {
        "schema_version", "kind", "gate", "root", "root_identity",
        "root_lock_identity", "action", "nonce_hex", "pid", "terminal",
        "record_sha256",
    }
    nonce = claim.get("nonce_hex")
    if (
        set(claim) != fields or not static_v1.selfhash_valid(claim)
        or type(claim.get("schema_version")) is not int
        or claim.get("schema_version") != SCHEMA_VERSION
        or claim.get("kind") != "paper400-nested-width10-resume-stage-claim-v1"
        or claim.get("gate") != GATE or claim.get("root") != str(root)
        or not static_v1.json_type_equal(
            claim.get("root_identity"), _root_identity(root)
        )
        or not static_v1.json_type_equal(
            claim.get("root_lock_identity"), _lock_file_identity(root)
        )
        or claim.get("action") != expected_action
        or claim.get("terminal") is not True
        or type(claim.get("pid")) is not int or claim.get("pid") <= 0
        or type(nonce) is not str or len(nonce) != 64
        or any(character not in "0123456789abcdef" for character in nonce)
    ):
        raise HierarchicalResumeRunnerError("terminal claim mismatch")


def _root_tree_identity(root: Path) -> list[dict[str, Any]]:
    runtime = root / RUNTIME_ROOT
    numbers = controller._generation_numbers(runtime)
    allowed_symlinks: set[Path] = set()
    latest_resumed_checkpoint_image: Path | None = None
    for generation in numbers:
        directory = controller._generation_dir(runtime, generation)
        checkpoint_path = directory / "checkpoint.commit.json"
        image_paths: set[Path] = set()
        if checkpoint_path.exists():
            checkpoint = controller._checkpoint_commit(directory, generation)
            image_paths = set(
                controller._verify_checkpoint_images(runtime, checkpoint)
            )
            if generation >= 1:
                latest_resumed_checkpoint_image = next(iter(image_paths))
        _generation_metadata_bytes(
            directory, image_paths, generation=generation,
        )
        if generation == 0 and image_paths:
            allowed_symlinks.add(directory / "images" / RESTART_ALIAS_NAME)
    _runtime_restart_pair(runtime, latest_resumed_checkpoint_image)
    if latest_resumed_checkpoint_image is not None:
        allowed_symlinks.add(runtime / RESTART_ALIAS_NAME)

    records: list[dict[str, Any]] = []
    for position, path in enumerate(sorted(root.rglob("*"))):
        if position >= 100_000:
            raise HierarchicalResumeRunnerError("final root entry count exceeds cap")
        info = os.stat(path, follow_symlinks=False)
        if stat.S_ISLNK(info.st_mode):
            if path not in allowed_symlinks:
                raise HierarchicalResumeRunnerError("unexpected symlink in final root")
            records.append({
                "relative_path": path.relative_to(root).as_posix(),
                "entry_type": "symlink", "device": info.st_dev,
                "inode": info.st_ino, "mode": stat.S_IMODE(info.st_mode),
                "uid": info.st_uid, "links": info.st_nlink,
                "bytes": info.st_size, "mtime_ns": info.st_mtime_ns,
                "ctime_ns": info.st_ctime_ns, "target": os.readlink(path),
            })
            continue
        if not (stat.S_ISREG(info.st_mode) or stat.S_ISDIR(info.st_mode)):
            raise HierarchicalResumeRunnerError("non-plain entry in final root")
        records.append({
            "relative_path": path.relative_to(root).as_posix(),
            "entry_type": "file" if stat.S_ISREG(info.st_mode) else "directory",
            "device": info.st_dev, "inode": info.st_ino,
            "mode": stat.S_IMODE(info.st_mode), "uid": info.st_uid,
            "links": info.st_nlink, "bytes": info.st_size,
            "mtime_ns": info.st_mtime_ns, "ctime_ns": info.st_ctime_ns,
        })
    return records


def verify_final_root(root: Path, **static_kwargs: Any) -> dict[str, Any]:
    """Freshly replay one real final root without writing inside that root."""

    target = _existing_root(root)
    with _root_lock(target, exclusive=False):
        checked_static_kwargs = _action_static_kwargs(target, static_kwargs)
        if (target / TRANSPORT_PRUNE_COMMIT).exists():
            claim = _read_transport_prune_claim(target)
            _read_transport_prune_commit(target)
            return _validate_pruned_scientific_evidence_locked(
                target, claim, fresh_replay=True, **checked_static_kwargs,
            )
        if (target / TRANSPORT_PRUNE_CLAIM).exists():
            raise HierarchicalResumeRunnerError(
                "transport prune is incomplete; rerun prune-transport"
            )
        return _verify_final_root_locked(target, **checked_static_kwargs)


def _verify_final_root_locked(
    root: Path, **static_kwargs: Any,
) -> dict[str, Any]:
    target = _existing_root(root)
    loaded, session = _load_session(target, **static_kwargs)
    chain = validate_transport_chain(
        target, session, loaded["record"]["resource_policy"],
        requirement=CHAIN_REQUIRE_STOPPED,
    )
    _coordinator_observation(chain)
    terminal = _read_json(target / TERMINAL_CLAIM)
    drat_commit = _read_json(target / DRAT_COMMIT)
    lrat_commit = _read_json(target / LRAT_COMMIT)
    certificate = _read_json(target / CERTIFICATE)
    validation = _read_json(target / VALIDATION)
    final_commit = _read_json(target / FINAL_COMMIT)
    expected_terminal_action = {
        proof_v1.TRANSPORT_STATE_CHECKPOINTED: "verify-checkpoint",
        proof_v1.TRANSPORT_STATE_INACTIVE: "harvest-inactive",
    }.get(chain["state"])
    _require_terminal_claim(
        target, terminal, expected_action=expected_terminal_action,
    )

    _require_record_sha256(drat_commit, {
        "schema_version", "kind", "gate", "root",
        "resume_static_sha256", "transport_chain_sha256",
        "terminal_claim_sha256", "proof", "bound_drat", "checker",
        "verified", "transport_trusted_for_scientific_proof",
        "record_sha256",
    }, label="DRAT commit")
    _require_record_sha256(lrat_commit, {
        "schema_version", "kind", "gate", "root",
        "drat_predecessor_sha256", "conversion", "conversion_bound_drat",
        "lrat_artifact", "bound_lrat", "lrat_checker", "verified",
        "record_sha256",
    }, label="LRAT commit")
    _require_record_sha256(final_commit, {
        "schema_version", "kind", "gate", "state", "root",
        "resume_static_sha256", "transport_chain_sha256",
        "drat_predecessor_sha256", "lrat_predecessor_sha256",
        "fresh_replay", "certificate_sha256", "validation_sha256",
        "strict_proof_unsat", "solver_clean_exit_observed",
        "solver_terminal_status_observed", "solver_exit_code_observed",
        "proof_replay_decision_complete", "proof_source_state",
        "proof_source_quiescent", "proof_v1_compatible",
        "proof_v1_failures", "global_distance_claim",
        "publication_certificate", "upload_authorized",
        "production_eligible_child_terminal",
        "no_further_scientific_artifact_writes_after_this_commit",
        "record_sha256",
    }, label="final commit")
    fresh_record = final_commit.get("fresh_replay")
    if type(fresh_record) is not dict:
        raise HierarchicalResumeRunnerError("fresh replay record missing")
    _require_record_sha256(fresh_record, {
        "schema_version", "kind", "gate", "root", "bound_drat",
        "bound_lrat", "drat_checker", "lrat_checker", "drat_stdout",
        "drat_stderr", "lrat_stdout", "lrat_stderr",
        "all_fresh_replay_passed", "record_sha256",
    }, label="fresh replay")

    if (
        drat_commit.get("schema_version") != SCHEMA_VERSION
        or drat_commit.get("kind") != "paper400-nested-width10-drat-verification-v1"
        or drat_commit.get("gate") != GATE
        or drat_commit.get("root") != str(target)
        or drat_commit.get("resume_static_sha256")
        != loaded["record"]["record_sha256"]
        or drat_commit.get("transport_chain_sha256") != chain["record_sha256"]
        or drat_commit.get("terminal_claim_sha256")
        != terminal["record_sha256"]
        or drat_commit.get("verified") is not True
        or drat_commit.get("transport_trusted_for_scientific_proof") is not False
        or type(drat_commit.get("checker")) is not dict
        or drat_commit["checker"].get("verified") is not True
    ):
        raise HierarchicalResumeRunnerError("DRAT commit binding mismatch")
    if (
        lrat_commit.get("schema_version") != SCHEMA_VERSION
        or lrat_commit.get("kind") != "paper400-nested-width10-lrat-verification-v1"
        or lrat_commit.get("gate") != GATE
        or lrat_commit.get("root") != str(target)
        or lrat_commit.get("drat_predecessor_sha256")
        != drat_commit["record_sha256"]
        or lrat_commit.get("verified") is not True
        or type(lrat_commit.get("conversion")) is not dict
        or lrat_commit["conversion"].get("verified") is not True
        or type(lrat_commit.get("lrat_checker")) is not dict
        or lrat_commit["lrat_checker"].get("verified") is not True
    ):
        raise HierarchicalResumeRunnerError("LRAT commit binding mismatch")

    certificate_failures = proof_v1.validate_child_certificate(
        certificate, loaded["campaign"],
    )
    validation_failures = proof_v1.validate_child_run_record(
        validation, loaded["campaign"],
    )
    if certificate_failures or validation_failures:
        raise HierarchicalResumeRunnerError(
            f"final child envelope mismatch: {certificate_failures + validation_failures}"
        )
    if not static_v1.json_type_equal(validation.get("certificate"), certificate):
        raise HierarchicalResumeRunnerError("validation embeds a different certificate")

    identity = _proof_identity(loaded)
    source_hash = static_v1.canonical_sha256({
        "resume_static_source_binding": loaded["record"]["source_binding"],
        "execution_source_binding": session["execution_source_binding"],
    })
    tool_hash = static_v1.canonical_sha256(
        loaded["record"]["toolchain_binding"]
    )
    expected_predecessor = static_v1.canonical_sha256([
        loaded["record"]["record_sha256"], session["record_sha256"],
        chain["record_sha256"], drat_commit["record_sha256"],
        lrat_commit["record_sha256"], fresh_record["record_sha256"],
    ])
    decision = certificate.get("decision")
    if (
        certificate.get("resume_static_sha256")
        != loaded["record"]["record_sha256"]
        or certificate.get("transport_chain_sha256") != chain["record_sha256"]
        or certificate.get("source_binding_sha256") != source_hash
        or certificate.get("toolchain_binding_sha256") != tool_hash
        or certificate.get("predecessor_chain_sha256") != expected_predecessor
        or type(decision) is not dict
        or not static_v1.json_type_equal(
            decision, proof_v1.expected_unsat_decision(chain["state"])
        )
        or type(certificate.get("transport_quiescence")) is not dict
        or certificate["transport_quiescence"].get("transport_state")
        != chain["state"]
        or not static_v1.json_type_equal(
            certificate.get("transport_provenance"),
            proof_v1.native_transport_provenance(),
        )
        or not static_v1.json_type_equal(
            validation.get("transport_provenance"),
            certificate.get("transport_provenance"),
        )
    ):
        raise HierarchicalResumeRunnerError("certificate predecessor mismatch")

    cnf_artifact = v2._physical_record(
        target / STATIC_DIMACS, target, "exact-hierarchical-child-cnf",
        cap=loaded["record"]["child"]["child_dimacs_bytes"],
    )
    drat_artifact = v2._physical_record(
        target / DRAT_ARTIFACT, target, "raw-binary-drat",
        cap=loaded["resource_caps"]["proof_max_bytes"],
    )
    lrat_artifact = v2._physical_record(
        target / LRAT_ARTIFACT, target, "converted-lrat",
        cap=proof_helper.LRAT_MAX_BYTES,
    )
    if (
        cnf_artifact.get("relative_path") != STATIC_DIMACS.as_posix()
        or cnf_artifact.get("file_sha256")
        != loaded["record"]["child"]["child_dimacs_sha256"]
        or cnf_artifact.get("bytes")
        != loaded["record"]["child"]["child_dimacs_bytes"]
        or drat_artifact.get("relative_path") != DRAT_ARTIFACT.as_posix()
        or lrat_artifact.get("relative_path") != LRAT_ARTIFACT.as_posix()
        or drat_artifact.get("links") != 1 or lrat_artifact.get("links") != 1
        or len({
            (cnf_artifact["device"], cnf_artifact["inode"]),
            (drat_artifact["device"], drat_artifact["inode"]),
            (lrat_artifact["device"], lrat_artifact["inode"]),
        }) != 3
        or not static_v1.json_type_equal(drat_commit.get("proof"), drat_artifact)
        or not static_v1.json_type_equal(
            lrat_commit.get("lrat_artifact"), lrat_artifact
        )
    ):
        raise HierarchicalResumeRunnerError("final artifact binding mismatch")
    proof_chain = certificate.get("proof_chain")
    if (
        type(proof_chain) is not dict
        or not static_v1.json_type_equal(
            proof_chain.get("binary_drat"), _artifact_reference(drat_artifact)
        )
        or not static_v1.json_type_equal(
            proof_chain.get("converted_lrat"), _artifact_reference(lrat_artifact)
        )
        or proof_chain.get("drat_record_sha256")
        != drat_commit["record_sha256"]
        or proof_chain.get("lrat_record_sha256")
        != lrat_commit["record_sha256"]
        or proof_chain.get("fresh_replay_record_sha256")
        != fresh_record["record_sha256"]
    ):
        raise HierarchicalResumeRunnerError("certificate proof-chain mismatch")

    if (
        final_commit.get("schema_version") != SCHEMA_VERSION
        or final_commit.get("kind") != "paper400-nested-width10-child-proof-final-v1"
        or final_commit.get("gate") != GATE
        or final_commit.get("state") != proof_v1.STATE_PROOF_UNSAT
        or final_commit.get("root") != str(target)
        or final_commit.get("resume_static_sha256")
        != loaded["record"]["record_sha256"]
        or final_commit.get("transport_chain_sha256") != chain["record_sha256"]
        or final_commit.get("drat_predecessor_sha256")
        != drat_commit["record_sha256"]
        or final_commit.get("lrat_predecessor_sha256")
        != lrat_commit["record_sha256"]
        or final_commit.get("certificate_sha256")
        != certificate["certificate_sha256"]
        or final_commit.get("validation_sha256")
        != validation["validation_sha256"]
        or final_commit.get("strict_proof_unsat") is not True
        or final_commit.get("solver_clean_exit_observed") is not False
        or final_commit.get("solver_terminal_status_observed") is not False
        or final_commit.get("solver_exit_code_observed") is not None
        or final_commit.get("proof_replay_decision_complete") is not True
        or final_commit.get("proof_source_state") != chain["state"]
        or final_commit.get("proof_source_quiescent") is not True
        or final_commit.get("proof_v1_compatible") is not True
        or final_commit.get("proof_v1_failures") != []
        or final_commit.get("global_distance_claim") is not None
        or final_commit.get("publication_certificate") is not False
        or final_commit.get("upload_authorized") is not False
        or final_commit.get("production_eligible_child_terminal")
        is not (not loaded["record"]["test_only"])
        or final_commit.get(
            "no_further_scientific_artifact_writes_after_this_commit"
        ) is not True
        or fresh_record.get("all_fresh_replay_passed") is not True
        or type(fresh_record.get("drat_checker")) is not dict
        or fresh_record["drat_checker"].get("verified") is not True
        or type(fresh_record.get("lrat_checker")) is not dict
        or fresh_record["lrat_checker"].get("verified") is not True
    ):
        raise HierarchicalResumeRunnerError("final commit truth table mismatch")

    tree_before_replay = _root_tree_identity(target)
    fresh_drat, _drat_out, _drat_err, _bound_drat = _run_checker(
        root=target, loaded=loaded, role="final-drat-replay",
        proof_path=target / DRAT_ARTIFACT, proof_record=drat_artifact,
        proof_cap=loaded["resource_caps"]["proof_max_bytes"],
    )
    fresh_lrat, _lrat_out, _lrat_err, _bound_lrat = _run_checker(
        root=target, loaded=loaded, role="final-lrat-replay",
        proof_path=target / LRAT_ARTIFACT, proof_record=lrat_artifact,
        proof_cap=proof_helper.LRAT_MAX_BYTES,
    )
    if fresh_drat.get("verified") is not True or fresh_lrat.get("verified") is not True:
        raise HierarchicalResumeRunnerError("final-root fresh proof replay failed")

    final_loaded, final_session = _load_session(target, **static_kwargs)
    final_chain = validate_transport_chain(
        target, final_session, final_loaded["record"]["resource_policy"],
        requirement=CHAIN_REQUIRE_STOPPED,
    )
    _coordinator_observation(final_chain)
    final_cnf = v2._physical_record(
        target / STATIC_DIMACS, target, "exact-hierarchical-child-cnf",
        cap=loaded["record"]["child"]["child_dimacs_bytes"],
    )
    final_drat = v2._physical_record(
        target / DRAT_ARTIFACT, target, "raw-binary-drat",
        cap=loaded["resource_caps"]["proof_max_bytes"],
    )
    final_lrat = v2._physical_record(
        target / LRAT_ARTIFACT, target, "converted-lrat",
        cap=proof_helper.LRAT_MAX_BYTES,
    )
    reread = {
        "terminal": _read_json(target / TERMINAL_CLAIM),
        "drat": _read_json(target / DRAT_COMMIT),
        "lrat": _read_json(target / LRAT_COMMIT),
        "certificate": _read_json(target / CERTIFICATE),
        "validation": _read_json(target / VALIDATION),
        "final": _read_json(target / FINAL_COMMIT),
    }
    tree_after_replay = _root_tree_identity(target)
    if (
        not static_v1.json_type_equal(tree_after_replay, tree_before_replay)
        or final_loaded["record"]["record_sha256"]
        != loaded["record"]["record_sha256"]
        or final_session["record_sha256"] != session["record_sha256"]
        or not static_v1.json_type_equal(final_chain, chain)
        or not static_v1.json_type_equal(final_cnf, cnf_artifact)
        or not static_v1.json_type_equal(final_drat, drat_artifact)
        or not static_v1.json_type_equal(final_lrat, lrat_artifact)
        or not static_v1.json_type_equal(reread["terminal"], terminal)
        or not static_v1.json_type_equal(reread["drat"], drat_commit)
        or not static_v1.json_type_equal(reread["lrat"], lrat_commit)
        or not static_v1.json_type_equal(reread["certificate"], certificate)
        or not static_v1.json_type_equal(reread["validation"], validation)
        or not static_v1.json_type_equal(reread["final"], final_commit)
    ):
        raise HierarchicalResumeRunnerError("final root changed during replay")

    attestation = seal({
        "schema_version": FINAL_ROOT_ATTESTATION_SCHEMA_VERSION,
        "kind": FINAL_ROOT_ATTESTATION_KIND,
        "gate": proof_v1.RUNNER_GATE,
        "root": str(target),
        "root_identity": _root_identity(target),
        **identity,
        "resume_static_sha256": loaded["record"]["record_sha256"],
        "session_sha256": session["record_sha256"],
        "transport_chain_sha256": chain["record_sha256"],
        "terminal_claim_sha256": terminal["record_sha256"],
        "drat_commit_sha256": drat_commit["record_sha256"],
        "lrat_commit_sha256": lrat_commit["record_sha256"],
        "final_commit_sha256": final_commit["record_sha256"],
        "certificate_sha256": certificate["certificate_sha256"],
        "validation_sha256": validation["validation_sha256"],
        "cnf_artifact": cnf_artifact,
        "drat_artifact": drat_artifact,
        "lrat_artifact": lrat_artifact,
        "source_binding_sha256": source_hash,
        "toolchain_binding_sha256": tool_hash,
        "fresh_drat_checker": fresh_drat,
        "fresh_lrat_checker": fresh_lrat,
        "proof_source_state": chain["state"],
        "proof_replay_decision_complete": True,
        "strict_proof_unsat": True,
        "valid": True,
        "failures": [],
    })
    if set(attestation) != FINAL_ROOT_ATTESTATION_FIELDS:
        raise HierarchicalResumeRunnerError("final-root attestation field drift")
    return attestation


def _transport_entry_record(root: Path, path: Path) -> dict[str, Any]:
    """Describe one transport entry without ever following a symlink."""

    try:
        relative = path.relative_to(root)
    except ValueError as exc:  # pragma: no cover - caller constructs descendants
        raise HierarchicalResumeRunnerError(
            "transport entry escaped the result root"
        ) from exc
    if (
        not relative.parts
        or relative.parts[: len(RUNTIME_ROOT.parts)] != RUNTIME_ROOT.parts
    ):
        raise HierarchicalResumeRunnerError(
            "transport entry is outside the exact removable subtree"
        )
    before = os.stat(path, follow_symlinks=False)
    common = {
        "relative_path": relative.as_posix(),
        "device": int(before.st_dev),
        "inode": int(before.st_ino),
        "mode": stat.S_IMODE(before.st_mode),
        "uid": int(before.st_uid),
    }
    if before.st_uid != os.geteuid():
        raise HierarchicalResumeRunnerError(
            "transport entry is not owned by the effective user"
        )
    if stat.S_ISDIR(before.st_mode):
        if before.st_dev != os.stat(root, follow_symlinks=False).st_dev:
            raise HierarchicalResumeRunnerError(
                "transport subtree crosses a filesystem boundary"
            )
        return {**common, "entry_type": "directory"}
    if stat.S_ISLNK(before.st_mode):
        target = os.readlink(path)
        after = os.stat(path, follow_symlinks=False)
        if _stat_identity(before) != _stat_identity(after):
            raise HierarchicalResumeRunnerError(
                "transport symlink changed while recording"
            )
        return {
            **common,
            "entry_type": "symlink",
            "links": int(before.st_nlink),
            "bytes": int(before.st_size),
            "target": target,
        }
    if not stat.S_ISREG(before.st_mode) or before.st_nlink != 1:
        raise HierarchicalResumeRunnerError(
            "transport subtree contains a non-plain or multiply-linked entry"
        )
    descriptor = os.open(
        path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW,
    )
    try:
        opened = os.fstat(descriptor)
        if _stat_identity(before) != _stat_identity(opened):
            raise HierarchicalResumeRunnerError(
                "transport file changed before hashing"
            )
        digest = hashlib.sha256()
        observed = 0
        while True:
            chunk = os.read(descriptor, 8 << 20)
            if not chunk:
                break
            observed += len(chunk)
            if observed > before.st_size:
                raise HierarchicalResumeRunnerError(
                    "transport file grew while hashing"
                )
            digest.update(chunk)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    if (
        _stat_identity(before) != _stat_identity(after)
        or observed != before.st_size
    ):
        raise HierarchicalResumeRunnerError(
            "transport file changed while hashing"
        )
    return {
        **common,
        "entry_type": "file",
        "links": int(before.st_nlink),
        "bytes": int(before.st_size),
        "sha256": digest.hexdigest(),
    }


def _transport_tree_entries(root: Path) -> list[dict[str, Any]]:
    """Return a stable, bounded manifest for the exact DMTCP subtree."""

    runtime = root / RUNTIME_ROOT
    if not os.path.lexists(runtime):
        return []
    records: list[dict[str, Any]] = []

    def visit(path: Path) -> None:
        if len(records) >= TRANSPORT_PRUNE_MAX_ENTRIES:
            raise HierarchicalResumeRunnerError(
                "transport prune entry count exceeds cap"
            )
        record = _transport_entry_record(root, path)
        records.append(record)
        if record["entry_type"] != "directory":
            return
        before = os.stat(path, follow_symlinks=False)
        try:
            with os.scandir(path) as iterator:
                children = sorted(
                    (Path(entry.path) for entry in iterator),
                    key=lambda item: item.name,
                )
        except OSError as exc:
            raise HierarchicalResumeRunnerError(
                "cannot enumerate transport subtree"
            ) from exc
        after = os.stat(path, follow_symlinks=False)
        if (
            before.st_dev != after.st_dev
            or before.st_ino != after.st_ino
            or before.st_mode != after.st_mode
            or before.st_uid != after.st_uid
        ):
            raise HierarchicalResumeRunnerError(
                "transport directory changed while recording"
            )
        for child in children:
            visit(child)

    visit(runtime)
    return sorted(
        records,
        key=lambda item: (
            len(Path(item["relative_path"]).parts), item["relative_path"],
        ),
    )


def _validate_transport_entries(entries: Any) -> list[dict[str, Any]]:
    if type(entries) is not list or not entries:
        raise HierarchicalResumeRunnerError(
            "transport prune manifest is empty or malformed"
        )
    if len(entries) > TRANSPORT_PRUNE_MAX_ENTRIES:
        raise HierarchicalResumeRunnerError(
            "transport prune manifest exceeds its entry cap"
        )
    checked: list[dict[str, Any]] = []
    seen: set[str] = set()
    directories: set[str] = set()
    for item in entries:
        if type(item) is not dict:
            raise HierarchicalResumeRunnerError(
                "transport prune entry is not an object"
            )
        kind = item.get("entry_type")
        common = {
            "relative_path", "entry_type", "device", "inode", "mode", "uid",
        }
        expected = {
            "directory": common,
            "file": common | {"links", "bytes", "sha256"},
            "symlink": common | {"links", "bytes", "target"},
        }.get(kind)
        relative_text = item.get("relative_path")
        if expected is None or set(item) != expected:
            raise HierarchicalResumeRunnerError(
                "transport prune entry schema mismatch"
            )
        if type(relative_text) is not str:
            raise HierarchicalResumeRunnerError(
                "transport prune path is malformed"
            )
        relative = Path(relative_text)
        if (
            relative.is_absolute()
            or relative.as_posix() != relative_text
            or any(part in {"", ".", ".."} for part in relative.parts)
            or relative.parts[: len(RUNTIME_ROOT.parts)] != RUNTIME_ROOT.parts
            or relative_text in seen
        ):
            raise HierarchicalResumeRunnerError(
                "transport prune path escapes or is duplicated"
            )
        if any(
            type(item.get(field)) is not int or item[field] < 0
            for field in ("device", "inode", "mode", "uid")
        ):
            raise HierarchicalResumeRunnerError(
                "transport prune inode identity is malformed"
            )
        if kind in {"file", "symlink"} and (
            type(item.get("links")) is not int or item["links"] != 1
            or type(item.get("bytes")) is not int or item["bytes"] < 0
        ):
            raise HierarchicalResumeRunnerError(
                "transport prune leaf identity is malformed"
            )
        if kind == "file" and (
            type(item.get("sha256")) is not str
            or re.fullmatch(r"[0-9a-f]{64}", item["sha256"]) is None
        ):
            raise HierarchicalResumeRunnerError(
                "transport prune file hash is malformed"
            )
        if kind == "symlink" and type(item.get("target")) is not str:
            raise HierarchicalResumeRunnerError(
                "transport prune symlink target is malformed"
            )
        parent = relative.parent.as_posix()
        if relative != RUNTIME_ROOT and parent not in directories:
            raise HierarchicalResumeRunnerError(
                "transport prune manifest lacks a parent directory"
            )
        if relative == RUNTIME_ROOT and kind != "directory":
            raise HierarchicalResumeRunnerError(
                "transport prune root is not a directory"
            )
        if kind == "directory":
            directories.add(relative_text)
        seen.add(relative_text)
        checked.append(dict(item))
    if [item["relative_path"] for item in checked] != sorted(
        seen, key=lambda value: (len(Path(value).parts), value),
    ):
        raise HierarchicalResumeRunnerError(
            "transport prune manifest order is non-canonical"
        )
    if checked[0]["relative_path"] != RUNTIME_ROOT.as_posix():
        raise HierarchicalResumeRunnerError(
            "transport prune manifest has the wrong root"
        )
    return checked


def _transport_manifest(root: Path) -> dict[str, Any]:
    entries = _validate_transport_entries(_transport_tree_entries(root))
    return {
        "relative_path": RUNTIME_ROOT.as_posix(),
        "entries": entries,
        "entry_count": len(entries),
        "regular_file_bytes": sum(
            item["bytes"] for item in entries if item["entry_type"] == "file"
        ),
        "manifest_sha256": static_v1.canonical_sha256(entries),
    }


def _validate_final_attestation(value: Any, root: Path) -> dict[str, Any]:
    raw = dict(value) if type(value) is dict else {}
    if (
        set(raw) != FINAL_ROOT_ATTESTATION_FIELDS
        or not static_v1.selfhash_valid(raw)
        or raw.get("schema_version") != FINAL_ROOT_ATTESTATION_SCHEMA_VERSION
        or raw.get("kind") != FINAL_ROOT_ATTESTATION_KIND
        or raw.get("gate") != proof_v1.RUNNER_GATE
        or raw.get("root") != str(root)
        or not static_v1.json_type_equal(
            raw.get("root_identity"), _root_identity(root)
        )
        or raw.get("valid") is not True
        or raw.get("failures") != []
        or raw.get("proof_replay_decision_complete") is not True
        or raw.get("strict_proof_unsat") is not True
    ):
        raise HierarchicalResumeRunnerError(
            "transport prune final-root attestation is invalid"
        )
    return raw


def _transport_prune_claim_value(
    root: Path, attestation: Mapping[str, Any], manifest: Mapping[str, Any],
) -> dict[str, Any]:
    return seal({
        "schema_version": TRANSPORT_PRUNE_SCHEMA_VERSION,
        "kind": TRANSPORT_PRUNE_CLAIM_KIND,
        "gate": GATE,
        "root": str(root),
        "root_identity": _root_identity(root),
        "runtime_relative_path": RUNTIME_ROOT.as_posix(),
        "final_root_attestation": dict(attestation),
        "final_root_attestation_sha256": attestation["record_sha256"],
        "transport_entries": list(manifest["entries"]),
        "transport_entry_count": manifest["entry_count"],
        "transport_regular_file_bytes": manifest["regular_file_bytes"],
        "transport_manifest_sha256": manifest["manifest_sha256"],
        "preserved_artifact_relative_paths": [
            STATIC_DIMACS.as_posix(), DRAT_ARTIFACT.as_posix(),
            LRAT_ARTIFACT.as_posix(), CERTIFICATE.as_posix(),
            VALIDATION.as_posix(), FINAL_COMMIT.as_posix(),
        ],
        "irreversible": True,
    })


def _read_transport_prune_claim(root: Path) -> dict[str, Any]:
    claim = _read_json(root / TRANSPORT_PRUNE_CLAIM)
    fields = {
        "schema_version", "kind", "gate", "root", "root_identity",
        "runtime_relative_path", "final_root_attestation",
        "final_root_attestation_sha256", "transport_entries",
        "transport_entry_count", "transport_regular_file_bytes",
        "transport_manifest_sha256", "preserved_artifact_relative_paths",
        "irreversible", "record_sha256",
    }
    entries = _validate_transport_entries(claim.get("transport_entries"))
    attestation = _validate_final_attestation(
        claim.get("final_root_attestation"), root,
    )
    if (
        set(claim) != fields
        or not static_v1.selfhash_valid(claim)
        or claim.get("schema_version") != TRANSPORT_PRUNE_SCHEMA_VERSION
        or claim.get("kind") != TRANSPORT_PRUNE_CLAIM_KIND
        or claim.get("gate") != GATE
        or claim.get("root") != str(root)
        or not static_v1.json_type_equal(
            claim.get("root_identity"), _root_identity(root)
        )
        or claim.get("runtime_relative_path") != RUNTIME_ROOT.as_posix()
        or claim.get("final_root_attestation_sha256")
        != attestation["record_sha256"]
        or claim.get("transport_entry_count") != len(entries)
        or claim.get("transport_regular_file_bytes") != sum(
            item["bytes"] for item in entries if item["entry_type"] == "file"
        )
        or claim.get("transport_manifest_sha256")
        != static_v1.canonical_sha256(entries)
        or claim.get("preserved_artifact_relative_paths") != [
            STATIC_DIMACS.as_posix(), DRAT_ARTIFACT.as_posix(),
            LRAT_ARTIFACT.as_posix(), CERTIFICATE.as_posix(),
            VALIDATION.as_posix(), FINAL_COMMIT.as_posix(),
        ]
        or claim.get("irreversible") is not True
    ):
        raise HierarchicalResumeRunnerError(
            "transport prune claim schema or binding mismatch"
        )
    return claim


def _artifact_matches_without_hash(
    root: Path, path: Path, expected: Mapping[str, Any],
) -> None:
    info = os.stat(path, follow_symlinks=False)
    try:
        relative = path.relative_to(root).as_posix()
    except ValueError as exc:  # pragma: no cover
        raise HierarchicalResumeRunnerError(
            "preserved artifact escaped the root"
        ) from exc
    if (
        not stat.S_ISREG(info.st_mode)
        or relative != expected.get("relative_path")
        or info.st_dev != expected.get("device")
        or info.st_ino != expected.get("inode")
        or stat.S_IMODE(info.st_mode) != expected.get("mode")
        or info.st_uid != os.geteuid()
        or info.st_nlink != expected.get("links")
        or info.st_size != expected.get("bytes")
    ):
        raise HierarchicalResumeRunnerError(
            "preserved scientific artifact identity changed"
        )


def _artifact_matches_with_hash(
    root: Path, path: Path, expected: Mapping[str, Any],
) -> None:
    expected_bytes = expected.get("bytes")
    expected_role = expected.get("role")
    if (
        type(expected_bytes) is not int or expected_bytes < 0
        or type(expected_role) is not str or not expected_role
    ):
        raise HierarchicalResumeRunnerError(
            "preserved scientific artifact record is malformed"
        )
    observed = v2._physical_record(
        path, root, expected_role, cap=max(1, expected_bytes),
    )
    if not static_v1.json_type_equal(observed, expected):
        raise HierarchicalResumeRunnerError(
            "preserved scientific artifact content changed"
        )


def _quiesce_transport_coordinators(
    root: Path, chain: Mapping[str, Any],
) -> None:
    generations = chain.get("generations")
    if type(generations) is not list or not generations:
        raise HierarchicalResumeRunnerError(
            "transport coordinator list is malformed"
        )
    command = DMTCP_PREFIX / "bin/dmtcp_command"
    for generation in generations:
        number = generation.get("generation") if type(generation) is dict else None
        port = (
            generation.get("coordinator_port")
            if type(generation) is dict else None
        )
        if (
            type(number) is not int or number < 0
            or type(port) is not int or not 1 <= port <= 65535
        ):
            raise HierarchicalResumeRunnerError(
                "transport coordinator identity is malformed"
            )
        port_file = (
            root / RUNTIME_ROOT / "generations" / f"{number:06d}"
            / "coordinator.port"
        )
        with _fixed_environment():
            controller._quit_coordinator_if_present(command, port_file)
        for _attempt in range(50):
            try:
                with _fixed_environment():
                    controller._query_status(command, port, timeout=0.2)
            except (
                controller.ResumeControllerError,
                subprocess.SubprocessError,
                OSError,
            ):
                break
        else:
            raise HierarchicalResumeRunnerError(
                "DMTCP coordinator remained reachable after shutdown"
            )


def _validate_pruned_scientific_evidence_locked(
    root: Path, claim: Mapping[str, Any], *, fresh_replay: bool,
    **static_kwargs: Any,
) -> dict[str, Any]:
    """Validate retained science without requiring the deleted transport."""

    loaded = _load_static(root, **static_kwargs)
    attestation = _validate_final_attestation(
        claim.get("final_root_attestation"), root,
    )
    identity = _proof_identity(loaded)
    if any(
        not static_v1.json_type_equal(attestation.get(key), value)
        for key, value in identity.items()
    ):
        raise HierarchicalResumeRunnerError(
            "pruned attestation leaf identity mismatch"
        )
    session = _read_json(root / SESSION_COMMIT)
    terminal = _read_json(root / TERMINAL_CLAIM)
    drat_commit = _read_json(root / DRAT_COMMIT)
    lrat_commit = _read_json(root / LRAT_COMMIT)
    certificate = _read_json(root / CERTIFICATE)
    validation = _read_json(root / VALIDATION)
    final_commit = _read_json(root / FINAL_COMMIT)
    if (
        not static_v1.selfhash_valid(session)
        or not static_v1.selfhash_valid(terminal)
        or not static_v1.selfhash_valid(drat_commit)
        or not static_v1.selfhash_valid(lrat_commit)
        or not static_v1.selfhash_valid(final_commit)
        or session.get("record_sha256") != attestation.get("session_sha256")
        or terminal.get("record_sha256")
        != attestation.get("terminal_claim_sha256")
        or drat_commit.get("record_sha256")
        != attestation.get("drat_commit_sha256")
        or lrat_commit.get("record_sha256")
        != attestation.get("lrat_commit_sha256")
        or final_commit.get("record_sha256")
        != attestation.get("final_commit_sha256")
        or certificate.get("certificate_sha256")
        != attestation.get("certificate_sha256")
        or validation.get("validation_sha256")
        != attestation.get("validation_sha256")
        or final_commit.get("strict_proof_unsat") is not True
        or final_commit.get("proof_replay_decision_complete") is not True
        or final_commit.get(
            "no_further_scientific_artifact_writes_after_this_commit"
        ) is not True
    ):
        raise HierarchicalResumeRunnerError(
            "pruned predecessor record binding mismatch"
        )
    certificate_failures = proof_v1.validate_child_certificate(
        certificate, loaded["campaign"],
    )
    validation_failures = proof_v1.validate_child_run_record(
        validation, loaded["campaign"],
    )
    if (
        certificate_failures
        or validation_failures
        or not static_v1.json_type_equal(
            validation.get("certificate"), certificate,
        )
    ):
        raise HierarchicalResumeRunnerError(
            "pruned child certificate or validation mismatch"
        )
    cnf = v2._physical_record(
        root / STATIC_DIMACS, root, "exact-hierarchical-child-cnf",
        cap=loaded["record"]["child"]["child_dimacs_bytes"],
    )
    drat = v2._physical_record(
        root / DRAT_ARTIFACT, root, "raw-binary-drat",
        cap=loaded["resource_caps"]["proof_max_bytes"],
    )
    lrat = v2._physical_record(
        root / LRAT_ARTIFACT, root, "converted-lrat",
        cap=proof_helper.LRAT_MAX_BYTES,
    )
    if (
        not static_v1.json_type_equal(cnf, attestation.get("cnf_artifact"))
        or not static_v1.json_type_equal(drat, attestation.get("drat_artifact"))
        or not static_v1.json_type_equal(lrat, attestation.get("lrat_artifact"))
        or not static_v1.json_type_equal(drat_commit.get("proof"), drat)
        or not static_v1.json_type_equal(lrat_commit.get("lrat_artifact"), lrat)
    ):
        raise HierarchicalResumeRunnerError(
            "pruned scientific artifact binding mismatch"
        )
    if not fresh_replay:
        return attestation
    fresh_drat, _do, _de, _db = _run_checker(
        root=root, loaded=loaded, role="final-drat-replay",
        proof_path=root / DRAT_ARTIFACT, proof_record=drat,
        proof_cap=loaded["resource_caps"]["proof_max_bytes"],
    )
    fresh_lrat, _lo, _le, _lb = _run_checker(
        root=root, loaded=loaded, role="final-lrat-replay",
        proof_path=root / LRAT_ARTIFACT, proof_record=lrat,
        proof_cap=proof_helper.LRAT_MAX_BYTES,
    )
    if (
        fresh_drat.get("verified") is not True
        or fresh_lrat.get("verified") is not True
    ):
        raise HierarchicalResumeRunnerError(
            "pruned final-root fresh proof replay failed"
        )
    refreshed = dict(attestation)
    refreshed.pop("record_sha256", None)
    refreshed["fresh_drat_checker"] = fresh_drat
    refreshed["fresh_lrat_checker"] = fresh_lrat
    return seal(refreshed)


def _delete_claimed_transport(root: Path, claim: Mapping[str, Any]) -> None:
    """Delete only entries authorized by the durable prune claim."""

    expected = {
        item["relative_path"]: item
        for item in _validate_transport_entries(claim["transport_entries"])
    }
    current_entries = _transport_tree_entries(root)
    for item in current_entries:
        allowed = expected.get(item["relative_path"])
        if allowed is None or not static_v1.json_type_equal(item, allowed):
            raise HierarchicalResumeRunnerError(
                "transport subtree changed after prune authorization"
            )
    for item in sorted(
        current_entries,
        key=lambda value: (len(Path(value["relative_path"]).parts),
                           value["relative_path"]),
        reverse=True,
    ):
        path = root / item["relative_path"]
        if not os.path.lexists(path):
            continue
        observed = _transport_entry_record(root, path)
        if not static_v1.json_type_equal(observed, item):
            raise HierarchicalResumeRunnerError(
                "transport entry changed immediately before deletion"
            )
        if item["entry_type"] == "directory":
            os.rmdir(path)
        else:
            os.unlink(path)
    if os.path.lexists(root / RUNTIME_ROOT):
        raise HierarchicalResumeRunnerError(
            "transport subtree remains after claimed deletion"
        )
    parent_fd = os.open(
        (root / RUNTIME_ROOT).parent,
        os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
    )
    try:
        os.fsync(parent_fd)
    finally:
        os.close(parent_fd)


def _transport_prune_commit_value(
    root: Path, claim: Mapping[str, Any],
) -> dict[str, Any]:
    attestation = claim["final_root_attestation"]
    return seal({
        "schema_version": TRANSPORT_PRUNE_SCHEMA_VERSION,
        "kind": TRANSPORT_PRUNE_COMMIT_KIND,
        "gate": GATE,
        "root": str(root),
        "root_identity": _root_identity(root),
        "claim_sha256": claim["record_sha256"],
        "final_root_attestation_sha256": attestation["record_sha256"],
        "transport_manifest_sha256": claim["transport_manifest_sha256"],
        "removed_relative_path": RUNTIME_ROOT.as_posix(),
        "removed_entry_count": claim["transport_entry_count"],
        "removed_regular_file_bytes": claim["transport_regular_file_bytes"],
        "runtime_absent": True,
        "cnf_artifact": attestation["cnf_artifact"],
        "drat_artifact": attestation["drat_artifact"],
        "lrat_artifact": attestation["lrat_artifact"],
        "strict_proof_unsat": True,
        "proof_replay_decision_complete": True,
        "scientific_artifacts_preserved": True,
        "transport_only_deleted": True,
        "irreversible": True,
    })


def _read_transport_prune_commit(root: Path) -> dict[str, Any]:
    claim = _read_transport_prune_claim(root)
    commit = _read_json(root / TRANSPORT_PRUNE_COMMIT)
    expected = _transport_prune_commit_value(root, claim)
    if not static_v1.json_type_equal(commit, expected):
        raise HierarchicalResumeRunnerError(
            "transport prune commit schema or binding mismatch"
        )
    if os.path.lexists(root / RUNTIME_ROOT):
        raise HierarchicalResumeRunnerError(
            "transport prune commit exists but runtime remains"
        )
    for key, relative in (
        ("cnf_artifact", STATIC_DIMACS),
        ("drat_artifact", DRAT_ARTIFACT),
        ("lrat_artifact", LRAT_ARTIFACT),
    ):
        _artifact_matches_without_hash(root, root / relative, commit[key])
    return commit


def prune_transport_root(root: Path, **static_kwargs: Any) -> dict[str, Any]:
    """Irreversibly remove DMTCP state after a fresh final proof replay."""

    target = _existing_root(root)
    with _root_lock(target, exclusive=True):
        checked_static_kwargs = _action_static_kwargs(target, static_kwargs)
        if (target / TRANSPORT_PRUNE_COMMIT).exists():
            commit = _read_transport_prune_commit(target)
            claim = _read_transport_prune_claim(target)
            _validate_pruned_scientific_evidence_locked(
                target, claim, fresh_replay=True, **checked_static_kwargs,
            )
            return commit
        if (target / TRANSPORT_PRUNE_CLAIM).exists():
            claim = _read_transport_prune_claim(target)
            _validate_pruned_scientific_evidence_locked(
                target, claim, fresh_replay=True, **checked_static_kwargs,
            )
        else:
            if not (target / FINAL_COMMIT).exists():
                raise HierarchicalResumeRunnerError(
                    "transport pruning requires a final child commit"
                )
            attestation = _verify_final_root_locked(
                target, **checked_static_kwargs,
            )
            loaded, session = _load_session(
                target, **checked_static_kwargs,
            )
            chain = validate_transport_chain(
                target, session, loaded["record"]["resource_policy"],
                requirement=CHAIN_REQUIRE_STOPPED,
            )
            _quiesce_transport_coordinators(target, chain)
            manifest = _transport_manifest(target)
            claim = _transport_prune_claim_value(
                target, attestation, manifest,
            )
            _publish_json(target / TRANSPORT_PRUNE_CLAIM, claim)
            claim = _read_transport_prune_claim(target)
        _delete_claimed_transport(target, claim)
        for key, relative in (
            ("cnf_artifact", STATIC_DIMACS),
            ("drat_artifact", DRAT_ARTIFACT),
            ("lrat_artifact", LRAT_ARTIFACT),
        ):
            _artifact_matches_with_hash(
                target, target / relative,
                claim["final_root_attestation"][key],
            )
        commit = _transport_prune_commit_value(target, claim)
        _publish_json(target / TRANSPORT_PRUNE_COMMIT, commit)
        return _read_transport_prune_commit(target)


def _pruned_status_locked(
    root: Path, **static_kwargs: Any,
) -> dict[str, Any]:
    _load_static(root, **static_kwargs)
    commit = _read_transport_prune_commit(root)
    chain = seal({
        "schema_version": TRANSPORT_PRUNE_SCHEMA_VERSION,
        "kind": TRANSPORT_PRUNE_STATUS_KIND,
        "gate": GATE,
        "root": str(root),
        "state": "PRUNED",
        "prune_commit_sha256": commit["record_sha256"],
        "transport_present": False,
        "scientific_artifacts_preserved": True,
        "transport_trusted_for_scientific_proof": False,
    })
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-nested-width10-resume-status-v1",
        "gate": GATE,
        "root": str(root),
        "resume_static_sha256": _read_json(
            root / STATIC_COMMIT
        )["record_sha256"],
        "session_sha256": _read_json(
            root / SESSION_COMMIT
        )["record_sha256"],
        "chain": chain,
        "terminal_claimed": True,
        "terminal_committed": True,
        "production_eligible": False,
    })


def _caps_from_args(args: argparse.Namespace) -> dict[str, int]:
    return {
        "proof_max_bytes": args.proof_max_bytes,
        "checkpoint_image_max_bytes": args.checkpoint_image_max_bytes,
        "checkpoint_images_per_generation_max": args.checkpoint_images_per_generation_max,
        "checkpoint_generation_max_count": args.checkpoint_generation_max_count,
        "checkpoint_generation_metadata_max_bytes": args.checkpoint_generation_metadata_max_bytes,
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    sub = parser.add_subparsers(dest="action", required=True)
    prepare = sub.add_parser("prepare", allow_abbrev=False)
    prepare.add_argument("--root", type=Path, required=True)
    prepare.add_argument("--parent-manifest", type=Path, required=True)
    prepare.add_argument("--width6-campaign", type=Path, required=True)
    prepare.add_argument("--width10-campaign", type=Path, required=True)
    prepare.add_argument("--parent-cube-index", type=int, required=True)
    prepare.add_argument("--global-leaf-index", type=int, required=True)
    prepare.add_argument("--proof-max-bytes", type=int, required=True)
    prepare.add_argument("--checkpoint-image-max-bytes", type=int, required=True)
    prepare.add_argument("--checkpoint-images-per-generation-max", type=int, required=True)
    prepare.add_argument("--checkpoint-generation-max-count", type=int, required=True)
    prepare.add_argument("--checkpoint-generation-metadata-max-bytes", type=int, required=True)
    for action in (
        "start", "checkpoint-stop", "resume", "status",
        "verify-checkpoint", "harvest-inactive",
        "verify-checkpoint-only", "verify-final", "prune-transport",
    ):
        child = sub.add_parser(action, allow_abbrev=False)
        child.add_argument("--root", type=Path, required=True)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.action == "prepare":
        parent = _read_json(args.parent_manifest)
        width6_campaign = _read_json(args.width6_campaign)
        width10_campaign = _read_json(args.width10_campaign)
        current_instance = nested.cube16.optimized.build_optimized_instance()
        verification = nested.verify_campaign_manifest(
            width10_campaign,
            width6_campaign,
            parent,
            current_instance,
            parent_cube_index=args.parent_cube_index,
            strict_base=True,
        )
        if verification.get("valid") is not True:
            raise HierarchicalResumeRunnerError(
                f"width-ten campaign replay failed: {verification.get('binding_failures')}"
            )
        child_dimacs = nested.verified_child_dimacs_from_verification(
            width10_campaign,
            width6_campaign,
            parent,
            current_instance,
            verification_record=verification,
            global_leaf_index=args.global_leaf_index,
            parent_cube_index=args.parent_cube_index,
            strict_base=True,
        )
        result = prepare_root_from_material(
            args.root,
            parent_manifest=parent,
            width6_campaign_manifest=width6_campaign,
            width10_campaign_manifest=width10_campaign,
            instance=None,
            parent_cube_index=args.parent_cube_index,
            global_leaf_index=args.global_leaf_index,
            campaign_verification_record=verification,
            verified_child_dimacs=child_dimacs,
            resource_caps=_caps_from_args(args),
            strict_base=True,
        )
    elif args.action == "start":
        result = start_root(args.root)
    elif args.action == "checkpoint-stop":
        result = checkpoint_stop_root(args.root)
    elif args.action == "resume":
        result = resume_root(args.root)
    elif args.action == "status":
        result = status_root(args.root)
    elif args.action == "verify-checkpoint":
        result = verify_checkpoint_root(args.root)
    elif args.action == "harvest-inactive":
        result = harvest_inactive_root(args.root)
    elif args.action == "verify-checkpoint-only":
        result = verify_checkpoint_only(args.root)
    elif args.action == "verify-final":
        result = verify_final_root(args.root)
    elif args.action == "prune-transport":
        result = prune_transport_root(args.root)
    else:  # pragma: no cover
        raise HierarchicalResumeRunnerError("unreachable action")
    sys.stdout.buffer.write(canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    try:
        _exit = main()
    except (
        HierarchicalResumeRunnerError, static_v1.ResumeStaticError,
        nested.NestedWidth10CampaignError,
        nested.width6.WidenedParentCampaignError,
        nested.hierarchy.HierarchicalCubeError,
        controller.ResumeControllerError,
        proof_helper.CubeProofRunnerError, OSError, ValueError, TypeError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        _exit = 2
    raise SystemExit(_exit)


__all__ = [
    "HierarchicalResumeRunnerError", "checkpoint_stop_root", "harvest_inactive_root",
    "prepare_root_from_material",
    "resume_root", "start_root", "status_root", "validate_transport_chain",
    "prune_transport_root", "verify_checkpoint_only", "verify_checkpoint_root",
    "verify_final_root",
    "FINAL_ROOT_ATTESTATION_FIELDS", "FINAL_ROOT_ATTESTATION_KIND",
    "FINAL_ROOT_ATTESTATION_SCHEMA_VERSION",
    "TRANSPORT_PRUNE_CLAIM", "TRANSPORT_PRUNE_CLAIM_KIND",
    "TRANSPORT_PRUNE_COMMIT", "TRANSPORT_PRUNE_COMMIT_KIND",
]
