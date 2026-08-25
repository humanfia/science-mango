#!/usr/bin/env python3
"""Run the native answer-blind chemistry campaign in per-target OS sandboxes.

The trusted controller creates 32 one-row workspaces.  Every workspace has a
different Unix UID/GID and Codex home, cannot traverse any sibling workspace,
and links the same controller-owned read-only Lake dependency snapshot.  Each
workspace runs Archon's unchanged native sequence with one objective and one
internal lane; this controller supplies the only global concurrency, capped at
four workers.  Preparation is the default.  ``--run`` starts a fresh campaign
and ``--resume`` resumes only incomplete targets.
"""

from __future__ import annotations

import argparse
import ctypes
import dataclasses
import datetime as dt
import errno
import fcntl
import grp
import hashlib
import importlib.util
import json
import os
import pwd
import re
import resource
import selectors
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

from PIL import Image


SCHEMA_VERSION = 1
PIPELINE = "archon-native-answer-blind-isolated-full32"
GLOBAL_MAX_PARALLEL = 4
PER_TARGET_MAX_PARALLEL = 1
BUNDLE_REL = Path("icho_2026_source/questions_only.jsonl")
MANIFEST_REL = Path("isolation_manifest.json")
CANONICAL_TARGET_IDS = (
    "icho_2026_t1_a3", "icho_2026_t1_a6",
    "icho_2026_t2_a2", "icho_2026_t2_a3", "icho_2026_t2_a5",
    "icho_2026_t3_a1", "icho_2026_t3_a2", "icho_2026_t3_a6",
    "icho_2026_t3_a7",
    "icho_2026_t4_a1", "icho_2026_t4_a4", "icho_2026_t4_a5",
    "icho_2026_t4_a6", "icho_2026_t4_a7", "icho_2026_t4_a8",
    "icho_2026_t4_a9",
    "icho_2026_t5_a1", "icho_2026_t5_a3", "icho_2026_t5_a4",
    "icho_2026_t6_a3", "icho_2026_t6_a4", "icho_2026_t6_a7",
    "icho_2026_t7_a2", "icho_2026_t7_a3",
    "icho_2026_t8_a5", "icho_2026_t8_a6", "icho_2026_t8_a9",
    "icho_2026_t9_a1", "icho_2026_t9_a3", "icho_2026_t9_a6",
    "icho_2026_t9_a7", "icho_2026_t9_a9",
)
_SAFE_USER_PREFIX = re.compile(r"[a-z_][a-z0-9_-]{0,20}")

# Linux Landlock ABI 4.  Network mediation is intentionally not enabled: the
# model transport needs TCP and this evaluation claims filesystem, not network,
# answer blindness.  Handling every ABI-4 filesystem right with a closed
# allowlist prevents the whole Archon/Codex process tree from opening /proc or
# a sibling target even if a future tool bypasses ordinary directory walking.
_LANDLOCK_CREATE_RULESET = 444
_LANDLOCK_ADD_RULE = 445
_LANDLOCK_RESTRICT_SELF = 446
_LANDLOCK_CREATE_VERSION = 1
_LANDLOCK_RULE_PATH_BENEATH = 1
_PR_SET_NO_NEW_PRIVS = 38
_PR_SET_PDEATHSIG = 1
_LANDLOCK_FS_RIGHTS = (1 << 15) - 1
_LANDLOCK_EXECUTE = 1 << 0
_LANDLOCK_WRITE_FILE = 1 << 1
_LANDLOCK_READ_FILE = 1 << 2
_LANDLOCK_READ_DIR = 1 << 3
_LANDLOCK_REFER = 1 << 13
_LANDLOCK_TRUNCATE = 1 << 14
_LANDLOCK_READ_WRITE_DEVICE_FILES = ("/dev/null",)


class _LandlockRulesetAttr(ctypes.Structure):
    _fields_ = [
        ("handled_access_fs", ctypes.c_uint64),
        ("handled_access_net", ctypes.c_uint64),
    ]


class _LandlockPathBeneathAttr(ctypes.Structure):
    _fields_ = [
        ("allowed_access", ctypes.c_uint64),
        ("parent_fd", ctypes.c_int32),
    ]


class CampaignError(RuntimeError):
    """The requested deployment does not preserve the isolation contract."""


def _load_sibling(name: str, module_name: str):
    path = Path(__file__).resolve().with_name(name)
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load trusted controller module: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


NATIVE = _load_sibling(
    "run_answer_blind_archon_campaign.py", "_archon_isolated_native",
)
ITERATION = _load_sibling(
    "run_answer_blind_iteration.py", "_archon_isolated_iteration",
)


def _utcnow() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z")


def _canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        + "\n"
    ).encode("utf-8")


def _pretty_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    ).encode("utf-8")


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _hash_index(value: Mapping[str, str]) -> str:
    return _sha256_bytes(_canonical_json_bytes(dict(sorted(value.items()))))


def _atomic_write(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, raw = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary = Path(raw)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(_pretty_json_bytes(value))
            stream.flush()
            os.fsync(stream.fileno())
        os.chmod(temporary, 0o600)
        os.replace(temporary, path)
        directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    except BaseException:
        temporary.unlink(missing_ok=True)
        raise


def _libc() -> ctypes.CDLL:
    return ctypes.CDLL(None, use_errno=True)


def _syscall(number: int, *arguments: object) -> int:
    result = _libc().syscall(number, *arguments)
    if result < 0:
        error = ctypes.get_errno()
        raise OSError(error, os.strerror(error))
    return int(result)


def landlock_abi() -> int:
    return _syscall(
        _LANDLOCK_CREATE_RULESET,
        ctypes.c_void_p(),
        0,
        _LANDLOCK_CREATE_VERSION,
    )


def _add_landlock_path(ruleset_fd: int, path: Path, *, writable: bool) -> str:
    resolved = path.resolve(strict=True)
    metadata = resolved.stat()
    if stat.S_ISDIR(metadata.st_mode):
        allowed = _LANDLOCK_FS_RIGHTS if writable else (
            _LANDLOCK_EXECUTE | _LANDLOCK_READ_FILE | _LANDLOCK_READ_DIR
        )
    else:
        allowed = (
            _LANDLOCK_EXECUTE | _LANDLOCK_READ_FILE | _LANDLOCK_WRITE_FILE
            | _LANDLOCK_TRUNCATE
            if writable
            else _LANDLOCK_EXECUTE | _LANDLOCK_READ_FILE
        )
    descriptor = os.open(resolved, os.O_PATH | os.O_CLOEXEC)
    try:
        attribute = _LandlockPathBeneathAttr(allowed, descriptor)
        _syscall(
            _LANDLOCK_ADD_RULE,
            ruleset_fd,
            _LANDLOCK_RULE_PATH_BENEATH,
            ctypes.byref(attribute),
            0,
        )
    finally:
        os.close(descriptor)
    return str(resolved)


def _apply_landlock(
    *, read_only: Sequence[Path], read_write: Sequence[Path]
) -> dict[str, Any]:
    abi = landlock_abi()
    if abi < 4:
        raise CampaignError(f"Landlock ABI 4+ is required; kernel reports {abi}")
    attribute = _LandlockRulesetAttr(_LANDLOCK_FS_RIGHTS, 0)
    ruleset = _syscall(
        _LANDLOCK_CREATE_RULESET,
        ctypes.byref(attribute),
        ctypes.sizeof(attribute),
        0,
    )
    read_only_receipt: list[str] = []
    read_write_receipt: list[str] = []
    try:
        seen: set[Path] = set()
        for candidate in read_only:
            if not candidate.exists():
                continue
            resolved = candidate.resolve(strict=True)
            if resolved in seen:
                continue
            seen.add(resolved)
            read_only_receipt.append(
                _add_landlock_path(ruleset, resolved, writable=False)
            )
        for candidate in read_write:
            resolved = candidate.resolve(strict=True)
            if resolved in seen:
                raise CampaignError(f"Landlock path has conflicting authority: {resolved}")
            seen.add(resolved)
            read_write_receipt.append(
                _add_landlock_path(ruleset, resolved, writable=True)
            )
        libc = _libc()
        if libc.prctl(_PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0:
            error = ctypes.get_errno()
            raise OSError(error, os.strerror(error))
        _syscall(_LANDLOCK_RESTRICT_SELF, ruleset, 0)
    finally:
        os.close(ruleset)
    return {
        "abi": abi,
        "handled_access_fs": _LANDLOCK_FS_RIGHTS,
        "deny_by_default": True,
        "no_new_privs": True,
        "read_only_paths": sorted(read_only_receipt),
        "read_write_paths": sorted(read_write_receipt),
    }


@dataclasses.dataclass(frozen=True)
class Identity:
    target_id: str
    username: str
    uid: int
    groupname: str
    gid: int


@dataclasses.dataclass(frozen=True)
class Config:
    campaign_root: Path
    seed_workspace: Path | None = None
    lake_packages: Path | None = None
    codex_home_template: Path | None = None
    archon_bin: str = "archon"
    python_bin: Path = Path(sys.executable)
    runtime_root: Path | None = None
    max_iterations: int = 100
    global_parallel: int = GLOBAL_MAX_PARALLEL
    user_prefix: str = "ichoab"
    uid_base: int = 26000
    provision_identities: bool = False

    @property
    def index_path(self) -> Path:
        return self.campaign_root / "campaign.json"

    @property
    def item_root(self) -> Path:
        return self.campaign_root / "items"

    @property
    def home_root(self) -> Path:
        return self.campaign_root / "homes"

    @property
    def shared_packages(self) -> Path:
        return self.campaign_root / "shared-lake-packages"

    @property
    def controller_log_root(self) -> Path:
        return self.campaign_root / "controller-logs"

    def target_root(self, target_id: str) -> Path:
        return self.item_root / target_id

    def user_home(self, target_id: str) -> Path:
        return self.home_root / target_id

    def codex_home(self, target_id: str) -> Path:
        return self.user_home(target_id) / ".codex"


def _identity_plan(config: Config) -> tuple[Identity, ...]:
    if _SAFE_USER_PREFIX.fullmatch(config.user_prefix) is None:
        raise CampaignError("user prefix is not a safe Unix account prefix")
    if config.uid_base < 1000 or config.uid_base + len(CANONICAL_TARGET_IDS) >= 60000:
        raise CampaignError("uid-base must reserve 32 ordinary Unix identities")
    identities = tuple(
        Identity(
            target_id=target_id,
            username=f"{config.user_prefix}{index:02d}",
            uid=config.uid_base + index - 1,
            groupname=f"{config.user_prefix}{index:02d}",
            gid=config.uid_base + index - 1,
        )
        for index, target_id in enumerate(CANONICAL_TARGET_IDS, start=1)
    )
    if len({item.username for item in identities}) != len(identities):
        raise CampaignError("generated solver usernames are not unique")
    return identities


def _run_account_command(arguments: Sequence[str]) -> None:
    completed = subprocess.run(
        list(arguments), check=False, capture_output=True, text=True,
    )
    if completed.returncode != 0:
        detail = (completed.stderr or completed.stdout).strip()
        raise CampaignError(f"identity provisioning failed: {detail}")


def _ensure_identity(identity: Identity, *, provision: bool) -> None:
    try:
        group = grp.getgrnam(identity.groupname)
    except KeyError:
        try:
            collision = grp.getgrgid(identity.gid)
        except KeyError:
            collision = None
        if collision is not None:
            raise CampaignError(
                f"gid {identity.gid} belongs to unexpected group {collision.gr_name}"
            )
        if not provision:
            raise CampaignError(f"missing solver group: {identity.groupname}")
        _run_account_command(
            ["groupadd", "--gid", str(identity.gid), identity.groupname]
        )
        group = grp.getgrnam(identity.groupname)
    if group.gr_gid != identity.gid:
        raise CampaignError(f"solver group {identity.groupname} has unexpected gid")

    try:
        user = pwd.getpwnam(identity.username)
    except KeyError:
        try:
            collision_user = pwd.getpwuid(identity.uid)
        except KeyError:
            collision_user = None
        if collision_user is not None:
            raise CampaignError(
                f"uid {identity.uid} belongs to unexpected user {collision_user.pw_name}"
            )
        if not provision:
            raise CampaignError(f"missing solver user: {identity.username}")
        _run_account_command([
            "useradd", "--uid", str(identity.uid), "--gid", str(identity.gid),
            "--no-create-home", "--home-dir", "/nonexistent",
            "--shell", "/usr/sbin/nologin", identity.username,
        ])
        user = pwd.getpwnam(identity.username)
    if user.pw_uid != identity.uid or user.pw_gid != identity.gid:
        raise CampaignError(f"solver user {identity.username} has unexpected uid/gid")


def _ensure_identities(config: Config, identities: Sequence[Identity]) -> None:
    if os.geteuid() != 0:
        raise CampaignError("isolated preparation and execution require a root controller")
    for identity in identities:
        _ensure_identity(identity, provision=config.provision_identities)
    # A dedicated numeric UID/GID is safe to sweep only when the system
    # account databases map it to exactly one expected name.  NSS permits
    # aliases with duplicate numeric ids; accepting one would let cleanup of
    # a solver identity signal an unrelated alias account's processes.
    users = tuple(pwd.getpwall())
    groups = tuple(grp.getgrall())
    for identity in identities:
        uid_names = tuple(
            entry.pw_name for entry in users if entry.pw_uid == identity.uid
        )
        gid_names = tuple(
            entry.gr_name for entry in groups if entry.gr_gid == identity.gid
        )
        if uid_names != (identity.username,):
            raise CampaignError(
                f"solver uid {identity.uid} is not uniquely bound to "
                f"{identity.username}"
            )
        if gid_names != (identity.groupname,):
            raise CampaignError(
                f"solver gid {identity.gid} is not uniquely bound to "
                f"{identity.groupname}"
            )
    protected_gids = {identity.gid for identity in identities}
    for identity in identities:
        memberships = {
            group.gr_gid for group in groups
            if identity.username in group.gr_mem
        } | {identity.gid}
        leaked = (memberships & protected_gids) - {identity.gid}
        if leaked:
            raise CampaignError(
                f"solver user {identity.username} belongs to another target group"
            )


def _load_full_seed(seed: Path) -> tuple[dict[str, Any], dict[str, dict[str, Any]]]:
    try:
        NATIVE._SEED.validate_seed(seed)
        manifest = json.loads((seed / MANIFEST_REL).read_text(encoding="utf-8"))
        rows = [
            json.loads(line)
            for line in (seed / BUNDLE_REL).read_text(encoding="utf-8").splitlines()
            if line.strip()
        ]
    except Exception as exc:
        raise CampaignError(f"full seed validation failed: {exc}") from exc
    ids = tuple(str(row.get("id") or "") for row in rows)
    if ids != CANONICAL_TARGET_IDS or tuple(manifest.get("target_ids") or ()) != ids:
        raise CampaignError("seed does not contain the exact canonical full32 order")
    by_id = {str(row["id"]): row for row in rows}
    if len(by_id) != len(CANONICAL_TARGET_IDS):
        raise CampaignError("seed contains duplicate canonical target ids")
    return manifest, by_id


def _copy_plain_file(source: Path, destination: Path) -> None:
    if source.is_symlink() or not source.is_file():
        raise CampaignError(f"seed projection source is missing or unsafe: {source}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, destination)


def _build_subset_seed(
    *, seed: Path, destination: Path, manifest: Mapping[str, Any], row: Mapping[str, Any]
) -> dict[str, Any]:
    """Create a validator-compatible seed containing exactly one problem row."""
    target_id = str(row.get("id") or "")
    if target_id not in CANONICAL_TARGET_IDS:
        raise CampaignError(f"noncanonical target requested: {target_id}")
    if destination.exists() or destination.is_symlink():
        raise CampaignError(f"subset seed destination already exists: {destination}")
    destination.mkdir(parents=True)

    lake = dict(manifest.get("lake_skeleton_files") or {})
    full_assets = dict(manifest.get("assets") or {})
    selected_assets: dict[str, str] = {}
    selected_images: list[tuple[str, str]] = []
    for asset in row.get("problem_assets") or []:
        if not isinstance(asset, Mapping):
            raise CampaignError(f"{target_id} contains an invalid problem asset")
        kind = asset.get("kind")
        name = str(asset.get("path") or "")
        if not name or Path(name).name != name:
            raise CampaignError(f"{target_id} contains an unsafe problem asset path")
        if kind == "problem_pdf":
            # Never project the full-paper PDF into a single-target workspace.
            # A fresh PDF is rendered below from exactly this row's allowed
            # page images and bound into a rewritten problem-only row.
            continue
        if kind != "problem_page":
            raise CampaignError(f"{target_id} contains an unsupported problem asset")
        relative = f"icho_2026_source/image/{name}"
        digest = str(asset.get("sha256") or "")
        if full_assets.get(relative) != digest:
            raise CampaignError(f"{target_id} asset is not bound by the full seed")
        selected_assets[relative] = digest
        selected_images.append((relative, digest))
    if not selected_images:
        raise CampaignError(f"{target_id} lacks a required problem image")

    for relative in sorted({*lake, *selected_assets}):
        _copy_plain_file(seed / relative, destination / relative)

    pdf_name = f"{target_id}-problem-only.pdf"
    pdf_relative = f"icho_2026_source/raw/{pdf_name}"
    pdf_path = destination / pdf_relative
    pdf_path.parent.mkdir(parents=True, exist_ok=True)
    images: list[Image.Image] = []
    try:
        for relative, _digest in selected_images:
            with Image.open(seed / relative) as source_image:
                images.append(source_image.convert("RGB"))
        images[0].save(
            pdf_path,
            "PDF",
            save_all=True,
            append_images=images[1:],
            resolution=150.0,
            title=f"Problem-only {target_id}",
            author="IChO answer-blind controller",
            creator="IChO answer-blind controller",
            producer="Pillow",
            creationDate="D:20000101000000Z",
            modDate="D:20000101000000Z",
        )
    finally:
        for image in images:
            image.close()
    pdf_digest = _sha256_bytes(pdf_path.read_bytes())
    selected_assets[pdf_relative] = pdf_digest

    projected_row = json.loads(json.dumps(row))
    projected_row["source_pdf"] = pdf_name
    projected_assets = []
    for asset in projected_row.get("problem_assets") or []:
        if asset.get("kind") == "problem_pdf":
            replacement = dict(asset)
            replacement.update({"path": pdf_name, "sha256": pdf_digest})
            replacement.pop("source_page", None)
            replacement["derived_from_problem_pages"] = [
                {"path": Path(relative).name, "sha256": digest}
                for relative, digest in selected_images
            ]
            projected_assets.append(replacement)
        else:
            projected_assets.append(asset)
    projected_row["problem_assets"] = projected_assets
    bundle_bytes = _canonical_json_bytes(projected_row)
    bundle_path = destination / BUNDLE_REL
    bundle_path.parent.mkdir(parents=True, exist_ok=True)
    bundle_path.write_bytes(bundle_bytes)
    bundle_digest = _sha256_bytes(bundle_bytes)

    payload = dict(lake)
    payload.update(selected_assets)
    payload[BUNDLE_REL.as_posix()] = bundle_digest
    subset = dict(manifest)
    subset.update({
        "engine_files": {},
        "engine_files_sha256": _hash_index({}),
        "lake_skeleton_files": dict(sorted(lake.items())),
        "lake_skeleton_sha256": _hash_index(lake),
        "blind_bundle": {
            "path": BUNDLE_REL.as_posix(), "row_count": 1,
            "sha256": bundle_digest, "size": len(bundle_bytes),
        },
        "blind_bundle_sha256": bundle_digest,
        "target_ids": [target_id],
        "target_ids_sha256": _sha256_bytes(_canonical_json_bytes([target_id])),
        "assets": dict(sorted(selected_assets.items())),
        "assets_sha256": _hash_index(selected_assets),
        "payload_files": dict(sorted(payload.items())),
        "payload_sha256": _hash_index(payload),
    })
    (destination / MANIFEST_REL).write_bytes(_pretty_json_bytes(subset))
    try:
        NATIVE._SEED.validate_seed(destination)
    except Exception as exc:
        raise CampaignError(f"single-target seed {target_id} is invalid: {exc}") from exc
    return {
        "manifest": subset,
        "parent_row_sha256": _sha256_bytes(_canonical_json_bytes(dict(row))),
        "projected_row_sha256": _sha256_bytes(bundle_bytes),
        "derived_pdf": {
            "path": pdf_relative,
            "sha256": pdf_digest,
            "source_images": [
                {"path": relative, "sha256": digest}
                for relative, digest in selected_images
            ],
        },
    }


def _set_owner_mode(path: Path, *, uid: int, gid: int, mode: int) -> None:
    if path.is_symlink():
        os.lchown(path, uid, gid)
        return
    os.chown(path, uid, gid)
    os.chmod(path, mode)


def _make_tree_read_only(root: Path, *, gid: int = 0) -> None:
    for directory, names, files in os.walk(root, topdown=False, followlinks=False):
        base = Path(directory)
        for name in sorted(files):
            path = base / name
            if path.is_symlink():
                os.lchown(path, 0, gid)
            else:
                _set_owner_mode(path, uid=0, gid=gid, mode=0o440 if gid else 0o444)
        for name in sorted(names):
            path = base / name
            if path.is_symlink():
                os.lchown(path, 0, gid)
            else:
                _set_owner_mode(path, uid=0, gid=gid, mode=0o550 if gid else 0o555)
    _set_owner_mode(root, uid=0, gid=gid, mode=0o550 if gid else 0o555)


def _make_plain_dir_solver_owned(path: Path, identity: Identity) -> None:
    if path.is_symlink() or not path.is_dir():
        raise CampaignError(f"solver-writable path must be a plain directory: {path}")
    _make_tree_solver_owned(path, identity)


def _make_tree_solver_owned(root: Path, identity: Identity) -> None:
    for directory, names, files in os.walk(root, topdown=False, followlinks=False):
        base = Path(directory)
        for name in sorted(files):
            path = base / name
            if path.is_symlink():
                os.lchown(path, identity.uid, identity.gid)
            else:
                _set_owner_mode(
                    path, uid=identity.uid, gid=identity.gid, mode=0o600
                )
        for name in sorted(names):
            path = base / name
            if path.is_symlink():
                os.lchown(path, identity.uid, identity.gid)
            else:
                _set_owner_mode(
                    path, uid=identity.uid, gid=identity.gid, mode=0o700
                )
    _set_owner_mode(root, uid=identity.uid, gid=identity.gid, mode=0o700)


def _copy_dependency_snapshot(source: Path, destination: Path) -> None:
    if source.is_symlink() or not source.is_dir():
        raise CampaignError("Lake package source must be a plain directory")
    if destination.exists() or destination.is_symlink():
        raise CampaignError("shared Lake package destination already exists")
    destination.mkdir(mode=0o700)
    completed = subprocess.run(
        ["cp", "-a", "--reflink=auto", f"{source.resolve()}/.", str(destination)],
        check=False, capture_output=True, text=True,
    )
    if completed.returncode != 0:
        raise CampaignError(
            "cannot create shared Lake package snapshot: "
            + (completed.stderr or completed.stdout).strip()
        )
    _make_tree_read_only(destination)


def _controller_tree_digest(root: Path) -> str:
    try:
        inventory = ITERATION._inventory_tree(root)
    except Exception as exc:
        raise CampaignError(f"cannot inventory controller tree {root}: {exc}") from exc
    return _hash_index(inventory)


def _verify_controller_tree(root: Path, expected_digest: str, *, label: str) -> None:
    try:
        ITERATION._assert_controller_tree(root, label=label)
    except Exception as exc:
        raise CampaignError(f"{label} is not root-owned read-only: {exc}") from exc
    if _controller_tree_digest(root) != expected_digest:
        raise CampaignError(f"{label} inventory changed after preparation")


def _prepare_codex_home(config: Config, identity: Identity) -> str:
    template = config.codex_home_template
    if template is None or template.is_symlink() or not template.is_dir():
        raise CampaignError("a plain trusted Codex home template is required")
    template_metadata = template.stat()
    if (
        template_metadata.st_uid != 0
        or template_metadata.st_gid != 0
        or stat.S_IMODE(template_metadata.st_mode) & 0o077
    ):
        raise CampaignError("Codex home template must be root-only")
    auth = template / "auth.json"
    try:
        auth_metadata = auth.lstat()
    except OSError as exc:
        raise CampaignError("Codex home template has no plain auth.json") from exc
    if (
        stat.S_ISLNK(auth_metadata.st_mode)
        or not stat.S_ISREG(auth_metadata.st_mode)
        or auth_metadata.st_nlink != 1
        or stat.S_IMODE(auth_metadata.st_mode) != 0o600
        or auth_metadata.st_uid != 0
        or auth_metadata.st_gid != 0
    ):
        raise CampaignError("Codex home template has no plain auth.json")
    home = config.user_home(identity.target_id)
    codex_home = config.codex_home(identity.target_id)
    home.mkdir(mode=0o700, parents=True, exist_ok=False)
    codex_home.mkdir(mode=0o700)
    for directory in (home / "tmp", home / ".cache", home / ".config"):
        directory.mkdir(mode=0o700)
    shutil.copy2(auth, codex_home / "auth.json")
    copied = (codex_home / "auth.json").lstat()
    if not stat.S_ISREG(copied.st_mode) or copied.st_nlink != 1:
        raise CampaignError("private Codex credential copy is not unique")
    # User configuration is deliberately not inherited.  The native harness
    # passes --ignore-user-config; only the login token crosses this boundary.
    _make_tree_solver_owned(home, identity)
    return _sha256_bytes((codex_home / "auth.json").read_bytes())


_SEALED_WORKSPACE_PATHS = (
    "isolation_manifest.json",
    "icho_2026_source",
    "ANSWER_BLIND_PROTOCOL.md",
    ".mcp.json",
    ".archon/config.json",
    ".archon/AGENTS.md",
    ".archon/prompts",
    ".archon/prover-modes",
    ".archon/physics-formalize",
    ".archon/lean-explore",
    "blueprint",
    "reports/icho_2026",
    "lakefile.toml",
    "lake-manifest.json",
    ".lake/package-overrides.json",
    "lean-toolchain",
    "archon-protected.yaml",
    "IChO2026Chem.lean",
    "IChO2026Chem",
    "IChO2026Run.lean",
    "IChO2026Run",
    "IChO2026Problems.lean",
    "IChO2026Problems/All.lean",
)


def _harden_target(config: Config, identity: Identity) -> None:
    target_root = config.target_root(identity.target_id)
    workspace = target_root / "workspace"
    if workspace.is_symlink() or not workspace.is_dir():
        raise CampaignError(f"prepared target workspace is unsafe: {workspace}")
    _make_tree_read_only(workspace)
    _set_owner_mode(workspace, uid=0, gid=0, mode=0o755)
    archon_root = workspace / ".archon"
    lake_root = workspace / ".lake"
    for protected_parent in (archon_root, lake_root):
        if protected_parent.is_symlink() or not protected_parent.is_dir():
            raise CampaignError(f"protected project parent is unsafe: {protected_parent}")
        _set_owner_mode(protected_parent, uid=0, gid=0, mode=0o755)
    packages_link = lake_root / "packages"
    if (
        not packages_link.is_symlink()
        or packages_link.resolve() != config.shared_packages.resolve()
    ):
        raise CampaignError("target has a stale dependency link")
    os.lchown(packages_link, 0, 0)

    mutable_directories = (
        "blind_candidates",
        ".lake/build", ".lake/config",
        ".archon/logs", ".archon/task_results", ".archon/proof-journal",
        ".archon/iter", ".archon/tmp", ".archon/preflight", ".archon/git-dir",
    )
    for relative in mutable_directories:
        path = workspace / relative
        path.mkdir(mode=0o700, parents=True, exist_ok=True)
        _make_plain_dir_solver_owned(path, identity)
    mutable_files = (
        f"IChO2026Problems/problem_{identity.target_id}.lean",
        *ITERATION.MUTABLE_STATE_FILES,
    )
    for relative in mutable_files:
        path = workspace / relative
        if path.is_symlink() or (path.exists() and not path.is_file()):
            raise CampaignError(f"mutable state path is unsafe: {path}")
        if not path.exists():
            path.parent.mkdir(mode=0o755, parents=True, exist_ok=True)
            path.touch(mode=0o600)
        _set_owner_mode(path, uid=identity.uid, gid=identity.gid, mode=0o600)
    for protected_parent in (workspace, archon_root, lake_root):
        _set_owner_mode(protected_parent, uid=0, gid=0, mode=0o755)
    _set_owner_mode(
        target_root, uid=identity.uid, gid=identity.gid, mode=0o700
    )
    for name in ("campaign.json", "run.log"):
        path = target_root / name
        if path.exists():
            _set_owner_mode(
                path, uid=identity.uid, gid=identity.gid, mode=0o600
            )


def _probe_as_identity(identity: Identity, path: Path) -> bool:
    """Return whether the identity can traverse ``path`` under real DAC."""
    completed = subprocess.run([
        "setpriv", f"--reuid={identity.uid}", f"--regid={identity.gid}",
        "--clear-groups", "/usr/bin/test", "-x", str(path),
    ], check=False, capture_output=True)
    return completed.returncode == 0


def _verify_dac_isolation(config: Config, identities: Sequence[Identity]) -> None:
    for identity in identities:
        own = config.target_root(identity.target_id)
        if not _probe_as_identity(identity, own):
            raise CampaignError(f"solver user cannot traverse its own target: {identity.username}")
        for peer in identities:
            if peer == identity:
                continue
            if _probe_as_identity(identity, config.target_root(peer.target_id)):
                raise CampaignError(
                    f"solver user {identity.username} can traverse {peer.target_id}"
                )


def _base_target_config(config: Config, target_id: str, *, seed: Path | None) -> Any:
    return NATIVE.Config(
        campaign_root=config.target_root(target_id),
        seed_workspace=seed,
        lake_packages=config.shared_packages,
        archon_bin=config.archon_bin,
        max_iterations=config.max_iterations,
        expected_items=1,
        max_parallel=PER_TARGET_MAX_PARALLEL,
        reuse_lake_packages=True,
        in_place_index=True,
    )


def _target_entry(config: Config, identity: Identity, *, status: str) -> dict[str, Any]:
    return {
        "target_id": identity.target_id,
        "workspace": str(config.target_root(identity.target_id) / "workspace"),
        "codex_home": str(config.codex_home(identity.target_id)),
        "username": identity.username,
        "uid": identity.uid,
        "groupname": identity.groupname,
        "gid": identity.gid,
        "internal_max_parallel": PER_TARGET_MAX_PARALLEL,
        "status": status,
        "updated_at": _utcnow(),
    }


def _base_index(config: Config, identities: Sequence[Identity]) -> dict[str, Any]:
    return {
        "schema_version": SCHEMA_VERSION,
        "pipeline": PIPELINE,
        "status": "preparing",
        "global_max_parallel": config.global_parallel,
        "row_count": len(CANONICAL_TARGET_IDS),
        "target_ids": list(CANONICAL_TARGET_IDS),
        "controller": {
            "seed_workspace": str(config.seed_workspace),
            "lake_packages_source": str(config.lake_packages),
            "codex_home_template": str(config.codex_home_template),
            "shared_lake_packages": str(config.shared_packages),
            "archon_bin": config.archon_bin,
            "python_bin": str(config.python_bin),
            "runtime_root": str(config.runtime_root) if config.runtime_root else None,
            "max_iterations": config.max_iterations,
            "user_prefix": config.user_prefix,
            "uid_base": config.uid_base,
        },
        "targets": {
            item.target_id: _target_entry(config, item, status="pending")
            for item in identities
        },
        "updated_at": _utcnow(),
    }


def _prepare_layout(config: Config) -> None:
    root = config.campaign_root
    if root.exists() and (not root.is_dir() or any(root.iterdir())):
        raise CampaignError(f"campaign root must be absent or empty: {root}")
    root.mkdir(mode=0o700, parents=True, exist_ok=True)
    config.item_root.mkdir(mode=0o711)
    config.home_root.mkdir(mode=0o711)
    config.controller_log_root.mkdir(mode=0o700)
    (root / "quarantine").mkdir(mode=0o700)
    # mkdir(2) applies the caller's umask.  Deployment intentionally uses
    # umask 077, so normalize the two traversal-only parents explicitly after
    # creation; otherwise every solver is blocked before reaching its own
    # UID-owned 0700 leaf.  Neither parent grants read or write authority.
    os.chmod(config.item_root, 0o711)
    os.chmod(config.home_root, 0o711)
    os.chmod(config.controller_log_root, 0o700)
    os.chmod(root / "quarantine", 0o700)
    os.chown(root, 0, 0)
    os.chmod(root, 0o700)


def _set_campaign_solver_access(config: Config, *, enabled: bool) -> None:
    root = config.campaign_root
    metadata = root.stat()
    if metadata.st_uid != 0 or metadata.st_gid != 0:
        raise CampaignError("campaign root must remain root-owned")
    os.chmod(root, 0o711 if enabled else 0o700)


def _global_lock_root() -> Path:
    root = Path("/run/lock/icho-answer-blind-isolated")
    try:
        os.mkdir(root, 0o700)
    except FileExistsError:
        pass
    metadata = os.lstat(root)
    if (
        not stat.S_ISDIR(metadata.st_mode)
        or metadata.st_uid != 0
        or metadata.st_gid != 0
        or stat.S_IMODE(metadata.st_mode) != 0o700
    ):
        raise CampaignError("global isolated-campaign lock root is unsafe")
    return root


def _acquire_global_lock(path: Path, *, busy_message: str) -> int:
    descriptor = os.open(
        path,
        os.O_RDWR | os.O_CREAT | os.O_CLOEXEC | os.O_NOFOLLOW,
        0o600,
    )
    try:
        metadata = os.fstat(descriptor)
        if (
            not stat.S_ISREG(metadata.st_mode)
            or metadata.st_uid != 0
            or metadata.st_gid != 0
            or metadata.st_nlink != 1
            or stat.S_IMODE(metadata.st_mode) != 0o600
        ):
            raise CampaignError(f"unsafe global lock inode: {path}")
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise CampaignError(busy_message) from exc
        return descriptor
    except BaseException:
        os.close(descriptor)
        raise


def _acquire_campaign_lock(campaign_root: Path) -> int:
    # The lock lives outside the campaign tree, so even an absent or root-only
    # tree can be serialized before this controller reads or chmods it.
    canonical = campaign_root.resolve(strict=False)
    key = _sha256_bytes(os.fsencode(str(canonical)))
    return _acquire_global_lock(
        _global_lock_root() / f"campaign-{key}.lock",
        busy_message="another isolated campaign controller is active",
    )


def _acquire_uid_locks(config: Config) -> list[int]:
    global_lock_root = _global_lock_root()
    descriptors: list[int] = []
    try:
        for uid in sorted(item.uid for item in _identity_plan(config)):
            descriptor = _acquire_global_lock(
                global_lock_root / f"uid-{uid}.lock",
                busy_message=f"solver uid {uid} is reserved by another campaign",
            )
            descriptors.append(descriptor)
    except BaseException:
        for descriptor in reversed(descriptors):
            os.close(descriptor)
        raise
    return descriptors


def _prepare_one(
    config: Config,
    identity: Identity,
    *,
    full_manifest: Mapping[str, Any],
    row: Mapping[str, Any],
) -> dict[str, Any]:
    target_root = config.target_root(identity.target_id)
    user_home = config.user_home(identity.target_id)
    stale_target = target_root.exists() or target_root.is_symlink()
    stale_home = user_home.exists() or user_home.is_symlink()
    if stale_target or stale_home:
        quarantine = Path(tempfile.mkdtemp(
            prefix=f"{identity.target_id}-",
            dir=config.campaign_root / "quarantine",
        ))
        if stale_target:
            os.replace(target_root, quarantine / "target")
        if stale_home:
            os.replace(user_home, quarantine / "home")
    with tempfile.TemporaryDirectory(prefix=f"isolated-{identity.target_id}-") as raw:
        subset = Path(raw) / "seed"
        projection = _build_subset_seed(
            seed=config.seed_workspace,
            destination=subset,
            manifest=full_manifest,
            row=row,
        )
        result = NATIVE.run_fresh(
            _base_target_config(config, identity.target_id, seed=subset),
            start_loop=False,
        )
    if result.get("status") != "prepared":
        raise CampaignError(
            f"native preparation failed for {identity.target_id}: {result.get('error')}"
        )
    auth_sha256 = _prepare_codex_home(config, identity)
    _harden_target(config, identity)
    entry = _target_entry(config, identity, status="prepared")
    entry["native"] = result.get("native")
    entry["grounding"] = result.get("grounding")
    entry["bundle_sha256"] = result.get("bundle_sha256")
    entry["codex_auth_sha256"] = auth_sha256
    entry["source_projection"] = {
        "parent_row_sha256": projection["parent_row_sha256"],
        "projected_row_sha256": projection["projected_row_sha256"],
        "derived_pdf": projection["derived_pdf"],
    }
    return entry


def _ensure_mutable_layout(workspace: Path, identity: Identity) -> tuple[Path, ...]:
    mutable_directories = (
        "blind_candidates",
        ".lake/build", ".lake/config",
        ".archon/logs", ".archon/task_results", ".archon/proof-journal",
        ".archon/iter", ".archon/tmp", ".archon/preflight", ".archon/git-dir",
    )
    paths = tuple(
        workspace.joinpath(*Path(relative).parts)
        for relative in (
            *mutable_directories,
            f"IChO2026Problems/problem_{identity.target_id}.lean",
            *ITERATION.MUTABLE_STATE_FILES,
        )
    )
    if any(not path.exists() or path.is_symlink() for path in paths):
        raise CampaignError("target mutable layout is incomplete or unsafe")
    return paths


def _runtime_root(config: Config) -> Path:
    if config.runtime_root is not None:
        root = config.runtime_root.resolve(strict=True)
    else:
        archon = Path(config.archon_bin).resolve(strict=True)
        if archon.parent.name != "bin":
            raise CampaignError("runtime-root is required for a nonstandard Archon path")
        root = archon.parent.parent
    if root.is_symlink() or not root.is_dir():
        raise CampaignError("runtime root must be a plain directory")
    if root.stat().st_uid != 0 or root.stat().st_mode & 0o022:
        raise CampaignError("runtime root must be controller-owned and read-only")
    return root


def _system_read_paths(runtime: Path) -> tuple[Path, ...]:
    try:
        system, _inventory = ITERATION._system_readonly_inventory(runtime)
    except Exception as exc:
        raise CampaignError(f"cannot inventory exact runtime dependencies: {exc}") from exc
    read_write_devices = set(_system_read_write_paths())
    devices = tuple(
        Path(raw).resolve(strict=True)
        for raw in ITERATION.SYSTEM_DEVICE_FILES
        if Path(raw).exists()
        and Path(raw).resolve(strict=True) not in read_write_devices
    )
    return tuple(dict.fromkeys((*system, *devices)))


def _system_read_write_paths() -> tuple[Path, ...]:
    devices: list[Path] = []
    for raw in _LANDLOCK_READ_WRITE_DEVICE_FILES:
        try:
            resolved = Path(raw).resolve(strict=True)
            metadata = resolved.stat()
        except OSError as exc:
            raise CampaignError(f"required writable device is unavailable: {raw}") from exc
        if (
            not stat.S_ISCHR(metadata.st_mode)
            or metadata.st_rdev != os.makedev(1, 3)
            or metadata.st_uid != 0
            or metadata.st_gid != 0
            or stat.S_IMODE(metadata.st_mode) != 0o666
        ):
            raise CampaignError(f"required writable device is unsafe: {resolved}")
        devices.append(resolved)
    return tuple(dict.fromkeys(devices))


def _deny_probe_paths(
    config: Config,
    identity: Identity,
    identities: Sequence[Identity],
    peer_pids: Sequence[int],
) -> tuple[Path, ...]:
    paths = [
        Path("/root"), Path("/tmp"), Path("/var/tmp"), Path("/dev/shm"),
        Path("/proc/1/environ"), Path("/proc/self/cmdline"),
        config.campaign_root, config.index_path, config.controller_log_root,
    ]
    paths.extend(Path(f"/proc/{pid}/cmdline") for pid in peer_pids if pid > 0)
    for peer in identities:
        if peer == identity:
            continue
        paths.extend((config.target_root(peer.target_id), config.user_home(peer.target_id)))
    return tuple(paths)


def _negative_open_probe(path: Path) -> dict[str, Any]:
    try:
        descriptor = os.open(path, os.O_RDONLY | os.O_CLOEXEC)
    except OSError as exc:
        if exc.errno not in {errno.EACCES, errno.EPERM}:
            raise CampaignError(
                f"deny probe did not fail with an access error: {path}: {exc}"
            ) from exc
        return {"path": str(path), "denied": True, "errno": exc.errno}
    else:
        os.close(descriptor)
        raise CampaignError(f"isolation deny probe unexpectedly succeeded: {path}")


def _solver_environment(config: Config, identity: Identity, runtime: Path) -> dict[str, str]:
    home = config.user_home(identity.target_id)
    environment = {
        "HOME": str(home),
        "CODEX_HOME": str(config.codex_home(identity.target_id)),
        "TMPDIR": str(home / "tmp"),
        "TMP": str(home / "tmp"),
        "TEMP": str(home / "tmp"),
        "XDG_CACHE_HOME": str(home / ".cache"),
        "XDG_CONFIG_HOME": str(home / ".config"),
        "USER": identity.username,
        "LOGNAME": identity.username,
        "SHELL": str(runtime / "bin/bash"),
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
        "PATH": ":".join((
            str(runtime / "bin"), str(runtime / "lean-v4.31.0/bin"),
        )),
        "PYTHONSAFEPATH": "1",
        "PYTHONNOUSERSITE": "1",
        "PYTHONDONTWRITEBYTECODE": "1",
        "GIT_OPTIONAL_LOCKS": "0",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_CONFIG_GLOBAL": "/dev/null",
        "GIT_CONFIG_SYSTEM": "/dev/null",
        "GIT_DISCOVERY_ACROSS_FILESYSTEM": "0",
        "TZ": "Etc/UTC",
        "PYTHONHASHSEED": "0",
    }
    for name in ("SSL_CERT_FILE", "SSL_CERT_DIR"):
        if os.environ.get(name):
            environment[name] = os.environ[name]
    return environment


def _write_child_receipt(descriptor: int, value: Mapping[str, Any]) -> None:
    payload = _canonical_json_bytes(dict(value))
    offset = 0
    while offset < len(payload):
        written = os.write(descriptor, payload[offset:])
        if written <= 0:
            raise CampaignError("isolation receipt pipe made no progress")
        offset += written


def _close_fds_except(kept: Sequence[int]) -> None:
    keep = sorted({0, 1, 2, *kept})
    soft, _hard = resource.getrlimit(resource.RLIMIT_NOFILE)
    maximum = 1_048_576 if soft == resource.RLIM_INFINITY else int(soft)
    cursor = 3
    for descriptor in keep:
        if descriptor < cursor:
            continue
        os.closerange(cursor, descriptor)
        cursor = descriptor + 1
    os.closerange(cursor, maximum)


def _uid_pids(uid: int) -> tuple[int, ...]:
    return tuple(ITERATION._real_uid_pids(uid))


def _proc_identity(process_id: int) -> tuple[int, str, str]:
    raw_stat = Path(f"/proc/{process_id}/stat").read_text(encoding="utf-8")
    close = raw_stat.rfind(")")
    if close < 0:
        raise CampaignError("malformed proc stat")
    tail = raw_stat[close + 2 :].split()
    if len(tail) <= 19:
        raise CampaignError("short proc stat")
    state = tail[0]
    start_ticks = tail[19]
    uid = int(next(
        line for line in Path(f"/proc/{process_id}/status").read_text().splitlines()
        if line.startswith("Uid:")
    ).split()[1])
    return uid, start_ticks, state


def _cleanup_identity_processes(
    identity: Identity, *, quiet_period_ms: int = 600,
) -> dict[str, Any]:
    if not hasattr(os, "pidfd_open") or not hasattr(signal, "pidfd_send_signal"):
        raise CampaignError("pidfd process cleanup is required")
    before = _uid_pids(identity.uid)
    prlimit_ok = True
    kill_rounds = 0
    quiet_since: float | None = None
    deadline = time.monotonic() + 10.0
    while time.monotonic() < deadline:
        pids = _uid_pids(identity.uid)
        ITERATION._reap_controller_children(pids)
        pids = _uid_pids(identity.uid)
        if not pids:
            if quiet_since is None:
                quiet_since = time.monotonic()
            if (time.monotonic() - quiet_since) * 1000 >= quiet_period_ms:
                if not prlimit_ok:
                    raise CampaignError(
                        f"kernel denied RLIMIT_NPROC freeze for solver UID {identity.uid}"
                    )
                return {
                    "mechanism": "dedicated_uid_starttime_pidfd_prlimit_v2",
                    "uid": identity.uid,
                    "before_pids": list(before),
                    "prlimit_zero_applied": prlimit_ok,
                    "pidfd_kill_used": bool(before or kill_rounds),
                    "kill_rounds": kill_rounds,
                    "quiet_period_ms": quiet_period_ms,
                    "after_pids": [],
                    "quiescent_after": prlimit_ok,
                }
            time.sleep(0.025)
            continue
        quiet_since = None
        kill_rounds += 1
        for process_id in pids:
            try:
                pidfd = os.pidfd_open(process_id, 0)
            except ProcessLookupError:
                continue
            stopped = False
            terminated = False
            try:
                # Bind the kernel process object first.  Reading /proc before
                # pidfd_open would allow the numeric PID to be recycled between
                # validation and SIGSTOP, potentially stopping an unrelated
                # process.  Every signal below targets this pidfd.
                try:
                    expected_uid, expected_start, _state = _proc_identity(process_id)
                except (OSError, StopIteration, ValueError, IndexError):
                    continue
                if expected_uid != identity.uid:
                    continue
                signal.pidfd_send_signal(pidfd, signal.SIGSTOP)
                stopped = True
                stop_deadline = time.monotonic() + 1.0
                disappeared = False
                while True:
                    try:
                        current_uid, current_start, current_state = _proc_identity(process_id)
                    except FileNotFoundError:
                        disappeared = True
                        break
                    if current_state in {"T", "t"}:
                        break
                    if time.monotonic() >= stop_deadline:
                        signal.pidfd_send_signal(pidfd, signal.SIGKILL)
                        terminated = True
                        stopped = False
                        raise CampaignError(
                            "dedicated-UID process did not stop before prlimit"
                        )
                    time.sleep(0.01)
                if disappeared:
                    continue
                if current_start != expected_start or current_uid != identity.uid:
                    raise CampaignError("pid identity changed during dedicated-UID cleanup")
                try:
                    resource.prlimit(process_id, resource.RLIMIT_NPROC, (0, 0))
                except ProcessLookupError:
                    continue
                except (PermissionError, OSError):
                    prlimit_ok = False
                signal.pidfd_send_signal(pidfd, signal.SIGKILL)
                terminated = True
                stopped = False
            except (ProcessLookupError, FileNotFoundError):
                pass
            finally:
                # If validation failed after SIGSTOP (including a /proc
                # start-time mismatch), never strand the pidfd-bound process
                # in a stopped state.  This signal cannot affect a recycled
                # numeric PID because it is sent through the original pidfd.
                if stopped and not terminated:
                    try:
                        signal.pidfd_send_signal(pidfd, signal.SIGCONT)
                    except ProcessLookupError:
                        pass
                os.close(pidfd)
        time.sleep(0.025)
    after = _uid_pids(identity.uid)
    raise CampaignError(
        f"dedicated solver UID {identity.uid} is not quiescent: {after}; "
        f"prlimit_ok={prlimit_ok}"
    )


def _sweep_identities(
    identities: Sequence[Identity], *, phase: str,
) -> tuple[dict[str, dict[str, Any]], list[str]]:
    """Sweep every verified identity even if an earlier sweep fails."""
    receipts: dict[str, dict[str, Any]] = {}
    errors: list[str] = []
    for identity in identities:
        try:
            receipts[identity.target_id] = _cleanup_identity_processes(identity)
        except BaseException as exc:
            errors.append(
                f"{identity.target_id}: {phase}: {type(exc).__name__}: {exc}"
            )
    return receipts, errors


def _child_main(
    config: Config,
    identity: Identity,
    identities: Sequence[Identity],
    *,
    control_fd: int,
    receipt_fd: int,
    resume: bool,
    controller_pid: int,
) -> None:
    try:
        library = _libc()
        if library.prctl(_PR_SET_PDEATHSIG, signal.SIGKILL, 0, 0, 0) != 0:
            error = ctypes.get_errno()
            raise OSError(error, os.strerror(error))
        if os.getppid() != controller_pid:
            raise CampaignError("trusted controller died during worker startup")
        raw = b""
        while not raw.endswith(b"\n"):
            chunk = os.read(control_fd, 4096)
            if not chunk:
                raise CampaignError("controller start barrier closed unexpectedly")
            raw += chunk
        peer_pids = tuple(int(value) for value in json.loads(raw))
        os.close(control_fd)
        os.setsid()

        target_root = config.target_root(identity.target_id)
        workspace = target_root / "workspace"
        mutable = _ensure_mutable_layout(workspace, identity)
        runtime = _runtime_root(config)
        os.chdir(workspace)
        landlock = _apply_landlock(
            read_only=(
                runtime, config.shared_packages, workspace,
                *_system_read_paths(runtime),
            ),
            read_write=(
                *_system_read_write_paths(),
                target_root / "campaign.json", target_root / "run.log",
                config.user_home(identity.target_id), *mutable,
            ),
        )
        os.setgroups([])
        os.setgid(identity.gid)
        os.setuid(identity.uid)
        # Linux clears PDEATHSIG across a credential transition.
        if library.prctl(_PR_SET_PDEATHSIG, signal.SIGKILL, 0, 0, 0) != 0:
            error = ctypes.get_errno()
            raise OSError(error, os.strerror(error))
        if os.getppid() != controller_pid:
            raise CampaignError("trusted controller died during identity transition")
        resource.setrlimit(resource.RLIMIT_NPROC, (128, 128))
        if os.geteuid() != identity.uid or os.getegid() != identity.gid:
            raise CampaignError("failed to enter the target solver identity")

        probe_paths = list(_deny_probe_paths(
            config, identity, identities, peer_pids,
        ))
        for process_id in peer_pids:
            probe_paths.extend((
                Path(f"/proc/{process_id}/environ"),
                Path(f"/proc/{process_id}/mem"),
                Path(f"/proc/{process_id}/fd"),
            ))
        for peer in identities:
            if peer != identity:
                probe_paths.append(config.codex_home(peer.target_id) / "auth.json")
        probes = [_negative_open_probe(path) for path in probe_paths]
        # Positive checks prove the allowlist is useful, not merely denying all
        # files.  The writable home probe uses an exact, target-private path.
        (config.user_home(identity.target_id) / "tmp" / ".isolation-probe").write_text(
            "ok\n", encoding="utf-8"
        )
        (workspace / BUNDLE_REL).read_bytes()
        receipt = {
            "target_id": identity.target_id,
            "uid": os.geteuid(), "gid": os.getegid(),
            "filesystem_answer_blind": True,
            "network_answer_blind": False,
            "landlock": landlock,
            "isolation_probes": probes,
            "peer_pids": list(peer_pids),
            "created_at": _utcnow(),
        }
        _write_child_receipt(receipt_fd, receipt)
        os.close(receipt_fd)

        os.environ.clear()
        os.environ.update(_solver_environment(config, identity, runtime))
        native_config = _base_target_config(config, identity.target_id, seed=None)
        result = NATIVE.resume_campaign(native_config)
        if result.get("status") != "succeeded":
            raise CampaignError(
                f"native target ended with status {result.get('status')}: "
                f"{result.get('error')}"
            )
        os._exit(0)
    except BaseException as exc:
        try:
            _write_child_receipt(receipt_fd, {
                "target_id": identity.target_id,
                "error": f"{type(exc).__name__}: {exc}",
                "created_at": _utcnow(),
            })
        except BaseException:
            pass
        try:
            os.write(2, f"isolated target failed: {type(exc).__name__}: {exc}\n".encode())
        except BaseException:
            pass
        os._exit(1)


@dataclasses.dataclass
class _Child:
    identity: Identity
    pid: int
    pidfd: int
    control_fd: int
    receipt_fd: int
    log_fd: int
    started: float


def _spawn_child(
    config: Config,
    identity: Identity,
    identities: Sequence[Identity],
    *,
    resume: bool,
) -> _Child:
    if threading.active_count() != 1:
        raise CampaignError("model workers may be forked only from a single-thread controller")
    control_read, control_write = os.pipe2(os.O_CLOEXEC)
    receipt_read, receipt_write = os.pipe2(os.O_CLOEXEC)
    log_path = config.controller_log_root / f"{identity.target_id}.log"
    log_fd = os.open(
        log_path,
        os.O_WRONLY | os.O_CREAT | os.O_APPEND | os.O_CLOEXEC | os.O_NOFOLLOW,
        0o600,
    )
    controller_pid = os.getpid()
    pid = os.fork()
    if pid == 0:
        os.close(control_write)
        os.close(receipt_read)
        null_fd = os.open("/dev/null", os.O_RDONLY | os.O_CLOEXEC)
        os.dup2(null_fd, 0)
        os.close(null_fd)
        os.dup2(log_fd, 1)
        os.dup2(log_fd, 2)
        if log_fd not in {1, 2}:
            os.close(log_fd)
        _close_fds_except((control_read, receipt_write))
        _child_main(
            config, identity, identities,
            control_fd=control_read, receipt_fd=receipt_write, resume=resume,
            controller_pid=controller_pid,
        )
        os._exit(127)
    os.close(control_read)
    os.close(receipt_write)
    try:
        pidfd = os.pidfd_open(pid, 0)
    except BaseException:
        os.kill(pid, signal.SIGKILL)
        os.waitpid(pid, 0)
        raise
    return _Child(
        identity, pid, pidfd, control_write, receipt_read, log_fd,
        time.monotonic(),
    )


def _terminate_child(child: _Child) -> dict[str, Any]:
    reaped = False
    try:
        signal.pidfd_send_signal(child.pidfd, signal.SIGTERM)
    except ProcessLookupError:
        pass
    deadline = time.monotonic() + 1.0
    while time.monotonic() < deadline:
        try:
            waited, _status = os.waitpid(child.pid, os.WNOHANG)
        except ChildProcessError:
            reaped = True
            break
        if waited:
            reaped = True
            break
        time.sleep(0.025)
    else:
        try:
            signal.pidfd_send_signal(child.pidfd, signal.SIGKILL)
        except ProcessLookupError:
            pass
        try:
            os.waitpid(child.pid, 0)
        except ChildProcessError:
            pass
        else:
            reaped = True
    if not reaped:
        try:
            os.waitpid(child.pid, 0)
        except ChildProcessError:
            pass
    return _cleanup_identity_processes(child.identity)


def _close_child_fds(child: _Child) -> None:
    for field in ("pidfd", "control_fd", "receipt_fd", "log_fd"):
        descriptor = getattr(child, field)
        if descriptor >= 0:
            try:
                os.close(descriptor)
            except OSError:
                pass
            setattr(child, field, -1)


def _read_receipt(child: _Child, *, timeout_seconds: float = 30.0) -> dict[str, Any]:
    payload = b""
    deadline = time.monotonic() + timeout_seconds
    selector = selectors.DefaultSelector()
    selector.register(child.receipt_fd, selectors.EVENT_READ)
    try:
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise CampaignError(
                    f"isolation receipt timed out for {child.identity.target_id}"
                )
            if not selector.select(remaining):
                raise CampaignError(
                    f"isolation receipt timed out for {child.identity.target_id}"
                )
            chunk = os.read(child.receipt_fd, 65536)
            if not chunk:
                break
            payload += chunk
            if len(payload) > 1024 * 1024:
                raise CampaignError(
                    f"oversized isolation receipt from {child.identity.target_id}"
                )
    finally:
        selector.close()
        os.close(child.receipt_fd)
        child.receipt_fd = -1
    try:
        rows = [json.loads(line) for line in payload.splitlines() if line.strip()]
    except json.JSONDecodeError as exc:
        raise CampaignError(
            f"invalid isolation receipt from {child.identity.target_id}"
        ) from exc
    if len(rows) != 1 or not isinstance(rows[0], dict):
        raise CampaignError(
            f"missing unique isolation receipt from {child.identity.target_id}"
        )
    return rows[0]


def _read_batch_receipts(
    children: Sequence[_Child], *, timeout_seconds: float = 30.0,
) -> tuple[dict[int, dict[str, Any]], dict[int, str]]:
    selector = selectors.DefaultSelector()
    payloads = {child.pid: bytearray() for child in children}
    by_fd = {child.receipt_fd: child for child in children}
    receipts: dict[int, dict[str, Any]] = {}
    errors: dict[int, str] = {}
    for descriptor in by_fd:
        selector.register(descriptor, selectors.EVENT_READ)
    deadline = time.monotonic() + timeout_seconds
    try:
        while by_fd:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                for child in by_fd.values():
                    errors[child.pid] = "isolation receipt timed out"
                break
            events = selector.select(remaining)
            if not events:
                continue
            for key, _mask in events:
                descriptor = key.fd
                child = by_fd.get(descriptor)
                if child is None:
                    continue
                chunk = os.read(descriptor, 65536)
                if chunk:
                    payloads[child.pid].extend(chunk)
                    if len(payloads[child.pid]) > 1024 * 1024:
                        errors[child.pid] = "oversized isolation receipt"
                        selector.unregister(descriptor)
                        by_fd.pop(descriptor)
                    continue
                selector.unregister(descriptor)
                by_fd.pop(descriptor)
                try:
                    rows = [
                        json.loads(line)
                        for line in bytes(payloads[child.pid]).splitlines()
                        if line.strip()
                    ]
                    if len(rows) != 1 or not isinstance(rows[0], dict):
                        raise ValueError("receipt is not one JSON object")
                    receipts[child.pid] = rows[0]
                except (json.JSONDecodeError, ValueError) as exc:
                    errors[child.pid] = f"invalid isolation receipt: {exc}"
    finally:
        selector.close()
        for child in children:
            if child.receipt_fd >= 0:
                try:
                    os.close(child.receipt_fd)
                except OSError:
                    pass
                child.receipt_fd = -1
    return receipts, errors


def _save_receipt(config: Config, target_id: str, receipt: Mapping[str, Any]) -> None:
    path = config.controller_log_root / f"{target_id}.isolation.json"
    _atomic_write(path, receipt)


def _validate_isolation_receipt(
    config: Config,
    identity: Identity,
    identities: Sequence[Identity],
    receipt: Mapping[str, Any],
) -> None:
    landlock = receipt.get("landlock")
    abi = landlock.get("abi") if isinstance(landlock, Mapping) else None
    if (
        receipt.get("target_id") != identity.target_id
        or receipt.get("uid") != identity.uid
        or receipt.get("gid") != identity.gid
        or receipt.get("filesystem_answer_blind") is not True
        or receipt.get("network_answer_blind") is not False
        or not isinstance(landlock, Mapping)
        or not isinstance(abi, int)
        or isinstance(abi, bool)
        or abi < 4
        or landlock.get("deny_by_default") is not True
        or landlock.get("no_new_privs") is not True
    ):
        raise CampaignError(f"isolation receipt metadata is invalid: {identity.target_id}")
    probes = receipt.get("isolation_probes")
    if not isinstance(probes, list) or not probes or any(
        not isinstance(row, Mapping)
        or not isinstance(row.get("path"), str)
        or row.get("denied") is not True
        or row.get("errno") not in {errno.EACCES, errno.EPERM}
        for row in probes
    ):
        raise CampaignError(f"isolation receipt probes are invalid: {identity.target_id}")
    actual = {str(row.get("path")) for row in probes}
    stable_required = {
        "/root", "/tmp", "/var/tmp", "/dev/shm", "/proc/1/environ",
        "/proc/self/cmdline", str(config.campaign_root), str(config.index_path),
        str(config.controller_log_root),
    }
    for peer in identities:
        if peer != identity:
            stable_required.update({
                str(config.target_root(peer.target_id)),
                str(config.user_home(peer.target_id)),
                str(config.codex_home(peer.target_id) / "auth.json"),
            })
    if not stable_required.issubset(actual):
        raise CampaignError(f"isolation receipt omits peer/proc probes: {identity.target_id}")


def _load_target_native_index(config: Config, target_id: str) -> dict[str, Any]:
    path = config.target_root(target_id) / "campaign.json"
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise CampaignError(f"target {target_id} has no valid native index") from exc
    if value.get("pipeline") != NATIVE.PIPELINE or value.get("row_count") != 1:
        raise CampaignError(f"target {target_id} native index has invalid scope")
    return value


def _validate_aggregate_index(config: Config, value: Mapping[str, Any]) -> None:
    targets = value.get("targets")
    controller = value.get("controller")
    if (
        value.get("schema_version") != SCHEMA_VERSION
        or value.get("pipeline") != PIPELINE
        or value.get("global_max_parallel") != GLOBAL_MAX_PARALLEL
        or value.get("row_count") != len(CANONICAL_TARGET_IDS)
        or tuple(value.get("target_ids") or ()) != CANONICAL_TARGET_IDS
        or not isinstance(targets, Mapping)
        or tuple(targets) != CANONICAL_TARGET_IDS
        or not isinstance(controller, Mapping)
    ):
        raise CampaignError("aggregate campaign index has invalid scope")
    lineage = value.get("source_lineage")
    row_hashes = (
        lineage.get("canonical_row_sha256")
        if isinstance(lineage, Mapping) else None
    )
    if (
        not isinstance(lineage, Mapping)
        or re.fullmatch(r"[0-9a-f]{64}", str(lineage.get("parent_manifest_sha256") or "")) is None
        or re.fullmatch(r"[0-9a-f]{64}", str(lineage.get("parent_bundle_sha256") or "")) is None
        or not isinstance(row_hashes, Mapping)
        or tuple(row_hashes) != CANONICAL_TARGET_IDS
        or any(
            re.fullmatch(r"[0-9a-f]{64}", str(digest or "")) is None
            for digest in row_hashes.values()
        )
    ):
        raise CampaignError("aggregate campaign source lineage is invalid")
    for name in (
        "runtime_inventory_sha256", "dependency_inventory_sha256",
        "original_seed_manifest_sha256", "original_seed_bundle_sha256",
    ):
        if re.fullmatch(r"[0-9a-f]{64}", str(controller.get(name) or "")) is None:
            raise CampaignError(f"aggregate controller hash is invalid: {name}")
    for target_id, row in targets.items():
        if (
            not isinstance(row, Mapping)
            or row.get("target_id") != target_id
            or row.get("internal_max_parallel") != 1
            or row.get("workspace")
            != str(config.target_root(target_id) / "workspace")
            or row.get("codex_home") != str(config.codex_home(target_id))
        ):
            raise CampaignError(f"aggregate campaign target entry drift: {target_id}")


def _verify_resume_bindings(config: Config, index: Mapping[str, Any]) -> None:
    identities = _identity_plan(config)
    by_id = {item.target_id: item for item in identities}
    for target_id, entry in index["targets"].items():
        identity = by_id[target_id]
        if (
            entry.get("uid") != identity.uid
            or entry.get("gid") != identity.gid
            or entry.get("username") != identity.username
            or entry.get("groupname") != identity.groupname
        ):
            raise CampaignError(f"target identity changed before resume: {target_id}")
        target_root = config.target_root(target_id)
        home = config.user_home(target_id)
        if entry.get("status") in {"pending", "preparation_failed"}:
            continue
        if not target_root.is_dir() or not home.is_dir():
            raise CampaignError(f"target workspace/home is missing before resume: {target_id}")
        target_meta = target_root.stat()
        home_meta = home.stat()
        if (
            (target_meta.st_uid, target_meta.st_gid, stat.S_IMODE(target_meta.st_mode))
            != (identity.uid, identity.gid, 0o700)
            or (home_meta.st_uid, home_meta.st_gid, stat.S_IMODE(home_meta.st_mode))
            != (identity.uid, identity.gid, 0o700)
        ):
            raise CampaignError(f"target workspace/home ownership drift: {target_id}")


def _load_index(config: Config) -> dict[str, Any]:
    try:
        value = json.loads(config.index_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise CampaignError("aggregate campaign index is missing or invalid") from exc
    if not isinstance(value, dict):
        raise CampaignError("aggregate campaign index is not an object")
    _validate_aggregate_index(config, value)
    return value


def _stored_config(campaign_root: Path) -> Config:
    root = campaign_root.resolve()
    path = root / "campaign.json"
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
        controller = value["controller"]
    except (OSError, UnicodeDecodeError, json.JSONDecodeError, KeyError, TypeError) as exc:
        raise CampaignError("cannot recover controller configuration") from exc
    runtime_value = controller.get("runtime_root")
    config = Config(
        campaign_root=root,
        seed_workspace=Path(controller["seed_workspace"]),
        lake_packages=Path(controller["lake_packages_source"]),
        codex_home_template=Path(controller["codex_home_template"]),
        archon_bin=str(controller["archon_bin"]),
        python_bin=Path(controller["python_bin"]),
        runtime_root=Path(runtime_value) if runtime_value else None,
        max_iterations=int(controller["max_iterations"]),
        global_parallel=int(value["global_max_parallel"]),
        user_prefix=str(controller["user_prefix"]),
        uid_base=int(controller["uid_base"]),
        provision_identities=False,
    )
    _validate_aggregate_index(config, value)
    return config


def _validate_fresh_config(config: Config) -> tuple[Path, Path]:
    if config.seed_workspace is None or config.lake_packages is None:
        raise CampaignError("fresh preparation requires seed and Lake package roots")
    if config.codex_home_template is None:
        raise CampaignError("fresh preparation requires a Codex home template")
    if config.global_parallel != GLOBAL_MAX_PARALLEL:
        raise CampaignError("the isolated campaign global concurrency must be exactly four")
    if config.max_iterations < 1:
        raise CampaignError("max_iterations must be positive")
    root = config.campaign_root.resolve()
    seed = config.seed_workspace.resolve()
    packages = config.lake_packages.resolve()
    if any(
        left == right or left.is_relative_to(right) or right.is_relative_to(left)
        for left, right in ((root, seed), (root, packages), (seed, packages))
    ):
        raise CampaignError("campaign, seed, and dependency roots must be disjoint")
    return seed, packages


def _prepare_campaign_locked(config: Config) -> dict[str, Any]:
    seed, packages = _validate_fresh_config(config)
    config = dataclasses.replace(
        config, campaign_root=config.campaign_root.resolve(),
        seed_workspace=seed, lake_packages=packages,
    )
    identities = _identity_plan(config)
    _ensure_identities(config, identities)
    full_manifest, rows = _load_full_seed(seed)
    _runtime_root(config)
    _prepare_layout(config)
    _copy_dependency_snapshot(packages, config.shared_packages)
    index = _base_index(config, identities)
    index["source_lineage"] = {
        "parent_manifest_sha256": _sha256_bytes((seed / MANIFEST_REL).read_bytes()),
        "parent_bundle_sha256": _sha256_bytes((seed / BUNDLE_REL).read_bytes()),
        "canonical_row_sha256": {
            target_id: _sha256_bytes(_canonical_json_bytes(rows[target_id]))
            for target_id in CANONICAL_TARGET_IDS
        },
    }
    runtime = _runtime_root(config)
    index["controller"]["runtime_inventory_sha256"] = _controller_tree_digest(runtime)
    index["controller"]["dependency_inventory_sha256"] = _controller_tree_digest(
        config.shared_packages
    )
    index["controller"]["original_seed_manifest_sha256"] = (
        index["source_lineage"]["parent_manifest_sha256"]
    )
    index["controller"]["original_seed_bundle_sha256"] = (
        index["source_lineage"]["parent_bundle_sha256"]
    )
    _atomic_write(config.index_path, index)

    with ThreadPoolExecutor(
        max_workers=config.global_parallel,
        thread_name_prefix="isolated-prepare",
    ) as executor:
        futures = {
            executor.submit(
                _prepare_one,
                config,
                identity,
                full_manifest=full_manifest,
                row=rows[identity.target_id],
            ): identity
            for identity in identities
        }
        for future in as_completed(futures):
            identity = futures[future]
            try:
                entry = future.result()
            except BaseException as exc:
                index["targets"][identity.target_id].update({
                    "status": "preparation_failed",
                    "error": f"{type(exc).__name__}: {exc}",
                    "updated_at": _utcnow(),
                })
                index.update(status="preparation_failed", updated_at=_utcnow())
                _atomic_write(config.index_path, index)
                for pending in futures:
                    pending.cancel()
                raise
            index["targets"][identity.target_id] = entry
            index["prepared_count"] = sum(
                row.get("status") == "prepared" for row in index["targets"].values()
            )
            index["updated_at"] = _utcnow()
            _atomic_write(config.index_path, index)

    index.update(
        status="prepared",
        phase="prepared",
        prepared_count=len(identities),
        dac_peer_isolation_verified=False,
        updated_at=_utcnow(),
    )
    _atomic_write(config.index_path, index)
    return index


def prepare_campaign(config: Config, *, start: bool) -> dict[str, Any]:
    config = dataclasses.replace(
        config, campaign_root=config.campaign_root.resolve(strict=False),
    )
    campaign_lock = _acquire_campaign_lock(config.campaign_root)
    uid_locks: list[int] = []
    access_enabled_by_us = False
    identities: tuple[Identity, ...] = ()
    identities_verified = False
    result: dict[str, Any] | None = None
    primary_error: BaseException | None = None
    cleanup_errors: list[str] = []
    try:
        # Every entry point uses campaign-lock -> sorted UID-lock ordering.
        # Nothing under the campaign root is read, created, or chmodded before
        # both lock classes are held.
        uid_locks = _acquire_uid_locks(config)
        identities = _identity_plan(config)
        _ensure_identities(config, identities)
        identities_verified = True
        _receipts, pre_errors = _sweep_identities(
            identities, phase="pre-prepare UID sweep",
        )
        if pre_errors:
            raise CampaignError(
                "dedicated UID pre-prepare cleanup failed: " + "; ".join(pre_errors)
            )
        index = _prepare_campaign_locked(config)
        prepare_cleanup, prepare_cleanup_errors = _sweep_identities(
            identities, phase="post-prepare UID sweep",
        )
        if prepare_cleanup_errors:
            raise CampaignError(
                "dedicated UID post-prepare cleanup failed: "
                + "; ".join(prepare_cleanup_errors)
            )
        _set_campaign_solver_access(config, enabled=True)
        access_enabled_by_us = True
        _verify_dac_isolation(config, identities)
        index.update(
            dac_peer_isolation_verified=True,
            dedicated_uid_prepare_cleanup=prepare_cleanup,
            updated_at=_utcnow(),
        )
        _atomic_write(config.index_path, index)
        if start:
            result = _run_campaign_locked(config, index=index, resume=False)
        else:
            result = index
    except BaseException as exc:
        primary_error = exc
    finally:
        try:
            if identities_verified:
                _receipts, cleanup_errors = _sweep_identities(
                    identities, phase="prepare final UID sweep",
                )
        finally:
            try:
                if access_enabled_by_us:
                    _set_campaign_solver_access(config, enabled=False)
            finally:
                for descriptor in reversed(uid_locks):
                    os.close(descriptor)
                os.close(campaign_lock)
    if cleanup_errors:
        message = "dedicated UID prepare cleanup failed: " + "; ".join(cleanup_errors)
        if primary_error is not None:
            raise CampaignError(message) from primary_error
        raise CampaignError(message)
    if primary_error is not None:
        raise primary_error
    if result is None:
        raise CampaignError("preparation returned no terminal index")
    return result


def _finish_partial_preparation(
    config: Config,
    index: dict[str, Any],
    identities: Sequence[Identity],
) -> dict[str, Any]:
    full_manifest, rows = _load_full_seed(config.seed_workspace)
    lineage = index.get("source_lineage") or {}
    current_lineage = {
        "parent_manifest_sha256": _sha256_bytes(
            (config.seed_workspace / MANIFEST_REL).read_bytes()
        ),
        "parent_bundle_sha256": _sha256_bytes(
            (config.seed_workspace / BUNDLE_REL).read_bytes()
        ),
        "canonical_row_sha256": {
            target_id: _sha256_bytes(_canonical_json_bytes(rows[target_id]))
            for target_id in CANONICAL_TARGET_IDS
        },
    }
    if lineage != current_lineage:
        raise CampaignError("source seed lineage changed during partial preparation")
    if not config.shared_packages.is_dir():
        raise CampaignError("shared dependency snapshot is missing on resume")
    pending_identities = [
        identity for identity in identities
        if index["targets"][identity.target_id].get("status")
        not in {"prepared", "running", "succeeded", "failed", "incomplete"}
    ]
    with ThreadPoolExecutor(
        max_workers=config.global_parallel,
        thread_name_prefix="isolated-prepare-resume",
    ) as executor:
        futures = {
            executor.submit(
                _prepare_one,
                config,
                identity,
                full_manifest=full_manifest,
                row=rows[identity.target_id],
            ): identity
            for identity in pending_identities
        }
        for future in as_completed(futures):
            identity = futures[future]
            index["targets"][identity.target_id] = future.result()
            index.update(status="preparing", updated_at=_utcnow())
            _atomic_write(config.index_path, index)
    index.update(
        status="prepared", phase="prepared", prepared_count=len(identities),
        # The campaign root remains root-only during recovery.  The run path
        # opens it only after holding every global UID lock, then performs the
        # real downgraded-user DAC probes immediately before spawning workers.
        dac_peer_isolation_verified=False, updated_at=_utcnow(),
    )
    _atomic_write(config.index_path, index)
    return index


def _run_campaign_verified(
    config: Config,
    *,
    identities: Sequence[Identity],
    index: dict[str, Any] | None = None,
    resume: bool,
) -> dict[str, Any]:
    startup_cleanup, startup_errors = _sweep_identities(
        identities, phase="startup UID sweep",
    )
    if startup_errors:
        raise CampaignError(
            "dedicated UID startup cleanup failed: " + "; ".join(startup_errors)
        )
    index = index or _load_index(config)
    controller = index.get("controller") or {}
    _verify_controller_tree(
        _runtime_root(config),
        str(controller.get("runtime_inventory_sha256") or ""),
        label="sealed runtime",
    )
    _verify_controller_tree(
        config.shared_packages,
        str(controller.get("dependency_inventory_sha256") or ""),
        label="shared Lake packages",
    )
    _verify_dac_isolation(config, identities)
    pending = [
        identity for identity in identities
        if index["targets"][identity.target_id].get("status") != "succeeded"
    ]
    if not pending:
        invalid = []
        for target_id in CANONICAL_TARGET_IDS:
            try:
                native = _load_target_native_index(config, target_id)
            except CampaignError as exc:
                invalid.append(f"{target_id}: {exc}")
                continue
            if (
                native.get("status") != "succeeded"
                or (native.get("native") or {}).get("complete") is not True
            ):
                invalid.append(f"{target_id}: native terminal evidence is incomplete")
        if invalid:
            raise CampaignError(
                "aggregate cannot trust stale target statuses: " + "; ".join(invalid)
            )
        index.update(
            status="succeeded", phase="complete",
            aggregate_build={
                "performed": False,
                "reason": "per-target native final Lake builds are authoritative",
                "unsafe_root_execution_forbidden": True,
            },
            updated_at=_utcnow(),
        )
        _atomic_write(config.index_path, index)
        return index

    stop_requested = False

    def request_stop(_number: int, _frame: Any) -> None:
        nonlocal stop_requested
        stop_requested = True

    previous_handlers = {
        number: signal.signal(number, request_stop)
        for number in (signal.SIGINT, signal.SIGTERM)
    }
    active: dict[int, _Child] = {}
    cleanup_failures: list[str] = []
    primary_error: BaseException | None = None
    try:
        index.update(status="running", phase="resume" if resume else "loop", updated_at=_utcnow())
        index["dedicated_uid_startup_cleanup"] = startup_cleanup
        _atomic_write(config.index_path, index)
        while pending or active:
            batch: list[_Child] = []
            while pending and len(active) < config.global_parallel and not stop_requested:
                identity = pending.pop(0)
                child = _spawn_child(
                    config, identity, identities, resume=resume,
                )
                batch.append(child)
                active[child.pid] = child
            if batch:
                all_pids = list(active)
                for child in batch:
                    peers = [pid for pid in all_pids if pid != child.pid]
                    os.write(child.control_fd, _canonical_json_bytes(peers))
                    os.close(child.control_fd)
                    child.control_fd = -1
                batch_receipts, batch_errors = _read_batch_receipts(batch)
                fatal_receipt_errors: list[str] = []
                for child in batch:
                    error = batch_errors.get(child.pid)
                    if error is not None:
                        try:
                            cleanup = _terminate_child(child)
                        finally:
                            active.pop(child.pid, None)
                            _close_child_fds(child)
                        index["targets"][child.identity.target_id].update({
                            "status": "failed",
                            "error": error,
                            "post_run_uid_cleanup": cleanup,
                            "updated_at": _utcnow(),
                        })
                        fatal_receipt_errors.append(
                            f"{child.identity.target_id}: {error}"
                        )
                        continue
                    receipt = batch_receipts[child.pid]
                    if receipt.get("error"):
                        _save_receipt(config, child.identity.target_id, receipt)
                        try:
                            cleanup = _terminate_child(child)
                        finally:
                            active.pop(child.pid, None)
                            _close_child_fds(child)
                        index["targets"][child.identity.target_id].update({
                            "status": "failed",
                            "error": str(receipt.get("error")),
                            "post_run_uid_cleanup": cleanup,
                            "updated_at": _utcnow(),
                        })
                        fatal_receipt_errors.append(
                            f"{child.identity.target_id}: {receipt.get('error')}"
                        )
                    else:
                        try:
                            _validate_isolation_receipt(
                                config, child.identity, identities, receipt,
                            )
                        except CampaignError as exc:
                            try:
                                cleanup = _terminate_child(child)
                            finally:
                                active.pop(child.pid, None)
                                _close_child_fds(child)
                            index["targets"][child.identity.target_id].update({
                                "status": "failed",
                                "error": str(exc),
                                "post_run_uid_cleanup": cleanup,
                                "updated_at": _utcnow(),
                            })
                            fatal_receipt_errors.append(
                                f"{child.identity.target_id}: {exc}"
                            )
                            continue
                        _save_receipt(config, child.identity.target_id, receipt)
                        index["targets"][child.identity.target_id].update({
                            "status": "running", "pid": child.pid,
                            "isolation_receipt": str(
                                config.controller_log_root
                                / f"{child.identity.target_id}.isolation.json"
                            ),
                            "updated_at": _utcnow(),
                        })
                if fatal_receipt_errors:
                    _atomic_write(config.index_path, index)
                    raise CampaignError(
                        "isolation preflight failed: " + "; ".join(fatal_receipt_errors)
                    )
                index["active_count"] = len(active)
                index["updated_at"] = _utcnow()
                _atomic_write(config.index_path, index)

            if stop_requested:
                for pid, child in list(active.items()):
                    cleanup = _terminate_child(child)
                    active.pop(pid, None)
                    _close_child_fds(child)
                    index["targets"][child.identity.target_id].update({
                        "status": "interrupted",
                        "post_run_uid_cleanup": cleanup,
                        "updated_at": _utcnow(),
                    })
                _atomic_write(config.index_path, index)
                break

            completed: list[tuple[int, int]] = []
            for pid in list(active):
                waited, status = os.waitpid(pid, os.WNOHANG)
                if waited:
                    completed.append((pid, status))
            if not completed:
                time.sleep(0.2)
                continue
            for pid, wait_status in completed:
                child = active.pop(pid)
                _close_child_fds(child)
                code = os.waitstatus_to_exitcode(wait_status)
                target_id = child.identity.target_id
                cleaned = _cleanup_identity_processes(child.identity)
                try:
                    native = _load_target_native_index(config, target_id)
                except CampaignError as exc:
                    native = {"status": "failed", "error": str(exc)}
                succeeded = code == 0 and native.get("status") == "succeeded" and (
                    native.get("native") or {}
                ).get("complete") is True and cleaned.get("quiescent_after") is True
                index["targets"][target_id].update({
                    "status": "succeeded" if succeeded else "interrupted" if stop_requested else "failed",
                    "returncode": code,
                    "native": native.get("native"),
                    "error": None if succeeded else native.get("error"),
                    "duration_seconds": round(time.monotonic() - child.started, 3),
                    "post_run_uid_cleanup": cleaned,
                    "dedicated_uid_quiescent": not _uid_pids(child.identity.uid),
                    "updated_at": _utcnow(),
                })
                index["targets"][target_id].pop("pid", None)
            index["active_count"] = len(active)
            index["succeeded_count"] = sum(
                row.get("status") == "succeeded" for row in index["targets"].values()
            )
            index["updated_at"] = _utcnow()
            _atomic_write(config.index_path, index)
            if stop_requested and not active:
                break
    except BaseException as exc:
        primary_error = exc
    finally:
        for number, handler in previous_handlers.items():
            signal.signal(number, handler)
        for child in active.values():
            try:
                _terminate_child(child)
            except BaseException as exc:
                cleanup_failures.append(
                    f"{child.identity.target_id}: {type(exc).__name__}: {exc}"
                )
            finally:
                _close_child_fds(child)
    if primary_error is not None:
        if cleanup_failures:
            index.update(
                status="failed", phase="cleanup",
                cleanup_errors=cleanup_failures, updated_at=_utcnow(),
            )
            _atomic_write(config.index_path, index)
            raise CampaignError(
                "campaign failed and dedicated UID cleanup also failed: "
                + "; ".join(cleanup_failures)
            ) from primary_error
        index.update(
            status="failed", phase="loop", error=f"{type(primary_error).__name__}: {primary_error}",
            active_count=0, updated_at=_utcnow(),
        )
        _atomic_write(config.index_path, index)
        raise primary_error

    if cleanup_failures:
        index.update(
            status="failed",
            phase="cleanup",
            cleanup_errors=cleanup_failures,
            updated_at=_utcnow(),
        )
        _atomic_write(config.index_path, index)
        raise CampaignError("dedicated UID cleanup failed: " + "; ".join(cleanup_failures))

    statuses = [row.get("status") for row in index["targets"].values()]
    all_targets_succeeded = all(value == "succeeded" for value in statuses)
    index.update(
        status=(
            "succeeded" if all_targets_succeeded
            else "interrupted" if stop_requested
            else "failed"
        ),
        # Every target's native success predicate already includes its exact
        # formalization gate, proof gate, no-sorry check, and final Lake build.
        # Never run solver-authored Lean as root for an aggregate compile: Lean
        # elaborators/run_tac can perform arbitrary IO.  A future aggregate
        # build must use a separately confined verifier UID.
        phase="complete" if all_targets_succeeded else "loop",
        aggregate_build={
            "performed": False,
            "reason": "per-target native final Lake builds are authoritative",
            "unsafe_root_execution_forbidden": True,
        },
        active_count=0,
        updated_at=_utcnow(),
    )
    _atomic_write(config.index_path, index)
    return index


def _run_campaign_locked(
    config: Config,
    *,
    index: dict[str, Any] | None = None,
    resume: bool,
) -> dict[str, Any]:
    """Run under held campaign/UID locks and close every verified UID path."""
    if os.geteuid() != 0:
        raise CampaignError("the isolated campaign scheduler must run as root")
    library = _libc()
    if library.prctl(36, 1, 0, 0, 0) != 0:  # PR_SET_CHILD_SUBREAPER
        error = ctypes.get_errno()
        raise CampaignError(f"cannot enable child subreaper: {os.strerror(error)}")
    identities = _identity_plan(config)
    # Do not act on numeric UIDs until all names, UID/GID bindings, and group
    # boundaries have been verified.  A collision here may belong to an
    # unrelated account and must never be swept by this controller.
    _ensure_identities(config, identities)

    result: dict[str, Any] | None = None
    primary_error: BaseException | None = None
    try:
        result = _run_campaign_verified(
            config, identities=identities, index=index, resume=resume,
        )
    except BaseException as exc:
        primary_error = exc
    finally:
        _receipts, final_errors = _sweep_identities(
            identities, phase="final UID sweep",
        )

    if final_errors:
        if index is not None:
            index.update(
                status="failed", phase="cleanup", cleanup_errors=final_errors,
                updated_at=_utcnow(),
            )
            try:
                _atomic_write(config.index_path, index)
            except BaseException:
                pass
        message = "dedicated UID final cleanup failed: " + "; ".join(final_errors)
        if primary_error is not None:
            raise CampaignError(message) from primary_error
        raise CampaignError(message)
    if primary_error is not None:
        raise primary_error
    if result is None:
        raise CampaignError("campaign returned no terminal index")
    return result


def run_campaign(
    config: Config,
    *,
    index: dict[str, Any] | None = None,
    resume: bool,
) -> dict[str, Any]:
    config = dataclasses.replace(
        config, campaign_root=config.campaign_root.resolve(strict=False),
    )
    campaign_lock = _acquire_campaign_lock(config.campaign_root)
    uid_lock_fds: list[int] = []
    access_enabled_by_us = False
    identities: tuple[Identity, ...] = ()
    identities_verified = False
    result: dict[str, Any] | None = None
    primary_error: BaseException | None = None
    cleanup_errors: list[str] = []
    try:
        uid_lock_fds = _acquire_uid_locks(config)
        identities = _identity_plan(config)
        _ensure_identities(config, identities)
        identities_verified = True
        _receipts, pre_errors = _sweep_identities(
            identities, phase="run preflight UID sweep",
        )
        if pre_errors:
            raise CampaignError(
                "dedicated UID run preflight cleanup failed: " + "; ".join(pre_errors)
            )
        _set_campaign_solver_access(config, enabled=True)
        access_enabled_by_us = True
        result = _run_campaign_locked(config, index=index, resume=resume)
    except BaseException as exc:
        primary_error = exc
    finally:
        try:
            if identities_verified:
                _receipts, cleanup_errors = _sweep_identities(
                    identities, phase="run final UID sweep",
                )
        finally:
            try:
                if access_enabled_by_us:
                    _set_campaign_solver_access(config, enabled=False)
            finally:
                for uid_fd in reversed(uid_lock_fds):
                    os.close(uid_fd)
                os.close(campaign_lock)
    if cleanup_errors:
        message = "dedicated UID run cleanup failed: " + "; ".join(cleanup_errors)
        if primary_error is not None:
            raise CampaignError(message) from primary_error
        raise CampaignError(message)
    if primary_error is not None:
        raise primary_error
    if result is None:
        raise CampaignError("campaign returned no terminal index")
    return result


def resume_campaign(campaign_root: Path) -> dict[str, Any]:
    root = campaign_root.resolve(strict=False)
    campaign_lock = _acquire_campaign_lock(root)
    uid_locks: list[int] = []
    config: Config | None = None
    access_enabled_by_us = False
    identities: tuple[Identity, ...] = ()
    identities_verified = False
    result: dict[str, Any] | None = None
    primary_error: BaseException | None = None
    cleanup_errors: list[str] = []
    try:
        # Read even the root-owned index only after the campaign lock.  Its
        # stored UID range then determines the second, globally ordered lock
        # layer which remains held through partial repair and execution.
        config = _stored_config(root)
        uid_locks = _acquire_uid_locks(config)
        index = _load_index(config)
        identities = _identity_plan(config)
        _ensure_identities(config, identities)
        identities_verified = True
        # A prior controller can leave double-forked descendants even though
        # its direct worker received PDEATHSIG.  Quiesce every dedicated UID
        # before reading or replacing any solver-owned target/home state.
        _receipts, pre_errors = _sweep_identities(
            identities, phase="resume preflight UID sweep",
        )
        if pre_errors:
            raise CampaignError(
                "dedicated UID resume preflight cleanup failed: "
                + "; ".join(pre_errors)
            )
        _verify_resume_bindings(config, index)
        if any(
            row.get("status") in {"pending", "preparation_failed"}
            for row in index["targets"].values()
        ):
            index = _finish_partial_preparation(config, index, identities)
        _set_campaign_solver_access(config, enabled=True)
        access_enabled_by_us = True
        result = _run_campaign_locked(config, index=index, resume=True)
    except BaseException as exc:
        primary_error = exc
    finally:
        try:
            if identities_verified:
                _receipts, cleanup_errors = _sweep_identities(
                    identities, phase="resume final UID sweep",
                )
        finally:
            try:
                if access_enabled_by_us and config is not None:
                    _set_campaign_solver_access(config, enabled=False)
            finally:
                for uid_lock in reversed(uid_locks):
                    os.close(uid_lock)
                os.close(campaign_lock)
    if cleanup_errors:
        message = "dedicated UID resume cleanup failed: " + "; ".join(cleanup_errors)
        if primary_error is not None:
            raise CampaignError(message) from primary_error
        raise CampaignError(message)
    if primary_error is not None:
        raise primary_error
    if result is None:
        raise CampaignError("resume returned no terminal index")
    return result


def dry_run(config: Config) -> dict[str, Any]:
    seed, packages = _validate_fresh_config(config)
    manifest, rows = _load_full_seed(seed)
    identities = _identity_plan(config)
    return {
        "status": "dry-run",
        "pipeline": PIPELINE,
        "row_count": len(rows),
        "target_ids": list(rows),
        "manifest_protocol": manifest.get("protocol"),
        "parent_manifest_sha256": _sha256_bytes(
            (seed / MANIFEST_REL).read_bytes()
        ),
        "parent_bundle_sha256": _sha256_bytes(
            (seed / BUNDLE_REL).read_bytes()
        ),
        "global_max_parallel": config.global_parallel,
        "internal_max_parallel": PER_TARGET_MAX_PARALLEL,
        "workspace_roots": [str(config.target_root(item.target_id)) for item in identities],
        "identities": [dataclasses.asdict(item) for item in identities],
        "shared_lake_packages_source": str(packages),
        "filesystem_answer_blind": True,
        "network_answer_blind": False,
        "landlock_min_abi": 4,
        "landlock_current_abi": landlock_abi(),
        "will_start_models": False,
    }


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--campaign-root", required=True, type=Path)
    parser.add_argument("--seed-workspace", type=Path)
    parser.add_argument("--lake-packages", type=Path)
    parser.add_argument("--codex-home-template", type=Path)
    parser.add_argument("--archon-bin", default="archon")
    parser.add_argument("--python-bin", type=Path, default=Path(sys.executable))
    parser.add_argument("--runtime-root", type=Path)
    parser.add_argument("--max-iterations", type=int, default=100)
    parser.add_argument("--global-parallel", type=int, default=GLOBAL_MAX_PARALLEL)
    parser.add_argument("--user-prefix", default="ichoab")
    parser.add_argument("--uid-base", type=int, default=26000)
    parser.add_argument(
        "--provision-identities", action="store_true",
        help="create the 32 fixed system users/groups when absent",
    )
    actions = parser.add_mutually_exclusive_group()
    actions.add_argument("--run", action="store_true", help="prepare and start all targets")
    actions.add_argument("--resume", action="store_true", help="resume incomplete targets")
    actions.add_argument("--dry-run", action="store_true", help="validate and print the plan only")
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        if args.resume:
            result = resume_campaign(args.campaign_root)
        else:
            config = Config(
                campaign_root=args.campaign_root,
                seed_workspace=args.seed_workspace,
                lake_packages=args.lake_packages,
                codex_home_template=args.codex_home_template,
                archon_bin=args.archon_bin,
                python_bin=args.python_bin,
                runtime_root=args.runtime_root,
                max_iterations=args.max_iterations,
                global_parallel=args.global_parallel,
                user_prefix=args.user_prefix,
                uid_base=args.uid_base,
                provision_identities=args.provision_identities,
            )
            result = dry_run(config) if args.dry_run else prepare_campaign(config, start=args.run)
    except (CampaignError, OSError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(result, ensure_ascii=False, sort_keys=True))
    return 0 if result.get("status") in {"prepared", "succeeded", "dry-run"} else 1


if __name__ == "__main__":
    raise SystemExit(main())
