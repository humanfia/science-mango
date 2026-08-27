#!/usr/bin/env python3
"""Launch a fresh answer-blind IChO T1 A4/A5 campaign with Kimi K3.

The root process remains alive for the complete model run.  It owns the
credential-less campaign controller, starts the credential broker, execs one
dedicated-UID solver worker, waits for that worker, and stops the broker in a
``finally`` block.  The solver receives only a loopback URL and the broker's
fixed public dummy token; the real Moonshot credential is never placed in the
worker environment, argv, home, workspace, or logs.

New runtime and overlay inventory digests are deliberately required on the
command line because they do not exist until those immutable trees have been
built.  Existing A4/A5 problem-only inputs retain their released hash binding.
This producer never accepts or installs a trusted prior-result receipt.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import pwd
import re
import shutil
import signal
import stat
import subprocess
import sys
import time
from pathlib import Path
from types import ModuleType
from typing import Any, Mapping, NoReturn


sys.dont_write_bytecode = True

VARIANT = "kimi-k3"
WIRE_MODEL = "kimi-k3"
CLI_MODEL = "kimi-k3[1m]"
UPSTREAM = "https://api.moonshot.cn/anthropic"
REQUEST_PROFILE = "agent_harness_v1"
PUBLIC_DUMMY_TOKEN = "answer-blind-public-dummy-token"

SOLVER_UID = 26320
SOLVER_GID = 26320
SOLVER_USER = "ichokimis1"
BROKER_UID = 26323
BROKER_GID = 26323
BROKER_USER = "ichokimib1"

BASE_LAUNCHER = Path("/root/t1pair_fresh_launch_64339475_bridgepair6.py")
BASE_LAUNCHER_SHA256 = (
    "3b032556534db8b40556c9242075e1e2055ec34026bccba91ecd6952f03ab5e7"
)
SEED = Path("/root/icho-t1-a4a5-seed-10b04c62-tgasimple1")
CONTROLLER_INPUT = Path("/root/icho-t1-a4a5-controller-10b04c62-tgasimple1")
PACKAGES = Path(
    "/srv/icho-blind-contest-v1-t5-97beac18/input/lake-packages-cf800f81"
)
EXPECTED_TARGET_IDS = ("icho_2026_t1_a4", "icho_2026_t1_a5")
EXPECTED_IMAGES = frozenset({"T1_page-2.png", "T1_page-3.png"})
EXPECTED_HASHES = {
    "seed_manifest": "9985bf9dff6b46440d3b360a52a951b64656998c094bb08e301e48711e7b2d71",
    "questions": "6ab26be8bc19fc19e750f5cf664c42e536ec273f9f003e3bafb31605c6bdbede",
    "lake_manifest": "cf800f81ecf5e27a8ff144bad0f8055c2c05bb7493eb94d0ed1f5ae4bae94143",
    "grader": "8946e221112b18acc8360987f1d4bd725c089fec52d2349d781b8ed8094bba00",
}
SEED_INVENTORY_SHA256 = (
    "e55de6c7b747030148916904634e8ce5f501c161f5e6971a392e8b1b293ffe15"
)
PACKAGES_INVENTORY_SHA256 = (
    "1caf70d07fa89eb3cc51aa5087e9c177f3724e634e160f994196c94ac9b2ec06"
)
RUNTIME_SOURCE_COMMIT = "10b04c62f66af0815bfa0bfa3c5cb3cbd5ef5358"
CLAUDE_BINARY_SHA256 = (
    "4e9bec1177ce9690e8bd988b710ac24105e70da428dd094c5adcbbe786a55555"
)

# Claude Code 2.1.226 is a Bun executable. Bun aborts during startup when these
# read-only kernel/cgroup metadata paths are hidden by Landlock. The worker
# installs Landlock before it forks Claude, so a rule for /proc/self would be
# pinned to the worker PID and would not cover the Claude child. Read-only
# procfs access is therefore allowed as one runtime metadata mount. The
# dedicated solver UID continues to deny other processes' environment, memory,
# and filesystem roots; the launch probes verify /proc/1/environ stays denied.
CLAUDE_CODE_RUNTIME_READONLY_PATHS = tuple(Path(item) for item in (
    "/proc",
    "/sys/fs/cgroup/cpu.max",
    "/sys/fs/cgroup/memory.max",
    "/sys/fs/cgroup/memory.high",
    "/sys/devices/system/cpu/online",
    "/sys/kernel/mm/transparent_hugepage/enabled",
))

MAX_PARALLEL = 2
MAX_ITERATIONS = 3
REVIEW_MAX_ITERATIONS = 3
NPROC_LIMIT = 4096
_SHA256 = re.compile(r"^[0-9a-f]{64}$")
_SAFE_RUN_ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,127}$")


class LaunchError(RuntimeError):
    """The launch would violate the fresh Kimi producer contract."""


def _fail(message: str) -> NoReturn:
    raise LaunchError(message)


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _canonical_bytes(value: Mapping[str, Any]) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        + "\n"
    ).encode("utf-8")


def _write_new_root_json(path: Path, value: Mapping[str, Any]) -> None:
    if path.exists() or path.is_symlink():
        _fail(f"controller receipt must be new: {path}")
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        payload = json.dumps(
            value, ensure_ascii=False, sort_keys=True, indent=2
        ).encode("utf-8") + b"\n"
        with os.fdopen(descriptor, "wb", closefd=False) as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
    finally:
        os.close(descriptor)
    os.chown(path, 0, 0)
    os.chmod(path, 0o400)


def _plain_root_file(path: Path, *, label: str) -> Path:
    if not path.is_absolute() or path.is_symlink() or not path.is_file():
        _fail(f"{label} must be an absolute plain file: {path}")
    metadata = path.stat(follow_symlinks=False)
    if (
        metadata.st_uid != 0
        or metadata.st_nlink != 1
        or stat.S_IMODE(metadata.st_mode) & 0o022
    ):
        _fail(f"{label} must be root-owned and not group/other writable: {path}")
    return path.resolve(strict=True)


def _load_file(path: Path, expected_sha256: str, *, name: str) -> ModuleType:
    source = _plain_root_file(path, label=name)
    if _sha256_file(source) != expected_sha256:
        _fail(f"{name} SHA-256 drift: {source}")
    spec = importlib.util.spec_from_file_location(
        f"_icho_kimi_{name.replace(' ', '_')}_{os.getpid()}", source
    )
    if spec is None or spec.loader is None:
        _fail(f"cannot load {name}: {source}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def _positive_sha256(value: str, *, label: str) -> str:
    if _SHA256.fullmatch(value) is None:
        _fail(f"{label} must be one lowercase SHA-256")
    return value


def _require_root() -> None:
    if os.geteuid() != 0:
        _fail("the Kimi producer launcher must run as root")


def _uid_pids(uid: int) -> tuple[int, ...]:
    result: list[int] = []
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit():
            continue
        try:
            rows = (entry / "status").read_text(encoding="utf-8").splitlines()
            uid_row = next(row for row in rows if row.startswith("Uid:"))
            if int(uid_row.split()[1]) == uid:
                result.append(int(entry.name))
        except (OSError, StopIteration, ValueError):
            continue
    return tuple(sorted(result))


def _account(name: str, uid: int, gid: int) -> pwd.struct_passwd:
    try:
        record = pwd.getpwnam(name)
    except KeyError as exc:
        raise LaunchError(
            f"dedicated account {name!r} is missing; rerun once with "
            "--provision-identities"
        ) from exc
    if (record.pw_uid, record.pw_gid) != (uid, gid):
        _fail(f"dedicated account {name!r} UID/GID drift")
    try:
        by_uid = pwd.getpwuid(uid)
    except KeyError as exc:  # pragma: no cover - getpwnam already found it
        raise LaunchError(f"dedicated UID {uid} is missing") from exc
    if by_uid.pw_name != name:
        _fail(f"dedicated UID {uid} belongs to {by_uid.pw_name!r}, not {name!r}")
    return record


def _provision_account(name: str, uid: int, gid: int) -> None:
    try:
        _account(name, uid, gid)
        return
    except LaunchError:
        pass
    try:
        pwd.getpwuid(uid)
    except KeyError:
        pass
    else:
        _fail(f"cannot provision {name!r}: UID {uid} is already assigned")
    group = subprocess.run(
        ["/usr/sbin/groupadd", "--system", "--gid", str(gid), name],
        check=False,
        capture_output=True,
        text=True,
    )
    if group.returncode != 0:
        _fail(f"cannot provision group {name!r}: {group.stderr.strip()}")
    user = subprocess.run(
        [
            "/usr/sbin/useradd", "--system", "--uid", str(uid), "--gid", str(gid),
            "--home-dir", "/nonexistent", "--shell", "/usr/sbin/nologin",
            "--no-create-home", name,
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    if user.returncode != 0:
        _fail(f"cannot provision user {name!r}: {user.stderr.strip()}")
    _account(name, uid, gid)


def _ensure_identities(*, provision: bool) -> None:
    if provision:
        _provision_account(SOLVER_USER, SOLVER_UID, SOLVER_GID)
        _provision_account(BROKER_USER, BROKER_UID, BROKER_GID)
    _account(SOLVER_USER, SOLVER_UID, SOLVER_GID)
    _account(BROKER_USER, BROKER_UID, BROKER_GID)
    if SOLVER_UID == BROKER_UID:
        _fail("solver and broker must use different UIDs")
    for uid, label in ((SOLVER_UID, "solver"), (BROKER_UID, "broker")):
        active = _uid_pids(uid)
        if active:
            _fail(f"dedicated {label} UID {uid} is already active: {active}")


def _dynamic_registry_parity(base: ModuleType) -> str:
    from archon.commands import chemistry_constant as registry

    groups = (
        tuple(registry.BASELINE_EMPIRICAL_RULE_IDS),
        tuple(registry.REFERENCE_ONLY_EMPIRICAL_RULE_IDS),
        tuple(registry.DORMANT_RUNTIME_BRIDGE_IDS),
    )
    flat = tuple(item for group in groups for item in group)
    if (
        not flat
        or len(flat) != len(set(flat))
        or tuple(registry.EMPIRICAL_RULE_IDS) != tuple(sorted(flat))
    ):
        _fail("sealed empirical-rule registry partition drift")
    installed_env = dict(os.environ)
    installed_env.pop("PYTHONPATH", None)
    overlay_env = dict(os.environ)
    overlay_env["PYTHONPATH"] = str(base.OVERLAY / "src")
    receipts: list[dict[str, Any]] = []
    for rule_id in registry.EMPIRICAL_RULE_IDS:
        installed = base._json_cli_result(
            subprocess.run(
                [str(base.RUNTIME / "bin/archon"), "chemistry-constant",
                 "empirical_rule", rule_id],
                check=False, capture_output=True, text=True,
                env=installed_env, timeout=30,
            ),
            f"installed registry query {rule_id}",
        )
        overlay = base._json_cli_result(
            subprocess.run(
                [str(base.PYTHON), "-P", "-m", "archon.cli",
                 "chemistry-constant", "empirical_rule", rule_id],
                check=False, capture_output=True, text=True,
                env=overlay_env, timeout=30,
            ),
            f"overlay registry query {rule_id}",
        )
        if installed != overlay or installed.get("approval", {}).get("status") != "approved":
            _fail(f"runtime/overlay registry drift: {rule_id}")
        receipts.append(installed)
    return hashlib.sha256(_canonical_bytes({"receipts": receipts})).hexdigest()


def _configure_base(arguments: argparse.Namespace) -> ModuleType:
    base = _load_file(
        arguments.base_launcher,
        arguments.base_launcher_sha256,
        name="base launcher",
    )
    campaign = arguments.campaign_root
    runtime = arguments.runtime
    overlay = arguments.overlay

    base.COMMIT = arguments.source_commit
    base.SHORT_SHA = arguments.source_commit[:8]
    base.BASE = campaign
    base.LIVE = campaign / "live"
    base.WORKSPACE = base.LIVE / "workspace"
    base.USER_KEY = "t1-a4a5-kimi"
    base.USER_HOME = campaign / "homes" / base.USER_KEY
    base.CONTROLLER_INPUT = arguments.controller_input
    base.SEED = arguments.seed
    base.PACKAGES = arguments.packages
    base.RUNTIME = runtime
    base.OVERLAY = overlay
    base.CONTROLLER = overlay / "scripts/run_answer_blind_archon_isolated_campaign.py"
    base.ARCHON = overlay / "scripts/run_answer_blind_overlay_archon.sh"
    base.PYTHON = runtime / "venv/bin/python"
    base.WORKER_LOG = campaign / "controller-worker.log"
    base.GRADER = arguments.controller_input / "grader.jsonl"
    base.OLD_CAMPAIGNS = ()
    base.SOLUTION_DENY_PATHS = tuple(arguments.solution_deny_path)
    base.IDENTITY_UID = SOLVER_UID
    base.IDENTITY_GID = SOLVER_GID
    base.IDENTITY_NAME = SOLVER_USER
    base.EXPECTED_TARGET_IDS = EXPECTED_TARGET_IDS
    base.EXPECTED_ITEMS = len(EXPECTED_TARGET_IDS)
    base.MAX_PARALLEL = MAX_PARALLEL
    base.MAX_ITERATIONS = MAX_ITERATIONS
    base.REVIEW_MAX_ITERATIONS = REVIEW_MAX_ITERATIONS
    base.NPROC_LIMIT = NPROC_LIMIT
    base.EXPECTED_HASHES = {
        arguments.seed / "isolation_manifest.json": EXPECTED_HASHES["seed_manifest"],
        arguments.seed / "icho_2026_source/questions_only.jsonl": EXPECTED_HASHES["questions"],
        arguments.seed / "lake-manifest.json": EXPECTED_HASHES["lake_manifest"],
        base.GRADER: EXPECTED_HASHES["grader"],
    }
    base.EXPECTED_OVERLAY_DIGEST = arguments.overlay_inventory_sha256
    base.EXPECTED_RUNTIME_DIGEST = arguments.runtime_inventory_sha256
    base.EXPECTED_PACKAGES_DIGEST = arguments.packages_inventory_sha256
    base.EXPECTED_SEED_DIGEST = arguments.seed_inventory_sha256

    def require_commit_receipt(root: Path) -> None:
        resolved = root.resolve(strict=True)
        if resolved == base.OVERLAY.resolve(strict=True):
            expected = arguments.source_commit
        elif resolved == base.RUNTIME.resolve(strict=True):
            expected = arguments.runtime_source_commit
        else:
            _fail(f"unexpected source-commit receipt root: {root}")
        receipt = resolved / "answer-blind-source-commit.txt"
        if not base._plain_file(receipt):
            _fail(f"missing source-commit receipt: {receipt}")
        if receipt.read_text(encoding="ascii") != f"{expected}\n":
            _fail(f"source-commit receipt drift: {receipt}")

    def seed_scope() -> None:
        forbidden = (
            base.SEED / ".archon", base.SEED / ".git",
            base.SEED / "IChO2026Problems", base.SEED / "grader.jsonl",
            base.SEED / "theory_solution.pdf",
        )
        for path in forbidden:
            if path.exists() or path.is_symlink():
                _fail(f"seed contains forbidden state/answer material: {path}")
        image_root = base.SEED / "icho_2026_source/image"
        images = frozenset(path.name for path in image_root.glob("*") if path.is_file())
        if images != EXPECTED_IMAGES:
            _fail(f"A4/A5 seed image closure drift: {sorted(images)}")

    def isolation_config(controller: ModuleType):
        return controller.Config(
            campaign_root=base.BASE,
            seed_workspace=base.SEED,
            lake_packages=base.PACKAGES,
            codex_home_template=None,
            archon_bin=str(base.ARCHON),
            python_bin=base.PYTHON,
            runtime_root=base.RUNTIME,
            max_iterations=base.MAX_ITERATIONS,
            global_parallel=base.MAX_PARALLEL,
            user_prefix=base.IDENTITY_NAME,
            uid_base=base.IDENTITY_UID,
            provision_identities=False,
        )

    def native_config(controller: ModuleType, *, seed: Path | None):
        return controller.NATIVE.Config(
            campaign_root=base.LIVE,
            seed_workspace=seed,
            lake_packages=base.PACKAGES,
            archon_bin=str(base.ARCHON),
            max_iterations=base.MAX_ITERATIONS,
            review_max_iterations=base.REVIEW_MAX_ITERATIONS,
            max_parallel=base.MAX_PARALLEL,
            expected_items=base.EXPECTED_ITEMS,
            target_lifecycle=True,
            reuse_lake_packages=True,
            in_place_index=True,
            trusted_prior_result_receipt=None,
            variant=VARIANT,
        )

    original_load_controller = base.load_controller

    def load_controller():
        controller = original_load_controller()
        original_environment = controller._solver_environment
        original_apply_landlock = controller._apply_landlock

        def apply_landlock(*, read_only: Any, read_write: Any):
            return original_apply_landlock(
                read_only=(*read_only, *CLAUDE_CODE_RUNTIME_READONLY_PATHS),
                read_write=read_write,
            )

        def solver_environment(*args: Any, **kwargs: Any) -> dict[str, str]:
            environment = original_environment(*args, **kwargs)
            broker_url = os.environ.get("ANSWER_BLIND_KIMI_BROKER_URL")
            dummy = os.environ.get("ANSWER_BLIND_KIMI_DUMMY_TOKEN")
            if not broker_url or dummy != PUBLIC_DUMMY_TOKEN:
                _fail("worker is missing its public loopback broker binding")
            environment.pop("CODEX_HOME", None)
            environment.pop("ANTHROPIC_API_KEY", None)
            environment.pop("MOONSHOT_API_KEY", None)
            environment.update({
                "CLAUDE_CONFIG_DIR": str(base.USER_HOME / ".claude"),
                "ANTHROPIC_BASE_URL": broker_url,
                "ANTHROPIC_AUTH_TOKEN": PUBLIC_DUMMY_TOKEN,
                "ANTHROPIC_MODEL": CLI_MODEL,
                "ANTHROPIC_DEFAULT_OPUS_MODEL": CLI_MODEL,
                "ANTHROPIC_DEFAULT_SONNET_MODEL": CLI_MODEL,
                "ANTHROPIC_DEFAULT_HAIKU_MODEL": CLI_MODEL,
                "ANTHROPIC_DEFAULT_FABLE_MODEL": CLI_MODEL,
                "CLAUDE_CODE_SUBAGENT_MODEL": CLI_MODEL,
                "CLAUDE_CODE_AUTO_COMPACT_WINDOW": "1048576",
                "CLAUDE_CODE_EFFORT_LEVEL": "max",
                "CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC": "1",
                "TMPDIR": "/dev/shm", "TMP": "/dev/shm", "TEMP": "/dev/shm",
            })
            environment["PATH"] = (
                str(base.OVERLAY / "bin") + ":" + environment["PATH"]
            )
            return environment

        controller._solver_environment = solver_environment
        controller._apply_landlock = apply_landlock
        return controller

    original_runtime_tools = base._require_runtime_tools

    def runtime_tools() -> None:
        original_runtime_tools()
        archon = base.ARCHON
        if archon.is_symlink() or not archon.is_file():
            _fail(f"sealed overlay lacks its Archon entry: {archon}")
        archon_metadata = archon.stat(follow_symlinks=False)
        if (
            archon_metadata.st_uid != 0
            or stat.S_IMODE(archon_metadata.st_mode) != 0o555
        ):
            _fail("sealed overlay Archon entry must be root-owned mode 0555")
        claude = base.OVERLAY / "bin/claude"
        if claude.is_symlink() or not claude.is_file():
            _fail(f"sealed runtime lacks a plain Claude Code binary: {claude}")
        for path in CLAUDE_CODE_RUNTIME_READONLY_PATHS:
            if path.is_symlink() or not (path.is_file() or path.is_dir()):
                _fail(f"Claude runtime metadata path is missing or unsafe: {path}")
            metadata = path.stat(follow_symlinks=False)
            if (
                metadata.st_uid != 0
                or stat.S_IMODE(metadata.st_mode) & 0o022
            ):
                _fail(f"Claude runtime metadata path is writable: {path}")
        metadata = claude.stat(follow_symlinks=False)
        if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) != 0o555:
            _fail("sealed Claude Code binary must be root-owned mode 0555")
        if _sha256_file(claude) != arguments.claude_binary_sha256:
            _fail("sealed Claude Code binary SHA-256 drift")

    base._require_seed_scope = seed_scope
    base._require_commit_receipt = require_commit_receipt
    base.isolation_config = isolation_config
    base.native_config = native_config
    base.load_controller = load_controller
    base._require_runtime_tools = runtime_tools
    base._registry_parity_smoke = lambda: _dynamic_registry_parity(base)
    return base


def _prepare_claude_home(base: ModuleType, controller: ModuleType) -> str:
    identity = base.identity(controller)
    home = base.USER_HOME
    if home.exists() or home.is_symlink():
        _fail(f"fresh Claude home already exists: {home}")
    home.mkdir(mode=0o700, parents=True)
    for relative in ("tmp", ".cache", ".config", ".claude"):
        (home / relative).mkdir(mode=0o700)
    controller._make_tree_solver_owned(home, identity)
    manifest = {
        "schema_version": 1,
        "kind": "credential-free-claude-home",
        "uid": SOLVER_UID,
        "gid": SOLVER_GID,
        "config_dir": ".claude",
        "contains_provider_credential": False,
    }
    return hashlib.sha256(_canonical_bytes(manifest)).hexdigest()


def _broker_module(arguments: argparse.Namespace) -> ModuleType:
    path = arguments.overlay / "scripts/run_answer_blind_model_broker.py"
    return _load_file(path, _sha256_file(path), name="sealed model broker")


def _read_broker_ready(path: Path, expected_sha256: str) -> dict[str, Any]:
    if path.is_symlink() or not path.is_file() or _sha256_file(path) != expected_sha256:
        _fail("model broker ready receipt is missing or changed")
    value = json.loads(path.read_text(encoding="utf-8"))
    expected = {
        "variant": VARIANT,
        "allowed_model": WIRE_MODEL,
        "request_profile": REQUEST_PROFILE,
        "upstream_origin": "https://api.moonshot.cn",
        "broker_uid": BROKER_UID,
    }
    if not isinstance(value, dict) or any(value.get(key) != item for key, item in expected.items()):
        _fail("model broker ready receipt binding drift")
    url = value.get("listen_url")
    if not isinstance(url, str) or re.fullmatch(r"http://127\.0\.0\.1:[1-9][0-9]{0,4}", url) is None:
        _fail("Kimi agent broker did not publish one loopback origin URL")
    return value


def _worker_arguments(arguments: argparse.Namespace, lock_fds: tuple[int, ...]) -> list[str]:
    return [
        str(arguments.runtime / "venv/bin/python"), "-B", str(Path(__file__).resolve()),
        "--worker", "--campaign-lock-fd", str(lock_fds[0]),
        "--uid-lock-fd", str(lock_fds[1]),
        "--campaign-root", str(arguments.campaign_root),
        "--runtime", str(arguments.runtime),
        "--runtime-inventory-sha256", arguments.runtime_inventory_sha256,
        "--overlay", str(arguments.overlay),
        "--overlay-inventory-sha256", arguments.overlay_inventory_sha256,
        "--source-commit", arguments.source_commit,
        "--runtime-source-commit", arguments.runtime_source_commit,
        "--base-launcher", str(arguments.base_launcher),
        "--base-launcher-sha256", arguments.base_launcher_sha256,
        "--seed", str(arguments.seed),
        "--seed-inventory-sha256", arguments.seed_inventory_sha256,
        "--controller-input", str(arguments.controller_input),
        "--packages", str(arguments.packages),
        "--packages-inventory-sha256", arguments.packages_inventory_sha256,
        "--claude-binary-sha256", arguments.claude_binary_sha256,
    ] + [
        item
        for path in arguments.solution_deny_path
        for item in ("--solution-deny-path", str(path))
    ]


def _worker_environment(arguments: argparse.Namespace, listen_url: str) -> dict[str, str]:
    return {
        "PATH": f"{arguments.overlay / 'bin'}:{arguments.runtime / 'bin'}",
        "PYTHONPATH": str(arguments.overlay / "src"),
        "PYTHONDONTWRITEBYTECODE": "1",
        "PYTHONSAFEPATH": "1",
        "LANG": "C.UTF-8", "LC_ALL": "C.UTF-8", "TZ": "Etc/UTC",
        "ANSWER_BLIND_KIMI_BROKER_URL": listen_url,
        "ANSWER_BLIND_KIMI_DUMMY_TOKEN": PUBLIC_DUMMY_TOKEN,
    }


def _prepare_and_run(arguments: argparse.Namespace) -> int:
    _require_root()
    os.umask(0o077)
    _ensure_identities(provision=arguments.provision_identities)
    base = _configure_base(arguments)
    controller = base.load_controller()
    target_ids = base.require_inputs(controller)
    if tuple(target_ids) != EXPECTED_TARGET_IDS:
        _fail(f"unexpected producer targets: {target_ids}")
    if arguments.campaign_root.exists() or arguments.campaign_root.is_symlink():
        _fail(f"fresh campaign root already exists: {arguments.campaign_root}")

    campaign_lock = controller._acquire_campaign_lock(arguments.campaign_root)
    uid_lock = controller._acquire_global_lock(
        controller._global_lock_root() / f"uid-{SOLVER_UID}.lock",
        busy_message=f"solver uid {SOLVER_UID} is reserved by another campaign",
    )
    broker_uid_lock = controller._acquire_global_lock(
        controller._global_lock_root() / f"uid-{BROKER_UID}.lock",
        busy_message=f"broker uid {BROKER_UID} is reserved by another campaign",
    )
    locks = (campaign_lock, uid_lock, broker_uid_lock)
    broker: ModuleType | None = None
    broker_started = False
    worker: subprocess.Popen[bytes] | None = None
    broker_transcript: Path | None = None
    try:
        if _uid_pids(SOLVER_UID) or _uid_pids(BROKER_UID):
            _fail("dedicated Kimi UIDs became active after lock acquisition")
        arguments.campaign_root.mkdir(mode=0o711)
        os.chmod(arguments.campaign_root, 0o711)
        prepared = controller.NATIVE.run_fresh(
            base.native_config(controller, seed=base.SEED), start_loop=False
        )
        if (
            prepared.get("status") != "prepared"
            or prepared.get("row_count") != len(EXPECTED_TARGET_IDS)
            or prepared.get("bundle_sha256") != EXPECTED_HASHES["questions"]
            or prepared.get("variant") != VARIANT
        ):
            _fail(f"Kimi native preparation failed or drifted: {prepared}")
        base.assert_zero_gate_state(controller, EXPECTED_TARGET_IDS)
        home_manifest_sha256 = _prepare_claude_home(base, controller)
        os.chown(arguments.campaign_root / "homes", 0, 0)
        os.chmod(arguments.campaign_root / "homes", 0o711)
        mutable = base.harden_workspace(
            controller, base.identity(controller), EXPECTED_TARGET_IDS
        )
        os.chown(arguments.campaign_root, 0, 0)
        os.chmod(arguments.campaign_root, 0o711)

        broker_dir = arguments.campaign_root / "model-broker"
        broker_dir.mkdir(mode=0o700)
        os.chown(broker_dir, 0, 0)
        os.chmod(broker_dir, 0o700)
        broker = _broker_module(arguments)
        ready_result = broker.start_broker(
            controller_dir=broker_dir,
            variant=VARIANT,
            run_id=arguments.run_id,
            model=WIRE_MODEL,
            upstream=UPSTREAM,
            credential_file=arguments.credential_file,
            credential_format=arguments.credential_format,
            token_name=arguments.token_name,
            broker_user=BROKER_USER,
            port=arguments.broker_port,
            request_profile=REQUEST_PROFILE,
        )
        broker_started = True
        ready_path = Path(ready_result["ready"])
        ready = _read_broker_ready(ready_path, str(ready_result["sha256"]))

        base.WORKER_LOG.touch(mode=0o600, exist_ok=False)
        os.chown(base.WORKER_LOG, SOLVER_UID, SOLVER_GID)
        os.chmod(base.WORKER_LOG, 0o600)
        with base.WORKER_LOG.open("ab", buffering=0) as output:
            worker = subprocess.Popen(
                _worker_arguments(arguments, locks),
                cwd="/",
                env=_worker_environment(arguments, str(ready["listen_url"])),
                stdin=subprocess.DEVNULL,
                stdout=output,
                stderr=subprocess.STDOUT,
                close_fds=True,
                pass_fds=locks[:2],
                start_new_session=True,
            )
        pid_path = arguments.campaign_root / "controller.pid"
        pid_path.write_text(f"{worker.pid}\n", encoding="ascii")
        os.chown(pid_path, 0, 0)
        os.chmod(pid_path, 0o400)
        launch_receipt = {
            "schema_version": 1,
            "pipeline": "icho-2026-answer-blind-kimi-native-producer-v1",
            "campaign_root": str(arguments.campaign_root),
            "worker_pid": worker.pid,
            "worker_log": str(base.WORKER_LOG),
            "source_commit": arguments.source_commit,
            "runtime_inventory_sha256": arguments.runtime_inventory_sha256,
            "overlay_inventory_sha256": arguments.overlay_inventory_sha256,
            "packages_inventory_sha256": arguments.packages_inventory_sha256,
            "seed_inventory_sha256": arguments.seed_inventory_sha256,
            "target_ids": list(EXPECTED_TARGET_IDS),
            "variant": VARIANT,
            "wire_model": WIRE_MODEL,
            "cli_model": CLI_MODEL,
            "request_profile": REQUEST_PROFILE,
            "solver_uid": SOLVER_UID,
            "broker_uid": BROKER_UID,
            "credential_exposed_to_solver": False,
            "claude_home_manifest_sha256": home_manifest_sha256,
            "broker_ready_sha256": ready_result["sha256"],
            "trusted_prior_result_receipt": None,
            "filesystem_answer_blind": True,
            "network_answer_blind": False,
            "max_parallel": MAX_PARALLEL,
            "max_iterations": MAX_ITERATIONS,
            "review_max_iterations": REVIEW_MAX_ITERATIONS,
            "mutable_path_count": len(mutable),
            "prepare_status": prepared.get("status"),
        }
        _write_new_root_json(arguments.campaign_root / "launch-receipt.json", launch_receipt)
        print(json.dumps(launch_receipt, ensure_ascii=False, sort_keys=True), flush=True)

        returncode = worker.wait()
        completion = {
            "schema_version": 1,
            "pipeline": launch_receipt["pipeline"],
            "campaign_root": str(arguments.campaign_root),
            "worker_pid": worker.pid,
            "worker_returncode": returncode,
            "completed_at": time.time(),
        }
        _write_new_root_json(arguments.campaign_root / "completion-receipt.json", completion)
        return returncode
    except KeyboardInterrupt:
        if worker is not None and worker.poll() is None:
            try:
                os.killpg(worker.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                worker.wait(timeout=15)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(worker.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
        return 130
    finally:
        if broker_started and broker is not None:
            try:
                broker_transcript = broker.stop_broker(
                    controller_dir=arguments.campaign_root / "model-broker",
                    variant=VARIANT,
                    timeout_s=30,
                )
            except Exception as exc:
                print(f"warning: broker shutdown failed: {type(exc).__name__}: {exc}", file=sys.stderr)
        if broker_transcript is not None:
            print(f"BROKER_TRANSCRIPT={broker_transcript}", flush=True)
        for descriptor in reversed(locks):
            try:
                os.close(descriptor)
            except OSError:
                pass


def _run_worker(arguments: argparse.Namespace) -> int:
    _require_root()
    if arguments.campaign_lock_fd < 0 or arguments.uid_lock_fd < 0:
        _fail("worker requires both inherited lock descriptors")
    if os.environ.get("ANSWER_BLIND_KIMI_DUMMY_TOKEN") != PUBLIC_DUMMY_TOKEN:
        _fail("worker received no exact public dummy broker token")
    if any(os.environ.get(name) for name in (
        "ANTHROPIC_API_KEY", "MOONSHOT_API_KEY", "KIMI_API_KEY"
    )):
        _fail("worker environment contains a real-provider credential variable")
    base = _configure_base(arguments)
    return int(base.run_worker(arguments.campaign_lock_fd, arguments.uid_lock_fd))


def _validate_arguments(arguments: argparse.Namespace) -> None:
    for name in (
        "runtime_inventory_sha256", "overlay_inventory_sha256",
        "packages_inventory_sha256", "seed_inventory_sha256",
        "base_launcher_sha256", "claude_binary_sha256",
    ):
        _positive_sha256(getattr(arguments, name), label=name)
    for name in ("source_commit", "runtime_source_commit"):
        commit = getattr(arguments, name)
        if len(commit) != 40 or any(character not in "0123456789abcdef" for character in commit):
            option = name.replace("_", "-")
            _fail(f"--{option} must be one lowercase 40-character Git object id")
    if _SAFE_RUN_ID.fullmatch(arguments.run_id) is None:
        _fail("--run-id is malformed")
    for name in (
        "campaign_root", "runtime", "overlay", "base_launcher", "seed",
        "controller_input", "packages",
    ):
        path = getattr(arguments, name)
        if not path.is_absolute() or ".." in path.parts:
            _fail(f"--{name.replace('_', '-')} must be a normalized absolute path")
    if not arguments.worker and arguments.credential_file is None and not arguments.check_inputs:
        _fail("--credential-file is required for a real launch")
    if arguments.credential_file is not None and not arguments.credential_file.is_absolute():
        _fail("--credential-file must be absolute")
    if not arguments.solution_deny_path:
        _fail("at least one --solution-deny-path is required")
    if arguments.seed == arguments.campaign_root or arguments.campaign_root.is_relative_to(arguments.seed):
        _fail("fresh campaign root must be disjoint from the sealed seed")


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--worker", action="store_true", help=argparse.SUPPRESS)
    mode.add_argument("--check-inputs", action="store_true")
    parser.add_argument("--campaign-lock-fd", type=int, default=-1, help=argparse.SUPPRESS)
    parser.add_argument("--uid-lock-fd", type=int, default=-1, help=argparse.SUPPRESS)
    parser.add_argument("--campaign-root", type=Path, required=True)
    parser.add_argument("--run-id", default="icho-2026-t1-a4a5-kimi-k3")
    parser.add_argument("--source-commit", required=True)
    parser.add_argument("--runtime", type=Path, required=True)
    parser.add_argument("--runtime-source-commit", default=RUNTIME_SOURCE_COMMIT)
    parser.add_argument("--runtime-inventory-sha256", required=True)
    parser.add_argument("--overlay", type=Path, required=True)
    parser.add_argument("--overlay-inventory-sha256", required=True)
    parser.add_argument("--base-launcher", type=Path, default=BASE_LAUNCHER)
    parser.add_argument("--base-launcher-sha256", default=BASE_LAUNCHER_SHA256)
    parser.add_argument("--seed", type=Path, default=SEED)
    parser.add_argument("--seed-inventory-sha256", default=SEED_INVENTORY_SHA256)
    parser.add_argument("--controller-input", type=Path, default=CONTROLLER_INPUT)
    parser.add_argument("--packages", type=Path, default=PACKAGES)
    parser.add_argument("--packages-inventory-sha256", default=PACKAGES_INVENTORY_SHA256)
    parser.add_argument("--claude-binary-sha256", default=CLAUDE_BINARY_SHA256)
    parser.add_argument("--credential-file", type=Path)
    parser.add_argument("--credential-format", choices=("raw", "json", "env"), default="raw")
    parser.add_argument("--token-name")
    parser.add_argument("--broker-port", type=int, default=0)
    parser.add_argument("--provision-identities", action="store_true")
    parser.add_argument(
        "--solution-deny-path", type=Path, action="append", default=[
            Path("/root/t1-two-stage-artifact-build-10b04c62-tgasimple1/source-a/icho_2026_source/raw/theory_solution.pdf"),
            Path("/root/t1-two-stage-artifact-build-10b04c62-tgasimple1/source-a/icho_2026_source/raw/experiment_solution.pdf"),
        ],
    )
    return parser


def main() -> int:
    arguments = _parser().parse_args()
    _validate_arguments(arguments)
    if arguments.worker:
        return _run_worker(arguments)
    if arguments.check_inputs:
        _require_root()
        _ensure_identities(provision=False)
        base = _configure_base(arguments)
        targets = base.require_inputs(base.load_controller())
        print(json.dumps({
            "status": "inputs_valid", "targets": list(targets),
            "variant": VARIANT, "wire_model": WIRE_MODEL, "cli_model": CLI_MODEL,
            "trusted_prior_result_receipt": None,
        }, sort_keys=True))
        return 0
    return _prepare_and_run(arguments)


if __name__ == "__main__":
    raise SystemExit(main())
