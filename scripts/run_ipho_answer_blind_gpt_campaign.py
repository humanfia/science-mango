#!/usr/bin/env python3
"""Run the 28-item IPhO answer-blind Archon loop with native Codex login.

The launcher reuses the existing IPhO dedicated-UID/Landlock confinement and
changes only the model-facing edge: it copies one root-only ``auth.json`` into
the fresh private solver home, runs Codex ephemerally, and admits HTTPS model
traffic. The copy is readable by the dedicated solver UID, so callers must use
a dedicated, revocable login. It never reads or supplies official answers or
grading material.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import re
import stat
import subprocess
import sys
from pathlib import Path
from types import ModuleType
from typing import Any, Iterable


ISOLATION_SCRIPT = Path(__file__).with_name(
    "run_ipho_answer_blind_confined_loop.py"
)
SEALED_RUNTIME = Path(
    "/opt/icho-answer-blind-runtime-10b04c62-rebuilt1-gpt-idle1800"
)
SEALED_HELPER = Path("libexec/run_answer_blind_iteration.py")
MODEL = "gpt-5.6-sol"
VARIANT = "gpt"
TARGET_COUNT = 28
HTTPS_PORT = 443
PROTOCOL = "ipho-2026-answer-blind-gpt-campaign-v1"
SAFE_TARGET_ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_-]{0,127}$")
REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
WORKSPACE_PROMPT_SOURCES = {
    ".archon/prover-modes/physics.md": (
        "src/archon/.archon-src/prover-modes/physics.md"
    ),
    ".archon/prover-modes/physics-formalize.md": (
        "src/archon/.archon-src/prover-modes/physics-formalize.md"
    ),
    ".archon/subagents/physics-reviewer.md": (
        "src/archon/.archon-src/subagents/physics-reviewer.md"
    ),
}
GPT_REQUIRED_EXTRA_ARGS = (
    "-c",
    "features.plugins=false",
    "-c",
    "features.apps=false",
    "-c",
    "features.browser_use=false",
    "-c",
    "features.browser_use_external=false",
    "-c",
    "features.in_app_browser=false",
    "-c",
    "features.computer_use=false",
    "-c",
    'web_search="disabled"',
    "-c",
    "features.standalone_web_search=false",
    "-c",
    "features.search_tool=false",
    "-c",
    "features.multi_agent=false",
    "-c",
    "features.multi_agent_v2=false",
    "-c",
    "features.skill_search=false",
    "-c",
    "features.responses_websockets=false",
    "-c",
    "features.responses_websockets_v2=false",
)


class CampaignError(RuntimeError):
    """The native GPT campaign failed a controller-side invariant."""


def _blind_record_sha256(row: dict[str, Any]) -> str:
    payload = (
        json.dumps(row, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        + "\n"
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _import_isolation() -> ModuleType:
    source = ISOLATION_SCRIPT.resolve(strict=True)
    spec = importlib.util.spec_from_file_location("_ipho_gpt_isolation", source)
    if spec is None or spec.loader is None:
        raise CampaignError(f"cannot import IPhO isolation module: {source}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def _load_sealed_helper(isolation: ModuleType, runtime: Path) -> ModuleType:
    pinned = isolation._plain_directory(SEALED_RUNTIME, label="pinned GPT runtime")
    if runtime != pinned:
        raise CampaignError(f"runtime root must be the pinned GPT tree: {pinned}")
    helper = isolation._plain_file(runtime / SEALED_HELPER, label="sealed jail helper")
    archon = isolation._plain_file(runtime / "bin/archon", label="sealed Archon")
    for path, label in ((helper, "sealed jail helper"), (archon, "sealed Archon")):
        metadata = path.stat(follow_symlinks=False)
        if metadata.st_uid != 0 or stat.S_IMODE(metadata.st_mode) & 0o022:
            raise CampaignError(f"{label} is not root-owned read-only: {path}")
    if not os.access(archon, os.X_OK):
        raise CampaignError("sealed Archon is not executable")
    spec = importlib.util.spec_from_file_location("_ipho_gpt_sealed_iteration", helper)
    if spec is None or spec.loader is None:
        raise CampaignError("cannot import the sealed jail helper")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def _validate_codex_binary(isolation: ModuleType, runtime: Path) -> Path:
    codex = isolation._plain_file(runtime / "bin/codex", label="sealed Codex")
    metadata = codex.stat(follow_symlinks=False)
    if (
        metadata.st_uid != 0
        or stat.S_IMODE(metadata.st_mode) & 0o022
        or not os.access(codex, os.X_OK)
    ):
        raise CampaignError("sealed Codex must be root-owned, read-only, and executable")
    return codex


def _validate_codex_auth_template(
    isolation: ModuleType, template: Path
) -> Path:
    root = isolation._plain_directory(template, label="Codex home template")
    metadata = root.stat(follow_symlinks=False)
    if (
        metadata.st_uid != 0
        or metadata.st_gid != 0
        or stat.S_IMODE(metadata.st_mode) & 0o022
    ):
        raise CampaignError("Codex home template must be root-owned and not writable")
    auth = root / "auth.json"
    try:
        auth_metadata = auth.lstat()
    except OSError as exc:
        raise CampaignError("Codex home template has no plain auth.json") from exc
    if (
        stat.S_ISLNK(auth_metadata.st_mode)
        or not stat.S_ISREG(auth_metadata.st_mode)
        or auth_metadata.st_nlink != 1
        or auth_metadata.st_uid != 0
        or auth_metadata.st_gid != 0
        or stat.S_IMODE(auth_metadata.st_mode) != 0o600
    ):
        raise CampaignError("Codex home template auth.json must be unique root mode 0600")
    return auth


def _copy_minimal_codex_auth(auth: Path, home: Path, identity: Any) -> Path:
    codex_home = home / ".codex"
    if codex_home.exists() or codex_home.is_symlink():
        raise CampaignError("private Codex home must be fresh")
    codex_home.mkdir(mode=0o700)
    os.chown(codex_home, identity.uid, identity.gid)
    destination = codex_home / "auth.json"
    source = os.open(auth, os.O_RDONLY | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0))
    target = os.open(
        destination,
        os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0),
        0o600,
    )
    try:
        while True:
            chunk = os.read(source, 1024 * 1024)
            if not chunk:
                break
            offset = 0
            while offset < len(chunk):
                offset += os.write(target, chunk[offset:])
        os.fsync(target)
        os.fchown(target, identity.uid, identity.gid)
        os.fchmod(target, 0o600)
    finally:
        os.close(source)
        os.close(target)
    copied = destination.lstat()
    if not stat.S_ISREG(copied.st_mode) or copied.st_nlink != 1:
        raise CampaignError("private Codex auth copy is not a unique regular file")
    return codex_home


def _validate_prepared_formalization_frontier(workspace: Path) -> dict[str, Any]:
    """Fail before launch unless deterministic question ingest prepared 28 tasks."""

    bundle = workspace / "ipho_2026_source/questions_only.jsonl"
    progress = workspace / ".archon/PROGRESS.md"
    config_path = workspace / ".archon/config.json"
    try:
        rows = [
            json.loads(line)
            for line in bundle.read_text(encoding="utf-8").splitlines()
            if line.strip()
        ]
        progress_text = progress.read_text(encoding="utf-8")
        config = json.loads(config_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise CampaignError(
            "GPT workspace has not completed deterministic physics-formalize ingest"
        ) from exc

    loop = config.get("loop") if isinstance(config, dict) else None
    harnesses = config.get("harnesses") if isinstance(config, dict) else None
    answer_blind = config.get("answer_blind") if isinstance(config, dict) else None
    descriptor = (
        harnesses.get("answer-blind-gpt") if isinstance(harnesses, dict) else None
    )
    domain = loop.get("domain_profile") if isinstance(loop, dict) else None
    expected_descriptor = {
        "runner": "codex",
        "model": MODEL,
        "effort": "max",
        "ignore_user_config": True,
        "ephemeral": True,
        "sandbox": "danger-full-access",
        "lean_explore_backend": "local",
        "mcp": ["lean-explore"],
        "extra_args": list(GPT_REQUIRED_EXTRA_ARGS),
    }
    if (
        not isinstance(loop, dict)
        or not isinstance(descriptor, dict)
        or not isinstance(answer_blind, dict)
        or not isinstance(domain, dict)
        or loop.get("harness") != "answer-blind-gpt"
        or loop.get("model") != MODEL
        or loop.get("max_parallel") != 32
        or loop.get("max_objectives") != TARGET_COUNT
        or any(descriptor.get(key) != value for key, value in expected_descriptor.items())
        or answer_blind.get("official_answer_seen") is not False
        or answer_blind.get("authority") != "problem-only"
        or domain.get("lean_search_packages") != ["Mathlib", "Physlib"]
    ):
        raise CampaignError("GPT workspace configuration is not the pinned Codex profile")

    invalid_prompts: list[str] = []
    for destination_rel, source_rel in WORKSPACE_PROMPT_SOURCES.items():
        source = REPOSITORY_ROOT / source_rel
        destination = workspace / destination_rel
        try:
            if _sha256_file(destination) != _sha256_file(source):
                invalid_prompts.append(destination_rel)
        except OSError:
            invalid_prompts.append(destination_rel)
    if invalid_prompts:
        raise CampaignError(
            "GPT workspace contains stale or missing physics prompts: "
            + ", ".join(invalid_prompts)
        )

    target_ids: list[str] = []
    for row in rows:
        target_id = str(row.get("id") or "").strip() if isinstance(row, dict) else ""
        if (
            not SAFE_TARGET_ID.fullmatch(target_id)
            or row.get("official_answer_seen") is not False
        ):
            raise CampaignError("GPT question-only frontier contains an invalid row")
        target_ids.append(target_id)
    if len(target_ids) != TARGET_COUNT or len(set(target_ids)) != TARGET_COUNT:
        raise CampaignError(f"GPT formalization frontier must contain {TARGET_COUNT} targets")

    expected = [f"IPhO2026Problems/problem_{target_id}.lean" for target_id in target_ids]
    missing_reports: list[str] = []
    invalid_reports: list[str] = []
    for target_id, row, output_lean in zip(target_ids, rows, expected, strict=True):
        report_rel = f"reports/ipho_2026/problem_{target_id}.source.json"
        report_path = workspace / report_rel
        if not report_path.is_file():
            missing_reports.append(target_id)
            continue
        try:
            report = json.loads(report_path.read_text(encoding="utf-8"))
        except (OSError, UnicodeDecodeError, json.JSONDecodeError):
            invalid_reports.append(target_id)
            continue
        entry = report.get("entry") if isinstance(report, dict) else None
        digest = _blind_record_sha256(row)
        if (
            not isinstance(entry, dict)
            or report.get("evaluation_mode") != "answer_blind"
            or report.get("official_answer_seen") is not False
            or report.get("output_lean") != output_lean
            or report.get("source_report") != report_rel
            or report.get("blind_record_sha256") != digest
            or entry.get("id") != target_id
            or entry.get("evaluation_mode") != "answer_blind"
            or entry.get("official_answer_seen") is not False
            or entry.get("blind_record_sha256") != digest
        ):
            invalid_reports.append(target_id)
    missing_chapters = [
        target_id
        for target_id in target_ids
        if not (
            workspace
            / f"blueprint/src/chapters/IPhO2026Problems_problem_{target_id}.tex"
        ).is_file()
    ]
    missing_objectives = [rel for rel in expected if rel not in progress_text]
    if missing_reports or invalid_reports or missing_chapters or missing_objectives:
        raise CampaignError(
            "GPT workspace is missing deterministic physics-formalize outputs: "
            f"reports={len(missing_reports)}, invalid_reports={len(invalid_reports)}, "
            f"chapters={len(missing_chapters)}, "
            f"objectives={len(missing_objectives)}"
        )
    if "autoformalize" not in progress_text.casefold():
        raise CampaignError("GPT fresh frontier is not staged for autoformalization")
    return {
        "target_count": TARGET_COUNT,
        "stage": "autoformalize",
        "harness": "answer-blind-gpt",
    }


def _archon_argv(
    runtime: Path, *, max_iterations: int, max_parallel: int, max_objectives: int
) -> tuple[str, ...]:
    return (
        str(runtime / "venv/bin/python"),
        "-P",
        "-c",
        isolation_bootstrap(),
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


def isolation_bootstrap() -> str:
    return (
        "import multiprocessing as mp, runpy; "
        "mp.set_start_method('fork'); "
        "runpy.run_module('archon.cli', run_name='__main__')"
    )


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--codex-home-template", type=Path, required=True)
    parser.add_argument("--controller-dir", type=Path, required=True)
    parser.add_argument("--workspace", type=Path, required=True)
    parser.add_argument("--dependency-root", type=Path, required=True)
    parser.add_argument("--private-home", type=Path, required=True)
    parser.add_argument("--private-tmp", type=Path, required=True)
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--solver-user", required=True)
    parser.add_argument("--runtime-root", type=Path, default=SEALED_RUNTIME)
    parser.add_argument(
        "--lean-explore-cache", type=Path, default=Path("/root/.lean_explore")
    )
    parser.add_argument("--lean-explore-hf-cache", type=Path, required=True)
    parser.add_argument("--lean-explore-site-packages", type=Path)
    parser.add_argument("--max-iterations", type=int, default=4)
    parser.add_argument("--max-parallel", type=int, default=32)
    parser.add_argument("--max-objectives", type=int, default=TARGET_COUNT)
    parser.add_argument("--timeout-s", type=int, default=172800)
    return parser


def run(
    args: argparse.Namespace, *, isolation: ModuleType | None = None
) -> tuple[dict[str, Any], int]:
    if os.geteuid() != 0:
        raise CampaignError("the IPhO GPT campaign controller must run as root")
    isolation = isolation or _import_isolation()
    if isolation.SAFE_RUN_ID.fullmatch(args.run_id) is None:
        raise CampaignError("run-id contains unsafe characters")
    if not 1 <= args.max_parallel <= 32:
        raise CampaignError("max-parallel must be between 1 and 32")
    if not 1 <= args.max_objectives <= TARGET_COUNT:
        raise CampaignError(f"max-objectives must be between 1 and {TARGET_COUNT}")
    if not 1 <= args.max_iterations <= 100 or args.timeout_s < 1:
        raise CampaignError("invalid iteration or timeout limit")

    workspace = isolation._plain_directory(args.workspace, label="solver workspace")
    dependency = isolation._plain_directory(args.dependency_root, label="Lean dependency root")
    runtime = isolation._plain_directory(args.runtime_root, label="sealed runtime")
    controller = isolation._plain_directory(args.controller_dir, label="controller directory")
    cache = isolation._plain_directory(args.lean_explore_cache, label="LeanExplore cache")
    hf_cache = isolation._plain_directory(
        args.lean_explore_hf_cache, label="LeanExplore Hugging Face cache"
    )
    hf_cache_inventory = isolation._validate_lean_explore_hf_cache(hf_cache)
    isolation._validate_controller_dir(controller)
    auth = _validate_codex_auth_template(isolation, args.codex_home_template)
    home = Path(args.private_home).absolute()
    temporary = Path(args.private_tmp).absolute()
    for path, label in ((home, "private home"), (temporary, "private tmp")):
        if path.exists() or path.is_symlink():
            raise CampaignError(f"{label} must be fresh and absent")
        isolation._plain_directory(path.parent, label=f"{label} parent")
    isolation._require_disjoint(
        {
            "workspace": workspace,
            "dependency root": dependency,
            "runtime root": runtime,
            "controller directory": controller,
            "Codex home template": auth.parent,
            "private home": home,
            "private tmp": temporary,
            "LeanExplore source cache": cache,
            "LeanExplore Hugging Face cache": hf_cache,
        }
    )
    if (workspace / ".git").exists() or (workspace / ".archon/.env").exists():
        raise CampaignError("solver workspace must contain neither Git history nor .archon/.env")
    prepared_frontier = _validate_prepared_formalization_frontier(workspace)

    sealed = _load_sealed_helper(isolation, runtime)
    isolation._install_seccomp_receive_deadline(sealed)
    isolation._allow_seccomp_socketpair(sealed)
    isolation._allow_seccomp_native_sockets(sealed)
    codex = _validate_codex_binary(isolation, runtime)
    isolation._parameterize_ipho_targets(sealed)
    identity = sealed._identity(args.solver_user)
    if identity.uid == 0:
        raise CampaignError("solver must use a dedicated non-root user")

    supplemental: Path | None = None
    supplemental_inventory: dict[str, int] | None = None
    python_path: str | None = None
    if args.lean_explore_site_packages is not None:
        supplemental = isolation._plain_directory(
            args.lean_explore_site_packages,
            label="LeanExplore supplemental site-packages",
        )
        supplemental_inventory = isolation._validate_readonly_tree(
            supplemental, label="LeanExplore supplemental site-packages"
        )
        sealed_site = isolation._sealed_site_packages(runtime)
        python_path = isolation._confirm_archon_origin(
            runtime_root=runtime,
            sealed_site=sealed_site,
            supplemental_site=supplemental,
        )

    anchor_method = isolation._ensure_legacy_umbrella_anchor(workspace)
    hardening = sealed.harden_solver_workspace(
        workspace=workspace,
        identity=identity,
        dependency_root=dependency,
        private_home=home,
        private_tmp=temporary,
        variant=VARIANT,
        run_id=args.run_id,
    )
    codex_home = _copy_minimal_codex_auth(auth, home, identity)
    cache_projection = isolation._project_lean_explore_cache(cache, home)

    probe_paths = [
        Path("/root"),
        Path("/tmp"),
        Path("/var/tmp"),
        Path("/dev/shm"),
        Path("/dev/tty"),
        Path("/proc/1/environ"),
        controller,
        cache,
        auth.parent,
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
        allowed_connect_tcp_ports=(HTTPS_PORT,),
    )
    policy = isolation._promote_dev_null_writable(sealed, policy)
    policy = isolation._promote_dev_shm_writable(sealed, policy)
    if supplemental is not None:
        policy = isolation._extend_readonly_policy(
            sealed,
            policy,
            supplemental,
            label="LeanExplore supplemental site-packages",
        )
    policy = isolation._extend_readonly_policy(
        sealed,
        policy,
        hf_cache,
        label="LeanExplore Hugging Face cache",
    )

    environment = sealed._minimal_environment(
        home=home,
        temporary=temporary,
        runtime_root=runtime,
        credential_values={},
    )
    environment.update(
        {
            "ANSWER_BLIND_MCP_RUNTIME_ROOT": str(runtime),
            "ANSWER_BLIND_MCP_DEPENDENCY_ROOT": str(dependency),
            "ANSWER_BLIND_MCP_WORKSPACE": str(workspace),
            "LEAN_EXPLORE_CACHE_DIR": str(home / ".lean_explore/cache"),
            "LEAN_EXPLORE_VERSION": isolation.LEAN_EXPLORE_VERSION,
            "TOKIO_WORKER_THREADS": "1",
            "GIT_CONFIG_COUNT": "1",
            "GIT_CONFIG_KEY_0": "safe.directory",
            "GIT_CONFIG_VALUE_0": str(dependency) + "/*",
            "SHELL": str(runtime / "bin/bash"),
            **isolation._lean_explore_hf_environment(hf_cache),
        }
    )
    environment["CODEX_HOME"] = str(codex_home)
    if python_path is not None:
        environment["PYTHONPATH"] = python_path

    argv = _archon_argv(
        runtime,
        max_iterations=args.max_iterations,
        max_parallel=args.max_parallel,
        max_objectives=args.max_objectives,
    )
    log_path = controller / f"{args.run_id}-ipho-gpt-campaign.log"
    receipt_path = controller / f"{args.run_id}-ipho-gpt-campaign.json"
    if receipt_path.exists() or log_path.exists():
        raise CampaignError("controller log/receipt already exists for this run-id")
    outcome = sealed.run_confined_command(
        argv=argv,
        cwd=workspace,
        environment=environment,
        identity=identity,
        policy=policy,
        log_path=log_path,
        timeout_s=args.timeout_s,
    )
    effective_exit = 126 if outcome.confinement_error else outcome.exit_code
    landlock_receipt = policy.receipt(
        connected_fd_injection_count=outcome.connected_fd_injection_count,
        seccomp_supervisor_fail_closed=outcome.seccomp_supervisor_fail_closed,
        seccomp_supervisor_stopped=outcome.seccomp_supervisor_stopped,
    )
    # The reused IPhO wrapper deliberately permits native Unix sockets and
    # native TCP connect; correct the base helper's broker-oriented labels so
    # the receipt does not overstate the direct-Codex network boundary.
    landlock_receipt.update(
        {
            "socket_creation_mode": "native_under_landlock_v1",
            "allowed_connect_tcp_endpoints": [f"*:{HTTPS_PORT}"],
            "inet_datagram_sockets_denied": False,
            "unix_sockets_denied": False,
            "socketpair_denied": False,
        }
    )
    receipt: dict[str, Any] = {
        "schema_version": 1,
        "protocol": PROTOCOL,
        "phase": "campaign_complete",
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
            "model_network": "native Codex; TCP connect limited to port 443",
            "grounding_packages": ["Mathlib", "Physlib"],
        },
        "prepared_frontier": prepared_frontier,
        "codex": {
            "path": str(codex),
            "private_auth_copy": True,
            "auth_copy_solver_readable": True,
            "ephemeral": True,
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
        "landlock": landlock_receipt,
        "stdout_log": {
            "path": str(log_path),
            "sha256": isolation._sha256_file(log_path),
            "size": log_path.stat().st_size,
        },
    }
    isolation._write_new_json(receipt_path, receipt)
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
    except (CampaignError, OSError, subprocess.SubprocessError, ValueError) as exc:
        parser.error(str(exc))
    print(json.dumps(result, ensure_ascii=False, sort_keys=True))
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
