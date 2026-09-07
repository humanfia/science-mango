#!/usr/bin/env python3
"""Validate and configure a problem-only IPhO solver workspace.

This controller-side utility intentionally has a small surface: it verifies the
sealed seed inventory and fresh Git boundary, then writes only the four files
needed by the existing answer-blind Archon launcher.  Provider credentials and
provider routing are supplied by the trusted launcher and never written here.
"""

from __future__ import annotations

import argparse
import hashlib
import ipaddress
import json
import os
import re
import stat
import subprocess
import tempfile
from pathlib import Path, PurePosixPath
from typing import Any, Iterable, Mapping, Sequence
from urllib.parse import urlsplit


SCHEMA_VERSION = 1
# These two identifiers remain unchanged because the sealed launcher validates
# them exactly.  They identify the isolation mechanism, not the science domain.
PROTOCOL = "icho-answer-blind-v1"
SEED_PROTOCOL = "icho-problem-only-solver-seed-v1"
SEED_MANIFEST = "isolation_manifest.json"
GENERATED_FILES = (
    ".archon/config.json",
    ".archon/AGENTS.md",
    ".mcp.json",
    "ANSWER_BLIND_PROTOCOL.md",
)
VARIANTS = ("kimi-k3", "gpt")
KIMI_MODEL = "anthropic-kimi-k3"
GPT_MODEL = "gpt-5.6-sol"
KIMI_PDF_COMPATIBILITY_PROMPT = (
    "Never use the Read tool on any .pdf file. Use the extracted question text "
    "and corresponding problem-page PNG image for the assigned target instead. "
    "LeanExplore is the only MCP service; use it for Mathlib and Physlib "
    "grounding, and always pass rerank_top: 0 with packages: [Mathlib, Physlib]. "
    "Verify Lean with the pinned local compiler feedback loop, and "
    "do not look for archon-lean-lsp. Put temporary crops and Lean scratch files "
    "under $TMPDIR or .archon/tmp, never /tmp. Compile only as lake env lean "
    "<file>; never hard-code an absolute lake path, and do not assume shell helpers "
    "such as mkdir, head, or tail are available."
)
DEFAULT_MAX_OBJECTIVES = 28
DEFAULT_MAX_PARALLEL = 4

_SHA256 = re.compile(r"[0-9a-f]{64}")
_WINDOWS_ABSOLUTE = re.compile(r"^[A-Za-z]:[\\/]")
_SECRET_PATTERNS: tuple[re.Pattern[str], ...] = (
    re.compile(r"sk-[A-Za-z0-9_-]{16,}"),
    re.compile(r"github_pat_[A-Za-z0-9_]{32,}"),
    re.compile(r"gh[pousr]_[A-Za-z0-9]{20,}"),
    re.compile(r"(?:AKIA|ASIA)[0-9A-Z]{16}"),
    re.compile(r"-----BEGIN [A-Z0-9 ]*PRIVATE KEY-----"),
)
_FORBIDDEN_GENERATED_KEY_PARTS = (
    "api_key",
    "auth_token",
    "access_token",
    "secret",
    "password",
    "credential",
    "base_url",
    "endpoint",
)


class WorkspaceConfigError(ValueError):
    """The requested workspace configuration violates the blind boundary."""


def _json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=True, indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")


def _sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _positive_int(value: Any, *, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 1:
        raise WorkspaceConfigError(f"{name} must be a positive integer")
    return value


def _safe_relative(raw: object, *, label: str) -> str:
    value = str(raw)
    if not value or "\\" in value or "\x00" in value:
        raise WorkspaceConfigError(f"{label} is not a safe project-relative path")
    path = PurePosixPath(value)
    if (
        path.is_absolute()
        or path.as_posix() != value
        or any(part in {"", ".", ".."} for part in path.parts)
    ):
        raise WorkspaceConfigError(f"{label} is not a normalized project-relative path")
    return path.as_posix()


def _load_seed_manifest(root: Path) -> dict[str, Any]:
    path = root / SEED_MANIFEST
    if path.is_symlink() or not path.is_file():
        raise WorkspaceConfigError(
            f"workspace must contain a plain {SEED_MANIFEST} from the sanitized seed"
        )
    try:
        manifest = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise WorkspaceConfigError(f"invalid {SEED_MANIFEST}") from exc
    if not isinstance(manifest, dict):
        raise WorkspaceConfigError(f"{SEED_MANIFEST} must contain a JSON object")
    if manifest.get("protocol") != SEED_PROTOCOL:
        raise WorkspaceConfigError("workspace is not a supported problem-only solver seed")

    legacy = manifest.get("isolation_claims")
    explicit = manifest.get("isolation")
    legacy_ok = legacy == {"filesystem": True, "network": False}
    explicit_ok = isinstance(explicit, dict) and explicit.get(
        "filesystem_answer_blind"
    ) is True and explicit.get("network_answer_blind") is False
    if not (legacy_ok or explicit_ok):
        raise WorkspaceConfigError(
            "seed manifest must attest filesystem answer blindness without "
            "claiming network answer blindness"
        )

    policy = manifest.get("workspace_policy")
    if not isinstance(policy, dict):
        raise WorkspaceConfigError("seed manifest is missing workspace_policy")
    if (
        policy.get("fresh_git_init") is not True
        or policy.get("history") is not False
        or policy.get("remotes") != []
    ):
        raise WorkspaceConfigError("seed manifest does not require fresh, remote-free Git")
    return manifest


def _payload_index(manifest: Mapping[str, Any]) -> dict[str, str]:
    raw = manifest.get("payload_files")
    if not isinstance(raw, dict) or not raw:
        raise WorkspaceConfigError("seed manifest payload_files must be a non-empty object")
    payload: dict[str, str] = {}
    for candidate, digest in raw.items():
        relative = _safe_relative(candidate, label="manifest payload path")
        if relative in {SEED_MANIFEST, *GENERATED_FILES} or ".git" in PurePosixPath(
            relative
        ).parts:
            raise WorkspaceConfigError(f"reserved path in seed payload: {relative}")
        if not isinstance(digest, str) or _SHA256.fullmatch(digest) is None:
            raise WorkspaceConfigError(f"invalid payload SHA-256 for {relative}")
        payload[relative] = digest
    return payload


def _verify_payload(root: Path, manifest: Mapping[str, Any]) -> None:
    payload = _payload_index(manifest)
    for relative, expected in payload.items():
        path = root.joinpath(*PurePosixPath(relative).parts)
        if path.is_symlink() or not path.is_file():
            raise WorkspaceConfigError(f"seed payload is missing or unsafe: {relative}")
        try:
            path.resolve(strict=True).relative_to(root)
        except (OSError, ValueError) as exc:
            raise WorkspaceConfigError(f"seed payload escapes the workspace: {relative}") from exc
        if _sha256(path.read_bytes()) != expected:
            raise WorkspaceConfigError(f"seed payload hash mismatch: {relative}")

    allowed = set(payload) | {SEED_MANIFEST, *GENERATED_FILES}
    for directory, names, files in os.walk(root, topdown=True, followlinks=False):
        base = Path(directory)
        kept: list[str] = []
        for name in sorted(names):
            candidate = base / name
            relative = candidate.relative_to(root).as_posix()
            if candidate.is_symlink():
                raise WorkspaceConfigError(f"symbolic link is forbidden: {relative}")
            if base == root and name == ".git":
                continue
            kept.append(name)
        names[:] = kept
        for name in sorted(files):
            candidate = base / name
            relative = candidate.relative_to(root).as_posix()
            if candidate.is_symlink():
                raise WorkspaceConfigError(f"symbolic link is forbidden: {relative}")
            if relative not in allowed:
                raise WorkspaceConfigError(
                    f"file is outside the sanitized seed inventory: {relative}"
                )


def _git(arguments: Sequence[str], *, cwd: Path) -> subprocess.CompletedProcess[str]:
    environment = os.environ.copy()
    environment["GIT_CONFIG_NOSYSTEM"] = "1"
    environment["GIT_CONFIG_GLOBAL"] = os.devnull
    environment["GIT_DISCOVERY_ACROSS_FILESYSTEM"] = "0"
    try:
        return subprocess.run(
            ["git", *arguments],
            cwd=cwd,
            env=environment,
            check=True,
            capture_output=True,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        raise WorkspaceConfigError(
            "workspace .git metadata is not a valid fresh repository"
        ) from exc


def _verify_fresh_git(root: Path) -> None:
    git_dir = root / ".git"
    if not git_dir.exists() and not git_dir.is_symlink():
        return
    if git_dir.is_symlink() or not git_dir.is_dir():
        raise WorkspaceConfigError("workspace .git must be absent or a plain fresh repository")
    top = Path(_git(["rev-parse", "--show-toplevel"], cwd=root).stdout.strip()).resolve()
    if top != root:
        raise WorkspaceConfigError("workspace .git belongs to a different worktree")
    if _git(["remote"], cwd=root).stdout.strip():
        raise WorkspaceConfigError("answer-blind workspace must not have Git remotes")
    if _git(["rev-list", "--all"], cwd=root).stdout.strip():
        raise WorkspaceConfigError("answer-blind workspace Git history must be empty")


def validate_solver_workspace(workspace: Path | str) -> tuple[Path, dict[str, Any]]:
    candidate = Path(workspace)
    if candidate.is_symlink():
        raise WorkspaceConfigError("workspace must not be a symbolic link")
    try:
        root = candidate.resolve(strict=True)
    except OSError as exc:
        raise WorkspaceConfigError("workspace does not exist") from exc
    if not root.is_dir():
        raise WorkspaceConfigError("workspace must be a directory")
    manifest = _load_seed_manifest(root)
    _verify_payload(root, manifest)
    _verify_fresh_git(root)
    return root, manifest


def _loopback_url(raw: str | None) -> str | None:
    if raw is None:
        return None
    value = raw.strip()
    if not value:
        raise WorkspaceConfigError("LeanExplore URL must not be empty")
    try:
        parsed = urlsplit(value)
        port = parsed.port
    except ValueError as exc:
        raise WorkspaceConfigError("LeanExplore URL has an invalid port") from exc
    if (
        parsed.scheme != "http"
        or not parsed.hostname
        or port is None
        or not 1 <= port <= 65535
        or parsed.username is not None
        or parsed.password is not None
        or parsed.query
        or parsed.fragment
        or not parsed.path.startswith("/")
    ):
        raise WorkspaceConfigError(
            "LeanExplore must be an explicit HTTP loopback URL with a port"
        )
    hostname = parsed.hostname.casefold()
    if hostname != "localhost":
        try:
            address = ipaddress.ip_address(hostname)
        except ValueError as exc:
            raise WorkspaceConfigError("LeanExplore host must be loopback") from exc
        if not address.is_loopback:
            raise WorkspaceConfigError("LeanExplore host must be loopback")
    return value


def build_mcp_config(*, lean_explore_url: str | None = None) -> dict[str, Any]:
    url = _loopback_url(lean_explore_url)
    if url is not None:
        server: dict[str, Any] = {"type": "http", "url": url}
    else:
        server = {
            "type": "stdio",
            "command": "python",
            "env": {
                "OMP_NUM_THREADS": "1",
                "OPENBLAS_NUM_THREADS": "1",
                "RAYON_NUM_THREADS": "1",
            },
            "args": [
                "-P",
                "-m",
                "archon.commands.tooling.lean_explore_mcp_shim",
                "--backend",
                "local",
                "--transport",
                "stdio",
            ],
            "timeout": 600000,
        }
    return {"mcpServers": {"lean-explore": server}}


def _domain_profile() -> dict[str, Any]:
    return {
        "name": "physics",
        "display_name": "IPhO physics",
        "preflight_imports": ["Mathlib", "Physlib"],
        "lean_search_packages": ["Mathlib", "Physlib"],
        "target_import_prefixes": ["Physlib"],
        "enforce_classical_physics_modeling": True,
        "require_explicit_mathlib_import": True,
    }


def _kimi_descriptor(*, lean_explore_url: str | None) -> dict[str, Any]:
    descriptor: dict[str, Any] = {
        "runner": "claude-code",
        "model": KIMI_MODEL,
        "backend": "default",
        "lean_explore_backend": "local",
        "claude_extra_args": [
            "--bare",
            "--no-session-persistence",
            "--append-system-prompt",
            KIMI_PDF_COMPATIBILITY_PROMPT,
            "--effort",
            "max",
            "--strict-mcp-config",
            "--mcp-config",
            ".mcp.json",
        ],
        "disallowed_tools": [
            "ListMcpResourcesTool",
            "ReadMcpResourceDirTool",
            "ReadMcpResourceTool",
            "WebSearch",
            "WebFetch",
            "Agent",
            "Task",
            "ScheduleWakeup",
        ],
    }
    if lean_explore_url is not None:
        descriptor["lean_explore_url"] = lean_explore_url
    return descriptor


def _gpt_descriptor(*, lean_explore_url: str | None) -> dict[str, Any]:
    descriptor: dict[str, Any] = {
        "runner": "codex",
        "model": GPT_MODEL,
        "effort": "max",
        # The root-side launcher provides a private CODEX_HOME containing only
        # auth.json.  No host settings, plugins, skills, or MCP configuration
        # are inherited by the solver.
        "ignore_user_config": True,
        "ephemeral": True,
        # Codex's own sandbox cannot start on this host.  The campaign launcher
        # supplies the actual dedicated-UID + Landlock boundary instead.
        "sandbox": "danger-full-access",
        "lean_explore_backend": "local",
        "mcp": ["lean-explore"],
        "extra_args": [
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
        ],
    }
    if lean_explore_url is not None:
        descriptor["lean_explore_url"] = lean_explore_url
    return descriptor


def build_archon_config(
    *,
    variant: str,
    max_objectives: int = DEFAULT_MAX_OBJECTIVES,
    max_parallel: int = DEFAULT_MAX_PARALLEL,
    lean_explore_url: str | None = None,
) -> dict[str, Any]:
    if variant not in VARIANTS:
        raise WorkspaceConfigError(f"variant must be one of: {', '.join(VARIANTS)}")
    objectives = _positive_int(max_objectives, name="max_objectives")
    parallel = _positive_int(max_parallel, name="max_parallel")
    url = _loopback_url(lean_explore_url)
    harness = f"answer-blind-{variant}"
    model = GPT_MODEL if variant == "gpt" else KIMI_MODEL
    descriptor = (
        _gpt_descriptor(lean_explore_url=url)
        if variant == "gpt"
        else _kimi_descriptor(lean_explore_url=url)
    )
    return {
        "schema_version": SCHEMA_VERSION,
        "answer_blind": {
            "protocol": PROTOCOL,
            "phase": "solve",
            "authority": "problem-only",
            "official_answer_seen": False,
            "policy_document": "ANSWER_BLIND_PROTOCOL.md",
            "isolation": {
                "filesystem_answer_blind": True,
                "network_answer_blind": False,
            },
        },
        "loop": {
            "max_iterations": 100,
            "parallel": True,
            "max_parallel": parallel,
            "max_objectives": objectives,
            "model": model,
            "verbose_logs": False,
            "no_review": False,
            "formalization_review_gate": True,
            "formalization_review_max_iterations": 10,
            "proof_review_gate": True,
            "proof_review_max_iterations": 10,
            "lean_aware": True,
            "physics_aware": True,
            "domain_profile": _domain_profile(),
            "debug_feedback": False,
            "claude_backend": "default",
            "harness": harness,
            "axiom_sweep": True,
            "axiom_sweep_scope": "current_objectives",
            "axiom_sweep_jobs": min(parallel, 2),
            "axiom_sweep_timeout_sec": 1800,
            "deterministic_plan": True,
            "shared_infrastructure": {
                "enabled": False,
                "module_roots": [],
                "scaffolder": "lean-scaffolder",
                "migration_refactor": "refactor",
            },
            "deterministic_review": True,
            "review_preflight_jobs": parallel,
            "review_preflight_timeout_sec": 3600,
            "parallel_target_review": True,
            "pipeline_target_review": True,
            "parallel_target_review_jobs": parallel,
            "parallel_target_review_max_attempts": 3,
            "parallel_target_review_backoff_sec": 5,
            "sync_leanok_timeout_sec": 1800,
            "parallel_formalization_review": True,
            "parallel_formalization_review_jobs": parallel,
            "parallel_formalization_review_max_attempts": 3,
            "parallel_formalization_review_backoff_sec": 5,
        },
        "harnesses": {harness: descriptor},
        "subagents": {"enabled": []},
        "state": {"recent_iter_window": 3},
        "multilane": {"enabled": False, "lanes": []},
    }


def build_protocol_document(*, variant: str, lean_explore_url: str | None = None) -> str:
    if variant not in VARIANTS:
        raise WorkspaceConfigError(f"variant must be one of: {', '.join(VARIANTS)}")
    url = _loopback_url(lean_explore_url)
    explore = (
        "LeanExplore is available only through the configured loopback service."
        if url is not None
        else "LeanExplore uses the controller-pinned local library index."
    )
    pinned = (
        f"`{GPT_MODEL}` via Codex"
        if variant == "gpt"
        else f"`{KIMI_MODEL}` via Claude Code"
    )
    compatibility = (
        "\nKimi compatibility: never use the Claude `Read` tool on a `.pdf` file because\n"
        "this endpoint does not accept PDF document blocks. Use the extracted question\n"
        "text and the corresponding problem-page PNG image instead.\n"
        if variant == "kimi-k3"
        else ""
    )
    return f"""# IPhO Answer-Blind Solver Protocol

Protocol: `{PROTOCOL}`
Solver variant: `{variant}`
Pinned harness: {pinned}

## Binding isolation declaration

- `filesystem_answer_blind = true`
- `network_answer_blind = false`
- Phase: `solve`
- Source authority: `problem-only`
- `official_answer_seen = false`

Network isolation is not claimed. This is not permission to seek answer-bearing
material. Browser and web tools are disabled. {explore}

## Problem-only source policy

Use only the IPhO problem-only bundle, its referenced problem statement assets,
the current-run artifacts, and local Lean libraries. Do not consult or reconstruct
official answers, worked solutions, marking schemes, rubrics, grader material,
prior-run reports, prior blueprints, reference packs, or another solver workspace.
If answer-bearing material is encountered, stop and report an isolation violation.

{compatibility}

LeanExplore may ground theorem and declaration names only in Mathlib and Physlib.
It is not authority for a physical premise or a numerical answer. Derive physical
assumptions and requested quantities from the problem statement before proving.

## Mandatory proof workflow

Every target must pass formalization review before proving and proof review before
acceptance. Keep deterministic planning, review, and the axiom sweep enabled. A
compiling theorem is insufficient if its statement is semantically weaker than the
problem or if it depends on `sorryAx` or another unapproved axiom.

Subagents and multilane execution are disabled. The only admitted MCP service is
local LeanExplore. Lean checking uses the pinned local compiler feedback loop.
"""


def build_agents_document(*, variant: str) -> str:
    if variant not in VARIANTS:
        raise WorkspaceConfigError(f"variant must be one of: {', '.join(VARIANTS)}")
    pdf_instruction = (
        "- Never use `Read` on a `.pdf`; use the extracted question text and corresponding\n"
        "  problem-page PNG image. The Kimi endpoint does not accept PDF document blocks.\n"
        if variant == "kimi-k3"
        else "- Use the extracted question text and corresponding problem-page PNG image.\n"
    )
    return f"""# IPhO Answer-Blind Agent Instructions

This workspace follows `{PROTOCOL}` for the `{variant}` solver. Read
`ANSWER_BLIND_PROTOCOL.md` before every phase and obey it as project policy.

- Use only problem-only sources, local Mathlib and Physlib, and current-run
  artifacts inside this isolated workspace.
- Use LeanExplore only to locate Mathlib/Physlib declarations and theorems.
- Never seek an official answer, solution, marking scheme, prior proof, prior
  blueprint, external model output, or another workspace.
{pdf_instruction.rstrip()}
- Do not edit `.mcp.json`, `.archon/config.json`, this file, the protocol,
  isolation manifest, source reports, question bundle, PDF, or problem images.
- Restrict writes to the assigned target, its candidate record, its own blueprint
  chapter, and the Archon task/review output requested by the current phase.
- State every physical assumption explicitly and tie it to problem-only material.
- Compilation is insufficient: formalization, proof, source-contract, axiom, and
  freeze gates must pass without `sorry`, `admit`, custom axioms, or unsupported
  answer-shaped premises.
"""


def _walk_json(value: Any, *, location: str = "$") -> Iterable[tuple[str, Any]]:
    yield location, value
    if isinstance(value, dict):
        for key, child in value.items():
            yield from _walk_json(child, location=f"{location}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from _walk_json(child, location=f"{location}[{index}]")


def _audit_generated(
    config: Mapping[str, Any], mcp: Mapping[str, Any], documents: str
) -> None:
    servers = mcp.get("mcpServers")
    if not isinstance(servers, dict) or set(servers) != {"lean-explore"}:
        raise WorkspaceConfigError("MCP config must contain only LeanExplore")
    lean_explore = servers["lean-explore"]
    local_lean_explore = build_mcp_config()["mcpServers"]["lean-explore"]
    if lean_explore != local_lean_explore:
        if (
            not isinstance(lean_explore, dict)
            or set(lean_explore) != {"type", "url"}
            or lean_explore.get("type") != "http"
            or not isinstance(lean_explore.get("url"), str)
            or _loopback_url(lean_explore["url"]) != lean_explore["url"]
        ):
            raise WorkspaceConfigError(
                "LeanExplore must use local stdio or loopback HTTP"
            )

    blind = config.get("answer_blind")
    loop = config.get("loop")
    harnesses = config.get("harnesses")
    if not isinstance(blind, dict) or not isinstance(loop, dict) or not isinstance(
        harnesses, dict
    ):
        raise WorkspaceConfigError("Archon config is missing required sections")
    descriptor = harnesses.get(loop.get("harness"))
    profile = loop.get("domain_profile")
    model = GPT_MODEL if loop.get("harness") == "answer-blind-gpt" else KIMI_MODEL
    runner = "codex" if loop.get("harness") == "answer-blind-gpt" else "claude-code"
    if (
        blind.get("protocol") != PROTOCOL
        or blind.get("authority") != "problem-only"
        or blind.get("official_answer_seen") is not False
        or loop.get("model") != model
        or loop.get("physics_aware") is not True
        or not isinstance(descriptor, dict)
        or descriptor.get("runner") != runner
        or descriptor.get("model") != model
        or descriptor.get("lean_explore_backend") != "local"
        or not isinstance(profile, dict)
        or profile.get("name") != "physics"
        or profile.get("preflight_imports") != ["Mathlib", "Physlib"]
        or profile.get("lean_search_packages") != ["Mathlib", "Physlib"]
    ):
        raise WorkspaceConfigError("Archon config is not pinned to IPhO physics mode")
    if runner == "codex" and (
        descriptor.get("effort") != "max"
        or descriptor.get("ephemeral") is not True
        or descriptor.get("ignore_user_config") is not True
        or descriptor.get("mcp") != ["lean-explore"]
        or any(
            key in descriptor
            for key in ("base_url_env", "key_env", "wire_api", "codex_home")
        )
        or "features.plugins=false" not in descriptor.get("extra_args", [])
        or "features.browser_use=false" not in descriptor.get("extra_args", [])
        or "features.multi_agent=false" not in descriptor.get("extra_args", [])
        or 'web_search="disabled"' not in descriptor.get("extra_args", [])
    ):
        raise WorkspaceConfigError("GPT harness is not minimally answer-blind")

    combined_text = documents.casefold()
    for forbidden in ("chemistry", "crnt"):
        if forbidden in combined_text:
            raise WorkspaceConfigError(f"generated policy contains forbidden domain: {forbidden}")
    for document_name, document in (("config", config), ("mcp", mcp)):
        for location, value in _walk_json(document):
            key = location.rsplit(".", 1)[-1].casefold()
            if any(part in key for part in _FORBIDDEN_GENERATED_KEY_PARTS):
                raise WorkspaceConfigError(f"provider or credential field forbidden at {location}")
            if isinstance(value, str):
                lowered = value.casefold()
                if "/root" in lowered:
                    raise WorkspaceConfigError(f"root path forbidden at {location}")
                if value.startswith(("/", "~/")) or _WINDOWS_ABSOLUTE.match(value):
                    raise WorkspaceConfigError(f"absolute filesystem path forbidden at {location}")
                if any(pattern.search(value) for pattern in _SECRET_PATTERNS):
                    raise WorkspaceConfigError(f"credential material forbidden at {location}")
                if any(domain in lowered for domain in ("chemistry", "crnt")):
                    raise WorkspaceConfigError(f"foreign domain forbidden at {location}")
    if "/root" in combined_text or any(
        pattern.search(documents) for pattern in _SECRET_PATTERNS
    ):
        raise WorkspaceConfigError("generated policy contains a forbidden path or credential")


def _atomic_write(path: Path, payload: bytes) -> None:
    if path.is_symlink() or (path.exists() and not path.is_file()):
        raise WorkspaceConfigError(f"refusing to replace unsafe output: {path.name}")
    descriptor, temporary = tempfile.mkstemp(prefix=".answer-blind-", dir=path.parent)
    temp_path = Path(temporary)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        temp_path.chmod(stat.S_IRUSR | stat.S_IWUSR | stat.S_IRGRP | stat.S_IROTH)
        os.replace(temp_path, path)
    except BaseException:
        temp_path.unlink(missing_ok=True)
        raise


def configure_ipho_answer_blind_workspace(
    workspace: Path | str,
    *,
    variant: str,
    max_objectives: int = DEFAULT_MAX_OBJECTIVES,
    max_parallel: int = DEFAULT_MAX_PARALLEL,
    lean_explore_url: str | None = None,
) -> dict[str, Any]:
    root, _manifest = validate_solver_workspace(workspace)
    url = _loopback_url(lean_explore_url)
    config = build_archon_config(
        variant=variant,
        max_objectives=max_objectives,
        max_parallel=max_parallel,
        lean_explore_url=url,
    )
    mcp = build_mcp_config(lean_explore_url=url)
    protocol = build_protocol_document(variant=variant, lean_explore_url=url)
    agents = build_agents_document(variant=variant)
    _audit_generated(config, mcp, protocol + "\n" + agents)

    archon_dir = root / ".archon"
    if archon_dir.is_symlink() or (archon_dir.exists() and not archon_dir.is_dir()):
        raise WorkspaceConfigError("workspace .archon must be a plain directory")
    archon_dir.mkdir(mode=0o755, exist_ok=True)
    payloads = {
        ".archon/config.json": _json_bytes(config),
        ".archon/AGENTS.md": agents.encode("utf-8"),
        ".mcp.json": _json_bytes(mcp),
        "ANSWER_BLIND_PROTOCOL.md": protocol.encode("utf-8"),
    }
    for relative in GENERATED_FILES:
        _atomic_write(root.joinpath(*PurePosixPath(relative).parts), payloads[relative])

    return {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        "variant": variant,
        "isolation": {
            "filesystem_answer_blind": True,
            "network_answer_blind": False,
        },
        "files": {
            relative: {
                "sha256": _sha256(payloads[relative]),
                "size": len(payloads[relative]),
            }
            for relative in sorted(payloads)
        },
    }


# Controller code uses the generic alias; retain the descriptive name for CLI users.
configure_workspace = configure_ipho_answer_blind_workspace


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("workspace", type=Path)
    parser.add_argument("--variant", choices=VARIANTS, default="kimi-k3")
    parser.add_argument("--max-objectives", type=int, default=DEFAULT_MAX_OBJECTIVES)
    parser.add_argument("--max-parallel", type=int, default=DEFAULT_MAX_PARALLEL)
    parser.add_argument("--lean-explore-url")
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    parser = _parser()
    args = parser.parse_args(argv)
    try:
        manifest = configure_ipho_answer_blind_workspace(
            args.workspace,
            variant=args.variant,
            max_objectives=args.max_objectives,
            max_parallel=args.max_parallel,
            lean_explore_url=args.lean_explore_url,
        )
    except WorkspaceConfigError as exc:
        parser.error(str(exc))
    print(json.dumps(manifest, ensure_ascii=True, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
