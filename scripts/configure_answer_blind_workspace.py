#!/usr/bin/env python3
"""Configure a sanitized answer-blind solver workspace.

This is a trusted-controller utility.  It accepts only a problem-only solver
seed (or the fresh, remote-free Git workspace copied from one) and writes the
three project-local files needed to run Archon without inheriting model tools
or controller paths:

* ``.archon/config.json``
* ``.mcp.json``
* ``ANSWER_BLIND_PROTOCOL.md``

No credential, provider endpoint, absolute filesystem path, target list, or
reference to another solver workspace is copied into those files.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import ipaddress
import json
import os
import re
import shutil
import stat
import subprocess
import tempfile
from pathlib import Path, PurePosixPath
from typing import Any, Iterable, Mapping, Sequence
from urllib.parse import urlsplit


SCHEMA_VERSION = 1
PROTOCOL = "icho-answer-blind-v1"
SEED_PROTOCOL = "icho-problem-only-solver-seed-v1"
SEED_MANIFEST = "isolation_manifest.json"
GENERATED_FILES = (
    ".archon/config.json",
    ".archon/AGENTS.md",
    ".mcp.json",
    "ANSWER_BLIND_PROTOCOL.md",
)
VARIANTS = ("gpt", "kimi-k3")
DEFAULT_MAX_OBJECTIVES = 32
DEFAULT_MAX_PARALLEL = 16

_SHA256 = re.compile(r"[0-9a-f]{64}")
_WINDOWS_ABSOLUTE = re.compile(r"^[A-Za-z]:[\\/]")
_SECRET_PATTERNS: tuple[re.Pattern[str], ...] = (
    re.compile(r"sk-ant-[A-Za-z0-9_-]{16,}"),
    re.compile(r"sk-proj-[A-Za-z0-9_-]{16,}"),
    re.compile(r"github_pat_[A-Za-z0-9_]{32,}"),
    re.compile(r"gh[pousr]_[A-Za-z0-9]{20,}"),
    re.compile(r"(?:AKIA|ASIA)[0-9A-Z]{16}"),
    re.compile(r"-----BEGIN [A-Z0-9 ]*PRIVATE KEY-----"),
)
_CREDENTIAL_KEY_PARTS = (
    "api_key",
    "auth_token",
    "access_token",
    "secret",
    "password",
    "credential",
    "base_url",
)


class WorkspaceConfigError(ValueError):
    """The workspace or requested configuration violates the blind boundary."""


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
        raise WorkspaceConfigError("workspace is not an answer-blind solver seed")

    legacy = manifest.get("isolation_claims")
    explicit = manifest.get("isolation")
    legacy_ok = legacy == {"filesystem": True, "network": False}
    explicit_ok = isinstance(explicit, dict) and explicit.get(
        "filesystem_answer_blind"
    ) is True and explicit.get("network_answer_blind") is False
    if not (legacy_ok or explicit_ok):
        raise WorkspaceConfigError(
            "seed manifest must attest filesystem answer blindness and must not "
            "claim network answer blindness"
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
    result: dict[str, str] = {}
    for candidate, digest in raw.items():
        relative = _safe_relative(candidate, label="manifest payload path")
        parts = PurePosixPath(relative).parts
        if relative in {SEED_MANIFEST, *GENERATED_FILES} or ".git" in parts:
            raise WorkspaceConfigError(f"reserved path in seed payload: {relative}")
        if not isinstance(digest, str) or _SHA256.fullmatch(digest) is None:
            raise WorkspaceConfigError(f"invalid payload SHA-256 for {relative}")
        result[relative] = digest
    return result


def _verify_payload(root: Path, manifest: Mapping[str, Any]) -> None:
    payload = _payload_index(manifest)
    for relative, expected in payload.items():
        path = root.joinpath(*PurePosixPath(relative).parts)
        if path.is_symlink() or not path.is_file():
            raise WorkspaceConfigError(f"seed payload is missing or unsafe: {relative}")
        try:
            resolved = path.resolve(strict=True)
            resolved.relative_to(root)
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


def _validate_full_seed_projection(root: Path, manifest: Mapping[str, Any]) -> None:
    """Run the seed builder's full fail-closed validator on a clean projection.

    A configured workspace may contain a fresh ``.git`` directory, while the
    canonical seed validator intentionally accepts no extras.  Copying only
    manifest-declared bytes into a controller temporary directory lets us
    reuse that validator without trusting a solver-authored lightweight
    manifest or Git metadata.
    """

    validator_script = Path(__file__).resolve().with_name(
        "build_answer_blind_solver_seed.py"
    )
    if not validator_script.is_file():
        raise WorkspaceConfigError("trusted seed validator is unavailable")
    spec = importlib.util.spec_from_file_location(
        "_answer_blind_seed_validator", validator_script
    )
    if spec is None or spec.loader is None:
        raise WorkspaceConfigError("trusted seed validator cannot be loaded")
    module = importlib.util.module_from_spec(spec)
    try:
        spec.loader.exec_module(module)
    except Exception as exc:  # pragma: no cover - packaging failure
        raise WorkspaceConfigError("trusted seed validator cannot be imported") from exc

    payload = _payload_index(manifest)
    with tempfile.TemporaryDirectory(prefix="answer-blind-seed-validation-") as raw:
        projection = Path(raw)
        for relative in payload:
            source = root.joinpath(*PurePosixPath(relative).parts)
            destination = projection.joinpath(*PurePosixPath(relative).parts)
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, destination)
        shutil.copyfile(root / SEED_MANIFEST, projection / SEED_MANIFEST)
        try:
            module.validate_seed(projection)
        except Exception as exc:
            raise WorkspaceConfigError(f"full seed validation failed: {exc}") from exc


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
    """Validate the seed boundary and return its resolved root and manifest."""

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
    _validate_full_seed_projection(root, manifest)
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
    if not parsed.path.startswith("/"):
        raise WorkspaceConfigError("LeanExplore URL must contain an absolute URL path")
    return value


def build_mcp_config(*, lean_explore_url: str | None = None) -> dict[str, Any]:
    """Return the closed, project-relative MCP allowlist."""

    url = _loopback_url(lean_explore_url)
    servers: dict[str, Any] = {
        "lean-lsp": {
            "type": "stdio",
            # The controller puts this root-owned, pinned launcher on PATH.
            # Never execute MCP implementation or dependency metadata from the
            # solver-writable project tree.
            "command": "lean-lsp-mcp-trusted",
            "args": [],
            "env": {"LEAN_PROJECT_PATH": "."},
        }
    }
    if url is not None:
        servers["lean-explore"] = {"type": "http", "url": url}
    return {"mcpServers": servers}


def _domain_profile() -> dict[str, Any]:
    return {
        "name": "chemistry",
        "display_name": "IChO chemistry",
        "preflight_imports": [
            "Mathlib",
            "Physlib.Units.Dimension",
            "Physlib.Units.WithDim.Basic",
            "CRNT.Basic.Reaction",
            "IChO2026Chem",
        ],
        "lean_search_packages": ["Mathlib", "Physlib", "CRNT"],
        "target_import_prefixes": [],
        "enforce_classical_physics_modeling": False,
        "require_explicit_mathlib_import": True,
    }


def _gpt_descriptor(*, lean_explore_url: str | None) -> dict[str, Any]:
    mcp = ["lean-lsp"]
    if lean_explore_url is not None:
        mcp.append("lean-explore")
    descriptor: dict[str, Any] = {
        "runner": "codex",
        "model": "gpt-5.6-sol",
        "effort": "max",
        # The solver never receives a real OpenAI credential.  The trusted
        # launcher supplies these two names with a loopback Responses broker
        # URL and a fixed public dummy key; the broker alone holds provider
        # authority outside the solver's filesystem/process boundary.
        "base_url_env": "ANSWER_BLIND_MODEL_BASE_URL",
        "key_env": "ANSWER_BLIND_MODEL_DUMMY_KEY",
        "wire_api": "responses",
        # Force Codex through the root-owned, audited launcher.  Omitting this
        # key makes the Codex harness fall back to ``uv run`` against a
        # project-relative tool tree, which is both mutable and networked.
        "lean_lsp_mcp_bin": "lean-lsp-mcp-trusted",
        "sandbox": "workspace-write",
        # The loop-owned grounding phase uses keyless hosted LeanExplore for
        # Mathlib/Physlib and the project-local overlay for CRNT.  This is not
        # an MCP/tool grant to the model.
        "lean_explore_backend": "hosted",
        "ignore_user_config": True,
        "ephemeral": True,
        "mcp": mcp,
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
            "features.responses_websockets=false",
            "-c",
            "features.responses_websockets_v2=false",
        ],
    }
    if lean_explore_url is not None:
        descriptor["lean_explore_url"] = lean_explore_url
    return descriptor


def _kimi_descriptor() -> dict[str, Any]:
    return {
        "runner": "claude-code",
        "model": "kimi-k3[1m]",
        "backend": "default",
        "claude_extra_args": [
            "--bare",
            "--no-session-persistence",
            "--effort",
            "max",
            "--strict-mcp-config",
            "--mcp-config",
            ".mcp.json",
        ],
        "disallowed_tools": [
            "WebSearch",
            "WebFetch",
            "Agent",
            "Task",
            "ScheduleWakeup",
        ],
    }


def build_archon_config(
    *,
    variant: str,
    max_objectives: int = DEFAULT_MAX_OBJECTIVES,
    max_parallel: int = DEFAULT_MAX_PARALLEL,
    lean_explore_url: str | None = None,
) -> dict[str, Any]:
    """Build one complete Archon config without consulting host settings."""

    if variant not in VARIANTS:
        raise WorkspaceConfigError(f"variant must be one of: {', '.join(VARIANTS)}")
    objectives = _positive_int(max_objectives, name="max_objectives")
    parallel = _positive_int(max_parallel, name="max_parallel")
    url = _loopback_url(lean_explore_url)
    harness = f"answer-blind-{variant}"
    model = "gpt-5.6-sol" if variant == "gpt" else "kimi-k3[1m]"
    descriptor = (
        _gpt_descriptor(lean_explore_url=url)
        if variant == "gpt"
        else _kimi_descriptor()
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
            "physics_aware": False,
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
            "pipeline_target_review": False,
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


def build_protocol_document(
    *, variant: str, lean_explore_url: str | None = None
) -> str:
    """Render the solver-visible policy; it contains no controller paths."""

    if variant not in VARIANTS:
        raise WorkspaceConfigError(f"variant must be one of: {', '.join(VARIANTS)}")
    url = _loopback_url(lean_explore_url)
    model = "gpt-5.6-sol via Codex" if variant == "gpt" else "kimi-k3[1m] via Claude Code"
    explore = (
        "LeanExplore is allowed only through the configured loopback MCP endpoint."
        if url is not None
        else "LeanExplore is not configured for this workspace."
    )
    return f"""# Answer-Blind Solver Protocol

Protocol: `{PROTOCOL}`
Solver variant: `{variant}`
Pinned harness: `{model}`

## Binding isolation declaration

- `filesystem_answer_blind = true`
- `network_answer_blind = false`
- Phase: `solve`
- Source authority: `problem-only`
- `official_answer_seen = false`

The network declaration records that operating-system-level network isolation is
not being claimed. It is not permission to seek answer-bearing material. Browser,
web, and search tools are disabled. {explore}

## Problem-only source policy

Use only the problem-only JSONL bundle, its referenced problem statement assets,
and the local Lean/library sources in this workspace. Derive every candidate from
those materials. Do not consult or reconstruct official answers, worked solutions,
marking schemes, rubrics, grader keys, prior-run reports, prior blueprints, reference
packs, or any other model's workspace. Do not import artifacts produced by another
solver variant.

If answer-bearing material is encountered, stop the solve phase and report an
isolation violation. Never copy such material into source, logs, prompts, reviews,
or candidate artifacts. Freeze candidate artifacts before any grader-side material
is opened.

## Mandatory proof workflow

Every target must pass the formalization review gate before proving and the proof
review gate before acceptance. Keep deterministic planning and review enabled, run
the configured parallel formalization and per-target reviews, keep pipelined target
review disabled, and retain the axiom sweep. A compiling theorem is not sufficient
when its statement is semantically weaker than the problem or when it depends on
`sorryAx` or another unapproved axiom.

Subagents and multilane execution are disabled. The only MCP tools admitted by the
project configuration are the controller-pinned, root-owned Lean LSP server and,
when explicitly configured, the loopback LeanExplore server.
"""


def build_agents_document(*, variant: str) -> str:
    """Render the mandatory phase preamble without the unsafe legacy template."""

    if variant not in VARIANTS:
        raise WorkspaceConfigError(f"variant must be one of: {', '.join(VARIANTS)}")
    return f"""# Answer-Blind Agent Instructions

This workspace follows `{PROTOCOL}` for the `{variant}` solver. Read
`ANSWER_BLIND_PROTOCOL.md` before every phase and obey it as the governing
project policy.

- Use only the problem-only sources, local Lean libraries, and current-run
  artifacts in this isolated workspace.
- Never search the web, call an external LLM, inspect another workspace, or
  seek an official answer, solution, rubric, marking scheme, prior proof, or
  prior blueprint.
- If answer-bearing material appears, stop and report an isolation violation.
- Do not edit `.mcp.json`, `.archon/config.json`, this file, the protocol,
  isolation manifest, source reports, question bundle, PDF, or problem images.
- Restrict writes to the current assigned target, its candidate JSON, its own
  blueprint chapter, and Archon task/review output explicitly requested by the
  phase prompt. Do not create memory files outside this workspace.
- Derive raw results before choosing a report value. Use only the reporting,
  tolerance, and candidate-domain policies fixed in the blind source record.
  Bind every candidate field to an explicit Lean declaration and theorem type.
- A compiling file is insufficient: all formalization, proof, source-contract,
  axiom, and freeze gates must pass without `sorry`, `admit`, custom axioms, or
  answer-shaped unsupported premises.
"""


def _walk_json(value: Any, *, location: str = "$") -> Iterable[tuple[str, Any]]:
    yield location, value
    if isinstance(value, dict):
        for key, child in value.items():
            yield from _walk_json(child, location=f"{location}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from _walk_json(child, location=f"{location}[{index}]")


def _audit_generated(config: Mapping[str, Any], mcp: Mapping[str, Any], doc: str) -> None:
    servers = mcp.get("mcpServers")
    if not isinstance(servers, dict) or not servers:
        raise WorkspaceConfigError("MCP config must have an explicit server allowlist")
    if not set(servers).issubset({"lean-lsp", "lean-explore"}) or "lean-lsp" not in servers:
        raise WorkspaceConfigError("MCP config contains a non-Lean server")
    lean_lsp = servers["lean-lsp"]
    if not isinstance(lean_lsp, dict) or lean_lsp.get("type") != "stdio":
        raise WorkspaceConfigError("lean-lsp must be an explicit stdio MCP server")
    if lean_lsp.get("command") != "lean-lsp-mcp-trusted" or lean_lsp.get(
        "args"
    ) != [] or lean_lsp.get("env") != {
        "LEAN_PROJECT_PATH": "."
    }:
        raise WorkspaceConfigError("lean-lsp must use the trusted pinned launcher")

    for document_name, document in (("config", config), ("mcp", mcp)):
        for location, value in _walk_json(document):
            key = location.rsplit(".", 1)[-1].casefold()
            gateway_env_name = (
                key == "base_url_env"
                and value == "ANSWER_BLIND_MODEL_BASE_URL"
            )
            if any(part in key for part in _CREDENTIAL_KEY_PARTS) and not gateway_env_name:
                raise WorkspaceConfigError(f"credential/provider field forbidden at {location}")
            if isinstance(value, str):
                if "/root" in value.casefold():
                    raise WorkspaceConfigError(f"root path forbidden at {location}")
                if value.startswith(("/", "~/")) or _WINDOWS_ABSOLUTE.match(value):
                    raise WorkspaceConfigError(f"absolute filesystem path forbidden at {location}")
                if any(pattern.search(value) for pattern in _SECRET_PATTERNS):
                    raise WorkspaceConfigError(f"credential material forbidden at {location}")
    if "/root" in doc.casefold() or any(pattern.search(doc) for pattern in _SECRET_PATTERNS):
        raise WorkspaceConfigError("protocol document contains a forbidden path or credential")


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


def configure_answer_blind_workspace(
    workspace: Path | str,
    *,
    variant: str,
    max_objectives: int = DEFAULT_MAX_OBJECTIVES,
    max_parallel: int = DEFAULT_MAX_PARALLEL,
    lean_explore_url: str | None = None,
) -> dict[str, Any]:
    """Validate and deterministically configure one solver workspace."""

    root, _seed_manifest = validate_solver_workspace(workspace)
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


# Short import-friendly alias for controller code.
configure_workspace = configure_answer_blind_workspace


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("workspace", type=Path)
    parser.add_argument("--variant", required=True, choices=VARIANTS)
    parser.add_argument("--max-objectives", type=int, default=DEFAULT_MAX_OBJECTIVES)
    parser.add_argument("--max-parallel", type=int, default=DEFAULT_MAX_PARALLEL)
    parser.add_argument("--lean-explore-url")
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    parser = _parser()
    args = parser.parse_args(argv)
    try:
        manifest = configure_answer_blind_workspace(
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
