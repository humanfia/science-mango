"""Project-local shared-infrastructure queue for the Archon loop.

Proof Review may discover that several targets need the same reusable Lean
definitions or lemmas.  This module turns an *explicit, structured* Review
request into one allowlisted project-local module objective.  It deliberately
does not install, synthesize, or update external Lake dependencies.

The queue is loop-owned state. Requests are coalesced by module path. A
dependent proof is reopened only after the module is declaration-complete and
axiom-clean, Lake emitted its build artifact, the consumer imports the shared
module, and a subsequent full ``lake build`` succeeds.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import tempfile
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable

from archon.commands.tooling.project_config import load_project_config


STATE_FILENAME = "shared-infrastructure.json"
STATE_VERSION = 1
PROJECT_LOCAL_KIND = "project_local_shared_module"
EXTERNAL_KIND = "external_dependency"
SUPPORTED_KINDS = {PROJECT_LOCAL_KIND, EXTERNAL_KIND}

_PLACEHOLDER_RE = re.compile(
    r"(?<![A-Za-z0-9_!?'])(?:sorry|sorryAx|admit)(?![A-Za-z0-9_!?'])"
)
_LEAN_DECLARATION_NAME_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$"
)
_LEAN_MODULE_SEGMENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
_LEAN_KEYWORDS = {
    "abbrev", "axiom", "class", "def", "deriving", "do", "else", "end",
    "export", "extends", "if", "import", "in", "inductive", "instance",
    "let", "match", "namespace", "opaque", "open", "private", "protected",
    "section", "structure", "theorem", "then", "universe", "variable",
    "where", "with",
}


@dataclass(frozen=True)
class SharedInfrastructurePolicy:
    enabled: bool
    module_roots: tuple[Path, ...]
    scaffolder: str
    migration_refactor: str


@dataclass(frozen=True)
class SharedInfrastructureObjective:
    module_path: str
    declarations: tuple[str, ...]
    dependents: tuple[str, ...]
    reason: str
    mode: str = "mathlib-build"

    @property
    def path(self) -> Path:
        return Path(self.module_path)


@dataclass(frozen=True)
class SharedConsumerMigrationObjective:
    target_path: str
    modules: tuple[str, ...]


@dataclass(frozen=True)
class SharedInfrastructureReconcileResult:
    verified_modules: tuple[str, ...]
    resolved_modules: tuple[str, ...]
    reopened_targets: tuple[str, ...]


def _utcnow() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def load_shared_infrastructure_policy(
    project_path: Path,
) -> SharedInfrastructurePolicy:
    """Load the opt-in, allowlisted project-local module policy."""
    loop = load_project_config(project_path).loop_section()
    raw = loop.get("shared_infrastructure")
    section = raw if isinstance(raw, dict) else {}
    roots: list[Path] = []
    raw_roots = section.get("module_roots", [])
    if isinstance(raw_roots, list):
        for value in raw_roots:
            path = Path(str(value).strip())
            if (
                str(path)
                and not path.is_absolute()
                and "." not in path.parts
                and ".." not in path.parts
            ):
                roots.append(path)
    return SharedInfrastructurePolicy(
        enabled=bool(section.get("enabled", False)) and bool(roots),
        module_roots=tuple(dict.fromkeys(roots)),
        scaffolder=str(section.get("scaffolder") or "lean-scaffolder"),
        migration_refactor=str(section.get("migration_refactor") or "refactor"),
    )


def _safe_module_path(
    project_path: Path,
    raw_module: Any,
    policy: SharedInfrastructurePolicy,
) -> str | None:
    value = str(raw_module or "").strip().replace("\\", "/")
    rel = Path(value)
    module_parts = rel.with_suffix("").parts
    if (
        not value
        or rel.is_absolute()
        or rel.suffix != ".lean"
        or any(part in {"", ".", ".."} for part in rel.parts)
        or any(
            not _LEAN_MODULE_SEGMENT_RE.fullmatch(part)
            or part in _LEAN_KEYWORDS
            for part in module_parts
        )
    ):
        return None
    project = project_path.resolve()
    candidate = (project / rel).resolve()
    try:
        candidate.relative_to(project)
    except ValueError:
        return None
    for root in policy.module_roots:
        allowed = (project / root).resolve()
        try:
            candidate.relative_to(allowed)
            return rel.as_posix()
        except ValueError:
            continue
    return None


def _safe_consumer_path(project_path: Path, raw_target: Any) -> str | None:
    value = str(raw_target or "").strip().replace("\\", "/")
    rel = Path(value)
    if (
        not value
        or rel.is_absolute()
        or rel.suffix != ".lean"
        or any(part in {"", ".", ".."} for part in rel.parts)
        or any(part in {".archon", ".git", ".lake", "lake-packages"}
               for part in rel.parts)
    ):
        return None
    project = project_path.resolve()
    try:
        (project / rel).resolve().relative_to(project)
    except ValueError:
        return None
    return rel.as_posix()


def normalize_infrastructure_request(
    raw: Any,
    *,
    project_path: Path,
) -> tuple[dict[str, Any] | None, str]:
    """Validate a Review request without granting external-package writes.

    The optional field is backward-compatible: ``None`` means no structured
    request.  ``external_dependency`` is retained as evidence but is never
    inserted into the project-local build queue.
    """
    if raw is None:
        return None, ""
    if not isinstance(raw, dict):
        return None, "infrastructure_request must be an object"
    kind = str(raw.get("kind") or "").strip().lower().replace("-", "_")
    if kind not in SUPPORTED_KINDS:
        return None, f"unsupported infrastructure_request kind {kind!r}"
    if kind == EXTERNAL_KIND:
        package = str(raw.get("package") or raw.get("module") or "").strip()
        if not package:
            return None, "external_dependency request requires package"
        return {"kind": EXTERNAL_KIND, "package": package}, ""

    policy = load_shared_infrastructure_policy(project_path)
    if not policy.enabled:
        return None, "project-local shared infrastructure is not enabled"
    raw_module = raw.get("module") or raw.get("module_path")
    raw_rel = Path(str(raw_module or "").strip().replace("\\", "/"))
    raw_parts = raw_rel.with_suffix("").parts
    if raw_rel.suffix == ".lean" and any(
        not _LEAN_MODULE_SEGMENT_RE.fullmatch(part)
        or part in _LEAN_KEYWORDS
        for part in raw_parts
    ):
        return None, (
            "project-local module must use non-keyword ASCII Lean "
            "identifier path segments"
        )
    module = _safe_module_path(project_path, raw_module, policy)
    if module is None:
        roots = ", ".join(path.as_posix() for path in policy.module_roots)
        return None, (
            "project-local module is outside the configured allowlist "
            f"({roots or 'empty'})"
        )
    raw_declarations = raw.get("declarations", [])
    if raw_declarations is None:
        raw_declarations = []
    if not isinstance(raw_declarations, list):
        return None, "infrastructure_request declarations must be a list"
    declarations = tuple(dict.fromkeys(
        str(item).strip() for item in raw_declarations if str(item).strip()
    ))
    if not declarations:
        return None, (
            "project_local_shared_module request requires at least one "
            "declaration"
        )
    if any(not _LEAN_DECLARATION_NAME_RE.fullmatch(name) for name in declarations):
        return None, (
            "infrastructure_request declarations must be dot-qualified "
            "ASCII Lean identifiers"
        )
    return {
        "kind": PROJECT_LOCAL_KIND,
        "module": module,
        "declarations": list(declarations),
    }, ""


def load_shared_infrastructure_state(state_dir: Path) -> dict[str, Any]:
    path = state_dir / STATE_FILENAME
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {"version": STATE_VERSION, "modules": {}}
    if not isinstance(raw, dict):
        return {"version": STATE_VERSION, "modules": {}}
    if not isinstance(raw.get("modules"), dict):
        raw["modules"] = {}
    return raw


def _write_state(state_dir: Path, state: dict[str, Any]) -> None:
    path = state_dir / STATE_FILENAME
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(
        json.dumps(state, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    tmp.replace(path)


def register_shared_infrastructure_request(
    *,
    state_dir: Path,
    project_path: Path,
    target_rel: str,
    raw_request: Any,
    reason: str,
    evidence: str,
    iter_num: int,
) -> tuple[dict[str, Any] | None, str]:
    """Persist one request, coalescing all dependents of the same module."""
    request, error = normalize_infrastructure_request(
        raw_request, project_path=project_path,
    )
    if request is None or request.get("kind") != PROJECT_LOCAL_KIND:
        return request, error
    module = str(request["module"])
    target = _safe_consumer_path(project_path, target_rel)
    if target is None:
        return None, "shared-infrastructure consumer must be a project-local .lean file"
    if target == module:
        return None, "shared-infrastructure module cannot depend on itself"
    state = load_shared_infrastructure_state(state_dir)
    modules = state["modules"]
    prior = modules.get(module)
    prior = prior if isinstance(prior, dict) else {}
    dependents = set(
        str(item) for item in prior.get("dependents", []) if str(item).strip()
    )
    dependents.add(target)
    declarations = set(
        str(item) for item in prior.get("declarations", []) if str(item).strip()
    )
    prior_declarations = set(declarations)
    declarations.update(request.get("declarations", []))
    prior_status = str(prior.get("status") or "")
    was_pending = prior_status == "pending"
    declarations_grew = declarations != prior_declarations
    request_epoch = time.time()
    consumer_migrations = prior.get("consumer_migrations", {})
    consumer_migrations = (
        dict(consumer_migrations)
        if isinstance(consumer_migrations, dict)
        else {}
    )
    # Every fresh Review request must re-establish the requesting consumer's
    # import/build evidence, even when the shared API itself is reusable.
    consumer_migrations.pop(target, None)
    consumer_request_iters = prior.get("consumer_request_iters", {})
    consumer_request_iters = (
        dict(consumer_request_iters)
        if isinstance(consumer_request_iters, dict)
        else {}
    )
    try:
        prior_consumer_iter = int(consumer_request_iters.get(target) or 0)
    except (TypeError, ValueError):
        prior_consumer_iter = 0
    consumer_request_iters[target] = max(prior_consumer_iter, int(iter_num))
    consumer_request_epochs = prior.get("consumer_request_epochs", {})
    consumer_request_epochs = (
        dict(consumer_request_epochs)
        if isinstance(consumer_request_epochs, dict)
        else {}
    )
    try:
        prior_consumer_epoch = float(
            consumer_request_epochs.get(target) or 0.0
        )
    except (TypeError, ValueError):
        prior_consumer_epoch = 0.0
    consumer_request_epochs[target] = max(
        prior_consumer_epoch, request_epoch,
    )
    reusable_verified = (
        prior_status in {"verified_awaiting_migration", "resolved"}
        and not declarations_grew
        and bool(prior.get("verified_sha256"))
    )
    if reusable_verified:
        next_status = "verified_awaiting_migration"
        requested_iter = int(prior.get("requested_iter") or iter_num)
    else:
        next_status = "pending"
        requested_iter = (
            min(int(prior.get("requested_iter") or iter_num), int(iter_num))
            if was_pending and not declarations_grew
            else int(iter_num)
        )
    modules[module] = {
        **prior,
        "status": next_status,
        "module": module,
        "declarations": sorted(declarations),
        "dependents": sorted(dependents),
        "reason": reason or str(prior.get("reason") or ""),
        "evidence": evidence or str(prior.get("evidence") or ""),
        "requested_iter": requested_iter,
        "requested_epoch": (
            float(prior.get("requested_epoch") or request_epoch)
            if reusable_verified
            else request_epoch
        ),
        "consumer_request_iters": consumer_request_iters,
        "consumer_request_epochs": consumer_request_epochs,
        "consumer_migrations": consumer_migrations,
        # Any enlarged contract invalidates prior build/sweep evidence.
        **({
            "resolved_iter": None,
            "verified_iter": None,
            "axiom_sweep_iter": None,
            "verified_sha256": None,
            "consumer_migrations": {},
        } if not reusable_verified and (declarations_grew or not was_pending) else {}),
        "updated_at": _utcnow(),
    }
    state.update({"version": STATE_VERSION, "updated_at": _utcnow()})
    _write_state(state_dir, state)
    return request, ""


def pending_shared_infrastructure_objectives(
    *, state_dir: Path, project_path: Path,
) -> list[SharedInfrastructureObjective]:
    """Return allowlisted pending module objectives in stable order."""
    policy = load_shared_infrastructure_policy(project_path)
    if not policy.enabled:
        return []
    state = load_shared_infrastructure_state(state_dir)
    objectives: list[SharedInfrastructureObjective] = []
    for key, raw in sorted(state.get("modules", {}).items()):
        record = raw if isinstance(raw, dict) else {}
        if record.get("status") != "pending":
            continue
        module = _safe_module_path(project_path, key, policy)
        if module is None:
            continue
        objectives.append(SharedInfrastructureObjective(
            module_path=module,
            declarations=tuple(str(x) for x in record.get("declarations", [])),
            dependents=tuple(str(x) for x in record.get("dependents", [])),
            reason=str(record.get("reason") or ""),
        ))
    return objectives


def missing_shared_module_objectives(
    *, state_dir: Path, project_path: Path,
) -> list[SharedInfrastructureObjective]:
    return [
        objective
        for objective in pending_shared_infrastructure_objectives(
            state_dir=state_dir, project_path=project_path,
        )
        if not (project_path / objective.module_path).is_file()
    ]


def pending_shared_consumer_migrations(
    *, state_dir: Path, project_path: Path,
) -> list[SharedConsumerMigrationObjective]:
    """Aggregate verified module imports that each blocked consumer still owes."""
    policy = load_shared_infrastructure_policy(project_path)
    if not policy.enabled:
        return []
    modules = load_shared_infrastructure_state(state_dir).get("modules", {})
    by_target: dict[str, list[tuple[str, dict[str, Any]]]] = {}
    for raw_module, raw_record in modules.items():
        record = raw_record if isinstance(raw_record, dict) else {}
        module = _safe_module_path(project_path, raw_module, policy)
        if module is None:
            continue
        for target in record.get("dependents", []):
            rel = _safe_consumer_path(project_path, target)
            if rel:
                by_target.setdefault(rel, []).append((module, record))

    result: list[SharedConsumerMigrationObjective] = []
    for target, prerequisites in sorted(by_target.items()):
        # Migrate once all modules are verified, so one refactor can add the
        # complete import set rather than repeatedly touching the consumer.
        if not prerequisites or any(
            record.get("status") not in {
                "verified_awaiting_migration", "resolved",
            }
            for _, record in prerequisites
        ):
            continue
        owed = []
        for module, record in prerequisites:
            migrations = record.get("consumer_migrations", {})
            migration = (
                migrations.get(target) if isinstance(migrations, dict) else None
            )
            if not isinstance(migration, dict) or migration.get("status") != "resolved":
                owed.append(module)
        if owed:
            result.append(SharedConsumerMigrationObjective(
                target_path=target,
                modules=tuple(sorted(owed)),
            ))
    return result


def shared_infrastructure_prompt_block(
    *, state_dir: Path, project_path: Path,
) -> str:
    """Inject mandatory scaffolding/build requests into the planner prompt."""
    objectives = pending_shared_infrastructure_objectives(
        state_dir=state_dir, project_path=project_path,
    )
    migrations = pending_shared_consumer_migrations(
        state_dir=state_dir, project_path=project_path,
    )
    if not objectives and not migrations:
        return ""
    policy = load_shared_infrastructure_policy(project_path)
    lines = [
        "",
        "## Mandatory project-local shared infrastructure",
        "",
        "These requests are allowlisted project-local Lean modules, not external "
        "Lake packages. Schedule them before their dependent problem files.",
        f"For a missing file, dispatch `{policy.scaffolder}` to create the shared "
        "module skeleton, then keep the module as a Current Objective tagged "
        "`[prover-mode: mathlib-build]`. Do not install or modify Lake dependencies.",
        "Module verification and consumer migration are separate hard gates.",
    ]
    for item in objectives:
        declarations = ", ".join(f"`{name}`" for name in item.declarations)
        dependents = ", ".join(f"`{name}`" for name in item.dependents)
        state = "missing; scaffold first" if not (project_path / item.module_path).is_file() else "exists; build axiom-clean"
        lines.extend([
            "",
            f"- **`{item.module_path}`** ({state}) "
            "[prover-mode: mathlib-build]",
            f"  - Required declarations: {declarations or '(derive from blocker evidence)'}",
            f"  - Blocked dependents: {dependents or '(none recorded)'}",
            f"  - Reason: {item.reason or '(not supplied)'}",
        ])
    if migrations:
        lines.extend([
            "",
            "### Mandatory consumer import migration",
            "",
            f"Dispatch `{policy.migration_refactor}` once per consumer below, "
            "with write scope restricted to that exact consumer file. Add the "
            "canonical imports and replace duplicate target-local definitions "
            "with the verified shared API. Do not edit the shared modules and do "
            "not install Lake packages.",
        ])
        for item in migrations:
            imports = ", ".join(
                f"`import {_module_import_name(module)}`"
                for module in item.modules
            )
            lines.append(f"- **`{item.target_path}`** — {imports}")
        lines.extend([
            "",
            "After the refactor subagents finish, write this exact Current "
            "Objectives marker so plan validation proceeds to finalize without "
            "dispatching a prover before build verification:",
            "`(no prover dispatch this iter — shared consumer imports migrated; "
            "await full lake build verification)`",
        ])
    return "\n".join(lines).rstrip() + "\n"


def _code_without_comments_and_strings(text: str) -> str:
    """Small lexer sufficient for placeholder checks in queue reconciliation."""
    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    while i < len(text):
        ch = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ""
        if block_depth:
            if ch == "/" and nxt == "-":
                block_depth += 1
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                i += 2
            else:
                i += 1
            continue
        if in_string:
            if ch == "\\" and i + 1 < len(text):
                i += 2
            elif ch == '"':
                in_string = False
                i += 1
            else:
                i += 1
            continue
        if ch == '"':
            in_string = True
            i += 1
        elif ch == "-" and nxt == "-":
            newline = text.find("\n", i + 2)
            i = len(text) if newline < 0 else newline
        elif ch == "/" and nxt == "-":
            block_depth = 1
            i += 2
        else:
            out.append(ch)
            i += 1
    return "".join(out)


def _module_ready(path: Path) -> bool:
    try:
        text = path.read_text(encoding="utf-8", errors="ignore")
    except OSError:
        return False
    return not _PLACEHOLDER_RE.search(_code_without_comments_and_strings(text))


_DECLARATION_RE = re.compile(
    r"(?m)^\s*((?:(?:private|protected|noncomputable)\s+)*)"
    r"(?:@\[[^\]]+\]\s*)*"
    r"(?:def|abbrev|theorem|lemma|structure|class|inductive|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)


def _module_declares(path: Path, declarations: Iterable[str]) -> bool:
    try:
        code = _code_without_comments_and_strings(
            path.read_text(encoding="utf-8", errors="ignore")
        )
    except OSError:
        return False
    present = {
        match.group(2).split(".")[-1]
        for match in _DECLARATION_RE.finditer(code)
        if "private" not in match.group(1).split()
    }
    required = {
        str(name).strip().split(".")[-1]
        for name in declarations if str(name).strip()
    }
    return bool(required) and required <= present


def _module_exports_declarations(
    project_path: Path,
    module: str,
    path: Path,
    declarations: Iterable[str],
) -> bool:
    """Check requested names in Lean, preserving their full namespaces.

    The lexical fallback exists only for pre-Lake scaffolds and lightweight
    tests. A real Lake project must accept every exact ``#check`` after the
    canonical module import; comparing basename strings is not sufficient.
    """
    requested = tuple(
        dict.fromkeys(str(name).strip() for name in declarations if str(name).strip())
    )
    if (
        not requested
        or any(not _LEAN_DECLARATION_NAME_RE.fullmatch(name) for name in requested)
    ):
        return False
    if not (
        (project_path / "lakefile.toml").is_file()
        or (project_path / "lakefile.lean").is_file()
    ):
        return _module_declares(path, requested)
    probe_text = "\n".join([
        f"import {_module_import_name(module)}",
        *(f"#check {name}" for name in requested),
        "",
    ])
    try:
        with tempfile.TemporaryDirectory(prefix="archon-shared-api-") as temp_dir:
            probe = Path(temp_dir) / "SharedApiProbe.lean"
            probe.write_text(probe_text, encoding="utf-8")
            result = subprocess.run(
                ["lake", "env", "lean", str(probe)],
                cwd=project_path,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                timeout=120,
                check=False,
            )
    except (OSError, subprocess.SubprocessError):
        return False
    return result.returncode == 0


def _module_has_current_olean(project_path: Path, module: str, source: Path) -> bool:
    """Require durable evidence that Lake included the module in its build."""
    rel = Path(module).with_suffix(".olean")
    candidates = (
        project_path / ".lake" / "build" / "lib" / "lean" / rel,
        project_path / ".lake" / "build" / "lib" / rel,
        project_path / "build" / "lib" / "lean" / rel,
    )
    source_mtime = source.stat().st_mtime
    return any(
        candidate.is_file() and candidate.stat().st_mtime >= source_mtime
        for candidate in candidates
    )


def _module_import_name(module: str) -> str:
    return ".".join(Path(module).with_suffix("").parts)


_IMPORT_RE = re.compile(r"(?m)^\s*import\s+([A-Za-z_][A-Za-z0-9_.]*)\b")


def _consumer_imports_module(path: Path, module: str) -> bool:
    try:
        code = _code_without_comments_and_strings(
            path.read_text(encoding="utf-8", errors="ignore")
        )
    except OSError:
        return False
    return _module_import_name(module) in set(_IMPORT_RE.findall(code))


def _consumer_compiles(project_path: Path, path: Path) -> bool:
    """Run the exact consumer file gate; default Lake targets may omit it."""
    if not (
        (project_path / "lakefile.toml").is_file()
        or (project_path / "lakefile.lean").is_file()
    ):
        # Lightweight state-machine tests may not materialize a Lake project.
        # Production reconciliation also requires real Finalize evidence.
        return path.is_file()
    try:
        rel = path.resolve().relative_to(project_path.resolve()).as_posix()
        result = subprocess.run(
            ["lake", "env", "lean", rel],
            cwd=project_path,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            timeout=300,
            check=False,
        )
    except (OSError, ValueError, subprocess.SubprocessError):
        return False
    return result.returncode == 0


def _sha256(path: Path) -> str:
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError:
        return ""


def _latest_successful_build(
    state_dir: Path, *, not_before_iter: int, not_before_epoch: float = 0.0,
) -> tuple[int, float] | None:
    log_root = state_dir / "logs"
    if not log_root.is_dir():
        return None
    successes: list[tuple[int, float]] = []
    for child in log_root.glob("iter-*/meta.json"):
        suffix = child.parent.name.removeprefix("iter-")
        if not suffix.isdigit() or int(suffix) < not_before_iter:
            continue
        try:
            data = json.loads(child.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        finalize = data.get("finalize") if isinstance(data, dict) else None
        lake = finalize.get("lake") if isinstance(finalize, dict) else None
        if isinstance(lake, dict) and lake.get("ok") is True:
            try:
                completed_epoch = float(lake.get("completedAtEpoch"))
            except (TypeError, ValueError):
                # Old meta files are usable only by legacy queue records that
                # predate wall-clock request epochs. The mtime of meta.json is
                # not trustworthy under --resume because unrelated writes
                # refresh it while retaining a stale finalize.lake.ok value.
                if not_before_epoch > 0:
                    continue
                completed_epoch = child.stat().st_mtime
            if completed_epoch >= not_before_epoch:
                successes.append((int(suffix), completed_epoch))
    return max(successes, default=None)


def _latest_clean_axiom_sweep(
    state_dir: Path,
    *,
    module: str,
    not_before_iter: int,
) -> tuple[int, float] | None:
    """Return latest target-specific axiom-clean sweep evidence."""
    log_root = state_dir / "logs"
    if not log_root.is_dir():
        return None
    clean: list[tuple[int, float]] = []
    for report_path in log_root.glob("iter-*/axiom-sweep.json"):
        suffix = report_path.parent.name.removeprefix("iter-")
        if not suffix.isdigit() or int(suffix) < not_before_iter:
            continue
        try:
            report = json.loads(report_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if not isinstance(report, dict):
            continue
        targets = report.get("targetFiles", [])
        failed = report.get("failedFiles", [])
        if not isinstance(targets, list) or module not in {
            str(item).lstrip("./") for item in targets
        }:
            continue
        if not isinstance(failed, list) or module in {
            str(item).lstrip("./") for item in failed
        }:
            continue
        bad = False
        for key in ("sorryLaunderings", "otherNonStandardAxioms"):
            findings = report.get(key, [])
            if not isinstance(findings, list):
                bad = True
                break
            if any(
                isinstance(item, dict)
                and str(item.get("file") or "").lstrip("./") == module
                for item in findings
            ):
                bad = True
                break
        if not bad:
            clean.append((int(suffix), report_path.stat().st_mtime))
    return max(clean, default=None)


def reconcile_shared_infrastructure(
    *, state_dir: Path, project_path: Path,
) -> SharedInfrastructureReconcileResult:
    """Advance build and consumer-migration gates from durable evidence."""
    policy = load_shared_infrastructure_policy(project_path)
    if not policy.enabled:
        return SharedInfrastructureReconcileResult((), (), ())
    state = load_shared_infrastructure_state(state_dir)
    modules = state.get("modules", {})
    verified_modules: list[str] = []
    resolved_modules: list[str] = []
    reopened: set[str] = set()
    changed = False

    # A verified module is immutable until all consumers migrate. If it was
    # edited, invalidate its evidence and send it back through mathlib-build.
    for raw_module, raw in sorted(modules.items()):
        record = raw if isinstance(raw, dict) else {}
        if record.get("status") not in {
            "verified_awaiting_migration", "resolved",
        }:
            continue
        module = _safe_module_path(project_path, raw_module, policy)
        if module is None:
            continue
        path = project_path / module
        if (
            not path.is_file()
            or _sha256(path) != str(record.get("verified_sha256") or "")
            or not _module_ready(path)
        ):
            record.update({
                "status": "pending",
                "verified_iter": None,
                "resolved_iter": None,
                "axiom_sweep_iter": None,
                "verified_sha256": None,
                "consumer_migrations": {},
                "updated_at": _utcnow(),
            })
            modules[raw_module] = record
            changed = True

    # Consumer proof files are mutable too. A resolved migration remains valid
    # across ordinary proof edits, but never after its canonical import is
    # removed. Invalid or legacy evidence returns that consumer to the
    # migration gate without needlessly rebuilding the shared module.
    for raw_module, raw in sorted(modules.items()):
        record = raw if isinstance(raw, dict) else {}
        if record.get("status") not in {
            "verified_awaiting_migration", "resolved",
        }:
            continue
        module = _safe_module_path(project_path, raw_module, policy)
        if module is None:
            continue
        dependents = {str(item) for item in record.get("dependents", [])}
        raw_migrations = record.get("consumer_migrations", {})
        migrations = (
            dict(raw_migrations) if isinstance(raw_migrations, dict) else {}
        )
        record_changed = not isinstance(raw_migrations, dict)
        for target in set(migrations) - dependents:
            migrations.pop(target, None)
            record_changed = True
        needs_migration = False
        for target in dependents:
            migration = migrations.get(target)
            rel = _safe_consumer_path(project_path, target)
            consumer = project_path / rel if rel is not None else None
            valid = (
                isinstance(migration, dict)
                and migration.get("status") == "resolved"
                and consumer is not None
                and consumer.is_file()
                and _consumer_imports_module(consumer, module)
            )
            if not valid:
                migrations.pop(target, None)
                needs_migration = True
                record_changed = True
        if needs_migration and record.get("status") == "resolved":
            record["status"] = "verified_awaiting_migration"
            record["resolved_iter"] = None
            record_changed = True
        if record_changed:
            record["consumer_migrations"] = migrations
            record["updated_at"] = _utcnow()
            modules[raw_module] = record
            changed = True

    # Gate 1: module exists, exports every requested declaration, is in Lake's
    # build graph, has a target-clean axiom sweep, and passed full lake build.
    for raw_module, raw in sorted(modules.items()):
        record = raw if isinstance(raw, dict) else {}
        if record.get("status") != "pending":
            continue
        module = _safe_module_path(project_path, raw_module, policy)
        if module is None:
            continue
        path = project_path / module
        declarations = record.get("declarations", [])
        if (
            not path.is_file()
            or not _module_ready(path)
            or not _module_exports_declarations(
                project_path, module, path, declarations,
            )
            or not _module_has_current_olean(project_path, module, path)
        ):
            continue
        requested_iter = int(record.get("requested_iter") or 0)
        try:
            requested_epoch = float(record.get("requested_epoch") or 0.0)
        except (TypeError, ValueError):
            requested_epoch = 0.0
        axiom_sweep = _latest_clean_axiom_sweep(
            state_dir,
            module=module,
            not_before_iter=requested_iter,
        )
        if axiom_sweep is None:
            continue
        sweep_iter, sweep_mtime = axiom_sweep
        if sweep_mtime < requested_epoch:
            continue
        build = _latest_successful_build(
            state_dir,
            not_before_iter=max(requested_iter, sweep_iter),
            not_before_epoch=max(requested_epoch, sweep_mtime),
        )
        if build is None:
            continue
        build_iter, build_mtime = build
        # A user edit after the successful build invalidates the evidence.
        if path.stat().st_mtime > min(sweep_mtime, build_mtime):
            continue
        digest = _sha256(path)
        record.update({
            "status": "verified_awaiting_migration",
            "verified_iter": build_iter,
            "resolved_iter": None,
            "axiom_sweep_iter": sweep_iter,
            "verified_sha256": digest,
            "consumer_migrations": {},
            "updated_at": _utcnow(),
        })
        modules[module] = record
        verified_modules.append(module)
        changed = True

    # Gate 2: all of a consumer's modules are verified and unchanged, its file
    # imports each canonical module, and a later full build succeeds. Only then
    # can the original problem proof leave infrastructure quarantine.
    by_target: dict[str, list[tuple[str, dict[str, Any]]]] = {}
    for raw_module, raw in modules.items():
        record = raw if isinstance(raw, dict) else {}
        module = _safe_module_path(project_path, raw_module, policy)
        if module is None:
            continue
        for target in record.get("dependents", []):
            rel = _safe_consumer_path(project_path, target)
            if rel:
                by_target.setdefault(rel, []).append((module, record))

    for target, prerequisites in sorted(by_target.items()):
        if not prerequisites or any(
            record.get("status") not in {
                "verified_awaiting_migration", "resolved",
            }
            for _, record in prerequisites
        ):
            continue
        needs_migration = any(
            not isinstance(record.get("consumer_migrations"), dict)
            or not isinstance(record["consumer_migrations"].get(target), dict)
            or record["consumer_migrations"][target].get("status") != "resolved"
            for _, record in prerequisites
        )
        if not needs_migration:
            continue
        consumer = project_path / target
        if not consumer.is_file():
            continue
        current_modules = True
        for module, record in prerequisites:
            source = project_path / module
            if (
                _sha256(source) != str(record.get("verified_sha256") or "")
                or not _consumer_imports_module(consumer, module)
            ):
                current_modules = False
                break
        if not current_modules:
            continue
        verified_iter = max(
            int(record.get("verified_iter") or 0)
            for _, record in prerequisites
        )
        consumer_request_iter = 0
        consumer_request_epoch = 0.0
        for _, record in prerequisites:
            request_iters = record.get("consumer_request_iters", {})
            raw_iter = (
                request_iters.get(target)
                if isinstance(request_iters, dict)
                else 0
            )
            try:
                consumer_request_iter = max(
                    consumer_request_iter, int(raw_iter or 0),
                )
            except (TypeError, ValueError):
                continue
            request_epochs = record.get("consumer_request_epochs", {})
            raw_epoch = (
                request_epochs.get(target)
                if isinstance(request_epochs, dict)
                else 0.0
            )
            try:
                consumer_request_epoch = max(
                    consumer_request_epoch, float(raw_epoch or 0.0),
                )
            except (TypeError, ValueError):
                continue
        build = _latest_successful_build(
            state_dir,
            not_before_iter=max(verified_iter, consumer_request_iter),
            not_before_epoch=consumer_request_epoch,
        )
        if build is None:
            continue
        build_iter, build_mtime = build
        source_mtimes = [
            (project_path / module).stat().st_mtime
            for module, _ in prerequisites
        ]
        if build_mtime < max([consumer.stat().st_mtime, *source_mtimes]):
            continue
        if not _consumer_compiles(project_path, consumer):
            continue
        for module, record in prerequisites:
            migrations = record.get("consumer_migrations", {})
            migrations = dict(migrations) if isinstance(migrations, dict) else {}
            migrations[target] = {
                "status": "resolved",
                "build_iter": build_iter,
                "consumer_sha256": _sha256(consumer),
                "updated_at": _utcnow(),
            }
            record["consumer_migrations"] = migrations
            modules[module] = record
        reopened.add(target)
        changed = True

    for module, raw in modules.items():
        record = raw if isinstance(raw, dict) else {}
        if record.get("status") != "verified_awaiting_migration":
            continue
        dependents = {str(x) for x in record.get("dependents", [])}
        migrations = record.get("consumer_migrations", {})
        if dependents and isinstance(migrations, dict) and all(
            isinstance(migrations.get(target), dict)
            and migrations[target].get("status") == "resolved"
            for target in dependents
        ):
            record["status"] = "resolved"
            record["resolved_iter"] = max(
                int(migrations[target].get("build_iter") or 0)
                for target in dependents
            )
            record["updated_at"] = _utcnow()
            modules[module] = record
            resolved_modules.append(module)
            changed = True

    # The state write and proof-gate write are intentionally separate atomic
    # operations. Re-emit the hand-off on every reconciliation while a target
    # has a fully resolved migration, so a process crash between those writes
    # cannot strand the dependent forever.
    for target, prerequisites in by_target.items():
        if prerequisites and all(
            record.get("status") == "resolved"
            and isinstance(record.get("consumer_migrations"), dict)
            and isinstance(record["consumer_migrations"].get(target), dict)
            and record["consumer_migrations"][target].get("status") == "resolved"
            for _, record in prerequisites
        ):
            reopened.add(target)
    if changed:
        state.update({
            "version": STATE_VERSION,
            "modules": modules,
            "updated_at": _utcnow(),
        })
        _write_state(state_dir, state)
    return SharedInfrastructureReconcileResult(
        verified_modules=tuple(verified_modules),
        resolved_modules=tuple(resolved_modules),
        reopened_targets=tuple(sorted(reopened)),
    )


def reopen_resolved_shared_dependents(
    *,
    state_dir: Path,
    result: SharedInfrastructureReconcileResult,
    iter_num: int,
) -> tuple[str, ...]:
    """Move resolved dependents from infrastructure-blocked back to retry.

    This narrow state transition completes the queue lifecycle while leaving
    legacy/external ``blocked_infrastructure`` records untouched.
    """
    if not result.reopened_targets:
        return ()
    gate_path = state_dir / "proof-review-gate.json"
    try:
        gate = json.loads(gate_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return ()
    if not isinstance(gate, dict) or not isinstance(gate.get("targets"), dict):
        return ()
    targets = gate["targets"]
    queue_modules = load_shared_infrastructure_state(state_dir).get("modules", {})
    reopened: list[str] = []
    for rel in result.reopened_targets:
        record = targets.get(rel)
        if not isinstance(record, dict):
            continue
        if record.get("status") != "blocked_infrastructure":
            continue
        target_modules = sorted(
            str(module)
            for module, module_record in queue_modules.items()
            if isinstance(module_record, dict)
            and rel in {str(x) for x in module_record.get("dependents", [])}
            and isinstance(module_record.get("consumer_migrations"), dict)
            and isinstance(module_record["consumer_migrations"].get(rel), dict)
            and module_record["consumer_migrations"][rel].get("status") == "resolved"
        )
        request = record.get("infrastructure_request")
        if (
            not isinstance(request, dict)
            or request.get("kind") != PROJECT_LOCAL_KIND
            or str(request.get("module") or "") not in target_modules
        ):
            # A later external/manual blocker must not be cleared merely
            # because an older local module request eventually finished.
            continue
        history = record.get("history")
        history = list(history) if isinstance(history, list) else []
        history.append({
            "iter": int(iter_num),
            "event": "shared_infrastructure_resolved",
            "modules": target_modules,
            "reviewed_at": _utcnow(),
        })
        targets[rel] = {
            **record,
            "status": "retry",
            "reason": (
                "project-local shared infrastructure, consumer migration, "
                "axiom sweep, and full lake build passed; retry the proof"
            ),
            "evidence": ", ".join(target_modules),
            "redraft_kind": "not_applicable",
            "infrastructure_request": None,
            "infrastructure_request_error": "",
            "infrastructure_resolved_iter": int(iter_num),
            "history": history[-50:],
            "updated_at": _utcnow(),
        }
        reopened.append(rel)
    if not reopened:
        return ()
    gate["targets"] = targets
    gate["updated_at"] = _utcnow()
    tmp = gate_path.with_suffix(gate_path.suffix + ".tmp")
    tmp.write_text(
        json.dumps(gate, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    tmp.replace(gate_path)

    # Keep the human-readable gate report and the next-plan routing note in
    # sync without making the queue depend on private state representation at
    # import time (which would introduce a circular import).
    from .proof_review_gate import _write_report, _write_routing_notes

    _write_report(state_dir, gate)
    _write_routing_notes(state_dir, gate)
    return tuple(sorted(reopened))
