#!/usr/bin/env python3
"""Thin full32 answer-blind entry point for Archon's native workflow.

One fresh workspace is prepared from the sanitized seed.  The only model-facing
command is ``archon loop``; Archon schedules all 32 targets (four at a time) and
owns formalization, both Review gates, proof construction, and final Lake build.
Without ``--run`` the script prepares the workspace but does not start the loop.
"""

from __future__ import annotations

import argparse
import collections
import dataclasses
import datetime as dt
import hashlib
import importlib.util
import json
import os
import shlex
import shutil
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence


SCHEMA_VERSION = 1
PIPELINE = "archon-native-answer-blind-full32"
EXPECTED_ITEMS = 32
MAX_PARALLEL = 4
BUNDLE_REL = Path("icho_2026_source/questions_only.jsonl")
SOURCE_REPORT_MARKER = "% archon:source-report "

NATIVE_AGENTS = """# Answer-Blind Native Archon Instructions

Use only the problem statement, problem images, local Lean libraries, and
artifacts created in this workspace. Never seek or read an official answer,
solution, rubric, marking scheme, grader output, prior run, or another solver's
workspace. Web/search/browser tools are disabled. If answer-bearing material is
visible, stop and report it without using it.

Do not edit the question bundle, source reports, problem PDF/images,
`isolation_manifest.json`, `.archon/config.json`, or this file. During a
target-scoped prover task, edit only the assigned Lean file and its task-result
report. Preserve the quantities, units, hypotheses, requested outputs, and
chemical alternatives stated in the problem; do not replace the goal with a
tautology or unsupported premise.

Archon's native acceptance path is: formalization, formalization Review, proof,
proof Review, and final Lake build. There is no separate seal/freeze protocol in
this run.
"""

NATIVE_PROTOCOL = """# Answer-Blind Native Archon Protocol

This run provides the model only the problem-only bundle, its referenced problem
assets, and local Lean libraries. `official_answer_seen = false`. It does not
claim operating-system network isolation; the harness disables web, search,
browser, plugins, and apps, and the solver must not seek answer-bearing material.

Archon performs the normal chemistry workflow in one workspace: create faithful
Lean statements, run formalization Review, fill proofs, run proof Review, then
run the final Lake build. No external answer-blind controller, seal, or freeze
step is part of this simplified run.
"""

NATIVE_FORMALIZE_MODE = """---
name: physics-formalize
description: "Formalize a problem-only chemistry chapter into compiling Lean statements."
compatible_stages:
  - autoformalize
read_blueprint: true
---

## Goal

Read the assigned problem-only blueprint chapter and every problem image listed
there. Translate the chemistry faithfully into definitions and theorem
statements with `by sorry` bodies. This stage writes the statement; it does not
solve the proof.

- Preserve every requested output, given quantity, unit, sign, bound, branch,
  conservation law, stoichiometric coefficient, and domain condition.
- Derive numerical values from the supplied data; do not invent empirical facts
  or encode a desired result as an assumption.
- Do not weaken the requested result to `True`, a reflexive equality, or an
  unrelated existence claim.
- Use local Mathlib/Physlib/CRNT/project declarations whose signatures you have
  checked. Use `lake env lean` to compile the assigned file.
- Edit only the assigned Lean file and its `.archon/task_results` report. Do not
  create a candidate JSON, edit the problem sources, or edit another target.
- If official answers, solutions, rubrics, grader data, or prior-run answers are
  visible, stop and report an answer-blind violation without reading them.
"""

NATIVE_PROOF_MODE = """---
name: physics
description: "Prove the reviewed chemistry statements without weakening them."
compatible_stages:
  - prover
read_blueprint: true
---

## Goal

Replace `sorry` in the assigned chemistry Lean file with sound proofs. Keep the
reviewed declaration signatures and chemical meaning fixed. Use the encoded
source data and governing relations, search the local Lean libraries, and run
`lake env lean` until the file compiles. Edit only the assigned Lean file and
its task-result report. If the statement is genuinely insufficient, report a
precise redraft need; do not weaken it. Never seek or use an official answer,
solution, rubric, grader output, prior run, or another solver's work.
"""

NATIVE_PLAN_GUIDE = """# Native answer-blind planning

Plan only from the problem-only blueprint, current Lean files, deterministic
Lean diagnostics, and the preceding Archon Review. Keep the current target set
small enough for the configured four prover lanes. Never seek an official
answer, solution, rubric, grader output, prior run, or another solver's work.
"""

NATIVE_REVIEW_GUIDE = """# Native answer-blind Review

Review the current targets against their problem-only blueprint chapters and
problem images. During autoformalize, decide whether each Lean statement is a
faithful and derivable encoding and emit the structured formalization Review
certificate requested by the invocation. During prover, audit the exact Lean
proof and emit the requested proof Review route. Write exactly one JSONL row for
every listed objective: no omissions, duplicates, or extra targets. Also write
the requested summary, recommendations, and PROJECT_STATUS files. Do not modify
Lean files and never seek an official answer, solution, rubric, grader output,
prior run, or another solver's work.
"""


class CampaignError(RuntimeError):
    pass


def _load_script(name: str):
    path = Path(__file__).resolve().with_name(name)
    spec = importlib.util.spec_from_file_location(f"_archon_native_{path.stem}", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


_SEED = _load_script("build_answer_blind_solver_seed.py")
_CONFIGURE = _load_script("configure_answer_blind_workspace.py")


def _utcnow() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z")


def _json_bytes(value: Any) -> bytes:
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n").encode()


@dataclasses.dataclass(frozen=True)
class Config:
    campaign_root: Path
    seed_workspace: Path | None = None
    lake_packages: Path | None = None
    archon_bin: str = "archon"
    max_iterations: int = 100

    @property
    def workspace(self) -> Path:
        return self.campaign_root / "workspace"

    @property
    def log_path(self) -> Path:
        return self.campaign_root / "run.log"

    @property
    def index_path(self) -> Path:
        return self.campaign_root / "campaign.json"

    @property
    def private_lake_packages(self) -> Path:
        return self.campaign_root / "lake-packages"


def _target_ids(root: Path) -> tuple[str, ...]:
    try:
        manifest = json.loads((root / "isolation_manifest.json").read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise CampaignError("invalid isolation_manifest.json") from exc
    ids = manifest.get("target_ids") if isinstance(manifest, dict) else None
    if (
        not isinstance(ids, list)
        or len(ids) != EXPECTED_ITEMS
        or len(set(map(str, ids))) != EXPECTED_ITEMS
    ):
        raise CampaignError("seed must declare exactly 32 unique target_ids")
    return tuple(map(str, ids))


def _targets(ids: Sequence[str]) -> tuple[str, ...]:
    return tuple(f"IChO2026Problems/problem_{item}.lean" for item in ids)


def _fresh_config(config: Config) -> tuple[Config, tuple[str, ...]]:
    if config.seed_workspace is None or config.lake_packages is None:
        raise CampaignError("fresh preparation requires --seed-workspace and --lake-packages")
    root, seed, packages = map(
        Path.resolve, (config.campaign_root, config.seed_workspace, config.lake_packages)
    )
    if not packages.is_dir():
        raise CampaignError(f"Lake packages directory is missing: {packages}")
    if root == seed or root.is_relative_to(seed) or seed.is_relative_to(root):
        raise CampaignError("campaign root and seed must be disjoint")
    if root.exists() and (not root.is_dir() or any(root.iterdir())):
        raise CampaignError(f"campaign root must be absent or empty: {root}")
    if config.max_iterations < 1:
        raise CampaignError("max_iterations must be positive")
    try:
        _SEED.validate_seed(seed)
    except Exception as exc:
        raise CampaignError(f"seed validation failed: {exc}") from exc
    resolved = dataclasses.replace(
        config, campaign_root=root, seed_workspace=seed, lake_packages=packages
    )
    return resolved, _target_ids(seed)


def _resume_config(config: Config) -> tuple[Config, tuple[str, ...]]:
    config = dataclasses.replace(config, campaign_root=config.campaign_root.resolve())
    if not config.workspace.is_dir() or not config.index_path.is_file():
        raise CampaignError(f"prepared workspace is missing: {config.workspace}")
    if config.max_iterations < 1:
        raise CampaignError("max_iterations must be positive")
    _check_native_config(config.workspace)
    return config, _target_ids(config.workspace)


def _patch_native_config(workspace: Path, *, max_iterations: int) -> None:
    path = workspace / ".archon/config.json"
    try:
        value = json.loads(path.read_text())
        loop = value["loop"]
        harness = value["harnesses"]["answer-blind-gpt"]
    except (OSError, json.JSONDecodeError, KeyError, TypeError) as exc:
        raise CampaignError("configured workspace lacks the GPT Archon harness") from exc
    for key in ("base_url_env", "key_env", "wire_api"):
        harness.pop(key, None)
    extra_args = list(harness.get("extra_args") or [])
    for setting in (
        "features.code_mode=false",
        "features.code_mode.enabled=false",
        "features.shell_snapshot=false",
        "features.shell_tool=true",
        "features.multi_agent=false",
        "features.multi_agent_v2=false",
    ):
        extra_args.extend(("-c", setting))
    harness.update({
        "runner": "codex",
        "model": "gpt-5.6-sol",
        "effort": "max",
        # This host disables unprivileged user namespaces, so Codex's
        # workspace-write sandbox cannot provide its execution host.  The
        # native loop instead runs as a dedicated non-root UID, while answer
        # and controller paths stay root-only; _run_loop enforces that boundary.
        "sandbox": "danger-full-access",
        "ignore_user_config": True,
        "ephemeral": True,
        # Keep the native path deliberately small.  Archon's deterministic
        # review preflight and finalizer invoke Lake directly, while Codex can
        # use the workspace shell for intermediate Lean checks.  No separate
        # answer-blind MCP jail is needed in this input-level isolation mode.
        "mcp": [],
        "extra_args": extra_args,
    })
    harness.pop("lean_lsp_mcp_bin", None)
    loop.update({
        "harness": "answer-blind-gpt",
        "model": "gpt-5.6-sol",
        "max_iterations": max_iterations,
        "parallel": True,
        "max_parallel": MAX_PARALLEL,
        "max_objectives": EXPECTED_ITEMS,
        "formalization_review_gate": True,
        "proof_review_gate": True,
        "review_preflight_jobs": MAX_PARALLEL,
        "parallel_target_review_jobs": MAX_PARALLEL,
        "parallel_formalization_review_jobs": MAX_PARALLEL,
        # Keep the semantic gates, but use Archon's ordinary Review agent.
        # The strict target-scoped reviewers implement the removed
        # candidate/seal protocol and are intentionally not part of this
        # problem-input-level workflow. Deterministic Lean preflight remains
        # four-way through review_preflight_jobs.
        "parallel_formalization_review": False,
        "parallel_target_review": False,
        "pipeline_target_review": False,
    })
    path.write_bytes(_json_bytes(value))


def _write_native_policy_files(workspace: Path) -> None:
    payloads = {
        workspace / ".archon/AGENTS.md": NATIVE_AGENTS,
        workspace / "ANSWER_BLIND_PROTOCOL.md": NATIVE_PROTOCOL,
        workspace / ".archon/prover-modes/physics-formalize.md": NATIVE_FORMALIZE_MODE,
        workspace / ".archon/prover-modes/chemistry-formalize.md": NATIVE_FORMALIZE_MODE,
        workspace / ".archon/prover-modes/physics.md": NATIVE_PROOF_MODE,
        workspace / ".archon/prover-modes/chemistry.md": NATIVE_PROOF_MODE,
        workspace / ".archon/prompts/plan.md": NATIVE_PLAN_GUIDE,
        workspace / ".archon/prompts/review.md": NATIVE_REVIEW_GUIDE,
        workspace / ".mcp.json": '{"mcpServers": {}}\n',
    }
    for path, text in payloads.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text.rstrip() + "\n", encoding="utf-8")


def _activate_native_review_profile(workspace: Path) -> None:
    path = workspace / ".archon/config.json"
    try:
        value = json.loads(path.read_text())
        domain = value["loop"]["domain_profile"]
    except (OSError, json.JSONDecodeError, KeyError, TypeError) as exc:
        raise CampaignError("cannot activate the native review profile") from exc
    if not isinstance(domain, dict) or domain.get("name") != "chemistry":
        raise CampaignError("prepared workspace lost its chemistry profile")
    domain.update({"name": "chemistry-native", "display_name": "IChO chemistry"})
    path.write_bytes(_json_bytes(value))
    _write_native_policy_files(workspace)


def _detach_strict_source_contract(workspace: Path, ids: Sequence[str]) -> None:
    """Keep problem text while selecting Archon's ordinary native Review."""
    chapter_root = workspace / "blueprint/src/chapters"
    for target_id in ids:
        path = chapter_root / f"IChO2026Problems_problem_{target_id}.tex"
        try:
            lines = path.read_text(encoding="utf-8").splitlines(keepends=True)
        except OSError as exc:
            raise CampaignError(f"missing prepared blueprint chapter: {path}") from exc
        marker_indexes = [
            index for index, line in enumerate(lines)
            if line.lstrip().startswith(SOURCE_REPORT_MARKER)
        ]
        if len(marker_indexes) != 1:
            raise CampaignError(f"prepared chapter has an invalid source marker: {path}")
        del lines[marker_indexes[0]]
        physics_indexes = [
            index for index, line in enumerate(lines)
            if line.strip() == "% archon:physics"
        ]
        if len(physics_indexes) != 1:
            raise CampaignError(f"prepared chapter has an invalid domain marker: {path}")
        del lines[physics_indexes[0]]
        chemistry_indexes = [
            index for index, line in enumerate(lines)
            if line.strip() == "% archon:chemistry"
        ]
        if len(chemistry_indexes) != 1:
            raise CampaignError(f"prepared chapter has an invalid chemistry marker: {path}")
        del lines[chemistry_indexes[0]]
        path.write_text("".join(lines), encoding="utf-8")


def _check_native_config(workspace: Path, *, preparation: bool = False) -> None:
    try:
        value = json.loads((workspace / ".archon/config.json").read_text())
        loop = value["loop"]
        harness = value["harnesses"]["answer-blind-gpt"]
    except (OSError, json.JSONDecodeError, KeyError, TypeError) as exc:
        raise CampaignError("prepared Archon config is invalid") from exc
    if (
        harness.get("runner") != "codex"
        or harness.get("sandbox") != "danger-full-access"
        or harness.get("mcp") != []
        or "lean_lsp_mcp_bin" in harness
        or any(key in harness for key in ("base_url_env", "key_env"))
        or "features.shell_tool=true" not in (harness.get("extra_args") or [])
        or "features.multi_agent=false" not in (harness.get("extra_args") or [])
        or (loop.get("domain_profile") or {}).get("name")
        != ("chemistry" if preparation else "chemistry-native")
        or loop.get("parallel_formalization_review") is not False
        or loop.get("parallel_target_review") is not False
        or loop.get("pipeline_target_review") is not False
    ):
        raise CampaignError("prepared harness is not native non-root Codex")
    for key in (
        "max_parallel",
        "review_preflight_jobs",
        "parallel_target_review_jobs",
        "parallel_formalization_review_jobs",
    ):
        if loop.get(key) != MAX_PARALLEL:
            raise CampaignError(f"prepared config has unexpected {key}")


def _write_all(workspace: Path, ids: Sequence[str]) -> None:
    path = workspace / "IChO2026Problems/All.lean"
    path.parent.mkdir(parents=True, exist_ok=True)
    imports = [target.removesuffix(".lean").replace("/", ".") for target in _targets(ids)]
    path.write_text("".join(f"import {item}\n" for item in imports))


def prepare_workspace(config: Config, ids: Sequence[str]) -> None:
    assert config.seed_workspace is not None and config.lake_packages is not None
    config.campaign_root.mkdir(parents=True, exist_ok=True)
    try:
        _SEED.copy_seed_to_workspace(config.seed_workspace, config.workspace, label="GPT")
        _CONFIGURE.configure_answer_blind_workspace(
            config.workspace,
            variant="gpt",
            max_objectives=EXPECTED_ITEMS,
            max_parallel=MAX_PARALLEL,
        )
    except Exception as exc:
        raise CampaignError(f"workspace preparation failed: {exc}") from exc
    _patch_native_config(config.workspace, max_iterations=config.max_iterations)
    _write_native_policy_files(config.workspace)
    _check_native_config(config.workspace, preparation=True)
    # Lake may refresh package-local Git metadata even for an otherwise clean
    # build.  Give this campaign its own copy so the native workflow cannot
    # mutate (or be invalidated by) a shared cache.
    try:
        shutil.copytree(
            config.lake_packages,
            config.private_lake_packages,
            symlinks=True,
        )
    except OSError as exc:
        raise CampaignError(f"cannot create private Lake package copy: {exc}") from exc
    link = config.workspace / ".lake/packages"
    link.parent.mkdir(parents=True, exist_ok=True)
    link.symlink_to(config.private_lake_packages, target_is_directory=True)
    _write_all(config.workspace, ids)


def physics_command(config: Config) -> list[str]:
    return [
        config.archon_bin, "physics-formalize", str(config.workspace),
        "--input-jsonl", str(config.workspace / BUNDLE_REL),
        "--image-root", str(config.workspace / "icho_2026_source/image"),
        "--out-dir", "IChO2026Problems",
        "--report-dir", "reports/icho_2026",
        "--work-dir", ".archon/physics-formalize/full32",
        "--evaluation-mode", "answer-blind",
        "--limit", "-1", "--update-progress",
    ]


def loop_command(config: Config, *, resume: bool) -> list[str]:
    command = [config.archon_bin, "loop", str(config.workspace)]
    command += ["--resume"] if resume else ["--from", "prover"]
    return command + [
        "--parallel", "--max-parallel", str(MAX_PARALLEL),
        "--max-objectives", str(EXPECTED_ITEMS),
        "--max-iterations", str(config.max_iterations),
        "--review", "--formalization-review-gate", "--proof-review-gate",
        "--no-dashboard", "--no-blueprint-web",
    ]


def _private_git_packages(config: Config) -> tuple[Path, ...]:
    root = config.private_lake_packages
    if root.is_symlink() or not root.is_dir():
        raise CampaignError(f"private Lake package root is not a real directory: {root}")
    try:
        entries = sorted(root.iterdir(), key=lambda path: path.name)
    except OSError as exc:
        raise CampaignError(f"cannot enumerate private Lake packages: {root}") from exc

    packages: list[Path] = []
    for entry in entries:
        if entry.is_symlink() or not entry.is_dir():
            raise CampaignError(f"invalid private Lake package entry: {entry}")
        git_dir = entry / ".git"
        if not git_dir.exists():
            continue
        if git_dir.is_symlink() or not git_dir.is_dir():
            raise CampaignError(f"invalid private Lake package Git directory: {git_dir}")
        packages.append(entry)
    if not packages:
        raise CampaignError(f"private Lake package root contains no Git packages: {root}")
    return tuple(packages)


def _run(command: Sequence[str], *, config: Config) -> tuple[int, float]:
    started = time.monotonic()
    # The campaign-local dependency checkout is controller-owned and read-only.
    # Git otherwise rejects it when Archon/Lean runs as the dedicated solver
    # user, which Lake misleadingly reports as a changed remote URL.  Limit the
    # ownership exceptions to this fresh workspace and the exact Git package
    # directories in this campaign. Git does not expand safe.directory globs.
    safe_directories = (config.workspace, *_private_git_packages(config))
    environment = os.environ.copy()
    environment["GIT_CONFIG_COUNT"] = str(len(safe_directories))
    for index, path in enumerate(safe_directories):
        environment[f"GIT_CONFIG_KEY_{index}"] = "safe.directory"
        environment[f"GIT_CONFIG_VALUE_{index}"] = str(path)
    with config.log_path.open("a", encoding="utf-8") as log:
        log.write(f"\n[{_utcnow()}] $ {shlex.join(command)}\n")
        log.flush()
        try:
            result = subprocess.run(
                list(command), cwd=config.workspace, stdout=log,
                stderr=subprocess.STDOUT, text=True, check=False,
                env=environment,
            )
            code = result.returncode
        except OSError as exc:
            log.write(f"failed to start: {exc}\n")
            code = 127
    return code, time.monotonic() - started


def validate_physics_metadata(workspace: Path, ids: Sequence[str]) -> None:
    try:
        latest = workspace / ".archon/physics-formalize/latest.json"
        value = json.loads(latest.read_text())
        entries = value["entries"]
        summary = value["work_dir"]
    except (OSError, json.JSONDecodeError, KeyError, TypeError) as exc:
        raise CampaignError("invalid physics-formalize metadata") from exc
    summary_path = Path(str(summary)) / "summary.jsonl"
    if not summary_path.is_absolute():
        summary_path = workspace / summary_path
    try:
        records = [json.loads(line) for line in summary_path.read_text().splitlines() if line.strip()]
    except (OSError, json.JSONDecodeError) as exc:
        raise CampaignError("invalid physics-formalize summary.jsonl") from exc
    if (
        value.get("command") != "physics-formalize"
        or value.get("evaluation_mode") != "answer_blind"
        or value.get("official_answer_seen") is not False
        or not isinstance(entries, list)
        or {str(row.get("id")) for row in entries if isinstance(row, dict)} != set(ids)
        or not isinstance(records, list)
        or {str(row.get("rel_lean")) for row in records if isinstance(row, dict)}
        != set(_targets(ids))
    ):
        raise CampaignError("physics-formalize did not prepare the exact blind full32 set")


def _gate_counts(path: Path, expected: set[str]) -> dict[str, int]:
    try:
        targets = json.loads(path.read_text()).get("targets", {})
    except (OSError, json.JSONDecodeError, AttributeError):
        targets = {}
    normalized = {
        str(key).replace("\\", "/").lstrip("./"): row
        for key, row in targets.items()
    } if isinstance(targets, dict) else {}
    statuses = [
        str(normalized[rel].get("status", "missing"))
        if isinstance(normalized.get(rel), dict) else "missing"
        for rel in expected
    ]
    return dict(sorted(collections.Counter(statuses).items()))


def _latest_build(workspace: Path) -> tuple[bool | None, int | None]:
    metas = []
    for path in (workspace / ".archon/logs").glob("iter-*/meta.json"):
        number = path.parent.name.removeprefix("iter-")
        if number.isdigit():
            metas.append((int(number), path))
    for _number, path in sorted(metas, reverse=True):
        try:
            value = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        if not value.get("completedAt"):
            continue
        lake = value.get("finalize", {}).get("lake", {})
        return lake.get("ok"), value.get("sorry_count")
    return None, None


def native_summary(workspace: Path, ids: Sequence[str]) -> dict[str, Any]:
    expected = set(_targets(ids))
    state = workspace / ".archon"
    formal = _gate_counts(state / "formalization-review-gate.json", expected)
    proof = _gate_counts(state / "proof-review-gate.json", expected)
    build_ok, sorry_count = _latest_build(workspace)
    complete = (
        formal.get("passed") == EXPECTED_ITEMS
        and proof.get("solved") == EXPECTED_ITEMS
        and build_ok is True and sorry_count == 0
    )
    return {
        "formalization_review": formal,
        "proof_review": proof,
        "lake_build_ok": build_ok,
        "sorry_count": sorry_count,
        "complete": complete,
    }


def _write_index(config: Config, value: Mapping[str, Any]) -> None:
    temporary = config.index_path.with_name(".campaign.json.tmp")
    temporary.write_bytes(_json_bytes(value))
    os.replace(temporary, config.index_path)


def _base_index(config: Config, ids: Sequence[str]) -> dict[str, Any]:
    bundle = config.workspace / BUNDLE_REL
    return {
        "schema_version": SCHEMA_VERSION,
        "pipeline": PIPELINE,
        "workspace": str(config.workspace),
        "row_count": len(ids),
        "bundle_sha256": hashlib.sha256(bundle.read_bytes()).hexdigest(),
        "max_parallel": MAX_PARALLEL,
        "status": "preparing",
        "updated_at": _utcnow(),
    }


def run_fresh(config: Config, *, start_loop: bool) -> dict[str, Any]:
    config, ids = _fresh_config(config)
    prepare_workspace(config, ids)
    index = _base_index(config, ids)
    _write_index(config, index)
    code, seconds = _run(physics_command(config), config=config)
    index.update(phase="physics-formalize", returncode=code, duration_seconds=round(seconds, 3))
    if code == 0:
        try:
            validate_physics_metadata(config.workspace, ids)
        except CampaignError as exc:
            code, index["error"] = 1, str(exc)
    if code != 0:
        index.update(status="failed", updated_at=_utcnow())
        _write_index(config, index)
        return index
    _detach_strict_source_contract(config.workspace, ids)
    _activate_native_review_profile(config.workspace)
    _check_native_config(config.workspace)
    index.update(status="prepared", native=native_summary(config.workspace, ids))
    _write_index(config, index)
    if not start_loop:
        return index
    return _run_loop(config, ids, index, resume=False)


def _run_loop(
    config: Config, ids: Sequence[str], index: dict[str, Any], *, resume: bool
) -> dict[str, Any]:
    if os.geteuid() == 0:
        raise CampaignError(
            "refusing to start the model loop as root; use the dedicated non-root solver UID"
        )
    index.update(status="running", phase="resume" if resume else "loop", updated_at=_utcnow())
    _write_index(config, index)
    code, seconds = _run(loop_command(config, resume=resume), config=config)
    native = native_summary(config.workspace, ids)
    index.update(
        returncode=code,
        duration_seconds=round(seconds, 3),
        native=native,
        status=(
            "succeeded" if code == 0 and native["complete"]
            else "failed" if code != 0
            else "incomplete"
        ),
        updated_at=_utcnow(),
    )
    _write_index(config, index)
    return index


def resume_campaign(config: Config) -> dict[str, Any]:
    config, ids = _resume_config(config)
    try:
        index = json.loads(config.index_path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise CampaignError("invalid campaign.json") from exc
    if index.get("pipeline") != PIPELINE:
        raise CampaignError("campaign.json belongs to a different pipeline")
    validate_physics_metadata(config.workspace, ids)
    # A prepare-only run has no Archon iteration to resume.  Treat the first
    # follow-up invocation as a normal start; after that, delegate recovery to
    # Archon's native --resume machinery.
    return _run_loop(
        config,
        ids,
        index,
        resume=index.get("status") != "prepared",
    )


def dry_run(config: Config, *, include_loop: bool) -> dict[str, Any]:
    config, ids = _fresh_config(config)
    return {
        "status": "dry-run",
        "row_count": len(ids),
        "workspace": str(config.workspace),
        "commands": [physics_command(config)]
        + ([loop_command(config, resume=False)] if include_loop else []),
    }


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--campaign-root", required=True, type=Path)
    parser.add_argument("--seed-workspace", type=Path)
    parser.add_argument("--lake-packages", type=Path)
    parser.add_argument("--archon-bin", default="archon")
    parser.add_argument("--max-iterations", type=int, default=100)
    actions = parser.add_mutually_exclusive_group()
    actions.add_argument("--run", action="store_true", help="prepare and start the loop")
    actions.add_argument("--resume", action="store_true", help="resume the existing loop")
    actions.add_argument("--dry-run", action="store_true", help="validate and print commands only")
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    config = Config(
        campaign_root=args.campaign_root,
        seed_workspace=args.seed_workspace,
        lake_packages=args.lake_packages,
        archon_bin=args.archon_bin,
        max_iterations=args.max_iterations,
    )
    try:
        if args.resume:
            result = resume_campaign(config)
        elif args.dry_run:
            result = dry_run(config, include_loop=True)
        else:
            result = run_fresh(config, start_loop=args.run)
    except CampaignError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(result, ensure_ascii=False, sort_keys=True))
    return 0 if result.get("status") in {"prepared", "succeeded", "dry-run"} else 1


if __name__ == "__main__":
    raise SystemExit(main())
