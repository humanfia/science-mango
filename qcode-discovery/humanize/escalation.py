"""Fail-closed planning and materialization for fresh campaign escalation.

This module deliberately does not start a process.  It turns sealed machine
evidence into a deterministic plan and, when an allow-listed template is both
launch- and proof-compatible, materializes one fresh pipeline JSON file.
"""

from __future__ import annotations

import copy
import hashlib
import json
import os
import re
import stat
import tempfile
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from types import SimpleNamespace
from typing import Any, Mapping

import yaml

from . import flow as flow_module


REGISTRY_SCHEMA_VERSION = 1
PLAN_SCHEMA_VERSION = 1
PROVENANCE_SCHEMA_VERSION = 1
MACHINE_EVIDENCE_SCHEMA_VERSION = 1
DEFAULT_REGISTRY_PATH = Path("configs/campaign_templates.v1.json")

_SHA256 = re.compile(r"[0-9a-f]{64}")
_SAFE_ID = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,127}")
_MACHINE_REGIMES = frozenset(
    {"expand_required", "representation_change_required"}
)
_TRANSITION_FOR_REGIME = {
    "expand_required": "expand_family",
    "representation_change_required": "representation_change",
}
_REVIEWER_ACTION_UNSET = object()


class EscalationError(ValueError):
    """Base class for fail-closed escalation errors."""


class RegistryError(EscalationError):
    """The registry or one of its hash-bound inputs is invalid."""


class ParentEvidenceError(EscalationError):
    """The parent machine evidence cannot authorize escalation."""


class MaterializationError(EscalationError):
    """A plan cannot be safely materialized."""


class ProofIncompatibleTemplateError(MaterializationError):
    """The selected representation lacks an end-to-end proof path."""


@dataclass(frozen=True)
class BoundFile:
    path: str
    sha256: str

    def serializable(self) -> dict[str, str]:
        return {"path": self.path, "sha256": self.sha256}


@dataclass(frozen=True)
class CampaignTemplate:
    template_id: str
    template_version: int
    description: str
    runner_kind: str
    transition_kind: str
    representation_id: str
    family_id: str
    checkpoint_compatibility_group: str
    proof_compatible: bool
    launch_compatible: bool
    auto_materialize: bool
    allowed_parent_representations: tuple[str, ...]
    allowed_machine_regimes: tuple[str, ...]
    base_pipeline: BoundFile | None
    evolution_config: BoundFile
    evolution_seed: BoundFile
    required_stage3_backend: str | None
    entry_sha256: str

    def serializable(self) -> dict[str, Any]:
        return {
            "template_id": self.template_id,
            "template_version": self.template_version,
            "description": self.description,
            "runner_kind": self.runner_kind,
            "transition_kind": self.transition_kind,
            "representation_id": self.representation_id,
            "family_id": self.family_id,
            "checkpoint_compatibility_group": (
                self.checkpoint_compatibility_group
            ),
            "proof_compatible": self.proof_compatible,
            "launch_compatible": self.launch_compatible,
            "auto_materialize": self.auto_materialize,
            "allowed_parent_representations": list(
                self.allowed_parent_representations
            ),
            "allowed_machine_regimes": list(self.allowed_machine_regimes),
            "base_pipeline": (
                None
                if self.base_pipeline is None
                else self.base_pipeline.serializable()
            ),
            "evolution_config": self.evolution_config.serializable(),
            "evolution_seed": self.evolution_seed.serializable(),
            "required_stage3_backend": self.required_stage3_backend,
        }


@dataclass(frozen=True)
class CampaignTemplateRegistry:
    repo_dir: Path
    registry_path: str
    registry_sha256: str
    templates: Mapping[str, CampaignTemplate]

    def template(self, template_id: str) -> CampaignTemplate:
        try:
            return self.templates[template_id]
        except KeyError as exc:
            raise RegistryError(f"unknown campaign template: {template_id}") from exc


@dataclass(frozen=True)
class EscalationPlan:
    repo_dir: Path
    registry_path: str
    registry_sha256: str
    template_id: str
    template_version: int
    template_entry_sha256: str
    parent_state_path: str
    parent_run_id: str
    machine_evidence_sha256: str
    parent_representation_id: str
    machine_regime: str
    transition_kind: str
    target_representation_id: str
    child_run_id: str
    idempotency_key: str
    proof_compatible: bool
    launch_compatible: bool
    materializable: bool
    block_reasons: tuple[str, ...]

    def serializable(self) -> dict[str, Any]:
        return {
            "schema_version": PLAN_SCHEMA_VERSION,
            "kind": "qcode-campaign-escalation-plan",
            "registry_path": self.registry_path,
            "registry_sha256": self.registry_sha256,
            "template_id": self.template_id,
            "template_version": self.template_version,
            "template_entry_sha256": self.template_entry_sha256,
            "parent_state_path": self.parent_state_path,
            "parent_run_id": self.parent_run_id,
            "machine_evidence_sha256": self.machine_evidence_sha256,
            "parent_representation_id": self.parent_representation_id,
            "machine_regime": self.machine_regime,
            "transition_kind": self.transition_kind,
            "target_representation_id": self.target_representation_id,
            "child_run_id": self.child_run_id,
            "idempotency_key": self.idempotency_key,
            "proof_compatible": self.proof_compatible,
            "launch_compatible": self.launch_compatible,
            "materializable": self.materializable,
            "block_reasons": list(self.block_reasons),
        }

    @property
    def plan_sha256(self) -> str:
        return _sha256(_canonical_bytes(self.serializable()))


@dataclass(frozen=True)
class MaterializedCampaign:
    path: Path
    child_run_id: str
    idempotency_key: str
    provenance_sha256: str
    pipeline_sha256: str
    created: bool


@dataclass(frozen=True)
class AutoEscalationPolicy:
    repo_dir: Path
    pipeline_config_path: str
    pipeline_config_sha256: str
    enabled: bool
    registry_path: str | None
    registry_sha256: str | None
    template_by_regime: Mapping[str, str]
    source_search_representation_id: str | None
    source_search_regime_policy_version: int
    source_max_rounds: int | None
    source_stop_on_representation_change: bool

    def serializable(self) -> dict[str, Any]:
        value = {
            "schema_version": 1,
            "kind": "qcode-auto-escalation-policy",
            "pipeline_config_path": self.pipeline_config_path,
            "pipeline_config_sha256": self.pipeline_config_sha256,
            "enabled": self.enabled,
            "registry_path": self.registry_path,
            "registry_sha256": self.registry_sha256,
            "template_by_regime": dict(self.template_by_regime),
            "source_search_representation_id": (
                self.source_search_representation_id
            ),
        }
        # Keep historical V1/V2 durable policy snapshots byte-compatible.
        # Budget-bound V3/V4 make these fields part of escalation authority.
        if (
            self.source_search_regime_policy_version
            in flow_module.SEARCH_REGIME_BUDGET_BOUND_POLICY_VERSIONS
        ):
            value.update({
                "source_search_regime_policy_version": (
                    self.source_search_regime_policy_version
                ),
                "source_max_rounds": self.source_max_rounds,
                "source_stop_on_representation_change": (
                    self.source_stop_on_representation_change
                ),
            })
        return value


@dataclass(frozen=True)
class EscalationReconciliation:
    disposition: str
    policy: AutoEscalationPolicy
    machine_regime: str | None
    template_id: str | None
    plan: EscalationPlan | None
    materialized: MaterializedCampaign | None
    block_reasons: tuple[str, ...]
    parent_state_sha256: str | None = None
    machine_evidence_sha256: str | None = None
    reviewer_action_advisory: Any = None
    reviewer_action_advisory_status: str = "not_present"
    reviewer_action_advisory_error: Mapping[str, str] | None = None

    def serializable(self) -> dict[str, Any]:
        return {
            "schema_version": 1,
            "kind": "qcode-campaign-escalation-reconciliation",
            "disposition": self.disposition,
            "policy": self.policy.serializable(),
            "machine_regime": self.machine_regime,
            "template_id": self.template_id,
            "plan": None if self.plan is None else self.plan.serializable(),
            "materialized": (
                None
                if self.materialized is None
                else {
                    "path": str(self.materialized.path),
                    "child_run_id": self.materialized.child_run_id,
                    "idempotency_key": self.materialized.idempotency_key,
                    "provenance_sha256": self.materialized.provenance_sha256,
                    "pipeline_sha256": self.materialized.pipeline_sha256,
                    "created": self.materialized.created,
                }
            ),
            "block_reasons": list(self.block_reasons),
            # These fields belong only to the parent operational sidecar.  They
            # are deliberately absent from plan identity and child config.
            "parent_state_sha256": self.parent_state_sha256,
            "machine_evidence_sha256": self.machine_evidence_sha256,
            "reviewer_action_advisory": _json_clone(
                self.reviewer_action_advisory
            ),
            "reviewer_action_advisory_status": (
                self.reviewer_action_advisory_status
            ),
            "reviewer_action_advisory_error": _json_clone(
                self.reviewer_action_advisory_error
            ),
        }


@dataclass(frozen=True)
class _ParentMachineEvidence:
    state_path: str
    state_sha256: str
    run_id: str
    status: str
    search_representation_id: str
    search_regime_policy_version: int
    max_rounds: int | None
    stop_on_representation_change: bool
    regime: dict[str, Any]
    rounds: tuple[dict[str, Any], ...]
    machine_evidence_sha256: str
    reviewer_action: Any
    reviewer_action_status: str
    reviewer_action_error: Mapping[str, str] | None


def _sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _canonical_bytes(value: Any) -> bytes:
    try:
        encoded = json.dumps(
            value,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
        )
    except (TypeError, ValueError) as exc:
        raise EscalationError(f"value is not canonical JSON: {exc}") from exc
    return encoded.encode("utf-8")


def _json_clone(value: Any) -> Any:
    return json.loads(_canonical_bytes(value))


def _object_without_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    value: dict[str, Any] = {}
    for key, item in pairs:
        if key in value:
            raise RegistryError(f"duplicate JSON key: {key}")
        value[key] = item
    return value


def _load_json(payload: bytes, *, label: str) -> Any:
    try:
        text = payload.decode("utf-8")
        return json.loads(text, object_pairs_hook=_object_without_duplicate_keys)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise RegistryError(f"invalid {label} JSON: {exc}") from exc


def _repo(repo_dir: Path) -> Path:
    try:
        repo = Path(repo_dir).resolve(strict=True)
    except OSError as exc:
        raise EscalationError(f"invalid repository path: {repo_dir}") from exc
    if not repo.is_dir() or not (repo / "humanize").is_dir():
        raise EscalationError("repo_dir must contain the humanize package")
    return repo


def _relative_path(raw: str | os.PathLike[str], *, label: str) -> Path:
    text = os.fspath(raw)
    if not isinstance(text, str) or not text or "\\" in text or "\x00" in text:
        raise EscalationError(f"unsafe {label} path: {text!r}")
    pure = PurePosixPath(text)
    if pure.is_absolute() or any(part in {"", ".", ".."} for part in text.split("/")):
        raise EscalationError(f"unsafe {label} path: {text!r}")
    return Path(*pure.parts)


def _path_relative_to_repo(
    repo: Path, raw: str | os.PathLike[str], *, label: str
) -> Path:
    path = Path(raw)
    if path.is_absolute():
        try:
            relative = path.relative_to(repo)
        except ValueError as exc:
            raise EscalationError(f"{label} escapes repository: {path}") from exc
        return _relative_path(relative.as_posix(), label=label)
    return _relative_path(os.fspath(raw), label=label)


def _reject_symlink_components(repo: Path, relative: Path, *, label: str) -> None:
    cursor = repo
    for part in relative.parts:
        cursor = cursor / part
        try:
            mode = os.lstat(cursor).st_mode
        except FileNotFoundError:
            continue
        if stat.S_ISLNK(mode):
            raise EscalationError(f"{label} contains symlink: {cursor}")


def _existing_bound_path(
    repo: Path, raw: str | os.PathLike[str], *, label: str
) -> tuple[Path, str]:
    relative = _path_relative_to_repo(repo, raw, label=label)
    _reject_symlink_components(repo, relative, label=label)
    path = repo / relative
    try:
        resolved = path.resolve(strict=True)
    except OSError as exc:
        raise EscalationError(f"missing {label}: {relative.as_posix()}") from exc
    if not resolved.is_relative_to(repo):
        raise EscalationError(f"{label} escapes repository: {relative.as_posix()}")
    mode = os.lstat(path).st_mode
    if not stat.S_ISREG(mode):
        raise EscalationError(f"{label} is not a regular file: {relative.as_posix()}")
    return path, relative.as_posix()


def _require_keys(
    value: Mapping[str, Any], expected: set[str], *, label: str
) -> None:
    missing = expected - set(value)
    unknown = set(value) - expected
    if missing or unknown:
        details = []
        if missing:
            details.append("missing=" + ",".join(sorted(missing)))
        if unknown:
            details.append("unknown=" + ",".join(sorted(unknown)))
        raise RegistryError(f"invalid {label} fields ({'; '.join(details)})")


def _safe_id(value: Any, *, label: str) -> str:
    if not isinstance(value, str) or not _SAFE_ID.fullmatch(value):
        raise RegistryError(f"{label} must be a safe identifier")
    if value in {".", ".."}:
        raise RegistryError(f"unsafe {label}")
    return value


def _string(value: Any, *, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise RegistryError(f"{label} must be a non-empty string")
    return value


def _bool(value: Any, *, label: str) -> bool:
    if not isinstance(value, bool):
        raise RegistryError(f"{label} must be boolean")
    return value


def _string_tuple(value: Any, *, label: str) -> tuple[str, ...]:
    if not isinstance(value, list) or not value:
        raise RegistryError(f"{label} must be a non-empty array")
    result = tuple(_string(item, label=label) for item in value)
    if len(set(result)) != len(result):
        raise RegistryError(f"{label} contains duplicates")
    return result


def _bound_file(repo: Path, value: Any, *, label: str) -> BoundFile:
    if not isinstance(value, dict):
        raise RegistryError(f"{label} must be an object")
    _require_keys(value, {"path", "sha256"}, label=label)
    expected = value["sha256"]
    if not isinstance(expected, str) or not _SHA256.fullmatch(expected):
        raise RegistryError(f"{label}.sha256 must be lowercase SHA-256")
    try:
        path, relative = _existing_bound_path(repo, value["path"], label=label)
    except EscalationError as exc:
        raise RegistryError(str(exc)) from exc
    actual = _sha256(path.read_bytes())
    if actual != expected:
        raise RegistryError(
            f"{label} hash mismatch: expected {expected}, found {actual}"
        )
    return BoundFile(relative, expected)


def _read_bound_file(repo: Path, bound: BoundFile, *, label: str) -> bytes:
    """Read an asset at its point of use and recheck its registry digest."""

    try:
        path, relative = _existing_bound_path(repo, bound.path, label=label)
    except EscalationError as exc:
        raise RegistryError(str(exc)) from exc
    payload = path.read_bytes()
    observed = _sha256(payload)
    if relative != bound.path or observed != bound.sha256:
        raise RegistryError(
            f"{label} changed after registry validation: expected "
            f"{bound.sha256}, found {observed}"
        )
    return payload


def _validate_launch_claim(
    repo: Path,
    *,
    base_pipeline: BoundFile,
    evolution_config: BoundFile,
    required_stage3_backend: str | None,
) -> None:
    pipeline_value = _load_json(
        (repo / base_pipeline.path).read_bytes(), label="base pipeline"
    )
    if not isinstance(pipeline_value, dict) or not isinstance(
        pipeline_value.get("stage1"), dict
    ):
        raise RegistryError("launch-compatible base pipeline needs stage1 object")
    if pipeline_value.get("candidate_inputs"):
        raise RegistryError("launch-compatible base pipeline cannot use candidate_inputs")
    stage3 = pipeline_value.get("stage3")
    if required_stage3_backend is not None:
        if (
            not isinstance(stage3, dict)
            or stage3.get("backend") != required_stage3_backend
            or stage3.get("exact") is not True
        ):
            raise RegistryError("base pipeline does not use required Stage 3 backend")

    try:
        evolution_value = yaml.safe_load((repo / evolution_config.path).read_text())
    except yaml.YAMLError as exc:
        raise RegistryError(f"invalid evolution YAML: {exc}") from exc
    if not isinstance(evolution_value, dict):
        raise RegistryError("launch-compatible evolution config must be a mapping")
    portfolio = evolution_value.get("qcode_search_portfolio")
    if not isinstance(portfolio, dict):
        raise RegistryError("launch-compatible config needs qcode_search_portfolio")
    portfolio_contracts = {
        2: (
            ["algebraic_relation_type", "support_split_type", "orbit_span_bin"],
            {
                "algebraic_relation_type": 5,
                "support_split_type": 6,
                "orbit_span_bin": 3,
            },
        ),
        3: (
            [
                "algebraic_relation_type",
                "support_split_type",
                "geometry_twist_class",
            ],
            {
                "algebraic_relation_type": 5,
                "support_split_type": 6,
                "geometry_twist_class": 3,
            },
        ),
    }
    schema_version = portfolio.get("schema_version")
    if (
        portfolio.get("enabled") is not True
        or schema_version not in portfolio_contracts
    ):
        raise RegistryError(
            "launch-compatible Humanize config requires portfolio schema_version 2 or 3"
        )
    # Preserve the historical schema-v2 launch claim accepted by existing
    # signed registries.  Schema v3 is new and must bind its checkpoint-
    # incompatible geometry dimensions explicitly from day one.
    if schema_version == 3:
        database = evolution_value.get("database")
        dimensions, bins = portfolio_contracts[schema_version]
        if (
            not isinstance(database, dict)
            or database.get("num_islands") != 5
            or database.get("feature_dimensions") != dimensions
            or database.get("feature_bins") != bins
        ):
            raise RegistryError(
                "launch-compatible evolution config has incompatible portfolio geometry"
            )


def load_template_registry(
    *,
    repo_dir: Path,
    registry_path: Path = DEFAULT_REGISTRY_PATH,
) -> CampaignTemplateRegistry:
    """Load and verify every path and digest in the template registry."""

    repo = _repo(repo_dir)
    try:
        path, relative = _existing_bound_path(repo, registry_path, label="registry")
    except EscalationError as exc:
        raise RegistryError(str(exc)) from exc
    payload = path.read_bytes()
    value = _load_json(payload, label="registry")
    if not isinstance(value, dict):
        raise RegistryError("registry must be a JSON object")
    _require_keys(value, {"schema_version", "kind", "templates"}, label="registry")
    if value["schema_version"] != REGISTRY_SCHEMA_VERSION:
        raise RegistryError("unsupported registry schema_version")
    if value["kind"] != "qcode-campaign-template-registry":
        raise RegistryError("unexpected registry kind")
    rows = value["templates"]
    if not isinstance(rows, list) or not rows:
        raise RegistryError("registry templates must be a non-empty array")

    expected_fields = {
        "template_id",
        "template_version",
        "description",
        "runner_kind",
        "transition_kind",
        "representation_id",
        "family_id",
        "checkpoint_compatibility_group",
        "proof_compatible",
        "launch_compatible",
        "auto_materialize",
        "allowed_parent_representations",
        "allowed_machine_regimes",
        "base_pipeline",
        "evolution_config",
        "evolution_seed",
        "required_stage3_backend",
    }
    templates: dict[str, CampaignTemplate] = {}
    for index, row in enumerate(rows):
        label = f"templates[{index}]"
        if not isinstance(row, dict):
            raise RegistryError(f"{label} must be an object")
        _require_keys(row, expected_fields, label=label)
        template_id = _safe_id(row["template_id"], label=f"{label}.template_id")
        if template_id in templates:
            raise RegistryError(f"duplicate template_id: {template_id}")
        version = row["template_version"]
        if isinstance(version, bool) or not isinstance(version, int) or version < 1:
            raise RegistryError(f"{label}.template_version must be a positive integer")
        runner_kind = _string(row["runner_kind"], label=f"{label}.runner_kind")
        if runner_kind != "five-stage-humanize":
            raise RegistryError(f"unsupported runner_kind: {runner_kind}")
        transition = _string(
            row["transition_kind"], label=f"{label}.transition_kind"
        )
        if transition not in {"expand_family", "representation_change"}:
            raise RegistryError(f"unsupported transition_kind: {transition}")
        regimes = _string_tuple(
            row["allowed_machine_regimes"],
            label=f"{label}.allowed_machine_regimes",
        )
        if any(item not in _MACHINE_REGIMES for item in regimes):
            raise RegistryError(f"{label} contains unsupported machine regime")
        expected_regime = (
            "expand_required"
            if transition == "expand_family"
            else "representation_change_required"
        )
        if regimes != (expected_regime,):
            raise RegistryError(
                f"{label} must allow exactly {expected_regime}"
            )
        proof_compatible = _bool(
            row["proof_compatible"], label=f"{label}.proof_compatible"
        )
        launch_compatible = _bool(
            row["launch_compatible"], label=f"{label}.launch_compatible"
        )
        auto_materialize = _bool(
            row["auto_materialize"], label=f"{label}.auto_materialize"
        )
        if auto_materialize and not (proof_compatible and launch_compatible):
            raise RegistryError(
                f"{label} auto_materialize requires proof and launch compatibility"
            )
        base_value = row["base_pipeline"]
        base_pipeline = (
            None
            if base_value is None
            else _bound_file(repo, base_value, label=f"{label}.base_pipeline")
        )
        if launch_compatible and base_pipeline is None:
            raise RegistryError(f"{label} launch-compatible template needs base_pipeline")
        evolution_config = _bound_file(
            repo, row["evolution_config"], label=f"{label}.evolution_config"
        )
        evolution_seed = _bound_file(
            repo, row["evolution_seed"], label=f"{label}.evolution_seed"
        )
        backend = row["required_stage3_backend"]
        if backend is not None:
            backend = _string(backend, label=f"{label}.required_stage3_backend")
        if launch_compatible:
            assert base_pipeline is not None
            _validate_launch_claim(
                repo,
                base_pipeline=base_pipeline,
                evolution_config=evolution_config,
                required_stage3_backend=backend,
            )
        template = CampaignTemplate(
            template_id=template_id,
            template_version=version,
            description=_string(row["description"], label=f"{label}.description"),
            runner_kind=runner_kind,
            transition_kind=transition,
            representation_id=_string(
                row["representation_id"], label=f"{label}.representation_id"
            ),
            family_id=_string(row["family_id"], label=f"{label}.family_id"),
            checkpoint_compatibility_group=_string(
                row["checkpoint_compatibility_group"],
                label=f"{label}.checkpoint_compatibility_group",
            ),
            proof_compatible=proof_compatible,
            launch_compatible=launch_compatible,
            auto_materialize=auto_materialize,
            allowed_parent_representations=_string_tuple(
                row["allowed_parent_representations"],
                label=f"{label}.allowed_parent_representations",
            ),
            allowed_machine_regimes=regimes,
            base_pipeline=base_pipeline,
            evolution_config=evolution_config,
            evolution_seed=evolution_seed,
            required_stage3_backend=backend,
            entry_sha256=_sha256(_canonical_bytes(row)),
        )
        templates[template_id] = template
    return CampaignTemplateRegistry(
        repo_dir=repo,
        registry_path=relative,
        registry_sha256=_sha256(payload),
        templates=templates,
    )


def _validated_parent_machine_evidence(
    *,
    repo: Path,
    parent_state_path: Path,
    reviewer_action: Any = _REVIEWER_ACTION_UNSET,
    require_escalation_regime: bool,
) -> _ParentMachineEvidence:
    try:
        parent_path, parent_relative = _existing_bound_path(
            repo, parent_state_path, label="parent state"
        )
    except EscalationError as exc:
        raise ParentEvidenceError(str(exc)) from exc
    parent_payload = parent_path.read_bytes()
    try:
        parent = _load_json(parent_payload, label="parent state")
    except RegistryError as exc:
        raise ParentEvidenceError(str(exc)) from exc
    if not isinstance(parent, dict):
        raise ParentEvidenceError("parent state must be a JSON object")
    try:
        parent_run_id = _safe_id(parent.get("run_id"), label="parent run_id")
    except RegistryError as exc:
        raise ParentEvidenceError(str(exc)) from exc
    if parent_path.name != "state.json" or parent_path.parent.name != parent_run_id:
        raise ParentEvidenceError(
            "parent state run_id must match its containing run directory"
        )
    status = parent.get("status")
    if status not in {"search-complete", "incomplete-unresolved"}:
        raise ParentEvidenceError(
            "parent status must be search-complete or incomplete-unresolved"
        )
    if parent.get("pending_round") is not None or parent.get("round_phase") is not None:
        raise ParentEvidenceError("parent has an unfinished round transaction")
    config = parent.get("config")
    if not isinstance(config, dict):
        raise ParentEvidenceError("parent state.config must be an object")
    policy_version = config.get("search_regime_policy_version", 1)
    if (
        isinstance(policy_version, bool)
        or not isinstance(policy_version, int)
        or policy_version not in flow_module.SEARCH_REGIME_POLICY_VERSIONS
    ):
        raise ParentEvidenceError(
            "parent search_regime_policy_version is invalid"
        )
    max_rounds = config.get("max_rounds")
    if (
        policy_version
        in flow_module.SEARCH_REGIME_BUDGET_BOUND_POLICY_VERSIONS
        and (
            isinstance(max_rounds, bool)
            or not isinstance(max_rounds, int)
            or max_rounds < 1
        )
    ):
        raise ParentEvidenceError(
            "parent budget-bound max_rounds binding is invalid"
        )
    try:
        search_representation_id = _safe_id(
            config.get("search_representation_id"),
            label="parent state.config.search_representation_id",
        )
    except RegistryError as exc:
        raise ParentEvidenceError(str(exc)) from exc
    rounds = parent.get("rounds")
    if not isinstance(rounds, list) or any(not isinstance(row, dict) for row in rounds):
        raise ParentEvidenceError("parent rounds must be a list of objects")
    current_round = parent.get("current_round")
    if (
        not rounds
        or isinstance(current_round, bool)
        or not isinstance(current_round, int)
        or current_round < 1
        or rounds[-1].get("round") != current_round
    ):
        raise ParentEvidenceError(
            "parent current_round must equal the last completed round"
        )
    rounds_root = parent_path.parent / "rounds"
    try:
        rounds_relative = rounds_root.relative_to(repo)
        _reject_symlink_components(repo, rounds_relative, label="parent rounds")
        replayed = flow_module._replay_search_regime(
            rounds,
            rounds_root=rounds_root,
            policy_version=policy_version,
            max_rounds=(
                max_rounds
                if policy_version
                in flow_module.SEARCH_REGIME_BUDGET_BOUND_POLICY_VERSIONS
                else None
            ),
        )
    except Exception as exc:
        raise ParentEvidenceError(f"parent search regime replay failed: {exc}") from exc
    recorded = parent.get("search_regime")
    if not isinstance(recorded, dict) or replayed != recorded:
        raise ParentEvidenceError(
            "parent search_regime disagrees with replayed sealed evidence"
        )
    machine_regime = recorded.get("status")
    if require_escalation_regime and machine_regime not in _MACHINE_REGIMES:
        raise ParentEvidenceError(
            "machine regime must be expand_required or representation_change_required"
        )

    # A representation-changing child is authorized only by the atomic
    # Stage-1 handoff transaction.  Replaying the regime alone is insufficient:
    # markerless policy-v2/v3 state can also arise from a campaign that was never
    # configured to stop and hand control to a fresh representation.
    if machine_regime == "representation_change_required":
        stop_on_change = config.get("stop_on_representation_change")
        if (
            isinstance(policy_version, bool)
            or policy_version not in {2, 3, 4}
            or stop_on_change is not True
        ):
            raise ParentEvidenceError(
                "representation-change escalation lacks versioned handoff "
                "authorization"
            )
        try:
            handoff_status = flow_module._validated_search_handoff(
                SimpleNamespace(
                    search_regime_policy_version=policy_version,
                    stop_on_representation_change=stop_on_change,
                    max_rounds=max_rounds,
                ),
                parent,
                rounds_root=rounds_root,
            )
        except Exception as exc:
            raise ParentEvidenceError(
                f"parent representation-change handoff replay failed: {exc}"
            ) from exc
        if handoff_status != status:
            raise ParentEvidenceError(
                "representation-change escalation requires the committed "
                "Stage-1 handoff markers"
            )

    advisory = reviewer_action
    advisory_status = "not_present"
    advisory_error: Mapping[str, str] | None = None
    if advisory is _REVIEWER_ACTION_UNSET:
        advisory = None
        if rounds:
            binding = rounds[-1].get("review_binding")
            if binding is not None:
                try:
                    flow_module._validated_bound_round_review(
                        rounds[-1], rounds_root
                    )
                except Exception as exc:
                    # Reviewer output is advisory and excluded from both the
                    # machine plan and child bytes.  Corrupt/missing reviewer
                    # artifacts remain visible in the operational sidecar but
                    # must never veto a sealed machine-authorized transition.
                    advisory_status = "unavailable"
                    advisory_error = {
                        "classification": type(exc).__name__,
                        "message": str(exc)[:1000],
                    }
                else:
                    # The replay above authenticates the artifact against this
                    # binding.  Consume the binding's classified action rather
                    # than arbitrary legacy top-level extras: legacy reviews
                    # were permissive and may legally contain a field named
                    # ``search_action`` without being reviewer-v2.
                    assert isinstance(binding, dict)
                    advisory = binding.get("search_action")
                    if advisory is not None:
                        advisory_status = "available"
    else:
        advisory_status = "available" if advisory is not None else "not_present"
    advisory = _json_clone(advisory)
    canonical_rounds: list[dict[str, Any]] = []
    for summary in rounds:
        canonical = {"round": summary["round"]}
        for field in (
            "sealed_exact_audit",
            "candidate_diversity",
            "search_regime",
        ):
            if field in summary:
                canonical[field] = copy.deepcopy(summary[field])
        canonical_rounds.append(canonical)
    canonical_evidence = {
        "schema_version": MACHINE_EVIDENCE_SCHEMA_VERSION,
        "kind": "qcode-campaign-escalation-machine-evidence",
        "parent_run_id": parent_run_id,
        "search_representation_id": search_representation_id,
        "current_round": current_round,
        "rounds": canonical_rounds,
        "search_regime": copy.deepcopy(replayed),
    }
    if (
        policy_version
        in flow_module.SEARCH_REGIME_BUDGET_BOUND_POLICY_VERSIONS
    ):
        canonical_evidence["search_regime_policy_version"] = policy_version
        canonical_evidence["max_rounds"] = max_rounds
        for canonical, summary in zip(canonical_rounds, rounds, strict=True):
            canonical["search_regime_policy_version"] = summary.get(
                "search_regime_policy_version"
            )
            canonical["trusted_win_total"] = summary.get(
                "trusted_win_total"
            )
    if machine_regime == "representation_change_required":
        canonical_evidence["search_handoff_reason"] = parent[
            "search_handoff_reason"
        ]
        canonical_evidence["search_handoff_at_round"] = parent[
            "search_handoff_at_round"
        ]
    return _ParentMachineEvidence(
        state_path=parent_relative,
        state_sha256=_sha256(parent_payload),
        run_id=parent_run_id,
        status=status,
        search_representation_id=search_representation_id,
        search_regime_policy_version=policy_version,
        max_rounds=(max_rounds if isinstance(max_rounds, int) else None),
        stop_on_representation_change=(
            config.get("stop_on_representation_change") is True
        ),
        regime=copy.deepcopy(recorded),
        rounds=tuple(copy.deepcopy(rounds)),
        machine_evidence_sha256=_sha256(_canonical_bytes(canonical_evidence)),
        reviewer_action=advisory,
        reviewer_action_status=advisory_status,
        reviewer_action_error=advisory_error,
    )


def _child_run_id(parent_run_id: str, template_id: str, key: str) -> str:
    suffix = f".esc.{template_id}.{key[:12]}"
    available = 128 - len(suffix)
    if available < 1:
        candidate = f"esc.{key[:32]}"
    else:
        candidate = parent_run_id[:available].rstrip(".-_") + suffix
    if not _SAFE_ID.fullmatch(candidate) or candidate == parent_run_id:
        candidate = f"esc.{key[:32]}"
    return candidate


def plan_campaign_escalation(
    *,
    repo_dir: Path,
    parent_state_path: Path,
    template_id: str,
    registry_path: Path = DEFAULT_REGISTRY_PATH,
    reviewer_action: Any = _REVIEWER_ACTION_UNSET,
) -> EscalationPlan:
    """Create a deterministic plan from sealed machine regime evidence.

    Reviewer advice is replayed for the parent sidecar only.  It never enters
    this plan, its identity, the child run id, or materialized child bytes.
    """

    registry = load_template_registry(repo_dir=repo_dir, registry_path=registry_path)
    repo = registry.repo_dir
    template = registry.template(template_id)
    evidence = _validated_parent_machine_evidence(
        repo=repo,
        parent_state_path=parent_state_path,
        reviewer_action=reviewer_action,
        require_escalation_regime=True,
    )
    machine_regime = evidence.regime["status"]
    parent_representation = evidence.search_representation_id
    expected_transition = _TRANSITION_FOR_REGIME[machine_regime]
    if template.transition_kind != expected_transition:
        raise ParentEvidenceError(
            f"{machine_regime} cannot select {template.transition_kind} template"
        )
    if machine_regime not in template.allowed_machine_regimes:
        raise ParentEvidenceError("template does not allow parent machine regime")
    if parent_representation not in template.allowed_parent_representations:
        raise ParentEvidenceError("template does not allow parent representation")
    if expected_transition == "expand_family":
        if template.representation_id != parent_representation:
            raise ParentEvidenceError("family expansion must preserve representation")
    elif template.representation_id == parent_representation:
        raise ParentEvidenceError("representation change must change representation_id")

    decision = {
        "schema_version": PLAN_SCHEMA_VERSION,
        "parent_run_id": evidence.run_id,
        "machine_evidence_sha256": evidence.machine_evidence_sha256,
        "parent_representation_id": parent_representation,
        "machine_regime": machine_regime,
        "transition_kind": template.transition_kind,
        "target_representation_id": template.representation_id,
        "registry_sha256": registry.registry_sha256,
        "template_entry_sha256": template.entry_sha256,
    }
    idempotency_key = _sha256(_canonical_bytes(decision))
    reasons: list[str] = []
    if not template.proof_compatible:
        reasons.append("proof_incompatible")
    if not template.launch_compatible:
        reasons.append("launch_incompatible")
    if not template.auto_materialize:
        reasons.append("auto_materialize_disabled")
    return EscalationPlan(
        repo_dir=repo,
        registry_path=registry.registry_path,
        registry_sha256=registry.registry_sha256,
        template_id=template.template_id,
        template_version=template.template_version,
        template_entry_sha256=template.entry_sha256,
        parent_state_path=evidence.state_path,
        parent_run_id=evidence.run_id,
        machine_evidence_sha256=evidence.machine_evidence_sha256,
        parent_representation_id=parent_representation,
        machine_regime=machine_regime,
        transition_kind=template.transition_kind,
        target_representation_id=template.representation_id,
        child_run_id=_child_run_id(
            evidence.run_id, template.template_id, idempotency_key
        ),
        idempotency_key=idempotency_key,
        proof_compatible=template.proof_compatible,
        launch_compatible=template.launch_compatible,
        materializable=not reasons,
        block_reasons=tuple(reasons),
    )


def parse_auto_escalation_policy(
    *,
    repo_dir: Path,
    pipeline_config_path: Path,
    expected_pipeline_config_sha256: str | None = None,
    expected_registry_sha256: str | None = None,
) -> AutoEscalationPolicy:
    """Parse a parent pipeline's allow-listed auto-escalation policy."""

    repo = _repo(repo_dir)
    try:
        path, relative = _existing_bound_path(
            repo, pipeline_config_path, label="pipeline config"
        )
    except EscalationError as exc:
        raise RegistryError(str(exc)) from exc
    payload = path.read_bytes()
    observed_pipeline_sha256 = _sha256(payload)
    if (
        expected_pipeline_config_sha256 is not None
        and observed_pipeline_sha256 != expected_pipeline_config_sha256
    ):
        raise RegistryError("pipeline config changed from its launch snapshot")
    value = _load_json(payload, label="pipeline config")
    if not isinstance(value, dict):
        raise RegistryError("pipeline config must be a JSON object")
    stage1 = value.get("stage1")
    source_representation: str | None = None
    source_policy_version = 1
    source_max_rounds: int | None = None
    source_stop_on_change = False
    if isinstance(stage1, dict) and stage1.get("search_representation_id") is not None:
        source_representation = _safe_id(
            stage1["search_representation_id"],
            label="pipeline stage1.search_representation_id",
        )
    if isinstance(stage1, dict):
        source_policy_version = stage1.get(
            "search_regime_policy_version", 1
        )
        if (
            isinstance(source_policy_version, bool)
            or not isinstance(source_policy_version, int)
            or source_policy_version
            not in flow_module.SEARCH_REGIME_POLICY_VERSIONS
        ):
            raise RegistryError(
                "pipeline stage1.search_regime_policy_version is invalid"
            )
        raw_max_rounds = stage1.get("max_rounds")
        if raw_max_rounds is not None:
            if (
                isinstance(raw_max_rounds, bool)
                or not isinstance(raw_max_rounds, int)
                or raw_max_rounds < 1
            ):
                raise RegistryError(
                    "pipeline stage1.max_rounds must be a positive integer"
                )
            source_max_rounds = raw_max_rounds
        raw_stop = stage1.get("stop_on_representation_change", False)
        if not isinstance(raw_stop, bool):
            raise RegistryError(
                "pipeline stage1.stop_on_representation_change must be boolean"
            )
        source_stop_on_change = raw_stop
    raw_policy = value.get("auto_escalation")
    if raw_policy is None:
        return AutoEscalationPolicy(
            repo_dir=repo,
            pipeline_config_path=relative,
            pipeline_config_sha256=observed_pipeline_sha256,
            enabled=False,
            registry_path=None,
            registry_sha256=None,
            template_by_regime={},
            source_search_representation_id=source_representation,
            source_search_regime_policy_version=source_policy_version,
            source_max_rounds=source_max_rounds,
            source_stop_on_representation_change=source_stop_on_change,
        )
    if not isinstance(raw_policy, dict):
        raise RegistryError("auto_escalation must be an object")
    _require_keys(
        raw_policy,
        {"enabled", "registry", "template_by_regime"},
        label="auto_escalation",
    )
    enabled = _bool(raw_policy["enabled"], label="auto_escalation.enabled")
    if (
        enabled
        and source_policy_version
        in flow_module.SEARCH_REGIME_BUDGET_BOUND_POLICY_VERSIONS
        and (
            source_max_rounds is None or not source_stop_on_change
        )
    ):
        raise RegistryError(
            "enabled budget-bound pipeline policy requires max_rounds and "
            "terminal handoff"
        )
    try:
        registry_relative = _relative_path(
            raw_policy["registry"], label="auto_escalation.registry"
        ).as_posix()
    except (TypeError, EscalationError) as exc:
        raise RegistryError(str(exc)) from exc
    mapping_value = raw_policy["template_by_regime"]
    if not isinstance(mapping_value, dict):
        raise RegistryError("auto_escalation.template_by_regime must be an object")
    mapping: dict[str, str] = {}
    for regime, selected_template in mapping_value.items():
        if regime not in _MACHINE_REGIMES:
            raise RegistryError(f"unsupported auto-escalation regime: {regime}")
        mapping[regime] = _safe_id(
            selected_template,
            label=f"auto_escalation.template_by_regime.{regime}",
        )
    if enabled and source_representation is None:
        raise RegistryError(
            "enabled auto_escalation requires stage1.search_representation_id"
        )
    registry = load_template_registry(
        repo_dir=repo, registry_path=Path(registry_relative)
    )
    if (
        expected_registry_sha256 is not None
        and registry.registry_sha256 != expected_registry_sha256
    ):
        raise RegistryError("campaign template registry changed from launch snapshot")
    for regime, selected_template in mapping.items():
        template = registry.template(selected_template)
        if regime not in template.allowed_machine_regimes:
            raise RegistryError(
                f"template {selected_template} does not allow mapped regime {regime}"
            )
        if template.transition_kind != _TRANSITION_FOR_REGIME[regime]:
            raise RegistryError(
                f"template {selected_template} has incompatible transition kind"
            )
        if (
            source_representation is not None
            and source_representation not in template.allowed_parent_representations
        ):
            raise RegistryError(
                f"template {selected_template} does not allow the policy source "
                "representation"
            )
        if template.transition_kind == "expand_family":
            if template.representation_id != source_representation:
                raise RegistryError(
                    f"template {selected_template} family expansion changes representation"
                )
        elif template.representation_id == source_representation:
            raise RegistryError(
                f"template {selected_template} representation change keeps representation"
            )
    return AutoEscalationPolicy(
        repo_dir=repo,
        pipeline_config_path=relative,
        pipeline_config_sha256=observed_pipeline_sha256,
        enabled=enabled,
        registry_path=registry_relative,
        registry_sha256=registry.registry_sha256,
        template_by_regime=mapping,
        source_search_representation_id=source_representation,
        source_search_regime_policy_version=source_policy_version,
        source_max_rounds=source_max_rounds,
        source_stop_on_representation_change=source_stop_on_change,
    )


def reconcile_campaign_escalation(
    *,
    repo_dir: Path,
    parent_state_path: Path,
    pipeline_config_path: Path,
    destination: Path | None = None,
    reviewer_action: Any = _REVIEWER_ACTION_UNSET,
    expected_pipeline_config_sha256: str | None = None,
    expected_registry_sha256: str | None = None,
) -> EscalationReconciliation:
    """Reconcile policy and sealed state, optionally materializing but never spawning."""

    policy = parse_auto_escalation_policy(
        repo_dir=repo_dir,
        pipeline_config_path=pipeline_config_path,
        expected_pipeline_config_sha256=expected_pipeline_config_sha256,
        expected_registry_sha256=expected_registry_sha256,
    )
    if not policy.enabled:
        return EscalationReconciliation(
            disposition="disabled",
            policy=policy,
            machine_regime=None,
            template_id=None,
            plan=None,
            materialized=None,
            block_reasons=(),
        )
    evidence = _validated_parent_machine_evidence(
        repo=policy.repo_dir,
        parent_state_path=parent_state_path,
        reviewer_action=reviewer_action,
        require_escalation_regime=False,
    )
    if evidence.search_representation_id != policy.source_search_representation_id:
        raise ParentEvidenceError(
            "parent state search representation disagrees with pipeline policy"
        )
    if (
        evidence.search_regime_policy_version
        != policy.source_search_regime_policy_version
    ):
        raise ParentEvidenceError(
            "parent search-regime policy version disagrees with pipeline policy"
        )
    if (
        policy.source_search_regime_policy_version
        in flow_module.SEARCH_REGIME_BUDGET_BOUND_POLICY_VERSIONS
        and (
            evidence.max_rounds != policy.source_max_rounds
            or evidence.stop_on_representation_change
            != policy.source_stop_on_representation_change
        )
    ):
        raise ParentEvidenceError(
            "parent budget/handoff authority disagrees with pipeline policy"
        )
    machine_regime = evidence.regime.get("status")
    if machine_regime not in _MACHINE_REGIMES:
        return EscalationReconciliation(
            disposition="not_required",
            policy=policy,
            machine_regime=(
                machine_regime if isinstance(machine_regime, str) else None
            ),
            template_id=None,
            plan=None,
            materialized=None,
            block_reasons=(),
            parent_state_sha256=evidence.state_sha256,
            machine_evidence_sha256=evidence.machine_evidence_sha256,
            reviewer_action_advisory=evidence.reviewer_action,
            reviewer_action_advisory_status=evidence.reviewer_action_status,
            reviewer_action_advisory_error=evidence.reviewer_action_error,
        )
    selected = policy.template_by_regime.get(machine_regime)
    if selected is None:
        return EscalationReconciliation(
            disposition="blocked",
            policy=policy,
            machine_regime=machine_regime,
            template_id=None,
            plan=None,
            materialized=None,
            block_reasons=("no_template_for_machine_regime",),
            parent_state_sha256=evidence.state_sha256,
            machine_evidence_sha256=evidence.machine_evidence_sha256,
            reviewer_action_advisory=evidence.reviewer_action,
            reviewer_action_advisory_status=evidence.reviewer_action_status,
            reviewer_action_advisory_error=evidence.reviewer_action_error,
        )
    assert policy.registry_path is not None
    plan = plan_campaign_escalation(
        repo_dir=policy.repo_dir,
        parent_state_path=parent_state_path,
        template_id=selected,
        registry_path=Path(policy.registry_path),
    )
    if plan.registry_sha256 != policy.registry_sha256:
        raise RegistryError("registry changed between policy and plan validation")
    if plan.machine_evidence_sha256 != evidence.machine_evidence_sha256:
        raise ParentEvidenceError(
            "parent machine evidence changed during escalation reconciliation"
        )
    if not plan.materializable:
        return EscalationReconciliation(
            disposition="blocked",
            policy=policy,
            machine_regime=machine_regime,
            template_id=selected,
            plan=plan,
            materialized=None,
            block_reasons=plan.block_reasons,
            parent_state_sha256=evidence.state_sha256,
            machine_evidence_sha256=evidence.machine_evidence_sha256,
            reviewer_action_advisory=evidence.reviewer_action,
            reviewer_action_advisory_status=evidence.reviewer_action_status,
            reviewer_action_advisory_error=evidence.reviewer_action_error,
        )
    if destination is None:
        return EscalationReconciliation(
            disposition="materializable",
            policy=policy,
            machine_regime=machine_regime,
            template_id=selected,
            plan=plan,
            materialized=None,
            block_reasons=(),
            parent_state_sha256=evidence.state_sha256,
            machine_evidence_sha256=evidence.machine_evidence_sha256,
            reviewer_action_advisory=evidence.reviewer_action,
            reviewer_action_advisory_status=evidence.reviewer_action_status,
            reviewer_action_advisory_error=evidence.reviewer_action_error,
        )
    materialized = materialize_child_pipeline(plan, destination=destination)
    return EscalationReconciliation(
        disposition="materialized",
        policy=policy,
        machine_regime=machine_regime,
        template_id=selected,
        plan=plan,
        materialized=materialized,
        block_reasons=(),
        parent_state_sha256=evidence.state_sha256,
        machine_evidence_sha256=evidence.machine_evidence_sha256,
        reviewer_action_advisory=evidence.reviewer_action,
        reviewer_action_advisory_status=evidence.reviewer_action_status,
        reviewer_action_advisory_error=evidence.reviewer_action_error,
    )


def _checkpoint_references(value: Any, *, trail: str = "$") -> list[str]:
    references: list[str] = []
    if isinstance(value, dict):
        for key, item in value.items():
            child = f"{trail}.{key}"
            if (
                "checkpoint" in str(key).lower()
                and item is not None
                and item != ""
                and item is not False
            ):
                references.append(child)
            references.extend(_checkpoint_references(item, trail=child))
    elif isinstance(value, list):
        for index, item in enumerate(value):
            references.extend(_checkpoint_references(item, trail=f"{trail}[{index}]"))
    elif isinstance(value, str) and "checkpoint" in value.lower():
        references.append(trail)
    return references


def _destination(repo: Path, raw: Path) -> tuple[Path, str]:
    try:
        relative = _path_relative_to_repo(repo, raw, label="destination")
        _reject_symlink_components(repo, relative, label="destination")
    except EscalationError as exc:
        raise MaterializationError(str(exc)) from exc
    path = repo / relative
    if path.exists() and path.is_symlink():
        raise MaterializationError(f"destination is a symlink: {relative.as_posix()}")
    return path, relative.as_posix()


def _atomic_create(path: Path, payload: bytes) -> bool:
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists() or path.is_symlink():
        if path.is_symlink() or not path.is_file():
            raise MaterializationError(f"unsafe existing destination: {path}")
        if path.read_bytes() == payload:
            return False
        raise MaterializationError("destination exists with different content")

    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        try:
            os.link(temporary, path, follow_symlinks=False)
            created = True
        except FileExistsError:
            if path.is_symlink() or not path.is_file() or path.read_bytes() != payload:
                raise MaterializationError(
                    "concurrent materialization produced different content"
                )
            created = False
        directory_fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
        return created
    finally:
        temporary.unlink(missing_ok=True)


def materialize_child_pipeline(
    plan: EscalationPlan,
    *,
    destination: Path,
) -> MaterializedCampaign:
    """Materialize a fresh child config without spawning or resuming a process."""

    if not isinstance(plan, EscalationPlan):
        raise MaterializationError("plan must be an EscalationPlan")
    try:
        replay = plan_campaign_escalation(
            repo_dir=plan.repo_dir,
            parent_state_path=Path(plan.parent_state_path),
            template_id=plan.template_id,
            registry_path=Path(plan.registry_path),
        )
    except EscalationError as exc:
        raise MaterializationError(f"plan replay failed: {exc}") from exc
    if replay != plan:
        raise MaterializationError("plan, registry, template, or parent evidence changed")
    if not plan.proof_compatible:
        raise ProofIncompatibleTemplateError(
            "template has no compatible end-to-end proof path"
        )
    if not plan.materializable:
        raise MaterializationError(
            "template is not auto-materializable: " + ", ".join(plan.block_reasons)
        )

    registry = load_template_registry(
        repo_dir=plan.repo_dir, registry_path=Path(plan.registry_path)
    )
    template = registry.template(plan.template_id)
    if template.base_pipeline is None:
        raise MaterializationError("template has no base pipeline")
    base = _load_json(
        _read_bound_file(
            registry.repo_dir, template.base_pipeline, label="base pipeline"
        ),
        label="base pipeline",
    )
    if not isinstance(base, dict):
        raise MaterializationError("base pipeline must be an object")
    pipeline = copy.deepcopy(base)
    stage1 = pipeline.get("stage1")
    if not isinstance(stage1, dict):
        raise MaterializationError("base pipeline lacks stage1 object")
    if pipeline.get("candidate_inputs"):
        raise MaterializationError("escalated search cannot inherit candidate_inputs")
    if stage1.get("candidate_file") not in {None, ""}:
        raise MaterializationError("escalated search cannot inherit candidate_file")
    pipeline["run_id"] = plan.child_run_id
    pipeline["resume"] = True
    # A child gets a fresh representation and therefore must not inherit a
    # policy whose source representation was the parent generator.
    pipeline.pop("auto_escalation", None)
    stage1["evolution_config"] = template.evolution_config.path
    stage1["evolution_seed"] = template.evolution_seed.path
    stage1["search_representation_id"] = template.representation_id
    # The selected template is already the fresh representation.  With no
    # matching child escalation policy, inheriting the parent's stop marker
    # would terminate this 12-round campaign at its own round 7 with nowhere
    # to hand off.  Keep policy-v2 regime feedback and restart scheduling, but
    # let the child use its complete authorized round budget.
    stage1.pop("stop_on_representation_change", None)
    if _checkpoint_references(pipeline):
        raise MaterializationError("base pipeline contains checkpoint references")

    body_sha256 = _sha256(_canonical_bytes(pipeline))
    lineage = {
        "parent_run_id": plan.parent_run_id,
        "child_run_id": plan.child_run_id,
        "machine_evidence_sha256": plan.machine_evidence_sha256,
        "machine_regime": plan.machine_regime,
        "transition_kind": plan.transition_kind,
        "parent_representation_id": plan.parent_representation_id,
        "target_representation_id": plan.target_representation_id,
        "idempotency_key": plan.idempotency_key,
    }
    metadata = {
        "schema_version": PROVENANCE_SCHEMA_VERSION,
        "kind": "qcode-campaign-escalation-provenance",
        **lineage,
        "lineage_sha256": _sha256(_canonical_bytes(lineage)),
        "registry_path": plan.registry_path,
        "registry_sha256": plan.registry_sha256,
        "template_id": plan.template_id,
        "template_version": plan.template_version,
        "template_entry_sha256": plan.template_entry_sha256,
        "base_pipeline": template.base_pipeline.serializable(),
        "evolution_config": template.evolution_config.serializable(),
        "evolution_seed": template.evolution_seed.serializable(),
        "materialized_pipeline_body_sha256": body_sha256,
        "plan_sha256": plan.plan_sha256,
    }
    provenance_sha256 = _sha256(_canonical_bytes(metadata))
    metadata["provenance_sha256"] = provenance_sha256
    pipeline["campaign_escalation"] = metadata
    output = (json.dumps(pipeline, ensure_ascii=False, sort_keys=True, indent=2) + "\n").encode(
        "utf-8"
    )
    path, _relative = _destination(registry.repo_dir, destination)
    path.parent.mkdir(parents=True, exist_ok=True)
    # Recheck after parent creation to catch an ordinary symlink/path
    # substitution before the final exclusive link.
    _reject_symlink_components(
        registry.repo_dir,
        path.relative_to(registry.repo_dir),
        label="destination",
    )
    created = _atomic_create(path, output)
    return MaterializedCampaign(
        path=path,
        child_run_id=plan.child_run_id,
        idempotency_key=plan.idempotency_key,
        provenance_sha256=provenance_sha256,
        pipeline_sha256=_sha256(output),
        created=created,
    )


def verify_materialized_child_pipeline(
    *,
    repo_dir: Path,
    config_path: Path,
    expected_pipeline_sha256: str | None = None,
    required: bool = True,
) -> dict[str, Any] | None:
    """Replay every hash binding consumed by an escalated child.

    This is intentionally called both immediately before spawn and inside the
    detached worker.  The second check closes the parent/worker hand-off window
    for the registry and all three template assets.
    """

    repo = _repo(repo_dir)
    path, _relative = _existing_bound_path(repo, config_path, label="child config")
    payload = path.read_bytes()
    pipeline_sha256 = _sha256(payload)
    if (
        expected_pipeline_sha256 is not None
        and pipeline_sha256 != expected_pipeline_sha256
    ):
        raise MaterializationError("materialized child config hash changed")
    value = _load_json(payload, label="materialized child config")
    if not isinstance(value, dict):
        raise MaterializationError("materialized child config must be an object")
    metadata = value.get("campaign_escalation")
    if metadata is None and not required:
        return None
    if not isinstance(metadata, dict):
        raise MaterializationError(
            "materialized child lacks campaign_escalation provenance"
        )
    expected_fields = {
        "schema_version",
        "kind",
        "parent_run_id",
        "child_run_id",
        "machine_evidence_sha256",
        "machine_regime",
        "transition_kind",
        "parent_representation_id",
        "target_representation_id",
        "idempotency_key",
        "lineage_sha256",
        "registry_path",
        "registry_sha256",
        "template_id",
        "template_version",
        "template_entry_sha256",
        "base_pipeline",
        "evolution_config",
        "evolution_seed",
        "materialized_pipeline_body_sha256",
        "plan_sha256",
        "provenance_sha256",
    }
    try:
        _require_keys(metadata, expected_fields, label="campaign_escalation")
    except RegistryError as exc:
        raise MaterializationError(str(exc)) from exc
    if (
        metadata["schema_version"] != PROVENANCE_SCHEMA_VERSION
        or metadata["kind"] != "qcode-campaign-escalation-provenance"
    ):
        raise MaterializationError("unsupported campaign escalation provenance")
    for field in (
        "machine_evidence_sha256",
        "idempotency_key",
        "lineage_sha256",
        "registry_sha256",
        "template_entry_sha256",
        "materialized_pipeline_body_sha256",
        "plan_sha256",
        "provenance_sha256",
    ):
        if not isinstance(metadata[field], str) or not _SHA256.fullmatch(
            metadata[field]
        ):
            raise MaterializationError(f"invalid campaign escalation {field}")

    unsigned = dict(metadata)
    claimed_provenance = unsigned.pop("provenance_sha256")
    if _sha256(_canonical_bytes(unsigned)) != claimed_provenance:
        raise MaterializationError("campaign escalation provenance hash mismatch")
    lineage_fields = (
        "parent_run_id",
        "child_run_id",
        "machine_evidence_sha256",
        "machine_regime",
        "transition_kind",
        "parent_representation_id",
        "target_representation_id",
        "idempotency_key",
    )
    lineage = {field: metadata[field] for field in lineage_fields}
    if _sha256(_canonical_bytes(lineage)) != metadata["lineage_sha256"]:
        raise MaterializationError("campaign escalation lineage hash mismatch")

    body = copy.deepcopy(value)
    body.pop("campaign_escalation", None)
    if _sha256(_canonical_bytes(body)) != metadata[
        "materialized_pipeline_body_sha256"
    ]:
        raise MaterializationError("materialized child pipeline body hash mismatch")
    if value.get("run_id") != metadata["child_run_id"]:
        raise MaterializationError("child run_id disagrees with escalation lineage")
    if value.get("resume") is not True:
        raise MaterializationError("escalated child must enable resume")
    if "auto_escalation" in value:
        raise MaterializationError("escalated child must not inherit parent policy")

    try:
        registry = load_template_registry(
            repo_dir=repo, registry_path=Path(str(metadata["registry_path"]))
        )
    except RegistryError as exc:
        raise MaterializationError(
            f"child registry or asset revalidation failed: {exc}"
        ) from exc
    if registry.registry_sha256 != metadata["registry_sha256"]:
        raise MaterializationError("child registry hash disagrees with provenance")
    template = registry.template(str(metadata["template_id"]))
    comparisons = {
        "template_version": template.template_version,
        "template_entry_sha256": template.entry_sha256,
        "base_pipeline": (
            None
            if template.base_pipeline is None
            else template.base_pipeline.serializable()
        ),
        "evolution_config": template.evolution_config.serializable(),
        "evolution_seed": template.evolution_seed.serializable(),
    }
    for field, expected in comparisons.items():
        if metadata[field] != expected:
            raise MaterializationError(
                f"child {field} disagrees with current hash-bound template"
            )
    if template.base_pipeline is None:
        raise MaterializationError("launchable child template lacks base pipeline")
    try:
        _read_bound_file(repo, template.base_pipeline, label="child base pipeline")
        _read_bound_file(repo, template.evolution_config, label="child evolution config")
        _read_bound_file(repo, template.evolution_seed, label="child evolution seed")
    except RegistryError as exc:
        raise MaterializationError(str(exc)) from exc
    stage1 = value.get("stage1")
    if not isinstance(stage1, dict):
        raise MaterializationError("materialized child lacks stage1")
    expected_stage1 = {
        "evolution_config": template.evolution_config.path,
        "evolution_seed": template.evolution_seed.path,
        "search_representation_id": template.representation_id,
    }
    for field, expected in expected_stage1.items():
        if stage1.get(field) != expected:
            raise MaterializationError(
                f"materialized child stage1.{field} disagrees with template"
            )
    return {
        "pipeline_sha256": pipeline_sha256,
        "child_run_id": metadata["child_run_id"],
        "idempotency_key": metadata["idempotency_key"],
        "registry_sha256": metadata["registry_sha256"],
        "machine_evidence_sha256": metadata["machine_evidence_sha256"],
    }
