"""Replay and freeze the post-diagnostic ansatz-v3/deep-proof split.

The ladder diagnostic and the fresh ansatz-v3 search have different evidence
domains.  This module joins them only at a sealed planning boundary:

* every diagnostic lower/upper bound is reconstructed and replayed;
* the fresh search points at one installed hash-bound template and inherits no
  diagnostic candidate or checkpoint;
* every fail-open candidate without a trusted upper bound enters a separate
  resumable proof plan, while replayed ``LB >= 9`` is only a priority signal.

Planning never starts either track.
"""

from __future__ import annotations

import hashlib
import json
from collections.abc import Mapping
from pathlib import Path
from typing import Any

from evaluation.construction import build_css_code_from_claim
from evaluation.distance_milp import get_code_matrices
from evaluation.distance_sat import css_sector_matrices
from evaluation.low_weight_oracle import (
    verify_css_low_weight_oracle,
    verify_low_weight_sector_evidence,
)
from humanize.audit_state import authoritative_candidate_digest
from humanize.escalation import load_template_registry


DUAL_TRACK_SCHEMA_VERSION = 1
DUAL_TRACK_CONTRACT_KIND = "qcode-ansatz-v3-dual-track-preregistration"
DUAL_TRACK_PLAN_KIND = "qcode-ansatz-v3-dual-track-plan"
DIAGNOSTIC_KIND = "qcode-stratified-target-aware-ladder-v1"
DIAGNOSTIC_DECISION_POLICY = "ansatz-or-deep-proof-gate-v1"
EXPECTED_DIAGNOSTIC_COMMIT = "eb4347518fe801057783dd43051bd5266f69e0a8"
_SHA256_FIELDS = frozenset({
    "contract_sha256",
    "decision_sha256",
    "result_sha256",
})


class DualTrackEvidenceError(ValueError):
    """The diagnostic or preregistration cannot be trusted for planning."""


def _canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def _canonical_sha256(value: Any) -> str:
    return hashlib.sha256(_canonical_bytes(value)).hexdigest()


def _file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _file_identity(path: Path) -> dict[str, Any]:
    path = Path(path)
    if path.is_symlink() or not path.is_file():
        raise DualTrackEvidenceError(f"bound file must be regular: {path}")
    path = path.resolve()
    stat = path.stat()
    return {
        "path": str(path),
        "bytes": stat.st_size,
        "sha256": _file_sha256(path),
    }


def _json_object(path: Path, *, label: str) -> dict[str, Any]:
    identity = _file_identity(path)
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise DualTrackEvidenceError(f"cannot read {label}: {exc}") from exc
    if not isinstance(value, dict):
        raise DualTrackEvidenceError(f"{label} must contain an object")
    if _file_identity(path) != identity:
        raise DualTrackEvidenceError(f"{label} changed while being read")
    return value


def _jsonl(path: Path, *, label: str) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    identity = _file_identity(path)
    payload = path.read_bytes()
    if payload and not payload.endswith(b"\n"):
        raise DualTrackEvidenceError(f"{label} ends in a partial row")
    rows = []
    for number, line in enumerate(payload.splitlines(), 1):
        if not line:
            continue
        try:
            value = json.loads(line)
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise DualTrackEvidenceError(
                f"{label}:{number} is invalid JSON"
            ) from exc
        if not isinstance(value, dict):
            raise DualTrackEvidenceError(f"{label}:{number} is not an object")
        rows.append(value)
    if _file_identity(path) != identity:
        raise DualTrackEvidenceError(f"{label} changed while being read")
    return rows, identity


def _validate_self_hash(value: Mapping[str, Any], field: str) -> None:
    if field not in _SHA256_FIELDS:
        raise DualTrackEvidenceError(f"unsupported self-hash field: {field}")
    unsigned = dict(value)
    stored = unsigned.pop(field, None)
    if not isinstance(stored, str) or stored != _canonical_sha256(unsigned):
        raise DualTrackEvidenceError(f"{field} does not replay")


def load_dual_track_contract(path: Path, *, repo_dir: Path) -> dict[str, Any]:
    path = path.resolve()
    repo = repo_dir.resolve()
    value = _json_object(path, label="dual-track preregistration")
    expected = {
        "schema_version",
        "kind",
        "diagnostic_contract",
        "fresh_ansatz_track",
        "targeted_deep_proof_track",
        "joint_semantics",
    }
    if set(value) != expected:
        raise DualTrackEvidenceError("dual-track preregistration fields are invalid")
    diagnostic = value["diagnostic_contract"]
    fresh = value["fresh_ansatz_track"]
    deep = value["targeted_deep_proof_track"]
    joint = value["joint_semantics"]
    if (
        value["schema_version"] != DUAL_TRACK_SCHEMA_VERSION
        or value["kind"] != DUAL_TRACK_CONTRACT_KIND
        or not isinstance(diagnostic, dict)
        or diagnostic.get("kind") != DIAGNOSTIC_KIND
        or diagnostic.get("schema_version") != 1
        or diagnostic.get("decision_policy") != DIAGNOSTIC_DECISION_POLICY
        or diagnostic.get("installed_git_commit") != EXPECTED_DIAGNOSTIC_COMMIT
        or diagnostic.get("rungs") != [6, 8, "required_distance_minus_1"]
        or diagnostic.get("unknown_semantics") != "fail_open_survivor"
        or not isinstance(fresh, dict)
        or fresh.get("fresh_checkpoint_required") is not True
        or fresh.get("may_consume_diagnostic_candidates") is not False
        or fresh.get("may_consume_diagnostic_proof_scores") is not False
        or fresh.get("launch_by_plan_builder") is not False
        or not isinstance(deep, dict)
        or deep.get("source_population")
        != ["result.trusted_distance_upper_bound_absent"]
        or deep.get("minimum_meaningful_replayed_lower_bound") != 9
        or not 1 <= deep.get("maximum_active_candidates", 0) <= 8
        or deep.get("durable_queue_all_remainder") is not True
        or deep.get("priority_policy")
        != (
            "threshold-survivor-first-then-descending-lower-bound-"
            "ascending-target-gap-candidate-key"
        )
        or deep.get("maximum_additional_rungs_per_candidate") != 16
        or deep.get("join_key") != "candidate_key"
        or deep.get("checkpoint_reuse_policy")
        != (
            "replay-bound-unsat-sectors-retry-only-unknown-sectors-"
            "then-both-sectors-on-new-rungs"
        )
        or deep.get("both_sectors_required_for_lower_bound") is not True
        or deep.get("unknown_semantics") != "fail_open_unresolved"
        or deep.get("positive_threshold_survivor_route")
        != "independent-exact-certificate-pipeline"
        or deep.get("fresh_ansatz_when_threshold_survivor")
        != "remain-prepared-no-automatic-launch"
        or deep.get("separate_run_required") is not True
        or deep.get("may_write_fresh_search_archive") is not False
        or deep.get("launch_by_plan_builder") is not False
        or not isinstance(joint, dict)
        or joint.get("tracks_may_be_planned_together") is not True
        or joint.get("distinct_run_ids_required") is not True
        or joint.get("distinct_artifact_roots_required") is not True
        or joint.get("distinct_checkpoint_ledgers_required") is not True
        or joint.get("retain_family_does_not_mean_reuse_fixed_ansatz") is not True
        or joint.get("fresh_search_and_old_survivor_proof_are_evidence_isolated")
        is not True
        or joint.get("bp_osd_positive_credit") is not False
        or joint.get("whole_family_abandonment_authorized") is not False
        or joint.get("automatic_launch") is not False
    ):
        raise DualTrackEvidenceError("dual-track preregistration semantics are invalid")
    required_bindings = deep.get("required_bindings")
    if required_bindings != [
        "contract_sha256",
        "decision_sha256",
        "selected_file_sha256",
        "selected_sha256",
        "structural_digest",
        "triage_digest",
        "result_sha256",
    ]:
        raise DualTrackEvidenceError("deep-proof source bindings are invalid")
    for key in ("registry",):
        target = (repo / str(fresh.get(key, ""))).resolve()
        if not target.is_relative_to(repo):
            raise DualTrackEvidenceError(f"fresh ansatz {key} escapes repository")
    return {
        **value,
        "contract_path": str(path),
        "contract_sha256": _file_sha256(path),
    }


def _replay_bound_result(
    result: Mapping[str, Any],
    selected: Mapping[str, Any],
    *,
    contract_sha256: str,
) -> dict[str, Any]:
    """Replay every proof fact later consumed by the split planner."""

    _validate_self_hash(result, "result_sha256")
    if (
        result.get("kind") != DIAGNOSTIC_KIND
        or result.get("candidate_key") != selected.get("candidate_key")
        or result.get("contract_sha256") != contract_sha256
        or result.get("selected_sha256") != _canonical_sha256(selected)
        or result.get("structural_digest") != selected.get("structural_digest")
        or result.get("n") != selected.get("n")
        or result.get("k") != selected.get("k")
        or result.get("target") != selected.get("target")
        or result.get("strata") != selected.get("strata")
    ):
        raise DualTrackEvidenceError("diagnostic result binding is inconsistent")

    claim = selected.get("claim")
    if not isinstance(claim, Mapping):
        raise DualTrackEvidenceError("selected diagnostic claim is absent")
    code = build_css_code_from_claim(claim)
    if (
        int(code.num_qudits) != selected.get("n")
        or int(code.dimension) != selected.get("k")
        or authoritative_candidate_digest(claim) != selected.get("structural_digest")
    ):
        raise DualTrackEvidenceError("diagnostic candidate reconstruction changed")
    hx, hz, lx, lz = get_code_matrices(code)
    initial = selected.get("initial_low_weight_oracle")
    if (
        not isinstance(initial, Mapping)
        or initial.get("outcome") != "UNSAT"
        or initial.get("max_weight") != 4
        or verify_css_low_weight_oracle(initial, hx, hz, lx, lz)
    ):
        raise DualTrackEvidenceError("initial d>=5 evidence does not replay")

    target = selected.get("target")
    required = target.get("required_distance") if isinstance(target, Mapping) else None
    if isinstance(required, bool) or not isinstance(required, int) or required < 1:
        raise DualTrackEvidenceError("diagnostic target is invalid")
    if result.get("stopped_reason") == "fail_open_worker_error":
        expected = {
            "final_distance_lower_bound": 5,
            "trusted_distance_upper_bound": None,
            "target_gap": max(0, required - 5),
            "rejected_by_w8": False,
            "survived_w8": True,
            "unknown_fail_open": True,
        }
        if result.get("rungs") != [] or any(
            result.get(field) != expected_value
            for field, expected_value in expected.items()
        ):
            raise DualTrackEvidenceError("fail-open worker result is inconsistent")
        return dict(result)

    thresholds = [6, 8]
    if required - 1 > 8:
        thresholds.append(required - 1)
    rungs = result.get("rungs")
    if not isinstance(rungs, list) or not rungs:
        raise DualTrackEvidenceError("diagnostic result has no replayable rungs")
    lower_bound = 5
    upper_bound: int | None = None
    rejected_by_w8 = False
    unknown = False
    for index, rung in enumerate(rungs):
        if (
            not isinstance(rung, Mapping)
            or index >= len(thresholds)
            or rung.get("threshold") != thresholds[index]
        ):
            raise DualTrackEvidenceError("diagnostic rung order is inconsistent")
        threshold = thresholds[index]
        sectors = rung.get("sectors")
        if not isinstance(sectors, Mapping) or set(sectors) != {"X", "Z"}:
            raise DualTrackEvidenceError("diagnostic rung lacks both sectors")
        outcomes: dict[str, Any] = {}
        witness_weights: list[int] = []
        for sector in ("X", "Z"):
            envelope = sectors[sector]
            evidence = envelope.get("evidence") if isinstance(envelope, Mapping) else None
            if not isinstance(evidence, Mapping):
                raise DualTrackEvidenceError("diagnostic sector evidence is absent")
            outcome = evidence.get("outcome")
            outcomes[sector] = outcome
            if outcome in {"SAT", "UNSAT"}:
                checks, logicals = css_sector_matrices(hx, hz, lx, lz, sector)
                failures = verify_low_weight_sector_evidence(
                    evidence,
                    checks,
                    logicals,
                    max_weight=threshold,
                    sector=sector,
                )
                if failures:
                    raise DualTrackEvidenceError(
                        "diagnostic sector evidence does not replay"
                    )
            elif outcome != "UNKNOWN":
                raise DualTrackEvidenceError("diagnostic sector outcome is invalid")
            if outcome == "SAT":
                witness = evidence.get("witness")
                weight = witness.get("weight") if isinstance(witness, Mapping) else None
                if isinstance(weight, bool) or not isinstance(weight, int):
                    raise DualTrackEvidenceError("diagnostic SAT witness is malformed")
                witness_weights.append(weight)
        if witness_weights:
            outcome = "SAT"
            upper_bound = min(witness_weights)
            rejected_by_w8 = threshold <= 8
        elif outcomes == {"X": "UNSAT", "Z": "UNSAT"}:
            outcome = "UNSAT"
            lower_bound = threshold + 1
        else:
            outcome = "UNKNOWN"
            unknown = True
        if (
            rung.get("outcome") != outcome
            or rung.get("distance_lower_bound_after_rung") != lower_bound
            or rung.get("distance_upper_bound_after_rung") != upper_bound
        ):
            raise DualTrackEvidenceError("diagnostic rung derivation changed")
        if outcome in {"SAT", "UNKNOWN"} and index != len(rungs) - 1:
            raise DualTrackEvidenceError("diagnostic continued after terminal rung")
    if rungs[-1].get("outcome") == "UNSAT" and len(rungs) != len(thresholds):
        raise DualTrackEvidenceError("diagnostic stopped before required next rung")
    derived = {
        "final_distance_lower_bound": lower_bound,
        "trusted_distance_upper_bound": upper_bound,
        "target_gap": max(0, required - lower_bound),
        "rejected_by_w8": rejected_by_w8,
        "survived_w8": not rejected_by_w8,
        "unknown_fail_open": unknown,
    }
    if any(result.get(field) != value for field, value in derived.items()):
        raise DualTrackEvidenceError("diagnostic result derived fields changed")
    return dict(result)


def _validate_decision(
    decision: Mapping[str, Any],
    results: list[Mapping[str, Any]],
    *,
    contract_sha256: str,
    results_identity: Mapping[str, Any],
) -> None:
    _validate_self_hash(decision, "decision_sha256")
    expected_fields = {
        "schema_version",
        "kind",
        "decision_policy",
        "sample_size",
        "rejected_by_w8",
        "rejected_by_w8_fraction",
        "survived_w8",
        "survived_w8_fraction",
        "unknown_fail_open",
        "meaningful_lb_ge_9",
        "near_target_gap_le_3",
        "action",
        "reason",
        "whole_family_abandonment_authorized",
        "bp_osd_positive_credit",
        "contract_sha256",
        "results",
        "decision_sha256",
    }
    if set(decision) != expected_fields:
        raise DualTrackEvidenceError("diagnostic decision fields are invalid")
    total = len(results)
    rejected = sum(row.get("rejected_by_w8") is True for row in results)
    survived = sum(row.get("survived_w8") is True for row in results)
    unknown = sum(row.get("unknown_fail_open") is True for row in results)
    meaningful = [
        str(row["candidate_key"])
        for row in results
        if int(row.get("final_distance_lower_bound", 0)) >= 9
    ]
    near_target = [
        str(row["candidate_key"])
        for row in results
        if int(row.get("target_gap", 10**9)) <= 3
    ]
    if survived / total >= 0.2 or meaningful or near_target:
        action = "retain_generalized_toric_family_and_targeted_deep_proof"
        reason = "survivor_or_lower_bound_signal"
    elif rejected / total >= 0.8:
        action = "change_ansatz_within_generalized_toric_family"
        reason = "low_weight_rejection_concentration"
    else:
        action = "inconclusive_collect_more_diagnostic_evidence"
        reason = "decision_thresholds_not_met"
    expected = {
        "schema_version": 1,
        "kind": DIAGNOSTIC_KIND,
        "decision_policy": DIAGNOSTIC_DECISION_POLICY,
        "sample_size": total,
        "rejected_by_w8": rejected,
        "rejected_by_w8_fraction": rejected / total,
        "survived_w8": survived,
        "survived_w8_fraction": survived / total,
        "unknown_fail_open": unknown,
        "meaningful_lb_ge_9": meaningful,
        "near_target_gap_le_3": near_target,
        "action": action,
        "reason": reason,
        "whole_family_abandonment_authorized": False,
        "bp_osd_positive_credit": False,
        "contract_sha256": contract_sha256,
        "results": dict(results_identity),
    }
    if any(decision.get(field) != value for field, value in expected.items()):
        raise DualTrackEvidenceError("diagnostic decision does not recompute")


def _deep_thresholds(result: Mapping[str, Any], required: int) -> list[int]:
    lower = int(result["final_distance_lower_bound"])
    upper = result.get("trusted_distance_upper_bound")
    ceiling = required - 1
    if isinstance(upper, int) and not isinstance(upper, bool):
        ceiling = min(ceiling, upper - 1)
    return list(range(lower, ceiling + 1)) if lower <= ceiling else []


def _diagnostic_thresholds(required: int) -> list[int]:
    thresholds = [6, 8]
    if required - 1 > 8:
        thresholds.append(required - 1)
    return thresholds


def _open_resume_ladder(
    result: Mapping[str, Any],
    required: int,
) -> list[dict[str, Any]]:
    """Resume only UNKNOWN sectors, then require both sectors on new rungs."""

    thresholds = _diagnostic_thresholds(required)
    rungs = result.get("rungs")
    if result.get("stopped_reason") == "fail_open_worker_error" or rungs == []:
        return [
            {
                "threshold": threshold,
                "retry_sectors": ["X", "Z"],
                "replayed_unsat_sectors": [],
            }
            for threshold in thresholds
        ]
    if not isinstance(rungs, list):
        raise DualTrackEvidenceError("open diagnostic result has malformed rungs")
    for index, rung in enumerate(rungs):
        if isinstance(rung, Mapping) and rung.get("outcome") == "UNKNOWN":
            sectors = rung.get("sectors")
            if not isinstance(sectors, Mapping) or set(sectors) != {"X", "Z"}:
                raise DualTrackEvidenceError(
                    "open diagnostic checkpoint lacks both sectors"
                )
            outcomes: dict[str, str] = {}
            for sector in ("X", "Z"):
                envelope = sectors[sector]
                evidence = (
                    envelope.get("evidence")
                    if isinstance(envelope, Mapping)
                    else None
                )
                outcome = (
                    evidence.get("outcome")
                    if isinstance(evidence, Mapping)
                    else None
                )
                if outcome not in {"UNSAT", "UNKNOWN"}:
                    raise DualTrackEvidenceError(
                        "UNKNOWN checkpoint has an invalid sector outcome"
                    )
                outcomes[sector] = outcome
            retry = [
                sector for sector in ("X", "Z")
                if outcomes[sector] == "UNKNOWN"
            ]
            if not retry:
                raise DualTrackEvidenceError(
                    "UNKNOWN checkpoint has no retryable sector"
                )
            ladder = [{
                "threshold": thresholds[index],
                "retry_sectors": retry,
                "replayed_unsat_sectors": [
                    sector for sector in ("X", "Z")
                    if outcomes[sector] == "UNSAT"
                ],
            }]
            ladder.extend({
                "threshold": threshold,
                "retry_sectors": ["X", "Z"],
                "replayed_unsat_sectors": [],
            } for threshold in thresholds[index + 1:])
            return ladder
    if result.get("unknown_fail_open") is True:
        raise DualTrackEvidenceError("fail-open diagnostic has no UNKNOWN rung")
    return []


def _load_replayed_diagnostic(
    diagnostic_dir: Path,
    *,
    installed_commit: str,
) -> dict[str, Any]:
    root = diagnostic_dir.resolve()
    contract_path = root / "contract.json"
    selected_path = root / "selected.jsonl"
    results_path = root / "results.jsonl"
    decision_path = root / "decision.json"
    contract = _json_object(contract_path, label="diagnostic contract")
    _validate_self_hash(contract, "contract_sha256")
    selected, selected_identity = _jsonl(selected_path, label="selected sample")
    results, results_identity = _jsonl(results_path, label="diagnostic results")
    decision = _json_object(decision_path, label="diagnostic decision")
    git_binding = contract.get("git_binding")
    if (
        contract.get("schema_version") != 1
        or contract.get("kind") != DIAGNOSTIC_KIND
        or contract.get("decision_policy") != DIAGNOSTIC_DECISION_POLICY
        or contract.get("rungs") != [6, 8, "required_distance_minus_1"]
        or contract.get("both_sectors_required_for_lower_bound") is not True
        or contract.get("both_sectors_attempted_per_rung") is not True
        or contract.get("unknown_semantics") != "fail_open_survivor"
        or contract.get("bp_osd_positive_credit") is not False
        or contract.get("selected") != selected_identity
        or contract.get("sample_size") != len(selected)
        or not isinstance(git_binding, Mapping)
        or git_binding.get("head") != installed_commit
        or git_binding.get("upstream_commit") != installed_commit
    ):
        raise DualTrackEvidenceError("diagnostic contract is incompatible")
    if not selected or len(selected) != len(results):
        raise DualTrackEvidenceError("diagnostic selected/results cardinality changed")
    keys = [row.get("candidate_key") for row in selected]
    if any(not isinstance(key, str) or not key for key in keys) or len(set(keys)) != len(keys):
        raise DualTrackEvidenceError("diagnostic candidate keys are invalid")
    replayed = []
    for selected_row, result in zip(selected, results, strict=True):
        replayed.append(_replay_bound_result(
            result,
            selected_row,
            contract_sha256=str(contract["contract_sha256"]),
        ))
    _validate_decision(
        decision,
        replayed,
        contract_sha256=str(contract["contract_sha256"]),
        results_identity=results_identity,
    )
    return {
        "root": root,
        "contract": contract,
        "contract_identity": _file_identity(contract_path),
        "selected": selected,
        "selected_identity": selected_identity,
        "results": replayed,
        "results_identity": results_identity,
        "decision": decision,
        "decision_identity": _file_identity(decision_path),
    }


def build_dual_track_plan(
    diagnostic_dir: Path,
    *,
    repo_dir: Path,
    preregistration_path: Path,
) -> dict[str, Any]:
    """Build a self-hashed, no-launch plan for the two isolated tracks."""

    repo = repo_dir.resolve()
    prereg = load_dual_track_contract(preregistration_path, repo_dir=repo)
    diagnostic_spec = prereg["diagnostic_contract"]
    diagnostic = _load_replayed_diagnostic(
        diagnostic_dir,
        installed_commit=diagnostic_spec["installed_git_commit"],
    )
    fresh_spec = prereg["fresh_ansatz_track"]
    registry_path = Path(str(fresh_spec["registry"]))
    registry = load_template_registry(repo_dir=repo, registry_path=registry_path)
    template = registry.template(str(fresh_spec["template_id"]))
    if (
        template.representation_id != fresh_spec["representation_id"]
        or not template.proof_compatible
        or not template.launch_compatible
        or "representation_change_required"
        not in template.allowed_machine_regimes
    ):
        raise DualTrackEvidenceError("fresh ansatz template is incompatible")

    selected_by_key = {
        str(row["candidate_key"]): row for row in diagnostic["selected"]
    }
    result_by_key = {
        str(row["candidate_key"]): row for row in diagnostic["results"]
    }
    meaningful = diagnostic["decision"]["meaningful_lb_ge_9"]
    meaningful_set = set(meaningful)
    # A meaningful lower bound is a prioritisation signal, not the source
    # boundary.  The durable proof queue must contain every candidate still
    # lacking a trusted upper bound and must not pull in already excluded
    # LB>=9 rows merely because they appear in the decision summary.
    source_keys = [
        str(result["candidate_key"])
        for result in diagnostic["results"]
        if result.get("trusted_distance_upper_bound") is None
    ]
    candidates = []
    for key in source_keys:
        selected = selected_by_key.get(key)
        result = result_by_key.get(key)
        if selected is None or result is None:
            raise DualTrackEvidenceError("deep-proof candidate is not source-bound")
        triage_digest = selected.get("triage_digest")
        if not isinstance(triage_digest, str) or not triage_digest:
            raise DualTrackEvidenceError("deep-proof candidate lacks triage digest")
        lower = int(result["final_distance_lower_bound"])
        required = int(selected["target"]["required_distance"])
        if key in meaningful_set and lower < prereg[
            "targeted_deep_proof_track"
        ]["minimum_meaningful_replayed_lower_bound"]:
            raise DualTrackEvidenceError("deep-proof candidate lost LB>=9")
        open_candidate = (
            result.get("unknown_fail_open") is True
            or result.get("trusted_distance_upper_bound") is None
        )
        resume_ladder = (
            _open_resume_ladder(result, required)
            if result.get("unknown_fail_open") is True
            else []
        )
        resume_thresholds = [
            int(entry["threshold"]) for entry in resume_ladder
        ]
        exactification_thresholds = (
            [] if open_candidate else _deep_thresholds(result, required)
        )
        planned_thresholds = resume_thresholds or exactification_thresholds
        if len(planned_thresholds) > int(
            prereg["targeted_deep_proof_track"][
                "maximum_additional_rungs_per_candidate"
            ]
        ):
            raise DualTrackEvidenceError(
                "deep-proof exactification exceeds preregistered rung budget"
            )
        threshold_survivor = lower >= required
        if threshold_survivor:
            next_route = "independent_exact_certificate"
        elif resume_thresholds:
            next_route = "diagnostic_checkpoint_retry"
        elif exactification_thresholds:
            next_route = "targeted_exactification"
        else:
            next_route = "no_additional_proof_rung"
        candidates.append({
            "candidate_key": key,
            "structural_digest": selected["structural_digest"],
            "triage_digest": triage_digest,
            "claim": selected["claim"],
            "n": selected["n"],
            "k": selected["k"],
            "target": selected["target"],
            "strata": selected["strata"],
            "replayed_distance_lower_bound": lower,
            "replayed_distance_upper_bound": result[
                "trusted_distance_upper_bound"
            ],
            "target_gap": result["target_gap"],
            "resume_thresholds": resume_thresholds,
            "resume_ladder": resume_ladder,
            "exactification_thresholds": exactification_thresholds,
            "threshold_survivor": threshold_survivor,
            "open_fail_open": result.get("unknown_fail_open") is True,
            "open_without_trusted_upper_bound": (
                result.get("trusted_distance_upper_bound") is None
            ),
            "source_reasons": [
                reason
                for condition, reason in (
                    (
                        result.get("unknown_fail_open") is True,
                        "unknown_fail_open",
                    ),
                    (
                        result.get("trusted_distance_upper_bound") is None,
                        "trusted_upper_bound_absent",
                    ),
                    (key in meaningful_set, "meaningful_lb_ge_9"),
                )
                if condition
            ],
            "next_route": next_route,
            "already_exact": (
                isinstance(result["trusted_distance_upper_bound"], int)
                and result["trusted_distance_upper_bound"] == lower
            ),
            "source_binding": {
                "contract_sha256": diagnostic["contract"]["contract_sha256"],
                "decision_sha256": diagnostic["decision"]["decision_sha256"],
                "selected_file_sha256": diagnostic["selected_identity"]["sha256"],
                "selected_sha256": _canonical_sha256(selected),
                "structural_digest": selected["structural_digest"],
                "triage_digest": triage_digest,
                "result_sha256": result["result_sha256"],
            },
        })
    candidates.sort(key=lambda row: (
        -int(row["threshold_survivor"]),
        -int(row["replayed_distance_lower_bound"]),
        int(row["target_gap"]),
        str(row["candidate_key"]),
    ))
    limit = int(
        prereg["targeted_deep_proof_track"]["maximum_active_candidates"]
    )
    for index, candidate in enumerate(candidates):
        candidate["queue_position"] = index
        candidate["scheduling_status"] = (
            "ACTIVE_FIRST_BATCH" if index < limit else "QUEUED_DURABLE"
        )
    active_candidates = candidates[:limit]
    queued_candidates = candidates[limit:]
    certificate_candidates = [
        row for row in candidates if row["threshold_survivor"]
    ]
    exactification_candidates = [
        row
        for row in candidates
        if not row["threshold_survivor"] and row["exactification_thresholds"]
    ]
    retry_candidates = [
        row
        for row in candidates
        if not row["threshold_survivor"] and row["resume_thresholds"]
    ]
    actionable = [
        row
        for row in active_candidates
        if row["threshold_survivor"]
        or row["exactification_thresholds"]
        or row["resume_thresholds"]
    ]

    payload = {
        "schema_version": DUAL_TRACK_SCHEMA_VERSION,
        "kind": DUAL_TRACK_PLAN_KIND,
        "preregistration": {
            "path": prereg["contract_path"],
            "sha256": prereg["contract_sha256"],
        },
        "diagnostic": {
            "root": str(diagnostic["root"]),
            "contract": diagnostic["contract_identity"],
            "contract_sha256": diagnostic["contract"]["contract_sha256"],
            "selected": diagnostic["selected_identity"],
            "results": diagnostic["results_identity"],
            "decision": diagnostic["decision_identity"],
            "decision_sha256": diagnostic["decision"]["decision_sha256"],
            "installed_git_commit": diagnostic_spec["installed_git_commit"],
        },
        "machine_decision": {
            "action": diagnostic["decision"]["action"],
            "reason": diagnostic["decision"]["reason"],
            "meaningful_lb_ge_9": list(meaningful),
            "near_target_gap_le_3": list(
                diagnostic["decision"]["near_target_gap_le_3"]
            ),
        },
        "fresh_ansatz_track": {
            "status": (
                "PREPARED_HELD_FOR_CERTIFICATE_DECISION"
                if certificate_candidates
                else "READY_NOT_LAUNCHED"
            ),
            "registry_path": registry.registry_path,
            "registry_sha256": registry.registry_sha256,
            "template_id": template.template_id,
            "template_version": template.template_version,
            "template_entry_sha256": template.entry_sha256,
            "representation_id": template.representation_id,
            "checkpoint_compatibility_group": (
                template.checkpoint_compatibility_group
            ),
            "fresh_checkpoint_required": True,
            "diagnostic_candidates_imported": 0,
            "diagnostic_proof_scores_imported": 0,
            "launch_authorized": False,
        },
        "targeted_deep_proof_track": {
            "status": (
                "PLAN_READY_DRIVER_REQUIRED_NOT_LAUNCHED"
                if actionable
                else "NO_ACTIONABLE_RUNG"
            ),
            "source_policy": (
                "all-candidates-without-trusted-upper-bound"
            ),
            "candidate_count": len(candidates),
            "active_candidate_count": len(active_candidates),
            "queued_candidate_count": len(queued_candidates),
            "actionable_candidate_count": len(actionable),
            "independent_certificate_candidate_count": len(
                certificate_candidates
            ),
            "targeted_exactification_candidate_count": len(
                exactification_candidates
            ),
            "diagnostic_checkpoint_retry_candidate_count": len(
                retry_candidates
            ),
            "active_candidate_limit": limit,
            "durable_queue_all_remainder": True,
            "priority_policy": prereg["targeted_deep_proof_track"][
                "priority_policy"
            ],
            "checkpoint_reuse_policy": prereg[
                "targeted_deep_proof_track"
            ]["checkpoint_reuse_policy"],
            "stage3_ranked_schema_directly_consumable": False,
            "dedicated_resumable_sector_driver_required": True,
            "candidates": candidates,
            "both_sectors_required_for_lower_bound": True,
            "unknown_semantics": "fail_open_unresolved",
            "fresh_search_archive_write_authorized": False,
            "launch_authorized": False,
        },
        "joint_decision": {
            "action": (
                "prioritize_independent_exact_certificate_keep_fresh_ansatz_prepared"
                if certificate_candidates
                else "prepare_fresh_richer_ansatz_and_separate_targeted_deep_proof"
            ),
            "retain_family_does_not_mean_reuse_fixed_ansatz": True,
            "evidence_isolated": True,
            "distinct_run_ids_required": True,
            "distinct_artifact_roots_required": True,
            "distinct_checkpoint_ledgers_required": True,
            "bp_osd_positive_credit": False,
            "whole_family_abandonment_authorized": False,
            "automatic_launch": False,
        },
    }
    return {**payload, "plan_sha256": _canonical_sha256(payload)}


__all__ = [
    "DUAL_TRACK_CONTRACT_KIND",
    "DUAL_TRACK_PLAN_KIND",
    "DualTrackEvidenceError",
    "build_dual_track_plan",
    "load_dual_track_contract",
]
