"""Preregistration and fail-closed family-switch gate for ansatz v3."""

from __future__ import annotations

import hashlib
import json
from collections.abc import Mapping
from pathlib import Path
from typing import Any


FINITE_DOMAIN_SCHEMA_VERSION = 1
FINITE_DOMAIN_KIND = "qcode-preregistered-finite-search-domain"
FAMILY_SWITCH_EVIDENCE_KIND = "qcode-ansatz-v3-family-switch-evidence"
TRUSTED_UPPER_BOUND_KINDS = frozenset({
    "replayed-logical-witness",
    "replayed-low-weight-sat",
    "exact-distance",
})


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _canonical_sha256(value: Any) -> str:
    return hashlib.sha256(json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")).hexdigest()


def _regular_json(path: Path, label: str) -> dict[str, Any]:
    lexical_path = Path(path)
    if lexical_path.is_symlink() or not lexical_path.is_file():
        raise ValueError(f"{label} must be a regular file: {lexical_path}")
    path = lexical_path.resolve(strict=True)
    if not path.is_file():
        raise ValueError(f"{label} must be a regular file: {path}")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot read {label}: {exc}") from exc
    if not isinstance(value, dict):
        raise ValueError(f"{label} must contain an object")
    return value


def _regular_jsonl(path: Path, label: str) -> list[dict[str, Any]]:
    lexical_path = Path(path)
    if lexical_path.is_symlink() or not lexical_path.is_file():
        raise ValueError(f"{label} must be a regular file: {lexical_path}")
    path = lexical_path.resolve(strict=True)
    if not path.is_file():
        raise ValueError(f"{label} must be a regular file: {path}")
    payload = path.read_bytes()
    if payload and not payload.endswith(b"\n"):
        raise ValueError(f"{label} ends in a partial row")
    rows: list[dict[str, Any]] = []
    for number, raw in enumerate(payload.splitlines(), 1):
        if not raw:
            continue
        try:
            row = json.loads(raw)
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise ValueError(f"{label}:{number} is invalid: {exc}") from exc
        if not isinstance(row, dict):
            raise ValueError(f"{label}:{number} is not an object")
        rows.append(row)
    return rows


def _descriptor_rows(descriptor: Mapping[str, Any]) -> list[dict[str, Any]]:
    path_text = descriptor.get("path")
    if not isinstance(path_text, str) or not path_text:
        raise ValueError("realized-domain source batch has no path")
    lexical_path = Path(path_text)
    rows = _regular_jsonl(lexical_path, "realized-domain source batch")
    path = lexical_path.resolve(strict=True)
    payload = path.read_bytes()
    if descriptor.get("sha256") != hashlib.sha256(payload).hexdigest() or (
        descriptor.get("bytes") != len(payload)
        or descriptor.get("rows") != len(rows)
    ):
        raise ValueError("realized-domain source batch identity changed")
    return rows


def _replay_stage2_upper_bound(
    row: dict[str, Any],
    *,
    canonical_digest: str,
    ledger_dir: Path,
) -> int:
    """Return only a freshly replayed mathematical upper bound."""

    from evaluation.construction import build_css_code_from_claim
    from humanize.reviewer import replay_search_oracle_upper_bound_geometry
    from scripts.audit_candidate_pool import (
        _construction_candidate,
        _stage2_audit_cache_binding,
        state_paths,
    )
    from scripts.screen_frontier_xor import (
        classify_xor_results,
        load_replayable_sectors,
        verify_bb_translation_symmetry,
    )

    geometry = replay_search_oracle_upper_bound_geometry(row)
    if isinstance(geometry, Mapping) and type(geometry.get("weight")) is int:
        code = build_css_code_from_claim(row)
        if (
            int(code.num_qudits) != row.get("n")
            or int(code.dimension) != row.get("k")
        ):
            raise ValueError("candidate parameters changed during witness replay")
        return int(geometry["weight"])

    candidate = _construction_candidate(row, canonical_digest)
    if isinstance(candidate.get("construction"), Mapping):
        # The installed v3 representation is BB/twisted-torus.  Do not
        # silently extend this gate to another proof schema.
        raise ValueError("compact Stage-2 witness replay is not installed")
    symmetry = verify_bb_translation_symmetry(candidate)
    if symmetry.get("verified") is not True:
        raise ValueError("Stage-2 translation symmetry did not replay")
    sectors = load_replayable_sectors(
        state_paths(ledger_dir, canonical_digest)["audit"],
        candidate,
        threshold_only=True,
        translation_symmetry=symmetry,
        expected_cache_binding=_stage2_audit_cache_binding(candidate, symmetry),
    )
    if classify_xor_results(
        sectors,
        required_distance=int(candidate["required_distance"]),
        threshold_only=True,
        symmetry_coverage_verified=True,
    ) != "REJECTED":
        raise ValueError("candidate has no replayed Stage-2 rejecting witness")
    weights = [
        int(sector["objective"])
        for sector in sectors
        if sector.get("witness_verified") is True
        and type(sector.get("objective")) is int
    ]
    if not weights:
        raise ValueError("Stage-2 rejection has no replayed witness weight")
    code = build_css_code_from_claim(candidate)
    if (
        int(code.num_qudits) != row.get("n")
        or int(code.dimension) != row.get("k")
    ):
        raise ValueError("candidate parameters changed during witness replay")
    return min(weights)


def replay_family_switch_artifacts(
    *,
    realized_domain_manifest_path: Path,
    stage2_selection_ledger_path: Path,
    contract: Mapping[str, Any],
    quota_contract: Mapping[str, Any],
) -> dict[str, Any]:
    """Replay the concrete Stage-1 domain and complete Stage-2 ledger.

    Self-declared ``replayed=true`` rows are deliberately not inputs to this
    function.  Eligibility is reconstructed from immutable source bytes and
    current-source mathematical witness replay.
    """

    from evaluation.selection_ledger import (
        snapshot_identity_sha256,
        validate_selection_ledger,
    )
    from humanize.state import code_key
    from scripts.audit_candidate_pool import _load_ranked_snapshot

    lexical_manifest_path = Path(realized_domain_manifest_path)
    manifest = _regular_json(
        lexical_manifest_path,
        "realized-domain manifest",
    )
    manifest_path = lexical_manifest_path.resolve(strict=True)
    unsigned_manifest = dict(manifest)
    manifest_sha256 = unsigned_manifest.pop("manifest_sha256", None)
    finite_binding = manifest.get("finite_domain_contract")
    quota_binding = manifest.get("formal_audit_quota")
    if (
        manifest.get("schema_version") != 1
        or manifest.get("kind") != "qcode-ansatz-v3-realized-finite-domain"
        or manifest.get("manifest_complete") is not True
        or manifest.get("representation_id") != contract.get("representation_id")
        or not isinstance(manifest_sha256, str)
        or manifest_sha256 != _canonical_sha256(unsigned_manifest)
        or not isinstance(finite_binding, Mapping)
        or finite_binding.get("sha256") != contract.get("contract_sha256")
        or not isinstance(quota_binding, Mapping)
        or quota_binding.get("sha256") != quota_contract.get("contract_sha256")
        or quota_binding.get("complete") is not True
        or quota_binding.get("unfilled_slots") != 0
    ):
        raise ValueError("realized-domain manifest is invalid or unbound")

    # A canonical self-hash detects accidental changes but cannot establish
    # that a manifest came from the sealed Stage-1 transaction history.  Rebuild
    # it from the bound state/round artifacts and demand byte-for-byte semantic
    # identity before accepting any claimed finite-domain coverage.
    state_binding = manifest.get("state")
    state_path_text = (
        state_binding.get("path")
        if isinstance(state_binding, Mapping)
        else None
    )
    if not isinstance(state_path_text, str) or not state_path_text:
        raise ValueError("realized-domain manifest has no Stage-1 state path")
    state_path = Path(state_path_text)
    if state_path.is_symlink() or not state_path.is_file():
        raise ValueError("realized-domain Stage-1 state is not a regular file")
    state_path = state_path.resolve(strict=True)
    if (
        not isinstance(state_binding, Mapping)
        or state_binding.get("sha256") != _sha256(state_path)
    ):
        raise ValueError("realized-domain Stage-1 state identity changed")
    finite_path = contract.get("contract_path")
    quota_path = quota_contract.get("contract_path")
    if not isinstance(finite_path, str) or not isinstance(quota_path, str):
        raise ValueError("family-switch contracts have no source paths")
    from scripts.build_ansatz_v3_domain_manifest import build_manifest

    rebuilt_manifest = build_manifest(
        state_path.parent,
        finite_domain_path=Path(finite_path),
        quota_path=Path(quota_path),
    )
    if rebuilt_manifest != manifest:
        raise ValueError(
            "realized-domain manifest does not replay from Stage-1 artifacts"
        )

    raw_batches = manifest.get("source_batches")
    if not isinstance(raw_batches, list) or not raw_batches:
        raise ValueError("realized-domain manifest has no source batches")
    domain_rows = [
        row
        for descriptor in raw_batches
        if isinstance(descriptor, Mapping)
        for row in _descriptor_rows(descriptor)
    ]
    domain_keys = {code_key(row) for row in domain_rows}
    if (
        len(domain_keys) != manifest.get("total_unique_candidates")
        or _canonical_sha256(sorted(domain_keys))
        != manifest.get("candidate_key_set_sha256")
    ):
        raise ValueError("realized-domain candidate key set did not replay")

    lexical_ledger_path = Path(stage2_selection_ledger_path)
    ledger = _regular_json(
        lexical_ledger_path,
        "Stage-2 selection ledger",
    )
    ledger_path = lexical_ledger_path.resolve(strict=True)
    prefix = f"{ledger_path.name}.ranked-snapshot"
    snapshot_manifest_path = ledger_path.with_name(f"{prefix}.manifest.json")
    snapshot_manifest = _regular_json(
        snapshot_manifest_path, "Stage-2 ranked snapshot manifest"
    )
    binding = snapshot_manifest.get("binding")
    inputs = binding.get("inputs") if isinstance(binding, Mapping) else None
    if not isinstance(inputs, list) or any(
        not isinstance(item, Mapping) or not isinstance(item.get("path"), str)
        for item in inputs
    ):
        raise ValueError("Stage-2 ranked snapshot input binding is malformed")
    snapshot = _load_ranked_snapshot(
        ledger_path,
        [Path(str(item["path"])) for item in inputs],
        target_mode=str(contract.get("target_mode")),
    )
    if snapshot is None:
        raise ValueError("Stage-2 ranked snapshot did not replay")
    validated_ledger = validate_selection_ledger(
        ledger,
        binding_sha256=str(ledger.get("binding_sha256")),
        snapshot_identity_sha256_value=snapshot_identity_sha256(snapshot.identity),
        snapshot_rows=snapshot.rows,
        eligible_rows=snapshot.eligible_rows,
    )
    if (
        validated_ledger.get("pending") is not None
        or validated_ledger.get("deferred_pages") != []
        or validated_ledger.get("cursor") != snapshot.eligible_rows
    ):
        raise ValueError("Stage-2 selection ledger is pending or unexhausted")

    snapshot_rows = _regular_jsonl(snapshot.snapshot_path, "Stage-2 ranked snapshot")
    snapshot_keys = {code_key(row) for row in snapshot_rows}
    if snapshot_keys != domain_keys or len(snapshot_rows) != len(domain_keys):
        raise ValueError("Stage-2 candidate key set differs from realized domain")
    eligible_digests = []
    all_digests = []
    for index, row in enumerate(snapshot_rows):
        identity = row.get("triage_identity")
        digest = identity.get("canonical_digest") if isinstance(identity, Mapping) else None
        if not isinstance(digest, str) or not digest or digest in all_digests:
            raise ValueError("Stage-2 ranked candidate digest is malformed")
        all_digests.append(digest)
        if index < snapshot.eligible_rows:
            eligible_digests.append(digest)
    if validated_ledger.get("committed_digests") != eligible_digests:
        raise ValueError("Stage-2 ledger does not commit the eligible candidate set")

    replayed = []
    for row, digest in zip(snapshot_rows, all_digests, strict=True):
        weight = _replay_stage2_upper_bound(
            row,
            canonical_digest=digest,
            ledger_dir=ledger_path.parent,
        )
        n, k = row.get("n"), row.get("k")
        if (
            type(n) is not int
            or type(k) is not int
            or n < 1
            or k < 1
            or weight < 1
            or k * weight * weight > 12 * n
        ):
            raise ValueError("replayed witness does not exclude strict FOM > 12")
        replayed.append({
            "canonical_digest": digest,
            "candidate_key": code_key(row),
            "n": n,
            "k": k,
            "trusted_upper_bound": {
                "kind": "replayed-logical-witness",
                "replayed": True,
                "weight": weight,
            },
            "fom_gt_12_excluded": True,
        })
    candidate_set_sha256 = _canonical_sha256(replayed)
    formal_audit = {
        "unfilled_slots": quota_binding["unfilled_slots"],
        "volume_counts": dict(quota_binding["volume_counts"]),
    }
    if quota_contract.get("schema_version") == 2:
        coverage = quota_binding.get("formal_audit_coverage")
        if (
            not isinstance(coverage, Mapping)
            or not isinstance(
                coverage.get("gate_satisfied_components"), Mapping
            )
            or coverage["gate_satisfied_components"].get(
                "coverage_components_satisfied"
            ) is not True
        ):
            raise ValueError(
                "realized-domain formal-audit science coverage is incomplete"
            )
        formal_audit["formal_audit_coverage"] = dict(coverage)
    return {
        "realized_domain_manifest_path": str(manifest_path),
        "realized_domain_manifest_file_sha256": _sha256(manifest_path),
        "realized_domain_manifest_sha256": manifest_sha256,
        "stage2_selection_ledger_path": str(ledger_path),
        "stage2_selection_ledger_file_sha256": _sha256(ledger_path),
        "stage2_ranked_snapshot_manifest_path": str(snapshot.manifest_path),
        "stage2_ranked_snapshot_manifest_file_sha256": _sha256(snapshot.manifest_path),
        "candidate_key_set_sha256": _canonical_sha256(sorted(domain_keys)),
        "replayed_candidate_set_sha256": candidate_set_sha256,
        "total_unique_candidates": len(domain_keys),
        "candidates": replayed,
        "campaign": dict(manifest["state"]),
        "formal_audit": formal_audit,
    }


def load_finite_domain_contract(
    path: Path,
    *,
    representation_id: str | None = None,
    rounds: int | None = None,
    iterations_per_round: int | None = None,
) -> dict[str, Any]:
    path = Path(path).resolve()
    if path.is_symlink() or not path.is_file():
        raise ValueError(f"finite-domain contract must be a regular file: {path}")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot read finite-domain contract: {exc}") from exc
    required = {
        "schema_version",
        "kind",
        "domain_id",
        "representation_id",
        "family_id",
        "checkpoint_compatibility_group",
        "geometry_contract",
        "target_mode",
        "fom_threshold",
        "search_budget",
        "support_domain",
        "published_target_volumes",
        "control_volumes",
        "mandatory_formal_audit_volumes",
        "formal_audit_quota",
        "blind_calibration",
        "family_switch_preconditions",
        "allowed_next_family_examples",
        "automatic_family_switch",
    }
    if not isinstance(value, dict) or set(value) != required:
        raise ValueError("finite-domain contract fields are invalid")
    budget = value["search_budget"]
    support = value["support_domain"]
    blind = value["blind_calibration"]
    if (
        value["schema_version"] != FINITE_DOMAIN_SCHEMA_VERSION
        or value["kind"] != FINITE_DOMAIN_KIND
        or value["family_id"] != "generalized-toric-bb"
        or value["target_mode"] != "scalar-fom-strict-v1"
        or value["fom_threshold"] != 12.0
        or value["automatic_family_switch"] is not False
        or not isinstance(budget, dict)
        or set(budget) != {
            "rounds",
            "iterations_per_round",
            "maximum_raw_support_proposals_per_lattice",
            "maximum_candidates_per_lattice",
        }
        or not isinstance(support, dict)
        or support.get("complete_supports_evolved") is not True
        or support.get("allowed_splits")
        != [[2, 4], [4, 2], [2, 3], [3, 2], [2, 2], [3, 3]]
        or support.get("maximum_total_terms") != 6
        or support.get("fixed_monomials") != []
        or support.get("published_anchor_injection") is not False
        or not isinstance(blind, dict)
        or blind.get("search_may_read_anchor_manifest") is not False
        or any(blind.get(field) != 0 for field in (
            "fitness_credit", "novelty_credit", "coverage_credit"
        ))
        or value["mandatory_formal_audit_volumes"] != [127, 132]
        or not isinstance(value["family_switch_preconditions"], list)
        or "no_unresolved_or_unknown_candidate"
        not in value["family_switch_preconditions"]
    ):
        raise ValueError("finite-domain contract semantics are invalid")
    for field in budget:
        if type(budget[field]) is not int or budget[field] < 1:
            raise ValueError(f"finite-domain search_budget.{field} is invalid")
    if representation_id is not None and value["representation_id"] != representation_id:
        raise ValueError("finite-domain representation is incompatible")
    if rounds is not None and budget["rounds"] != rounds:
        raise ValueError("finite-domain round budget is incompatible")
    if (
        iterations_per_round is not None
        and budget["iterations_per_round"] != iterations_per_round
    ):
        raise ValueError("finite-domain iteration budget is incompatible")
    return {
        **value,
        "contract_path": str(path),
        "contract_sha256": _sha256(path),
    }


def family_switch_decision(
    evidence: Mapping[str, Any],
    *,
    contract: Mapping[str, Any],
    quota_contract: Mapping[str, Any],
    realized_domain_manifest_path: Path | None = None,
    stage2_selection_ledger_path: Path | None = None,
) -> dict[str, Any]:
    """Authorize only a manual family transition after complete negatives.

    This function never launches a different family.  It emits a replayable
    eligibility decision and remains blocked for every missing, unknown, or
    merely decoder-estimated candidate.
    """

    blockers: list[str] = []
    replay: dict[str, Any] | None = None
    if (
        realized_domain_manifest_path is None
        or stage2_selection_ledger_path is None
    ):
        blockers.append("bound_artifact_replay_missing")
    else:
        try:
            replay = replay_family_switch_artifacts(
                realized_domain_manifest_path=realized_domain_manifest_path,
                stage2_selection_ledger_path=stage2_selection_ledger_path,
                contract=contract,
                quota_contract=quota_contract,
            )
        except (OSError, TypeError, ValueError) as exc:
            blockers.append("bound_artifact_replay_failed")
    if (
        not isinstance(evidence, Mapping)
        or evidence.get("schema_version") != 1
        or evidence.get("kind") != FAMILY_SWITCH_EVIDENCE_KIND
    ):
        blockers.append("invalid_evidence_schema")
        evidence = {}
    if evidence.get("representation_id") != contract.get("representation_id"):
        blockers.append("representation_mismatch")
    if evidence.get("finite_domain_contract_sha256") != contract.get(
        "contract_sha256"
    ):
        blockers.append("finite_domain_contract_unbound")
    if evidence.get("formal_audit_quota_sha256") != quota_contract.get(
        "contract_sha256"
    ):
        blockers.append("formal_audit_quota_unbound")

    campaign = evidence.get("campaign")
    replay_campaign = replay.get("campaign") if replay is not None else None
    if not (
        isinstance(campaign, Mapping)
        and campaign.get("sealed") is True
        and campaign.get("rounds_completed")
        == contract.get("search_budget", {}).get("rounds")
        and campaign.get("pending_round") is None
        and isinstance(replay_campaign, Mapping)
        and replay_campaign.get("status") == "search-complete"
        and replay_campaign.get("rounds_completed")
        == campaign.get("rounds_completed")
        and replay_campaign.get("pending_round") is None
    ):
        blockers.append("campaign_budget_not_sealed")

    domain = evidence.get("realized_domain")
    total_unique = domain.get("total_unique_candidates") if isinstance(domain, Mapping) else None
    audited_unique = domain.get("audited_unique_candidates") if isinstance(domain, Mapping) else None
    if not (
        isinstance(domain, Mapping)
        and domain.get("manifest_complete") is True
        and type(total_unique) is int
        and total_unique > 0
        and audited_unique == total_unique
        and replay is not None
        and total_unique == replay.get("total_unique_candidates")
        and domain.get("manifest_sha256")
        == replay.get("realized_domain_manifest_sha256")
        and domain.get("candidate_key_set_sha256")
        == replay.get("candidate_key_set_sha256")
    ):
        blockers.append("realized_finite_domain_not_fully_audited")

    stage2 = evidence.get("stage2")
    if not (
        isinstance(stage2, Mapping)
        and stage2.get("ranked_snapshot_exhausted") is True
        and stage2.get("selection_ledger_pending") is None
        and stage2.get("unresolved_candidates") == 0
        and stage2.get("unknown_candidates") == 0
        and replay is not None
        and stage2.get("selection_ledger_sha256")
        == replay.get("stage2_selection_ledger_file_sha256")
        and stage2.get("replayed_candidate_set_sha256")
        == replay.get("replayed_candidate_set_sha256")
    ):
        blockers.append("stage2_unresolved_or_unexhausted")

    candidates = evidence.get("candidates")
    if not isinstance(candidates, list) or not candidates:
        blockers.append("candidate_upper_bounds_missing")
    else:
        seen: set[str] = set()
        invalid = False
        for row in candidates:
            upper = row.get("trusted_upper_bound") if isinstance(row, Mapping) else None
            digest = row.get("canonical_digest") if isinstance(row, Mapping) else None
            n = row.get("n") if isinstance(row, Mapping) else None
            k = row.get("k") if isinstance(row, Mapping) else None
            weight = upper.get("weight") if isinstance(upper, Mapping) else None
            excludes_strict_fom = (
                type(n) is int
                and n > 0
                and type(k) is int
                and k > 0
                and type(weight) is int
                and weight > 0
                and k * weight * weight <= 12 * n
            )
            if (
                not isinstance(row, Mapping)
                or not isinstance(digest, str)
                or not digest
                or digest in seen
                or row.get("fom_gt_12_excluded") is not True
                or not excludes_strict_fom
                or not isinstance(upper, Mapping)
                or upper.get("replayed") is not True
                or upper.get("kind") not in TRUSTED_UPPER_BOUND_KINDS
            ):
                invalid = True
                continue
            seen.add(digest)
        if invalid or (type(total_unique) is int and len(seen) != total_unique):
            blockers.append("not_every_candidate_has_trusted_excluding_upper_bound")
        if replay is None or candidates != replay.get("candidates"):
            blockers.append("candidate_witness_replay_mismatch")

    audit = evidence.get("formal_audit")
    counts = audit.get("volume_counts") if isinstance(audit, Mapping) else None
    replay_audit = replay.get("formal_audit") if replay is not None else None
    required_counts = {
        str(row["volume"]): row["quota"]
        for row in quota_contract.get("volume_quotas", [])
    }
    if not (
        isinstance(audit, Mapping)
        and audit.get("unfilled_slots") == 0
        and isinstance(counts, Mapping)
        and all(counts.get(volume) == quota for volume, quota in required_counts.items())
        and isinstance(replay_audit, Mapping)
        and dict(audit) == dict(replay_audit)
    ):
        blockers.append("formal_audit_quota_incomplete")
    if quota_contract.get("schema_version") == 2:
        coverage = (
            audit.get("formal_audit_coverage")
            if isinstance(audit, Mapping)
            else None
        )
        if (
            not isinstance(coverage, Mapping)
            or not isinstance(
                coverage.get("gate_satisfied_components"), Mapping
            )
            or coverage["gate_satisfied_components"].get(
                "coverage_components_satisfied"
            ) is not True
        ):
            blockers.append("formal_audit_science_coverage_incomplete")
    if evidence.get("trusted_novel_wins") != 0:
        blockers.append("trusted_novel_win_requires_result_review_not_family_switch")
    if evidence.get("unresolved_items") not in ([], 0):
        blockers.append("unresolved_items_present")

    blockers = sorted(set(blockers))
    return {
        "schema_version": 1,
        "kind": "qcode-ansatz-v3-family-switch-decision",
        "representation_id": contract.get("representation_id"),
        "eligible_for_manual_family_transition": not blockers,
        "automatic_family_switch": False,
        "block_reasons": blockers,
        "artifact_replay": replay,
        "allowed_next_family_examples": list(
            contract.get("allowed_next_family_examples", [])
        ) if not blockers else [],
        "semantics": (
            "eligibility evidence only; a reviewer cannot launch an uninstalled "
            "or incompatible representation"
        ),
    }


__all__ = [
    "FAMILY_SWITCH_EVIDENCE_KIND",
    "family_switch_decision",
    "load_finite_domain_contract",
    "replay_family_switch_artifacts",
]
