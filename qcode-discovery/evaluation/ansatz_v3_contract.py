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
) -> dict[str, Any]:
    """Authorize only a manual family transition after complete negatives.

    This function never launches a different family.  It emits a replayable
    eligibility decision and remains blocked for every missing, unknown, or
    merely decoder-estimated candidate.
    """

    blockers: list[str] = []
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
    if not (
        isinstance(campaign, Mapping)
        and campaign.get("sealed") is True
        and campaign.get("rounds_completed")
        == contract.get("search_budget", {}).get("rounds")
        and campaign.get("pending_round") is None
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
    ):
        blockers.append("realized_finite_domain_not_fully_audited")

    stage2 = evidence.get("stage2")
    if not (
        isinstance(stage2, Mapping)
        and stage2.get("ranked_snapshot_exhausted") is True
        and stage2.get("selection_ledger_pending") is None
        and stage2.get("unresolved_candidates") == 0
        and stage2.get("unknown_candidates") == 0
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

    audit = evidence.get("formal_audit")
    counts = audit.get("volume_counts") if isinstance(audit, Mapping) else None
    required_counts = {
        str(row["volume"]): row["quota"]
        for row in quota_contract.get("volume_quotas", [])
    }
    if not (
        isinstance(audit, Mapping)
        and audit.get("unfilled_slots") == 0
        and isinstance(counts, Mapping)
        and all(counts.get(volume) == quota for volume, quota in required_counts.items())
    ):
        blockers.append("formal_audit_quota_incomplete")
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
]
