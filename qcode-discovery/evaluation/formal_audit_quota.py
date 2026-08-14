"""Deterministic preregistered Stage-1 formal-audit quotas.

This module controls *which* otherwise eligible candidates receive scarce
formal audits.  It never supplies distance evidence.  Candidate priority
within a slot is proof-safe and BP/OSD magnitudes are deliberately absent
from every stratum and tie-break defined here.
"""

from __future__ import annotations

import hashlib
import json
import re
from collections import Counter
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any

from evaluation.algebraic_mechanisms import (
    RELATION_TYPES,
    classify_algebraic_mechanism,
)
from evaluation.geometry import candidate_geometry
from evaluation.target_policy import validate_target_mode


QUOTA_SCHEMA_VERSION = 1
QUOTA_SCHEMA_VERSION_V2 = 2
QUOTA_KIND = "qcode-preregistered-formal-audit-quota"
SELECTION_SCHEMA_VERSION = 1
SELECTION_SCHEMA_VERSION_V2 = 2
SELECTION_KIND = "qcode-formal-audit-quota-selection"
ASSIGNMENT_FIELD = "formal_audit_quota_assignment"
SCIENTIFIC_SELECTOR_POLICY_VERSION = 7
SELECTOR_CONTEXT_SCHEMA_VERSION = 1
NEGATIVE_WITNESS_SELECTOR_POLICY = (
    "qcode-replayed-xz-low-weight-negative-only-selector-priority-v1"
)
MINIMUM_SUPPORT_SPLITS = ("2+2", "2+3", "3+2")
_ALL_SUPPORT_SPLITS = ("2+2", "2+3", "3+2", "2+4", "4+2", "3+3")
_QUOTA_V1_SELECTION_POLICY = (
    "proof-priority-within-preregistered-stratum-bp-upper-bound-neutral"
)
_QUOTA_V2_SELECTION_POLICY = (
    "proof-priority-within-preregistered-volume-coverage-deficit-strata-"
    "bp-upper-bound-neutral"
)
_SHA256 = re.compile(r"[0-9a-f]{64}")


def _canonical_sha256(value: Any) -> str:
    return hashlib.sha256(json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")).hexdigest()


def _file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _validated_reviewer_focus_binding(value: Any) -> dict[str, Any] | None:
    if value is None:
        return None
    required = {
        "source_round",
        "artifact_sha256",
        "action_sha256",
        "intent",
        "focus",
    }
    if not isinstance(value, Mapping) or set(value) != required:
        raise ValueError("selector reviewer-focus binding is malformed")
    source_round = value["source_round"]
    if (
        type(source_round) is not int
        or source_round < 1
        or value["intent"] not in {"diversify", "explore_undercovered"}
        or not isinstance(value["artifact_sha256"], str)
        or _SHA256.fullmatch(value["artifact_sha256"]) is None
        or not isinstance(value["action_sha256"], str)
        or _SHA256.fullmatch(value["action_sha256"]) is None
    ):
        raise ValueError("selector reviewer-focus binding is invalid")
    focus = value["focus"]
    if not isinstance(focus, list) or not 1 <= len(focus) <= 8:
        raise ValueError("selector reviewer-focus items are invalid")
    normalized_focus: list[dict[str, str]] = []
    for item in focus:
        if not isinstance(item, Mapping) or set(item) != {
            "dimension",
            "value",
            "direction",
            "priority",
        }:
            raise ValueError("selector reviewer-focus item is malformed")
        dimension = item["dimension"]
        focus_value = item["value"]
        if not isinstance(dimension, str) or not isinstance(focus_value, str):
            raise ValueError("selector reviewer-focus item is invalid")
        allowed_values = (
            _ALL_SUPPORT_SPLITS
            if dimension == "support_split_type"
            else RELATION_TYPES
            if dimension == "algebraic_relation_type"
            else ()
        )
        if (
            focus_value not in allowed_values
            or item["direction"] != "increase"
            or item["priority"] not in {"high", "medium", "low"}
        ):
            raise ValueError("selector reviewer-focus item is invalid")
        normalized_focus.append({
            "dimension": dimension,
            "value": focus_value,
            "direction": "increase",
            "priority": item["priority"],
        })
    return {
        "source_round": source_round,
        "artifact_sha256": value["artifact_sha256"],
        "action_sha256": value["action_sha256"],
        "intent": value["intent"],
        "focus": normalized_focus,
    }


def _validated_negative_witness_context(value: Any) -> dict[str, Any] | None:
    if value is None:
        return None
    required = {
        "context_sha256",
        "source_rows_sha256",
        "source_rows",
        "target_mode",
        "representation_id",
        "risk_index_sha256",
        "unknown_semantics",
        "bp_osd_positive_credit",
        "sector_canonicalization",
    }
    if not isinstance(value, Mapping) or set(value) != required:
        raise ValueError("selector negative-witness context is malformed")
    unsigned = dict(value)
    claimed = unsigned.pop("context_sha256", None)
    if (
        not isinstance(claimed, str)
        or _SHA256.fullmatch(claimed) is None
        or claimed != _canonical_sha256(unsigned)
        or not isinstance(value["source_rows_sha256"], str)
        or _SHA256.fullmatch(value["source_rows_sha256"]) is None
        or type(value["source_rows"]) is not int
        or value["source_rows"] < 0
        or validate_target_mode(value["target_mode"]) != value["target_mode"]
        or (
            value["representation_id"] is not None
            and (
                not isinstance(value["representation_id"], str)
                or not value["representation_id"]
            )
        )
        or not isinstance(value["risk_index_sha256"], str)
        or _SHA256.fullmatch(value["risk_index_sha256"]) is None
        or value["unknown_semantics"] != "fail-open-no-vote"
        or value["bp_osd_positive_credit"] is not False
        or value["sector_canonicalization"]
        != "bb-xz-inversion-block-swap-rowspace-v1"
    ):
        raise ValueError("selector negative-witness context is invalid")
    return dict(value)


def build_negative_witness_context(
    *,
    source_rows_sha256: str,
    source_rows: int,
    target_mode: str,
    representation_id: str | None,
    risk_index_sha256: str,
) -> dict[str, Any]:
    """Bind the replayed, negative-only X/Z selector input without evidence credit."""

    unsigned = {
        "source_rows_sha256": source_rows_sha256,
        "source_rows": source_rows,
        "target_mode": target_mode,
        "representation_id": representation_id,
        "risk_index_sha256": risk_index_sha256,
        "unknown_semantics": "fail-open-no-vote",
        "bp_osd_positive_credit": False,
        "sector_canonicalization": "bb-xz-inversion-block-swap-rowspace-v1",
    }
    validated = _validated_negative_witness_context({
        "context_sha256": _canonical_sha256(unsigned),
        **unsigned,
    })
    assert validated is not None
    return validated


def build_selector_context(
    *,
    reviewer_focus: Mapping[str, Any] | None = None,
    negative_witness_context: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Build the only selector context admitted into a schema-v2 report."""

    return {
        "schema_version": SELECTOR_CONTEXT_SCHEMA_VERSION,
        "policy_version": SCIENTIFIC_SELECTOR_POLICY_VERSION,
        "reviewer_focus": _validated_reviewer_focus_binding(reviewer_focus),
        "negative_witness_policy": NEGATIVE_WITNESS_SELECTOR_POLICY,
        "negative_witness_context": _validated_negative_witness_context(
            negative_witness_context
        ),
    }


def validate_selector_context(value: Any) -> dict[str, Any]:
    required = {
        "schema_version",
        "policy_version",
        "reviewer_focus",
        "negative_witness_policy",
        "negative_witness_context",
    }
    if not isinstance(value, Mapping) or set(value) != required:
        raise ValueError("formal-audit selector context is malformed")
    expected = build_selector_context(
        reviewer_focus=value["reviewer_focus"],
        negative_witness_context=value["negative_witness_context"],
    )
    if (
        value["schema_version"] != SELECTOR_CONTEXT_SCHEMA_VERSION
        or value["policy_version"] != SCIENTIFIC_SELECTOR_POLICY_VERSION
        or value["negative_witness_policy"]
        != NEGATIVE_WITNESS_SELECTOR_POLICY
        or dict(value) != expected
    ):
        raise ValueError("formal-audit selector context is invalid")
    return expected


def load_quota_contract(
    path: Path,
    *,
    representation_id: str | None = None,
    rounds: int | None = None,
    slots_per_round: int | None = None,
) -> dict[str, Any]:
    path = Path(path).resolve()
    if path.is_symlink() or not path.is_file():
        raise ValueError(f"formal-audit quota must be a regular file: {path}")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot read formal-audit quota: {exc}") from exc
    required_v1 = {
        "schema_version",
        "kind",
        "representation_id",
        "total_fresh_slots",
        "rounds",
        "slots_per_round",
        "unfilled_slot_policy",
        "selection_evidence_policy",
        "stratification_order",
        "volume_quotas",
        "mandatory_audited_volumes",
        "positive_promotion_forbidden_sources",
    }
    required_v2 = required_v1 | {
        "support_split_minimum_quotas",
        "automatic_representation_switch_gate",
    }
    if not isinstance(value, dict):
        raise ValueError("formal-audit quota fields are invalid")
    schema_version = value.get("schema_version")
    if schema_version == QUOTA_SCHEMA_VERSION_V2 and type(schema_version) is not int:
        raise ValueError("formal-audit quota fields are invalid")
    required = (
        required_v1
        if schema_version == QUOTA_SCHEMA_VERSION
        else required_v2
        if schema_version == QUOTA_SCHEMA_VERSION_V2
        else None
    )
    if required is None or set(value) != required:
        raise ValueError("formal-audit quota fields are invalid")
    expected_selection_policy = (
        _QUOTA_V1_SELECTION_POLICY
        if schema_version == QUOTA_SCHEMA_VERSION
        else _QUOTA_V2_SELECTION_POLICY
    )
    if (
        value["kind"] != QUOTA_KIND
        or value["unfilled_slot_policy"] != "durable-no-reallocation"
        or value["selection_evidence_policy"]
        != expected_selection_policy
        or value["stratification_order"] != [
            "published_volume",
            "lattice_q",
            "algebraic_mechanism",
            "support_split",
        ]
    ):
        raise ValueError("formal-audit quota contract semantics are invalid")
    for field in ("total_fresh_slots", "rounds", "slots_per_round"):
        if type(value[field]) is not int or value[field] < 1:
            raise ValueError(f"formal-audit quota {field} must be positive")
    if value["total_fresh_slots"] != value["rounds"] * value["slots_per_round"]:
        raise ValueError("formal-audit quota size disagrees with round budget")
    rows = value["volume_quotas"]
    if not isinstance(rows, list) or not rows:
        raise ValueError("formal-audit volume_quotas must be non-empty")
    seen: set[int] = set()
    total = 0
    for index, row in enumerate(rows):
        if not isinstance(row, dict) or set(row) != {"volume", "quota", "role"}:
            raise ValueError(f"formal-audit volume_quotas[{index}] is malformed")
        volume, quota, role = row["volume"], row["quota"], row["role"]
        if (
            type(volume) is not int
            or volume < 1
            or volume in seen
            or type(quota) is not int
            or quota < 1
            or not isinstance(role, str)
            or not role
        ):
            raise ValueError(f"formal-audit volume_quotas[{index}] is invalid")
        seen.add(volume)
        total += quota
    if total != value["total_fresh_slots"]:
        raise ValueError("formal-audit volume quotas do not sum to total slots")
    mandatory = value["mandatory_audited_volumes"]
    if (
        not isinstance(mandatory, list)
        or not mandatory
        or any(type(volume) is not int or volume not in seen for volume in mandatory)
        or len(set(mandatory)) != len(mandatory)
    ):
        raise ValueError("formal-audit mandatory volumes are invalid")
    forbidden = value["positive_promotion_forbidden_sources"]
    if (
        not isinstance(forbidden, list)
        or not {"bp_osd", "osd_cs", "decoder_distance"}.issubset(forbidden)
        or any(not isinstance(item, str) or not item for item in forbidden)
    ):
        raise ValueError("formal-audit forbidden promotion sources are invalid")
    if schema_version == QUOTA_SCHEMA_VERSION_V2:
        minimum_rows = value["support_split_minimum_quotas"]
        if (
            not isinstance(minimum_rows, list)
            or len(minimum_rows) != len(MINIMUM_SUPPORT_SPLITS)
        ):
            raise ValueError(
                "formal-audit support-split minimum quotas are invalid"
            )
        observed_splits: list[str] = []
        minimum_total = 0
        for index, row in enumerate(minimum_rows):
            if (
                not isinstance(row, dict)
                or set(row)
                != {"support_split", "minimum_fresh_audits"}
            ):
                raise ValueError(
                    "formal-audit support-split minimum quota "
                    f"{index} is malformed"
                )
            split = row["support_split"]
            minimum = row["minimum_fresh_audits"]
            if (
                not isinstance(split, str)
                or split not in MINIMUM_SUPPORT_SPLITS
                or split in observed_splits
                or type(minimum) is not int
                or minimum < 1
            ):
                raise ValueError(
                    "formal-audit support-split minimum quota "
                    f"{index} is invalid"
                )
            observed_splits.append(split)
            minimum_total += minimum
        if (
            tuple(observed_splits) != MINIMUM_SUPPORT_SPLITS
            or minimum_total > value["total_fresh_slots"]
        ):
            raise ValueError(
                "formal-audit support-split minimum quotas are invalid"
            )

        gate = value["automatic_representation_switch_gate"]
        gate_fields = {
            "minimum_terminal_fresh_audits",
            "stagnation_rounds",
            "minimum_proven_fom_improvement",
            "retain_family_if_lower_bound_at_least",
            "retain_family_if_target_gap_at_most",
            "minimum_distinct_lattice_q",
            "minimum_algebraic_mechanism_audits",
            "require_zero_unresolved",
            "require_all_audited_target_negative",
        }
        if not isinstance(gate, dict) or set(gate) != gate_fields:
            raise ValueError(
                "formal-audit automatic representation switch gate is malformed"
            )
        for field in (
            "minimum_terminal_fresh_audits",
            "stagnation_rounds",
            "retain_family_if_lower_bound_at_least",
            "minimum_distinct_lattice_q",
        ):
            if type(gate[field]) is not int or gate[field] < 1:
                raise ValueError(
                    "formal-audit automatic representation switch gate "
                    f"{field} is invalid"
                )
        target_gap = gate["retain_family_if_target_gap_at_most"]
        if type(target_gap) is not int or target_gap < 0:
            raise ValueError(
                "formal-audit automatic representation switch gate "
                "retain_family_if_target_gap_at_most is invalid"
            )
        improvement = gate["minimum_proven_fom_improvement"]
        if (
            isinstance(improvement, bool)
            or not isinstance(improvement, (int, float))
            or not 0.0 <= float(improvement) <= 12.0
        ):
            raise ValueError(
                "formal-audit automatic representation switch gate "
                "minimum_proven_fom_improvement is invalid"
            )
        mechanism_rows = gate["minimum_algebraic_mechanism_audits"]
        if (
            not isinstance(mechanism_rows, list)
            or len(mechanism_rows) != len(RELATION_TYPES)
        ):
            raise ValueError(
                "formal-audit automatic representation switch mechanism "
                "minimums are invalid"
            )
        observed_mechanisms: list[str] = []
        mechanism_minimum_total = 0
        for index, row in enumerate(mechanism_rows):
            if (
                not isinstance(row, dict)
                or set(row)
                != {"algebraic_mechanism", "minimum_fresh_audits"}
            ):
                raise ValueError(
                    "formal-audit automatic representation switch mechanism "
                    f"minimum {index} is malformed"
                )
            mechanism = row["algebraic_mechanism"]
            minimum = row["minimum_fresh_audits"]
            if (
                not isinstance(mechanism, str)
                or mechanism not in RELATION_TYPES
                or mechanism in observed_mechanisms
                or type(minimum) is not int
                or minimum < 1
            ):
                raise ValueError(
                    "formal-audit automatic representation switch mechanism "
                    f"minimum {index} is invalid"
                )
            observed_mechanisms.append(mechanism)
            mechanism_minimum_total += minimum
        if (
            tuple(observed_mechanisms) != RELATION_TYPES
            or mechanism_minimum_total > value["total_fresh_slots"]
            or gate["minimum_terminal_fresh_audits"]
            > value["total_fresh_slots"]
            or gate["stagnation_rounds"] > value["rounds"]
            or gate["minimum_distinct_lattice_q"]
            > value["total_fresh_slots"]
            or gate["require_zero_unresolved"] is not True
            or gate["require_all_audited_target_negative"] is not True
        ):
            raise ValueError(
                "formal-audit automatic representation switch gate is invalid"
            )
    if representation_id is not None and value["representation_id"] != representation_id:
        raise ValueError("formal-audit quota representation is incompatible")
    if rounds is not None and value["rounds"] != rounds:
        raise ValueError("formal-audit quota round budget is incompatible")
    if slots_per_round is not None and value["slots_per_round"] != slots_per_round:
        raise ValueError("formal-audit quota per-round budget is incompatible")
    return {
        **value,
        "contract_path": str(path),
        "contract_sha256": _file_sha256(path),
    }


def quota_slot_schedule(contract: Mapping[str, Any]) -> tuple[int, ...]:
    """Interleave volume quotas without silently reallocating a missing lane."""

    rows = contract.get("volume_quotas")
    if not isinstance(rows, list):
        raise ValueError("formal-audit quota has no volume rows")
    remaining = {int(row["volume"]): int(row["quota"]) for row in rows}
    order = tuple(remaining)
    schedule: list[int] = []
    while any(remaining.values()):
        for volume in order:
            if remaining[volume] <= 0:
                continue
            schedule.append(volume)
            remaining[volume] -= 1
    if len(schedule) != contract.get("total_fresh_slots"):
        raise ValueError("formal-audit quota schedule cardinality is invalid")
    return tuple(schedule)


def round_quota_slots(
    contract: Mapping[str, Any],
    round_number: int,
) -> tuple[dict[str, int], ...]:
    if type(round_number) is not int or not 1 <= round_number <= contract.get("rounds", 0):
        raise ValueError("formal-audit round number is outside the contract")
    per_round = int(contract["slots_per_round"])
    schedule = quota_slot_schedule(contract)
    start = (round_number - 1) * per_round
    return tuple(
        {"slot_index": index, "volume": schedule[index]}
        for index in range(start, start + per_round)
    )


def candidate_volume(row: Mapping[str, Any]) -> int | None:
    ell, m = row.get("ell"), row.get("m")
    if type(ell) is not int or type(m) is not int or ell < 1 or m < 1:
        return None
    return ell * m


def candidate_audit_strata(row: Mapping[str, Any]) -> dict[str, Any] | None:
    """Freshly derive quota coordinates from defining construction fields."""

    volume = candidate_volume(row)
    ell, m = row.get("ell"), row.get("m")
    a_terms, b_terms = row.get("A_terms"), row.get("B_terms")
    if volume is None or not isinstance(a_terms, (list, tuple)) or not isinstance(
        b_terms, (list, tuple)
    ):
        return None
    try:
        geometry = candidate_geometry(row)
        twist = 0 if geometry is None else int(geometry["twist"])
        mechanism = classify_algebraic_mechanism(
            a_terms,
            b_terms,
            ell=int(ell),
            m=int(m),
            geometry=geometry,
        )
    except (KeyError, TypeError, ValueError):
        return None
    return {
        "published_volume": volume,
        "lattice_q": [int(ell), int(m), twist],
        "algebraic_mechanism": mechanism["relation_type"],
        "support_split": mechanism["support_split_type"],
    }


def strata_sets(rows: Sequence[Mapping[str, Any]]) -> dict[str, set[Any]]:
    result: dict[str, set[Any]] = {
        "full": set(),
        "lattice_q": set(),
        "algebraic_mechanism": set(),
        "support_split": set(),
    }
    for row in rows:
        strata = candidate_audit_strata(row)
        if strata is None:
            continue
        lattice_q = tuple(strata["lattice_q"])
        result["full"].add((
            strata["published_volume"],
            lattice_q,
            strata["algebraic_mechanism"],
            strata["support_split"],
        ))
        result["lattice_q"].add(lattice_q)
        result["algebraic_mechanism"].add(strata["algebraic_mechanism"])
        result["support_split"].add(strata["support_split"])
    return result


def stratum_novelty_key(
    strata: Mapping[str, Any],
    observed: Mapping[str, set[Any]],
) -> tuple[int, int, int, int]:
    lattice_q = tuple(strata["lattice_q"])
    full = (
        strata["published_volume"],
        lattice_q,
        strata["algebraic_mechanism"],
        strata["support_split"],
    )
    return (
        int(full not in observed["full"]),
        int(lattice_q not in observed["lattice_q"]),
        int(strata["algebraic_mechanism"] not in observed["algebraic_mechanism"]),
        int(strata["support_split"] not in observed["support_split"]),
    )


def observe_strata(strata: Mapping[str, Any], observed: dict[str, set[Any]]) -> None:
    lattice_q = tuple(strata["lattice_q"])
    observed["full"].add((
        strata["published_volume"],
        lattice_q,
        strata["algebraic_mechanism"],
        strata["support_split"],
    ))
    observed["lattice_q"].add(lattice_q)
    observed["algebraic_mechanism"].add(strata["algebraic_mechanism"])
    observed["support_split"].add(strata["support_split"])


def _empty_filled_slot_counts() -> dict[str, Any]:
    return {
        "filled_fresh_slots": 0,
        "full": Counter(),
        "published_volume": Counter(),
        "lattice_q": Counter(),
        "algebraic_mechanism": Counter(),
        "support_split": Counter(),
    }


def _copy_filled_slot_counts(counts: Mapping[str, Any]) -> dict[str, Any]:
    required = {
        "filled_fresh_slots",
        "full",
        "published_volume",
        "lattice_q",
        "algebraic_mechanism",
        "support_split",
    }
    if not isinstance(counts, Mapping) or set(counts) != required:
        raise ValueError("formal-audit filled-slot counts are malformed")
    filled = counts["filled_fresh_slots"]
    if type(filled) is not int or filled < 0:
        raise ValueError("formal-audit filled-slot count is invalid")
    copied: dict[str, Any] = {"filled_fresh_slots": filled}
    for field in required - {"filled_fresh_slots"}:
        source = counts[field]
        if not isinstance(source, Mapping) or any(
            type(count) is not int or count < 1
            for count in source.values()
        ):
            raise ValueError("formal-audit filled-slot strata counts are invalid")
        copied[field] = Counter(source)
    if any(sum(copied[field].values()) != filled for field in (
        "full",
        "published_volume",
        "lattice_q",
        "algebraic_mechanism",
        "support_split",
    )):
        raise ValueError("formal-audit filled-slot strata totals disagree")
    return copied


def observe_filled_slot_strata(
    counts: dict[str, Any],
    strata: Mapping[str, Any],
) -> None:
    """Add one FILLED fresh slot to a mutable count object."""

    required = {
        "published_volume",
        "lattice_q",
        "algebraic_mechanism",
        "support_split",
    }
    if not isinstance(strata, Mapping) or set(strata) != required:
        raise ValueError("formal-audit filled-slot strata are malformed")
    volume = strata["published_volume"]
    lattice_q = strata["lattice_q"]
    mechanism = strata["algebraic_mechanism"]
    split = strata["support_split"]
    if (
        type(volume) is not int
        or volume < 1
        or not isinstance(lattice_q, (list, tuple))
        or len(lattice_q) != 3
        or any(type(coordinate) is not int for coordinate in lattice_q)
        or lattice_q[0] < 1
        or lattice_q[1] < 1
        or not 0 <= lattice_q[2] < lattice_q[1]
        or lattice_q[0] * lattice_q[1] != volume
        or mechanism not in RELATION_TYPES
        or split not in _ALL_SUPPORT_SPLITS
    ):
        raise ValueError("formal-audit filled-slot strata are invalid")
    lattice_key = tuple(lattice_q)
    full_key = (volume, lattice_key, mechanism, split)
    counts["filled_fresh_slots"] += 1
    counts["full"][full_key] += 1
    counts["published_volume"][volume] += 1
    counts["lattice_q"][lattice_key] += 1
    counts["algebraic_mechanism"][mechanism] += 1
    counts["support_split"][split] += 1


def support_split_minimum_deficits(
    contract: Mapping[str, Any],
    counts: Mapping[str, Any],
) -> dict[str, int]:
    """Return remaining v2 minimum fresh-audit counts per required split."""

    if contract.get("schema_version") != QUOTA_SCHEMA_VERSION_V2:
        raise ValueError("support-split minimum deficits require quota schema v2")
    copied = _copy_filled_slot_counts(counts)
    return {
        row["support_split"]: max(
            0,
            int(row["minimum_fresh_audits"])
            - int(copied["support_split"].get(row["support_split"], 0)),
        )
        for row in contract["support_split_minimum_quotas"]
    }


def formal_audit_coverage(
    contract: Mapping[str, Any],
    counts: Mapping[str, Any],
) -> dict[str, Any]:
    """Project validated FILLED-slot counts into a closed JSON coverage view."""

    if contract.get("schema_version") != QUOTA_SCHEMA_VERSION_V2:
        raise ValueError("formal-audit coverage requires quota schema v2")
    copied = _copy_filled_slot_counts(counts)
    deficits = support_split_minimum_deficits(contract, copied)
    split_minimums = {
        row["support_split"]: int(row["minimum_fresh_audits"])
        for row in contract["support_split_minimum_quotas"]
    }
    gate = contract["automatic_representation_switch_gate"]
    mechanism_minimums = {
        row["algebraic_mechanism"]: int(row["minimum_fresh_audits"])
        for row in gate["minimum_algebraic_mechanism_audits"]
    }
    split_components = [
        {
            "support_split": split,
            "minimum_fresh_audits": split_minimums[split],
            "observed_filled_fresh_audits": int(
                copied["support_split"].get(split, 0)
            ),
            "deficit": deficits[split],
            "satisfied": deficits[split] == 0,
        }
        for split in MINIMUM_SUPPORT_SPLITS
    ]
    mechanism_components = [
        {
            "algebraic_mechanism": mechanism,
            "minimum_fresh_audits": mechanism_minimums[mechanism],
            "observed_filled_fresh_audits": int(
                copied["algebraic_mechanism"].get(mechanism, 0)
            ),
            "deficit": max(
                0,
                mechanism_minimums[mechanism]
                - int(copied["algebraic_mechanism"].get(mechanism, 0)),
            ),
            "satisfied": (
                int(copied["algebraic_mechanism"].get(mechanism, 0))
                >= mechanism_minimums[mechanism]
            ),
        }
        for mechanism in RELATION_TYPES
    ]
    distinct_lattice_q = len(copied["lattice_q"])
    lattice_required = int(gate["minimum_distinct_lattice_q"])
    mandatory_volume_components = [
        {
            "published_volume": int(volume),
            "minimum_fresh_audits": 1,
            "observed_filled_fresh_audits": int(
                copied["published_volume"].get(int(volume), 0)
            ),
            "satisfied": int(
                copied["published_volume"].get(int(volume), 0)
            ) >= 1,
        }
        for volume in contract["mandatory_audited_volumes"]
    ]
    coverage_components_satisfied = bool(
        all(row["satisfied"] for row in split_components)
        and all(row["satisfied"] for row in mechanism_components)
        and all(row["satisfied"] for row in mandatory_volume_components)
        and distinct_lattice_q >= lattice_required
    )
    return {
        "schema_version": 1,
        "basis": "validated-filled-fresh-formal-audit-slots",
        "filled_fresh_slots": copied["filled_fresh_slots"],
        "distinct_lattice_q": distinct_lattice_q,
        "published_volume_counts": [
            {"published_volume": volume, "count": count}
            for volume, count in sorted(copied["published_volume"].items())
        ],
        "lattice_q_counts": [
            {"lattice_q": list(lattice_q), "count": count}
            for lattice_q, count in sorted(copied["lattice_q"].items())
        ],
        "algebraic_mechanism_counts": [
            {
                "algebraic_mechanism": mechanism,
                "count": int(copied["algebraic_mechanism"].get(mechanism, 0)),
            }
            for mechanism in RELATION_TYPES
        ],
        "support_split_counts": [
            {
                "support_split": split,
                "count": int(copied["support_split"].get(split, 0)),
            }
            for split in _ALL_SUPPORT_SPLITS
        ],
        "full_stratum_counts": [
            {
                "published_volume": full[0],
                "lattice_q": list(full[1]),
                "algebraic_mechanism": full[2],
                "support_split": full[3],
                "count": count,
            }
            for full, count in sorted(copied["full"].items())
        ],
        "gate_satisfied_components": {
            "support_split_minimum_quotas": split_components,
            "minimum_distinct_lattice_q": {
                "minimum": lattice_required,
                "observed": distinct_lattice_q,
                "satisfied": distinct_lattice_q >= lattice_required,
            },
            "minimum_algebraic_mechanism_audits": mechanism_components,
            "mandatory_audited_volumes": mandatory_volume_components,
            "coverage_components_satisfied": coverage_components_satisfied,
            "outcome_components_evaluated": False,
        },
    }


def _filled_slot_counts_from_records(
    records: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    counts = _empty_filled_slot_counts()
    for row in records:
        if row.get("status") != "FILLED":
            continue
        strata = row.get("strata")
        if not isinstance(strata, Mapping):
            raise ValueError("filled formal-audit slot has no strata")
        observe_filled_slot_strata(counts, strata)
    return counts


def _merge_filled_slot_counts(
    first: Mapping[str, Any],
    second: Mapping[str, Any],
) -> dict[str, Any]:
    result = _copy_filled_slot_counts(first)
    added = _copy_filled_slot_counts(second)
    result["filled_fresh_slots"] += added["filled_fresh_slots"]
    for field in (
        "full",
        "published_volume",
        "lattice_q",
        "algebraic_mechanism",
        "support_split",
    ):
        result[field].update(added[field])
    return result


def _filled_slot_counts_from_coverage(
    contract: Mapping[str, Any],
    value: Any,
) -> dict[str, Any]:
    if not isinstance(value, Mapping):
        raise ValueError("formal-audit coverage is malformed")
    full_rows = value.get("full_stratum_counts")
    if not isinstance(full_rows, list):
        raise ValueError("formal-audit coverage full strata are malformed")
    counts = _empty_filled_slot_counts()
    seen: set[tuple[Any, ...]] = set()
    for row in full_rows:
        required = {
            "published_volume",
            "lattice_q",
            "algebraic_mechanism",
            "support_split",
            "count",
        }
        if not isinstance(row, Mapping) or set(row) != required:
            raise ValueError("formal-audit coverage full stratum is malformed")
        count = row["count"]
        lattice_q = row["lattice_q"]
        if (
            not isinstance(lattice_q, list)
            or len(lattice_q) != 3
            or any(type(coordinate) is not int for coordinate in lattice_q)
            or not isinstance(row["algebraic_mechanism"], str)
            or not isinstance(row["support_split"], str)
        ):
            raise ValueError("formal-audit coverage full stratum is invalid")
        identity = (
            row["published_volume"],
            tuple(lattice_q),
            row["algebraic_mechanism"],
            row["support_split"],
        )
        if type(count) is not int or count < 1 or identity in seen:
            raise ValueError("formal-audit coverage full stratum is invalid")
        seen.add(identity)
        strata = {
            "published_volume": row["published_volume"],
            "lattice_q": lattice_q,
            "algebraic_mechanism": row["algebraic_mechanism"],
            "support_split": row["support_split"],
        }
        for _ in range(count):
            observe_filled_slot_strata(counts, strata)
    if dict(value) != formal_audit_coverage(contract, counts):
        raise ValueError("formal-audit coverage is non-canonical")
    return counts


def assigned_candidate(
    row: Mapping[str, Any],
    *,
    slot: Mapping[str, int],
    strata: Mapping[str, Any],
) -> dict[str, Any]:
    selected = dict(row)
    selected[ASSIGNMENT_FIELD] = {
        "schema_version": 1,
        "slot_index": int(slot["slot_index"]),
        "volume": int(slot["volume"]),
        "strata": dict(strata),
        "semantics": "audit-scheduling-only-no-distance-credit",
    }
    return selected


def selection_report(
    *,
    contract: Mapping[str, Any],
    round_number: int,
    selected_fresh: Sequence[Mapping[str, Any]],
    retry_candidate_keys: Sequence[str],
    candidate_key_fn,
    prior_reports: Sequence[Mapping[str, Any]] | None = None,
    selector_context: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    slots = [dict(slot) for slot in round_quota_slots(contract, round_number)]
    assignments: dict[int, Mapping[str, Any]] = {}
    for row in selected_fresh:
        assignment = row.get(ASSIGNMENT_FIELD)
        if not isinstance(assignment, Mapping):
            raise ValueError("fresh quota selection lacks a slot assignment")
        index = assignment.get("slot_index")
        if type(index) is not int or index in assignments:
            raise ValueError("fresh quota selection repeats or corrupts a slot")
        assignments[index] = row
    retry_count = len(retry_candidate_keys)
    expected_indices = {slot["slot_index"] for slot in slots}
    if (
        retry_count > len(slots)
        or not set(assignments).issubset(expected_indices)
        or len(set(retry_candidate_keys)) != retry_count
    ):
        raise ValueError("formal-audit quota assignments exceed this round")
    round_start = (round_number - 1) * int(contract["slots_per_round"])
    active_fresh_slots = len(slots) - retry_count
    records = []
    for offset, slot in enumerate(slots):
        row = assignments.get(slot["slot_index"])
        if row is not None:
            assignment = row[ASSIGNMENT_FIELD]
            if assignment["volume"] != slot["volume"]:
                raise ValueError("fresh quota selection filled the wrong volume")
            records.append({
                **slot,
                "status": "FILLED",
                "candidate_key": candidate_key_fn(row),
                "strata": dict(assignment["strata"]),
                "unfilled_reason": None,
            })
        else:
            records.append({
                **slot,
                "status": "UNFILLED",
                "candidate_key": None,
                "strata": None,
                "unfilled_reason": (
                    "retry-lane-reserved"
                    if offset >= active_fresh_slots
                    else "no-eligible-candidate-in-assigned-volume"
                ),
            })
    payload: dict[str, Any] = {
        "schema_version": SELECTION_SCHEMA_VERSION,
        "kind": SELECTION_KIND,
        "representation_id": contract["representation_id"],
        "contract_path": contract["contract_path"],
        "contract_sha256": contract["contract_sha256"],
        "round": round_number,
        "round_slot_range": [round_start, round_start + len(slots)],
        "slots": records,
        "retry_candidate_keys": list(retry_candidate_keys),
        "filled_fresh_slots": sum(row["status"] == "FILLED" for row in records),
        "unfilled_fresh_slots": sum(row["status"] == "UNFILLED" for row in records),
        "bp_osd_positive_promotion": False,
    }
    contract_schema = contract.get("schema_version")
    v2_prior: list[Mapping[str, Any]] | None = None
    if contract_schema == QUOTA_SCHEMA_VERSION_V2:
        prior = [] if prior_reports is None else list(prior_reports)
        if len(prior) != round_number - 1:
            raise ValueError(
                "schema-v2 formal-audit report requires every prior report"
            )
        prior_counts = audited_filled_slot_counts(
            prior,
            contract=contract,
        )
        current_counts = _filled_slot_counts_from_records(records)
        after_counts = _merge_filled_slot_counts(
            prior_counts,
            current_counts,
        )
        payload["schema_version"] = SELECTION_SCHEMA_VERSION_V2
        payload["selector_context"] = validate_selector_context(
            build_selector_context()
            if selector_context is None
            else selector_context
        )
        payload["formal_audit_coverage_before"] = formal_audit_coverage(
            contract,
            prior_counts,
        )
        payload["formal_audit_coverage_after"] = formal_audit_coverage(
            contract,
            after_counts,
        )
        v2_prior = prior
    elif contract_schema != QUOTA_SCHEMA_VERSION:
        raise ValueError("formal-audit quota schema is unsupported")
    elif selector_context is not None:
        raise ValueError(
            "schema-v1 formal-audit report does not accept v2 context"
        )
    result = {**payload, "report_sha256": _canonical_sha256(payload)}
    if v2_prior is not None:
        validate_selection_report_sequence(
            [*v2_prior, result],
            contract=contract,
        )
    return result


def validate_selection_report(
    report: Mapping[str, Any],
    *,
    contract: Mapping[str, Any],
    round_number: int,
    prior_reports: Sequence[Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    value = dict(report)
    expected_fields_v1 = {
        "schema_version",
        "kind",
        "representation_id",
        "contract_path",
        "contract_sha256",
        "round",
        "round_slot_range",
        "slots",
        "retry_candidate_keys",
        "filled_fresh_slots",
        "unfilled_fresh_slots",
        "bp_osd_positive_promotion",
        "report_sha256",
    }
    contract_schema = contract.get("schema_version")
    expected_fields = (
        expected_fields_v1
        if contract_schema == QUOTA_SCHEMA_VERSION
        else expected_fields_v1
        | {
            "selector_context",
            "formal_audit_coverage_before",
            "formal_audit_coverage_after",
        }
        if contract_schema == QUOTA_SCHEMA_VERSION_V2
        else set()
    )
    if set(value) != expected_fields:
        raise ValueError("formal-audit quota selection report fields are invalid")
    unsigned = dict(value)
    claimed = unsigned.pop("report_sha256", None)
    if (
        value.get("schema_version")
        != (
            SELECTION_SCHEMA_VERSION
            if contract_schema == QUOTA_SCHEMA_VERSION
            else SELECTION_SCHEMA_VERSION_V2
        )
        or value.get("kind") != SELECTION_KIND
        or value.get("representation_id") != contract["representation_id"]
        or value.get("contract_path") != contract["contract_path"]
        or value.get("contract_sha256") != contract["contract_sha256"]
        or value.get("round") != round_number
        or value.get("bp_osd_positive_promotion") is not False
        or not isinstance(claimed, str)
        or _SHA256.fullmatch(claimed) is None
        or claimed != _canonical_sha256(unsigned)
    ):
        raise ValueError("formal-audit quota selection report is invalid")
    expected_slots = [dict(slot) for slot in round_quota_slots(contract, round_number)]
    slots = value.get("slots")
    if not isinstance(slots, list) or len(slots) != len(expected_slots):
        raise ValueError("formal-audit quota report slot count is invalid")
    retry_keys = value.get("retry_candidate_keys")
    if (
        not isinstance(retry_keys, list)
        or len(retry_keys) > len(expected_slots)
        or any(not isinstance(key, str) or not key for key in retry_keys)
        or len(set(retry_keys)) != len(retry_keys)
    ):
        raise ValueError("formal-audit quota retry keys are invalid")
    round_start = (round_number - 1) * int(contract["slots_per_round"])
    if value.get("round_slot_range") != [
        round_start,
        round_start + len(expected_slots),
    ]:
        raise ValueError("formal-audit quota slot range is invalid")
    active_fresh_slots = len(expected_slots) - len(retry_keys)
    filled_keys: list[str] = []
    filled = 0
    for offset, (expected, row) in enumerate(
        zip(expected_slots, slots, strict=True)
    ):
        expected_row_fields = {
            "slot_index",
            "volume",
            "status",
            "candidate_key",
            "strata",
            "unfilled_reason",
        }
        if (
            not isinstance(row, Mapping)
            or set(row) != expected_row_fields
            or row.get("slot_index") != expected["slot_index"]
            or row.get("volume") != expected["volume"]
            or row.get("status") not in {"FILLED", "UNFILLED"}
        ):
            raise ValueError("formal-audit quota report slot is invalid")
        if row["status"] == "FILLED":
            key = row.get("candidate_key")
            strata = row.get("strata")
            lattice_q = strata.get("lattice_q") if isinstance(strata, Mapping) else None
            if (
                offset >= active_fresh_slots
                or not isinstance(key, str)
                or not key
                or not isinstance(strata, Mapping)
                or set(strata) != {
                    "published_volume",
                    "lattice_q",
                    "algebraic_mechanism",
                    "support_split",
                }
                or strata.get("published_volume") != expected["volume"]
                or not isinstance(lattice_q, list)
                or len(lattice_q) != 3
                or any(type(coordinate) is not int for coordinate in lattice_q)
                or lattice_q[0] < 1
                or lattice_q[1] < 1
                or not 0 <= lattice_q[2] < lattice_q[1]
                or lattice_q[0] * lattice_q[1] != expected["volume"]
                or not isinstance(strata.get("algebraic_mechanism"), str)
                or not strata["algebraic_mechanism"]
                or not isinstance(strata.get("support_split"), str)
                or not strata["support_split"]
                or (
                    contract_schema == QUOTA_SCHEMA_VERSION_V2
                    and (
                        strata["algebraic_mechanism"] not in RELATION_TYPES
                        or strata["support_split"] not in _ALL_SUPPORT_SPLITS
                    )
                )
                or row.get("unfilled_reason") is not None
            ):
                raise ValueError("filled formal-audit quota slot is invalid")
            filled += 1
            filled_keys.append(key)
        else:
            expected_reason = (
                "retry-lane-reserved"
                if offset >= active_fresh_slots
                else "no-eligible-candidate-in-assigned-volume"
            )
            if (
                row.get("candidate_key") is not None
                or row.get("strata") is not None
                or row.get("unfilled_reason") != expected_reason
            ):
                raise ValueError("unfilled formal-audit quota slot is invalid")
    if (
        len(set(filled_keys)) != len(filled_keys)
        or set(filled_keys).intersection(retry_keys)
        or value.get("filled_fresh_slots") != filled
        or value.get("unfilled_fresh_slots") != len(expected_slots) - filled
    ):
        raise ValueError("formal-audit quota report counts are invalid")
    if contract_schema == QUOTA_SCHEMA_VERSION:
        return value

    validated_context = validate_selector_context(value["selector_context"])
    negative_context = validated_context["negative_witness_context"]
    if (
        negative_context is not None
        and negative_context["representation_id"]
        != contract["representation_id"]
    ):
        raise ValueError(
            "schema-v2 selector context representation is incompatible"
        )
    reported_before = _filled_slot_counts_from_coverage(
        contract,
        value["formal_audit_coverage_before"],
    )
    if prior_reports is not None:
        prior = list(prior_reports)
        if len(prior) != round_number - 1:
            raise ValueError(
                "schema-v2 formal-audit report history is incomplete"
            )
        expected_before = audited_filled_slot_counts(
            prior,
            contract=contract,
        )
        if formal_audit_coverage(contract, expected_before) != value[
            "formal_audit_coverage_before"
        ]:
            raise ValueError(
                "schema-v2 formal-audit prior coverage changed"
            )
    elif round_number == 1 and reported_before["filled_fresh_slots"] != 0:
        raise ValueError("first formal-audit report has nonempty prior coverage")
    current_counts = _filled_slot_counts_from_records(slots)
    expected_after = _merge_filled_slot_counts(
        reported_before,
        current_counts,
    )
    if formal_audit_coverage(contract, expected_after) != value[
        "formal_audit_coverage_after"
    ]:
        raise ValueError("schema-v2 formal-audit coverage delta is invalid")
    return value


def validate_selection_report_sequence(
    reports: Sequence[Mapping[str, Any]],
    *,
    contract: Mapping[str, Any],
) -> list[dict[str, Any]]:
    """Replay a contiguous schema-v2 report prefix and its coverage chain."""

    if contract.get("schema_version") != QUOTA_SCHEMA_VERSION_V2:
        raise ValueError("report-sequence validation requires quota schema v2")
    if not isinstance(reports, Sequence) or isinstance(reports, (str, bytes)):
        raise ValueError("formal-audit report sequence is malformed")
    if len(reports) > int(contract["rounds"]):
        raise ValueError("formal-audit report sequence exceeds the round budget")
    validated: list[dict[str, Any]] = []
    filled_keys: set[str] = set()
    counts = _empty_filled_slot_counts()
    for round_number, report in enumerate(reports, start=1):
        value = validate_selection_report(
            report,
            contract=contract,
            round_number=round_number,
        )
        if value["formal_audit_coverage_before"] != formal_audit_coverage(
            contract,
            counts,
        ):
            raise ValueError("formal-audit report coverage chain changed")
        for slot in value["slots"]:
            if slot["status"] != "FILLED":
                continue
            key = slot["candidate_key"]
            if key in filled_keys:
                raise ValueError(
                    "formal-audit report sequence repeats a fresh candidate"
                )
            filled_keys.add(key)
        counts = _merge_filled_slot_counts(
            counts,
            _filled_slot_counts_from_records(value["slots"]),
        )
        if value["formal_audit_coverage_after"] != formal_audit_coverage(
            contract,
            counts,
        ):
            raise ValueError("formal-audit report coverage chain changed")
        validated.append(value)
    return validated


def audited_filled_slot_counts(
    reports: Sequence[Mapping[str, Any]],
    *,
    contract: Mapping[str, Any],
) -> dict[str, Any]:
    """Count only validated FILLED fresh slots; retry lanes never contribute."""

    validated = validate_selection_report_sequence(
        reports,
        contract=contract,
    )
    counts = _empty_filled_slot_counts()
    for report in validated:
        current = _filled_slot_counts_from_records(report["slots"])
        counts = _merge_filled_slot_counts(counts, current)
    return counts


__all__ = [
    "ASSIGNMENT_FIELD",
    "MINIMUM_SUPPORT_SPLITS",
    "NEGATIVE_WITNESS_SELECTOR_POLICY",
    "SCIENTIFIC_SELECTOR_POLICY_VERSION",
    "audited_filled_slot_counts",
    "assigned_candidate",
    "build_negative_witness_context",
    "build_selector_context",
    "candidate_audit_strata",
    "candidate_volume",
    "formal_audit_coverage",
    "load_quota_contract",
    "observe_strata",
    "observe_filled_slot_strata",
    "quota_slot_schedule",
    "round_quota_slots",
    "selection_report",
    "strata_sets",
    "stratum_novelty_key",
    "support_split_minimum_deficits",
    "validate_selection_report",
    "validate_selection_report_sequence",
    "validate_selector_context",
]
