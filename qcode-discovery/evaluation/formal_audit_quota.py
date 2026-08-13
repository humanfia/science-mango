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
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any

from evaluation.algebraic_mechanisms import classify_algebraic_mechanism
from evaluation.geometry import candidate_geometry


QUOTA_SCHEMA_VERSION = 1
QUOTA_KIND = "qcode-preregistered-formal-audit-quota"
SELECTION_SCHEMA_VERSION = 1
SELECTION_KIND = "qcode-formal-audit-quota-selection"
ASSIGNMENT_FIELD = "formal_audit_quota_assignment"
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
    required = {
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
    if not isinstance(value, dict) or set(value) != required:
        raise ValueError("formal-audit quota fields are invalid")
    if (
        value["schema_version"] != QUOTA_SCHEMA_VERSION
        or value["kind"] != QUOTA_KIND
        or value["unfilled_slot_policy"] != "durable-no-reallocation"
        or value["selection_evidence_policy"]
        != "proof-priority-within-preregistered-stratum-bp-upper-bound-neutral"
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
    payload = {
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
    return {**payload, "report_sha256": _canonical_sha256(payload)}


def validate_selection_report(
    report: Mapping[str, Any],
    *,
    contract: Mapping[str, Any],
    round_number: int,
) -> dict[str, Any]:
    value = dict(report)
    expected_fields = {
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
    if set(value) != expected_fields:
        raise ValueError("formal-audit quota selection report fields are invalid")
    unsigned = dict(value)
    claimed = unsigned.pop("report_sha256", None)
    if (
        value.get("schema_version") != SELECTION_SCHEMA_VERSION
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
    return value


__all__ = [
    "ASSIGNMENT_FIELD",
    "assigned_candidate",
    "candidate_audit_strata",
    "candidate_volume",
    "load_quota_contract",
    "observe_strata",
    "quota_slot_schedule",
    "round_quota_slots",
    "selection_report",
    "strata_sets",
    "stratum_novelty_key",
    "validate_selection_report",
]
