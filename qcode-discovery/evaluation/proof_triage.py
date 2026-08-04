"""Proof-oriented ranking for qLDPC search candidates.

Search incumbents are upper bounds: a large incumbent distance or FOM is not
evidence that a candidate satisfies the challenge.  This module instead ranks
candidates by progress towards a lower-bound proof.  In priority order it uses
the number of threshold-safe logical directions, the weakest and terminal MILP
dual-bound ratios, and logical-direction coverage.  FOM is deliberately absent
from the ranking key.

The helpers accept both expanded-search rows, whose construction claim is
nested under ``claim``, and the flat rows emitted by the frontier search.
"""

from __future__ import annotations

import hashlib
import json
import math
from collections.abc import Iterable, Mapping, Sequence
from pathlib import Path
from typing import Any

from evaluation.geometry import normalize_geometry


SCHEMA_VERSION = 1
_BOUND_KEYS = ("mip_dual_bound", "dual_bound", "best_objective_bound")
_STRUCTURAL_FIELDS = (
    "code_type",
    "geometry",
    "ell",
    "m",
    "A_terms",
    "B_terms",
    "C_terms",
    "D_terms",
    "H_X",
    "H_Z",
    "stabilizer",
)
_EVIDENCE_FIELDS = (
    "directions",
    "direction",
    "sectors",
    "expected_directions",
    "completed_directions",
    "required_distance",
    "status",
)
_BOUND_TOLERANCE = 1e-7


def normalize_record(
    row: Mapping[str, Any],
    source: str | Path | None = None,
    line_number: int | None = None,
) -> dict[str, Any]:
    """Return a flat candidate row without mutating ``row``.

    ``claim`` fields are promoted for expanded-search rows.  A saved audit
    artifact may additionally wrap the search row under ``candidate``; its
    proof evidence is promoted as well.  Top-level derived values always win
    over claim values.
    """
    if not isinstance(row, Mapping):
        raise TypeError("candidate row must be a mapping")

    outer = dict(row)
    wrapped = outer.get("candidate")
    base = dict(wrapped) if isinstance(wrapped, Mapping) else outer
    claim = base.get("claim")

    flat: dict[str, Any] = {}
    if isinstance(claim, Mapping):
        flat.update(claim)
    flat.update(
        (key, value)
        for key, value in base.items()
        if key not in {"claim", "candidate"}
    )

    if isinstance(wrapped, Mapping):
        for key in _EVIDENCE_FIELDS:
            if key in outer:
                flat[key] = outer[key]
        for key in ("trial", "ansatz", "source", "novelty", "canonical_digest"):
            if key in outer and key not in flat:
                flat[key] = outer[key]

    if source is not None:
        flat["_triage_source"] = str(source)
    if line_number is not None:
        if line_number < 1:
            raise ValueError("line_number must be positive")
        flat["_triage_line_number"] = int(line_number)
    return flat


def _canonicalize(value: Any, *, unordered: bool = False) -> Any:
    """Convert JSON-like input to a deterministic structural representation."""
    if isinstance(value, Mapping):
        return {
            str(key): _canonicalize(item)
            for key, item in sorted(value.items(), key=lambda pair: str(pair[0]))
        }
    if isinstance(value, (list, tuple)):
        items = [_canonicalize(item) for item in value]
        if unordered:
            items.sort(
                key=lambda item: json.dumps(
                    item, sort_keys=True, separators=(",", ":"),
                )
            )
        return items
    return value


def _structural_digest(record: Mapping[str, Any]) -> tuple[str, str]:
    payload: dict[str, Any] = {}
    for field in _STRUCTURAL_FIELDS:
        if field not in record or record[field] is None:
            continue
        if field == "geometry":
            geometry = normalize_geometry(
                record.get("ell"),
                record.get("m"),
                record[field],
            )
            if geometry is None:
                continue
            payload[field] = geometry
            continue
        payload[field] = _canonicalize(
            record[field],
            unordered=field.endswith("_terms"),
        )
    if payload:
        encoded = json.dumps(
            payload, sort_keys=True, separators=(",", ":"),
        ).encode()
        return (
            f"claim-sha256:{hashlib.sha256(encoded).hexdigest()}",
            "structural-claim",
        )

    source_bits = {
        key: record.get(key)
        for key in (
            "source", "ansatz", "trial", "_triage_source",
            "_triage_line_number",
        )
        if record.get(key) is not None
    }
    encoded = json.dumps(
        source_bits, sort_keys=True, separators=(",", ":"),
    ).encode()
    return (
        f"source-sha256:{hashlib.sha256(encoded).hexdigest()}",
        "source-fallback",
    )


def candidate_identity(
    record: Mapping[str, Any],
    source: str | Path | None = None,
    line_number: int | None = None,
) -> dict[str, str]:
    """Return canonical and provenance identities for one candidate.

    A registry/BLISS digest is preferred.  When it is absent, a deterministic
    digest of the explicit construction claim is used; this fallback only
    deduplicates identical claims and does not assert graph isomorphism.
    """
    normalized = normalize_record(
        record, source=source, line_number=line_number,
    )
    novelty = normalized.get("novelty")
    digest = normalized.get("canonical_digest")
    digest_kind = "canonical"
    if not digest and isinstance(novelty, Mapping):
        digest = novelty.get("canonical_digest")
        digest_kind = "registry-canonical"
    if not digest and normalized.get("bliss_hash"):
        digest = normalized["bliss_hash"]
        digest_kind = "bliss"
    if not digest:
        digest, digest_kind = _structural_digest(normalized)

    origin = normalized.get("_triage_source")
    if origin is None:
        origin = (
            normalized.get("source") or normalized.get("ansatz") or "unknown"
        )
    parts = [str(origin)]
    if normalized.get("trial") is not None:
        parts.append(f"trial={normalized['trial']}")
    if normalized.get("_triage_line_number") is not None:
        parts.append(f"line={normalized['_triage_line_number']}")
    return {
        "canonical_digest": str(digest),
        "digest_kind": digest_kind,
        "source_identity": "#".join(parts),
    }


def _as_finite_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        number = float(value)
    except (TypeError, ValueError):
        return None
    return number if math.isfinite(number) else None


def _dual_bound(evidence: Mapping[str, Any]) -> float | None:
    for key in _BOUND_KEYS:
        value = _as_finite_float(evidence.get(key))
        if value is not None:
            return value
    return None


def _evidence_items(record: Mapping[str, Any]) -> list[dict[str, Any]]:
    normalized = normalize_record(record)
    for field in ("directions", "sectors"):
        values = normalized.get(field)
        if (
            isinstance(values, Sequence)
            and not isinstance(values, (str, bytes))
        ):
            items = [
                dict(item) for item in values if isinstance(item, Mapping)
            ]
            if items:
                return items
    direction = normalized.get("direction")
    return [dict(direction)] if isinstance(direction, Mapping) else []


def _evidence_identity(
    evidence: Mapping[str, Any], ordinal: int,
) -> tuple[Any, ...]:
    if evidence.get("position") is not None:
        return ("position", evidence.get("position"))
    if evidence.get("sector") is not None:
        return ("sector", evidence.get("sector"))
    if (
        evidence.get("logical_type") is not None
        or evidence.get("logical_index") is not None
    ):
        return (
            "logical",
            evidence.get("logical_type"),
            evidence.get("logical_index"),
            evidence.get("check_matrix"),
        )
    return ("ordinal", ordinal)


def _unique_evidence(record: Mapping[str, Any]) -> list[dict[str, Any]]:
    unique: list[dict[str, Any]] = []
    seen: set[tuple[Any, ...]] = set()
    for ordinal, evidence in enumerate(_evidence_items(record)):
        identity = _evidence_identity(evidence, ordinal)
        if identity in seen:
            continue
        seen.add(identity)
        unique.append(evidence)
    return unique


def _verified_low_witness(
    evidence: Mapping[str, Any], required: int,
) -> bool:
    objective = _as_finite_float(evidence.get("objective"))
    return bool(
        evidence.get("witness_verified") is True
        and objective is not None
        and objective < required
    )


def _threshold_safe(evidence: Mapping[str, Any], required: int) -> bool:
    if _verified_low_witness(evidence, required):
        return False
    if (
        evidence.get("threshold_infeasible") is True
        and evidence.get("operator") is None
        and _as_finite_float(evidence.get("max_weight")) == required - 1
    ):
        return True

    bound = _dual_bound(evidence)
    if bound is not None and bound >= required - _BOUND_TOLERANCE:
        return True

    objective = _as_finite_float(evidence.get("objective"))
    gap = _as_finite_float(evidence.get("mip_gap"))
    return bool(
        (evidence.get("success") is True or evidence.get("exact") is True)
        and gap is not None
        and abs(gap) <= _BOUND_TOLERANCE
        and objective is not None
        and objective >= required
        and evidence.get("witness_verified") is True
    )


def _expected_directions(
    record: Mapping[str, Any], evidence: Sequence[Mapping[str, Any]],
) -> int:
    normalized = normalize_record(record)
    # A pair of whole-sector XOR results covers all logical combinations in
    # X and Z. Optimized schema-v2 rows also carry the direction-level ``2k``
    # expectation when ``directions`` is empty, so sector evidence must select
    # its own two-unit proof domain before consulting that field.
    if evidence and all(
        item.get("sector") in {"X", "Z"} for item in evidence
    ):
        return 2
    explicit = normalized.get("expected_directions")
    try:
        if explicit is not None and int(explicit) > 0:
            return int(explicit)
    except (TypeError, ValueError):
        pass
    if normalized.get("sectors") is not None:
        return 2
    try:
        k = int(normalized.get("k", 0))
    except (TypeError, ValueError):
        k = 0
    return 2 * k if k > 0 else len(evidence)


def evidence_score(record: Mapping[str, Any]) -> dict[str, Any]:
    """Summarize lower-bound proof progress for one normalized or raw row."""
    normalized = normalize_record(record)
    try:
        required = int(normalized["required_distance"])
    except (KeyError, TypeError, ValueError) as exc:
        raise ValueError(
            "candidate requires a positive required_distance",
        ) from exc
    if required <= 0:
        raise ValueError("candidate requires a positive required_distance")

    evidence = _unique_evidence(normalized)
    expected = _expected_directions(normalized, evidence)
    completed = min(len(evidence), expected) if expected else len(evidence)
    rejected = any(
        _verified_low_witness(item, required) for item in evidence
    )
    safe = sum(_threshold_safe(item, required) for item in evidence)
    safe = min(safe, expected) if expected else safe

    ratios = [
        bound / required
        for item in evidence
        if (bound := _dual_bound(item)) is not None
    ]
    terminal_bound = _dual_bound(evidence[-1]) if evidence else None
    terminal_ratio = (
        terminal_bound / required if terminal_bound is not None else None
    )
    min_ratio = min(ratios) if ratios else None
    coverage = min(completed / expected, 1.0) if expected else 0.0
    dual_coverage = min(len(ratios) / expected, 1.0) if expected else 0.0

    if rejected:
        status = "REJECTED"
    elif expected and safe == expected:
        status = "THRESHOLD_PROVEN"
    elif evidence:
        status = "PROMISING"
    else:
        status = "UNSCREENED"

    ratio_floor = -1.0
    return {
        "schema_version": SCHEMA_VERSION,
        "status": status,
        "rejected": rejected,
        "required_distance": required,
        "expected_directions": expected,
        "completed_directions": completed,
        "threshold_safe_directions": safe,
        "threshold_safe_fraction": safe / expected if expected else 0.0,
        "coverage": coverage,
        "dual_bound_directions": len(ratios),
        "dual_coverage": dual_coverage,
        "min_dual_ratio": min_ratio,
        "terminal_dual_ratio": terminal_ratio,
        "rank_vector": [
            safe,
            min_ratio if min_ratio is not None else ratio_floor,
            terminal_ratio if terminal_ratio is not None else ratio_floor,
            coverage,
            dual_coverage,
        ],
    }


def rank_record(
    row: Mapping[str, Any],
    source: str | Path | None = None,
    line_number: int | None = None,
) -> dict[str, Any]:
    """Normalize and annotate one row with identity and proof score."""
    normalized = normalize_record(
        row, source=source, line_number=line_number,
    )
    normalized["triage_identity"] = candidate_identity(normalized)
    normalized["proof_score"] = evidence_score(normalized)
    return normalized


def stable_sort_key(ranked: Mapping[str, Any]) -> tuple[Any, ...]:
    """Return an ascending key whose first item is the best proof candidate."""
    score = ranked.get("proof_score")
    if not isinstance(score, Mapping):
        score = evidence_score(ranked)
    identity = ranked.get("triage_identity")
    if not isinstance(identity, Mapping):
        identity = candidate_identity(ranked)

    def ratio(name: str) -> float:
        value = _as_finite_float(score.get(name))
        return value if value is not None else -1.0

    return (
        1 if score.get("rejected") is True else 0,
        -int(score.get("threshold_safe_directions", 0)),
        -ratio("min_dual_ratio"),
        -ratio("terminal_dual_ratio"),
        -ratio("coverage"),
        -ratio("dual_coverage"),
        str(identity.get("canonical_digest", "")),
        str(identity.get("source_identity", "")),
    )


def deduplicate_ranked(
    records: Iterable[Mapping[str, Any]],
    sources: Iterable[str | Path | None] | None = None,
) -> list[dict[str, Any]]:
    """Deduplicate candidates by digest, keep the strongest, and rank them."""
    rows = list(records)
    origins = [None] * len(rows) if sources is None else list(sources)
    if len(origins) != len(rows):
        raise ValueError("sources must have the same length as records")

    groups: dict[str, dict[str, Any]] = {}
    for line_number, (row, source) in enumerate(
        zip(rows, origins), start=1,
    ):
        ranked = rank_record(
            row, source=source, line_number=line_number,
        )
        identity = ranked["triage_identity"]
        digest = str(identity["canonical_digest"])
        source_identity = str(identity["source_identity"])
        group = groups.get(digest)
        if group is None:
            groups[digest] = {
                "best": ranked,
                "sources": {source_identity},
                "count": 1,
            }
            continue
        group["count"] += 1
        group["sources"].add(source_identity)
        ranked_rejected = ranked["proof_score"]["rejected"] is True
        best_rejected = group["best"]["proof_score"]["rejected"] is True
        # A replay-verified low witness is conclusive for every duplicate of
        # the same canonical code.  Never hide it behind an older unresolved
        # row merely because rejected rows sort after live audit candidates.
        if ranked_rejected and not best_rejected:
            group["best"] = ranked
        elif ranked_rejected == best_rejected and (
            stable_sort_key(ranked) < stable_sort_key(group["best"])
        ):
            group["best"] = ranked

    result: list[dict[str, Any]] = []
    for group in groups.values():
        best = dict(group["best"])
        identity = dict(best["triage_identity"])
        identity["source_identities"] = sorted(group["sources"])
        identity["merged_record_count"] = int(group["count"])
        identity["duplicate_count"] = int(group["count"]) - 1
        best["triage_identity"] = identity
        result.append(best)
    return sorted(result, key=stable_sort_key)


__all__ = [
    "SCHEMA_VERSION",
    "candidate_identity",
    "deduplicate_ranked",
    "evidence_score",
    "normalize_record",
    "rank_record",
    "stable_sort_key",
]
