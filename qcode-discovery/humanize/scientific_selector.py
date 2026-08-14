"""Negative-only scientific tie-breaks for formal-audit selection.

This module deliberately has a narrow authority boundary.  It replays sealed
Stage-1 evidence, converts every verified BB X/Z witness to one canonical
sector, and counts structural motifs associated with a target-excluding
low-weight logical.  The resulting counts may only *deprioritize* a fresh
candidate.  They are never a distance lower bound, fitness value, promotion
signal, or representation-switch decision.

In particular, BP/OSD fields and reviewer prose are absent from every feature
and priority calculation.  Unresolved (``UNKNOWN``) evidence casts no vote.
"""

from __future__ import annotations

import copy
import hashlib
import json
import re
from collections import Counter
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from math import gcd
from typing import Any

from evaluation.algebraic_mechanisms import classify_algebraic_mechanism
from evaluation.bb_sector_isometry import (
    BB_XZ_ISOMETRY_METHOD,
    bb_xz_inversion_block_swap_permutation,
    verify_bb_xz_sector_isometry,
)
from evaluation.geometry import candidate_geometry, reduce_coordinate
from evaluation.target_policy import (
    DEFAULT_TARGET_MODE,
    target_binding,
    validate_target_mode,
)
from humanize.audit_state import AuditOutcome, classify_evaluation
from humanize.state import code_key


NEGATIVE_WITNESS_POLICY_ID = (
    "qcode-replayed-xz-low-weight-negative-only-selector-priority-v1"
)
NEGATIVE_WITNESS_RISK_INDEX_KIND = (
    "qcode-replayed-negative-witness-selector-risk-index"
)
NEGATIVE_WITNESS_RISK_INDEX_SCHEMA_VERSION = 1
SECTOR_CANONICALIZATION = BB_XZ_ISOMETRY_METHOD

_DIMENSIONS = ("full", "factor", "mechanism_split", "lattice_q")
_WEIGHT_BUCKETS = (
    "weight_le_6",
    "weight_le_8",
    "target_excluding",
)
_SHA256 = re.compile(r"[0-9a-f]{64}")
NEGATIVE_WITNESS_PRIORITY_COMPONENTS = len(_DIMENSIONS) * len(
    _WEIGHT_BUCKETS
)


def _canonical_sha256(value: Any) -> str:
    encoded = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _strict_positive_int(value: Any, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 1:
        raise ValueError(f"{label} must be a positive integer")
    return int(value)


def _normalised_support(
    value: Any,
    *,
    label: str,
    ell: int,
    m: int,
    geometry: Mapping[str, Any] | None,
) -> tuple[tuple[int, int], ...]:
    if not isinstance(value, (list, tuple)) or not value:
        raise ValueError(f"{label} must be a non-empty support")
    terms: list[tuple[int, int]] = []
    for index, term in enumerate(value):
        if (
            not isinstance(term, (list, tuple))
            or len(term) != 2
            or any(isinstance(item, bool) or not isinstance(item, int) for item in term)
        ):
            raise ValueError(f"{label}[{index}] must be an integer pair")
        terms.append(
            reduce_coordinate(
                ell,
                m,
                int(term[0]),
                int(term[1]),
                geometry,
            )
        )
    if len(set(terms)) != len(terms):
        raise ValueError(f"{label} contains duplicate quotient monomials")
    return tuple(sorted(terms))


def _element_order(
    delta: tuple[int, int],
    *,
    ell: int,
    m: int,
    geometry: Mapping[str, Any] | None,
) -> int:
    reduced = reduce_coordinate(ell, m, delta[0], delta[1], geometry)
    if reduced == (0, 0):
        return 1
    for multiplier in range(1, ell * m + 1):
        if reduce_coordinate(
            ell,
            m,
            multiplier * reduced[0],
            multiplier * reduced[1],
            geometry,
        ) == (0, 0):
            return multiplier
    raise ValueError("quotient element order exceeds its finite volume")


def _difference_order_multiset(
    terms: tuple[tuple[int, int], ...],
    *,
    ell: int,
    m: int,
    geometry: Mapping[str, Any] | None,
) -> list[int]:
    return sorted(
        _element_order(
            (right[0] - left[0], right[1] - left[1]),
            ell=ell,
            m=m,
            geometry=geometry,
        )
        for index, left in enumerate(terms)
        for right in terms[index + 1 :]
    )


def _candidate_feature_descriptors(
    row: Mapping[str, Any],
) -> dict[str, dict[str, Any]]:
    """Derive risk coordinates solely from the defining BB construction."""

    ell = _strict_positive_int(row.get("ell"), "ell")
    m = _strict_positive_int(row.get("m"), "m")
    geometry = candidate_geometry(row)
    twist = 0 if geometry is None else int(geometry["twist"])
    support_a = _normalised_support(
        row.get("A_terms"),
        label="A_terms",
        ell=ell,
        m=m,
        geometry=geometry,
    )
    support_b = _normalised_support(
        row.get("B_terms"),
        label="B_terms",
        ell=ell,
        m=m,
        geometry=geometry,
    )
    mechanism = classify_algebraic_mechanism(
        support_a,
        support_b,
        ell=ell,
        m=m,
        geometry=geometry,
    )
    lattice_q = {"ell": ell, "m": m, "q": twist}
    smith_d1 = gcd(gcd(ell, m), twist)
    factor = {
        "smith_invariants": [smith_d1, ell * m // smith_d1],
        "A_difference_orders": _difference_order_multiset(
            support_a,
            ell=ell,
            m=m,
            geometry=geometry,
        ),
        "B_difference_orders": _difference_order_multiset(
            support_b,
            ell=ell,
            m=m,
            geometry=geometry,
        ),
        "orbit_span_bin": int(mechanism["orbit_span_bin"]),
        "difference_spectrum_bin": int(
            mechanism["difference_spectrum_bin"]
        ),
    }
    mechanism_split = {
        "algebraic_mechanism": str(mechanism["relation_type"]),
        "support_split": str(mechanism["support_split_type"]),
    }
    return {
        "full": {
            "lattice_q": lattice_q,
            "A_terms": [list(term) for term in support_a],
            "B_terms": [list(term) for term in support_b],
        },
        "factor": factor,
        "mechanism_split": mechanism_split,
        "lattice_q": lattice_q,
    }


def _feature_keys(
    descriptors: Mapping[str, Mapping[str, Any]],
) -> dict[str, str]:
    return {
        dimension: _canonical_sha256(
            {"dimension": dimension, "descriptor": descriptors[dimension]}
        )
        for dimension in _DIMENSIONS
    }


def _formal_witness(row: Mapping[str, Any]) -> Mapping[str, Any] | None:
    if row.get("threshold_proof_source") == "symplectic_upper_bound":
        witness = row.get("symplectic_weight_witness")
        return witness if isinstance(witness, Mapping) else None
    details = row.get("milp_details")
    witness = (
        details.get("minimum_direction_witness")
        if isinstance(details, Mapping)
        else None
    )
    if not isinstance(witness, Mapping):
        witness = row.get("threshold_proof_witness")
    return witness if isinstance(witness, Mapping) else None


def _validated_witness(
    row: Mapping[str, Any], witness: Mapping[str, Any]
) -> tuple[str, int, tuple[int, ...]]:
    n = _strict_positive_int(row.get("n"), "n")
    side = witness.get("side")
    weight = witness.get("weight")
    bits = witness.get("bits")
    if (
        side not in {"X", "Z"}
        or isinstance(weight, bool)
        or not isinstance(weight, int)
        or weight < 1
        or not isinstance(bits, list)
        or len(bits) != n
        or any(type(bit) is not int or bit not in {0, 1} for bit in bits)
        or sum(bits) != weight
    ):
        raise ValueError("formal low-weight witness is malformed")
    return str(side), int(weight), tuple(
        index for index, bit in enumerate(bits) if bit
    )


def _rebuild_bb_matrices(row: Mapping[str, Any]) -> tuple[Any, Any]:
    from evaluation.bb_code import build_bb_code
    from evaluation.distance_milp import get_code_matrices

    ell = _strict_positive_int(row.get("ell"), "ell")
    m = _strict_positive_int(row.get("m"), "m")
    code = build_bb_code(
        ell,
        m,
        [tuple(term) for term in row.get("A_terms", ())],
        [tuple(term) for term in row.get("B_terms", ())],
        geometry=candidate_geometry(row),
    )
    if (
        int(code.num_qudits) != _strict_positive_int(row.get("n"), "n")
        or int(code.dimension) != _strict_positive_int(row.get("k"), "k")
    ):
        raise ValueError("formal witness candidate dimensions do not replay")
    hx, hz, _lx, _lz = get_code_matrices(code)
    return hx, hz


def _canonical_witness_support(
    row: Mapping[str, Any],
    *,
    side: str,
    support: tuple[int, ...],
) -> tuple[tuple[int, ...], dict[str, Any]]:
    """Verify the BB isometry and erase the raw X/Z sector label."""

    ell = _strict_positive_int(row.get("ell"), "ell")
    m = _strict_positive_int(row.get("m"), "m")
    geometry = candidate_geometry(row)
    hx, hz = _rebuild_bb_matrices(row)
    report = verify_bb_xz_sector_isometry(
        hx,
        hz,
        ell=ell,
        m=m,
        geometry=geometry,
    )
    if report.get("verified") is not True:
        raise ValueError("BB X/Z sector isometry did not replay")
    permutation = bb_xz_inversion_block_swap_permutation(
        ell,
        m,
        geometry=geometry,
    )
    canonical = (
        support
        if side == "X"
        else tuple(sorted(int(permutation[index]) for index in support))
    )
    if len(canonical) != len(support) or len(set(canonical)) != len(canonical):
        raise ValueError("BB X/Z sector canonicalization is not bijective")
    return tuple(sorted(canonical)), report


def _weight_bucket_names(weight: int) -> tuple[str, ...]:
    # Every admitted observation was already checked at ``weight < required``.
    # Name the cumulative terminal rung explicitly so a sealed artifact cannot
    # be mistaken for a count of all formal negative outcomes.
    buckets = ["target_excluding"]
    if weight <= 8:
        buckets.insert(0, "weight_le_8")
    if weight <= 6:
        buckets.insert(0, "weight_le_6")
    return tuple(buckets)


@dataclass(frozen=True)
class NegativeWitnessRiskIndex:
    """Hash-bound, negative-only lookup used as a late selector tie-break."""

    source_rows_sha256: str
    source_rows: int
    target_mode: str
    representation_id: str
    risks: dict[str, dict[str, dict[str, Any]]]
    observations: tuple[dict[str, Any], ...]
    exclusion_counts: dict[str, int]

    def _risk_payload(self) -> dict[str, Any]:
        """Return the non-recursive payload committed by selector context."""

        return {
            "schema_version": NEGATIVE_WITNESS_RISK_INDEX_SCHEMA_VERSION,
            "kind": NEGATIVE_WITNESS_RISK_INDEX_KIND,
            "policy_id": NEGATIVE_WITNESS_POLICY_ID,
            "target_mode": self.target_mode,
            "representation_id": self.representation_id,
            "source_rows_sha256": self.source_rows_sha256,
            "source_rows": self.source_rows,
            "risks": copy.deepcopy(self.risks),
            "observations": [copy.deepcopy(item) for item in self.observations],
            "diagnostics": self.build_diagnostics(),
            "semantics": "negative-selector-tie-break-only",
        }

    def risk_index_sha256(self) -> str:
        return _canonical_sha256(self._risk_payload())

    def context(self) -> dict[str, Any]:
        """Return the closed, self-hashed context admitted by quota schema v2."""

        unsigned = {
            "source_rows_sha256": self.source_rows_sha256,
            "source_rows": self.source_rows,
            "target_mode": self.target_mode,
            "representation_id": self.representation_id,
            "risk_index_sha256": self.risk_index_sha256(),
            "unknown_semantics": "fail-open-no-vote",
            "bp_osd_positive_credit": False,
            "sector_canonicalization": SECTOR_CANONICALIZATION,
        }
        return {"context_sha256": _canonical_sha256(unsigned), **unsigned}

    def priority_key(self, row: Mapping[str, Any]) -> tuple[int, ...]:
        """Return a lexicographic key where larger values are always preferred.

        Every component is zero or negative.  Thus this policy can only add a
        penalty for resemblance to replayed bad witnesses; it can never grant
        positive distance credit to any candidate.
        """

        try:
            keys = _feature_keys(_candidate_feature_descriptors(row))
        except (KeyError, TypeError, ValueError):
            return (0,) * NEGATIVE_WITNESS_PRIORITY_COMPONENTS
        values: list[int] = []
        for dimension in _DIMENSIONS:
            entry = self.risks.get(dimension, {}).get(keys[dimension], {})
            counts = entry.get("counts", {}) if isinstance(entry, Mapping) else {}
            values.extend(-int(counts.get(bucket, 0)) for bucket in _WEIGHT_BUCKETS)
        return tuple(values)

    def diagnostics(self, row: Mapping[str, Any]) -> dict[str, Any]:
        """Explain a priority key without exposing any positive score signal."""

        try:
            descriptors = _candidate_feature_descriptors(row)
            keys = _feature_keys(descriptors)
        except (KeyError, TypeError, ValueError):
            return {
                "policy_id": NEGATIVE_WITNESS_POLICY_ID,
                "eligible": False,
                "priority_key": list(self.priority_key(row)),
                "semantics": "invalid-coordinate-no-vote",
            }
        matched: dict[str, Any] = {}
        for dimension in _DIMENSIONS:
            entry = self.risks.get(dimension, {}).get(keys[dimension])
            matched[dimension] = {
                "feature_sha256": keys[dimension],
                "counts": (
                    {bucket: int(entry["counts"][bucket]) for bucket in _WEIGHT_BUCKETS}
                    if isinstance(entry, Mapping)
                    else {bucket: 0 for bucket in _WEIGHT_BUCKETS}
                ),
            }
        return {
            "policy_id": NEGATIVE_WITNESS_POLICY_ID,
            "eligible": True,
            "priority_key": list(self.priority_key(row)),
            "matched_negative_risk": matched,
            "semantics": "negative-only-no-distance-or-promotion-credit",
        }

    def build_diagnostics(self) -> dict[str, Any]:
        return {
            "policy_id": NEGATIVE_WITNESS_POLICY_ID,
            "source_rows": self.source_rows,
            "distinct_negative_candidates": len(self.observations),
            "exclusion_counts": dict(sorted(self.exclusion_counts.items())),
            "weight_counts": dict(sorted(Counter(
                (
                    "weight_le_6"
                    if item["weight"] <= 6
                    else "weight_le_8"
                    if item["weight"] <= 8
                    else "weight_gt_8"
                )
                for item in self.observations
            ).items())),
            "raw_sector_counts_available": False,
            "unknown_semantics": "fail-open-no-vote",
            "bp_osd_positive_credit": False,
        }

    def as_dict(self) -> dict[str, Any]:
        payload = self._risk_payload()
        return {
            **payload,
            "context": self.context(),
            "risk_index_sha256": _canonical_sha256(payload),
        }


def build_negative_witness_risk_index(
    prior_audit_rows: Sequence[Mapping[str, Any]],
    *,
    target_mode: str = DEFAULT_TARGET_MODE,
    representation_id: str,
    source_rows_sha256: str | None = None,
) -> NegativeWitnessRiskIndex:
    """Replay formal checkpoints and build a sector-neutral risk index.

    Malformed, missing, timeout, or otherwise unresolved evidence is ignored
    (fail open).  Only an exact target loser or a formally threshold-rejected
    candidate with a verified witness below the recomputed required distance
    contributes one negative vote.  Repeated rows for one ``candidate_key``
    contribute at most once; the lowest-weight replayed witness wins.
    """

    if isinstance(prior_audit_rows, (str, bytes)) or not isinstance(
        prior_audit_rows, Sequence
    ):
        raise TypeError("prior_audit_rows must be a sequence")
    rows = [dict(row) for row in prior_audit_rows]
    target_mode = validate_target_mode(target_mode)
    if not isinstance(representation_id, str) or not representation_id:
        raise ValueError("representation_id must be a non-empty string")
    observed_source_sha256 = _canonical_sha256(rows)
    if source_rows_sha256 is None:
        source_rows_sha256 = observed_source_sha256
    elif (
        not isinstance(source_rows_sha256, str)
        or _SHA256.fullmatch(source_rows_sha256) is None
        or source_rows_sha256 != observed_source_sha256
    ):
        raise ValueError(
            "source_rows_sha256 must match the canonical source rows"
        )

    exclusions: Counter[str] = Counter()
    by_candidate: dict[
        str,
        tuple[tuple[int, str, str], dict[str, Any], dict[str, dict[str, Any]]],
    ] = {}
    for row in rows:
        if row.get("search_representation_id") != representation_id:
            exclusions["incompatible_representation_no_vote"] += 1
            continue
        attempt = row.get("audit_attempt")
        if (
            not isinstance(attempt, Mapping)
            or attempt.get("schema_version") != 2
            or not isinstance(attempt.get("evidence"), Mapping)
        ):
            exclusions["not_sealed_formal_checkpoint"] += 1
            continue
        try:
            outcome = classify_evaluation(row)
        except Exception:
            # A corrupted or incompatible historical proof is not evidence
            # that the current candidate family is bad.  It therefore casts
            # no vote instead of failing the selector closed around bad data.
            exclusions["formal_replay_failed_no_vote"] += 1
            continue
        if outcome not in {AuditOutcome.EXACT, AuditOutcome.THRESHOLD_REJECTED}:
            exclusions["unknown_no_vote"] += 1
            continue
        try:
            n = _strict_positive_int(row.get("n"), "n")
            k = _strict_positive_int(row.get("k"), "k")
            required = int(target_binding(n, k, target_mode)["required_distance"])
            if outcome is AuditOutcome.EXACT:
                exact_distance = _strict_positive_int(row.get("d"), "d")
                if exact_distance >= required:
                    exclusions["exact_target_nonnegative_no_vote"] += 1
                    continue
            witness = _formal_witness(row)
            if witness is None:
                exclusions["missing_witness_no_vote"] += 1
                continue
            side, weight, support = _validated_witness(row, witness)
            if weight >= required:
                exclusions["witness_not_target_negative_no_vote"] += 1
                continue
            canonical_support, isometry = _canonical_witness_support(
                row,
                side=side,
                support=support,
            )
            descriptors = _candidate_feature_descriptors(row)
            keys = _feature_keys(descriptors)
            candidate_key = code_key(dict(row))
            witness_sha256 = _canonical_sha256(dict(witness))
        except Exception:
            exclusions["witness_or_isometry_replay_failed_no_vote"] += 1
            continue
        observation = {
            "candidate_key": candidate_key,
            "outcome": outcome.value,
            "weight": weight,
            "required_distance": required,
            "canonical_sector": "X",
            "sector_canonicalization": SECTOR_CANONICALIZATION,
            "canonical_support_sha256": _canonical_sha256(
                {"sector": "X", "support": list(canonical_support)}
            ),
            "witness_sha256": witness_sha256,
            "isometry_report_sha256": isometry.get("report_sha256"),
            "feature_keys": keys,
        }
        previous = by_candidate.get(candidate_key)
        order = (weight, witness_sha256, outcome.value)
        if previous is None or order < previous[0]:
            if previous is not None:
                exclusions["duplicate_candidate_replaced"] += 1
            by_candidate[candidate_key] = (order, observation, descriptors)
        else:
            exclusions["duplicate_candidate_ignored"] += 1

    risks: dict[str, dict[str, dict[str, Any]]] = {
        dimension: {} for dimension in _DIMENSIONS
    }
    observations: list[dict[str, Any]] = []
    for candidate_key in sorted(by_candidate):
        _order, observation, descriptors = by_candidate[candidate_key]
        observations.append(observation)
        for dimension in _DIMENSIONS:
            feature_key = observation["feature_keys"][dimension]
            entry = risks[dimension].setdefault(
                feature_key,
                {
                    "descriptor": copy.deepcopy(descriptors[dimension]),
                    "counts": {bucket: 0 for bucket in _WEIGHT_BUCKETS},
                },
            )
            for bucket in _weight_bucket_names(int(observation["weight"])):
                entry["counts"][bucket] += 1

    return NegativeWitnessRiskIndex(
        source_rows_sha256=source_rows_sha256,
        source_rows=len(rows),
        target_mode=target_mode,
        representation_id=representation_id,
        risks=risks,
        observations=tuple(observations),
        exclusion_counts=dict(sorted(exclusions.items())),
    )


__all__ = [
    "NEGATIVE_WITNESS_POLICY_ID",
    "NEGATIVE_WITNESS_PRIORITY_COMPONENTS",
    "NEGATIVE_WITNESS_RISK_INDEX_KIND",
    "NEGATIVE_WITNESS_RISK_INDEX_SCHEMA_VERSION",
    "NegativeWitnessRiskIndex",
    "SECTOR_CANONICALIZATION",
    "build_negative_witness_risk_index",
]
