"""Proof-safe OpenEvolve evaluator for coset two-block Stage 1.

There is deliberately no BP/OSD call in this module.  Decoder-returned logical
weights are distance upper bounds and cannot improve fitness.  Positive
distance credit is derived only from a complete two-sector low-weight UNSAT
decision (or a future independently replayed exact-distance field produced by
this evaluator).  A replayed SAT witness rejects the candidate whenever it is
below the dynamic FOM=12 exclusion threshold.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import math
import os
import sys
import time
from collections import Counter
from collections.abc import Mapping
from pathlib import Path
from typing import Any

import numpy as np
from qldpc import codes
from qldpc.objects import Pauli

from evaluation.low_weight_oracle import (
    evaluate_css_low_weight_oracle,
    verify_css_low_weight_oracle,
)
from evolve.coset_search_contract import (
    COSET_ACTION_FAMILY_METRIC,
    COSET_EVALUATOR_KIND,
    COSET_FEATURE_BINS,
    COSET_MAP_SCHEMA_METRIC,
    COSET_MAP_SCHEMA_VERSION,
    COSET_SUBGROUP_NORMALITY_METRIC,
    COSET_SUPPORT_ORBIT_METRIC,
    LOW_WEIGHT_ORACLE_THRESHOLD,
    MAX_GENERATED_CANDIDATES,
    TARGET_FOM,
    action_search_view,
    action_search_views,
    candidate_digest,
    normalize_candidate,
    quota_by_normality,
    support_orbit_bin,
)


MAP_DESCRIPTOR_VERSION_METRIC = "map_descriptor_version"
MAP_DESCRIPTOR_VERSION = 4  # launcher envelope; coset semantics use own v1 marker
EVALUATOR_KIND_ID_METRIC = "qcode_evaluator_kind_id"
EVALUATOR_KIND_ID = 1.0
ACTION_CATALOG_ID_METRIC = "qcode_action_catalog_id"
CANDIDATE_LOG_PATH_ENV = "QCODE_CANDIDATE_LOG_PATH"
PREFLIGHT_CONTRACT_ID_ENV = "QCODE_WINNER_PREFLIGHT_CONTRACT_ID"
PREFLIGHT_CONTRACT_VERSION = 2
PREFLIGHT_UNIT_KIND_ID = 1.0  # action strata, not BB lattices
PREFLIGHT_UNIT_KIND_ID_METRIC = "winner_preflight_unit_kind_id"
PREFLIGHT_UNITS_METRIC = "winner_preflight_units"
PREFLIGHT_ACTION_STRATA_METRIC = "winner_preflight_action_strata"
MAX_ORACLE_CANDIDATES = 8


def _source_sha256(path: str | Path) -> str:
    source = Path(path)
    if source.is_symlink() or not source.is_file():
        raise ValueError(f"evolved program must be a regular file: {source}")
    return hashlib.sha256(source.read_bytes()).hexdigest()


def _load_program(program_path: str):
    path = Path(program_path).resolve(strict=True)
    source_hash = _source_sha256(path)
    module_name = f"qcode_coset_candidate_{source_hash}_{os.getpid()}"
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load evolved coset program")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    try:
        spec.loader.exec_module(module)
    finally:
        sys.modules.pop(module_name, None)
    if _source_sha256(path) != source_hash:
        raise RuntimeError("evolved coset program changed during import")
    generator = getattr(module, "generate_candidates", None)
    if not callable(generator):
        raise ValueError("evolved coset program has no generate_candidates()")
    return generator, source_hash, path


def _gf2_rank(matrix: np.ndarray) -> int:
    """Rank over F2 using packed Python rows, independent of qldpc caches."""

    array = np.ascontiguousarray(np.asarray(matrix, dtype=np.uint8) & 1)
    if array.ndim != 2:
        raise ValueError("parity check must be a matrix")
    rows = [
        int.from_bytes(np.packbits(row, bitorder="little").tobytes(), "little")
        for row in array
    ]
    rank = 0
    column_count = int(array.shape[1])
    for column in range(column_count - 1, -1, -1):
        pivot = next(
            (index for index in range(rank, len(rows)) if (rows[index] >> column) & 1),
            None,
        )
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        pivot_row = rows[rank]
        for index in range(len(rows)):
            if index != rank and ((rows[index] >> column) & 1):
                rows[index] ^= pivot_row
        rank += 1
        if rank == len(rows):
            break
    return rank


def _matrix_pair_from_builder(candidate: Mapping[str, Any]):
    """Build through the immutable catalog and normalize its public result."""

    from evaluation import coset_two_block as builder

    build = getattr(builder, "build_coset_candidate", None)
    if not callable(build):
        build = getattr(builder, "build_coset_two_block", None)
    if not callable(build):
        raise RuntimeError(
            "coset builder does not expose build_coset_candidate()"
        )
    try:
        built = build(candidate)
    except TypeError:
        built = build(
            candidate["action_id"],
            candidate["left_support"],
            candidate["right_support"],
        )
    if isinstance(built, Mapping):
        code = built.get("code")
        hx = built.get("hx", built.get("matrix_x"))
        hz = built.get("hz", built.get("matrix_z"))
    else:
        code = built
        hx = getattr(built, "matrix_x", None)
        hz = getattr(built, "matrix_z", None)
    if code is not None and (hx is None or hz is None):
        hx = getattr(code, "matrix_x", None)
        hz = getattr(code, "matrix_z", None)
    if hx is None or hz is None:
        raise RuntimeError("coset builder did not return HX/HZ matrices")
    matrix_x = np.ascontiguousarray(np.asarray(hx, dtype=np.uint8) & 1)
    matrix_z = np.ascontiguousarray(np.asarray(hz, dtype=np.uint8) & 1)
    if matrix_x.ndim != 2 or matrix_z.ndim != 2:
        raise ValueError("coset HX/HZ must be matrices")
    if matrix_x.shape[1] != matrix_z.shape[1]:
        raise ValueError("coset HX/HZ have different block lengths")
    return matrix_x, matrix_z


def _action_catalog_sha256() -> str:
    """Return the immutable action-catalog identity used by later stages."""

    from evaluation import coset_two_block as builder

    value = getattr(builder, "ACTION_CATALOG_SHA256", None)
    if callable(value):
        value = value()
    if value is None:
        provider = getattr(builder, "action_catalog_sha256", None)
        if callable(provider):
            value = provider()
    if value is None:
        catalog_path = Path(builder.__file__).with_name(
            "coset_two_block_actions.v1.json"
        )
        value = _source_sha256(catalog_path)
    if (
        not isinstance(value, str)
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise RuntimeError("coset action catalog SHA-256 is invalid")
    return value


def _action_catalog_contract_id() -> float:
    # Thirteen hex digits fit exactly in an IEEE-754 double and therefore
    # survive OpenEvolve's numeric metric/checkpoint round trip.
    return float(int(_action_catalog_sha256()[:13], 16))


def _stage2_construction(candidate: Mapping[str, Any]) -> dict[str, Any]:
    """Export the compact, source-bound construction consumed by Stage 2."""

    normalized = normalize_candidate(candidate)
    construction = {
        "kind": "coset-two-block-v1",
        "action_id": normalized["action_id"],
        "action_catalog_sha256": _action_catalog_sha256(),
        "left_support": list(normalized["left_support"]),
        "right_support": list(normalized["right_support"]),
    }
    # When the immutable builder exposes its normalizer, replay it here.  The
    # explicit projection below ensures evolved code still cannot add fields.
    from evaluation import coset_two_block as builder

    validator = getattr(builder, "normalize_construction", None)
    if not callable(validator):
        validator = getattr(builder, "normalize_coset_construction", None)
    if callable(validator):
        replayed = validator(construction)
        if isinstance(replayed, Mapping) and isinstance(
            replayed.get("construction"), Mapping
        ):
            replayed = replayed["construction"]
        if not isinstance(replayed, Mapping):
            raise RuntimeError("coset construction normalizer returned no object")
        for name, expected in construction.items():
            if replayed.get(name) != expected:
                raise RuntimeError(
                    f"coset construction normalizer changed {name}"
                )
    return construction


def _tanner_component_count(hx: np.ndarray, hz: np.ndarray) -> int:
    """Count connected components of the combined CSS Tanner graph."""

    checks = np.vstack((hx, hz))
    check_count, qubit_count = checks.shape
    node_count = check_count + qubit_count
    parents = list(range(node_count))

    def find(node: int) -> int:
        while parents[node] != node:
            parents[node] = parents[parents[node]]
            node = parents[node]
        return node

    def union(left: int, right: int) -> None:
        root_left = find(left)
        root_right = find(right)
        if root_left != root_right:
            parents[root_right] = root_left

    for check_index, row in enumerate(checks):
        for qubit_index in np.flatnonzero(row):
            union(check_index, check_count + int(qubit_index))
    return len({find(node) for node in range(node_count)})


def _static_candidate(candidate: Mapping[str, Any]) -> dict[str, Any]:
    normalized = normalize_candidate(candidate)
    view = action_search_view(normalized["action_id"])
    hx, hz = _matrix_pair_from_builder(normalized)
    n = int(hx.shape[1])
    if n != 2 * view.block_size:
        raise ValueError("coset builder block size disagrees with catalog")
    css_commutation = not bool(np.any((hx @ hz.T) & 1))
    row_weights = np.concatenate((hx.sum(axis=1), hz.sum(axis=1)))
    column_degrees = np.vstack((hx, hz)).sum(axis=0)
    max_check_weight = int(row_weights.max(initial=0))
    max_qubit_degree = int(column_degrees.max(initial=0))
    tanner_components = _tanner_component_count(hx, hz)
    legal = bool(
        css_commutation
        and max_check_weight <= 6
        and max_qubit_degree <= 6
        and tanner_components == 1
    )
    rank_x = _gf2_rank(hx)
    rank_z = _gf2_rank(hz)
    k = n - rank_x - rank_z
    if k < 0:
        raise RuntimeError("coset CSS rank accounting produced negative k")
    return {
        "candidate": normalized,
        "construction": _stage2_construction(normalized),
        "candidate_sha256": candidate_digest(normalized),
        "action_id": view.action_id,
        "action_family_bin": view.action_family_bin,
        "subgroup_normal": view.subgroup_normal,
        "support_orbit_bin": support_orbit_bin(normalized),
        "hx": hx,
        "hz": hz,
        "n": n,
        "k": int(k),
        "rank_x": rank_x,
        "rank_z": rank_z,
        "css_commutation": css_commutation,
        "max_check_weight": max_check_weight,
        "max_qubit_degree": max_qubit_degree,
        "tanner_components": tanner_components,
        "static_legal": legal,
    }


def _dynamic_rejection_cutoff(n: int, k: int) -> int | None:
    if k <= 0:
        return None
    return int(math.floor(math.sqrt(TARGET_FOM * n / k)))


def _oracle_probe_rows(
    rows: list[dict[str, Any]],
    limit: int = MAX_ORACLE_CANDIDATES,
) -> list[dict[str, Any]]:
    """Select proof probes without starving an action/normality stratum."""

    eligible = [
        row for row in rows if row["static_legal"] and row["k"] > 0
    ]
    views = action_search_views()
    quotas = quota_by_normality(views, min(limit, len(eligible)))

    def priority(row: Mapping[str, Any]) -> tuple[Any, ...]:
        return (
            -(row["k"] / row["n"]),
            row["support_orbit_bin"],
            row["candidate_sha256"],
        )

    selected: list[dict[str, Any]] = []
    selected_digests: set[str] = set()
    for view in views:
        action_rows = sorted(
            (
                row for row in eligible
                if row["action_id"] == view.action_id
            ),
            key=priority,
        )
        # Probe both high-rate and low-rate ends.  Ranking only by k/n starves
        # the short-logical controls that provide the most useful concrete
        # mutation failures.
        diverse_action_rows: list[dict[str, Any]] = []
        left, right = 0, len(action_rows) - 1
        while left <= right:
            diverse_action_rows.append(action_rows[left])
            left += 1
            if left <= right:
                diverse_action_rows.append(action_rows[right])
                right -= 1
        for row in diverse_action_rows[:quotas.get(view.action_id, 0)]:
            selected.append(row)
            selected_digests.add(row["candidate_sha256"])
    if len(selected) < min(limit, len(eligible)):
        remainder = sorted(
            (
                row for row in eligible
                if row["candidate_sha256"] not in selected_digests
            ),
            key=lambda row: (
                row["subgroup_normal"],
                *priority(row),
            ),
        )
        selected.extend(remainder[:limit - len(selected)])
    return selected


def _run_oracle(row: dict[str, Any]) -> None:
    if not row["static_legal"] or row["k"] <= 0:
        row.update({
            "oracle_outcome": "NOT_RUN",
            "oracle_threshold": None,
            "low_weight_oracle": None,
            "distance_lower_bound": None,
            "low_weight_witness": None,
            "threshold_rejected": False,
            "search_status": "invalid",
        })
        return
    cutoff = _dynamic_rejection_cutoff(row["n"], row["k"])
    assert cutoff is not None
    threshold = min(LOW_WEIGHT_ORACLE_THRESHOLD, cutoff)
    if threshold < 1:
        row.update({
            "oracle_outcome": "NOT_RUN",
            "oracle_threshold": None,
            "low_weight_oracle": None,
            "distance_lower_bound": None,
            "low_weight_witness": None,
            "threshold_rejected": False,
            "search_status": "unresolved",
        })
        return
    code = codes.CSSCode(
        row["hx"],
        row["hz"],
        field=2,
        promise_equal_distance_xz=False,
    )
    if int(code.dimension) != row["k"]:
        raise RuntimeError("independent CSSCode dimension disagrees with GF2 rank")
    lx = np.asarray(code.get_logical_ops(Pauli.X), dtype=np.uint8)
    lz = np.asarray(code.get_logical_ops(Pauli.Z), dtype=np.uint8)
    evidence = evaluate_css_low_weight_oracle(
        row["hx"],
        row["hz"],
        lx,
        lz,
        max_weight=threshold,
        hard_timeout_s=30.0,
    )
    failures = verify_css_low_weight_oracle(
        evidence,
        row["hx"],
        row["hz"],
        lx,
        lz,
    )
    if failures:
        raise RuntimeError("low-weight oracle did not replay: " + "; ".join(failures))
    outcome = evidence["outcome"]
    witness = evidence.get("witness") if outcome == "SAT" else None
    witness_weight = (
        witness.get("weight") if isinstance(witness, Mapping) else None
    )
    row.update({
        "oracle_outcome": outcome,
        "oracle_threshold": threshold,
        "low_weight_oracle": evidence,
        "distance_lower_bound": evidence.get("distance_lower_bound"),
        "low_weight_witness": witness,
        "threshold_rejected": bool(
            outcome == "SAT"
            and isinstance(witness_weight, int)
            and witness_weight <= cutoff
        ),
        "oracle_evidence_sha256": evidence.get("evidence_sha256"),
    })
    if outcome == "SAT" and isinstance(witness_weight, int):
        upper_fom = row["k"] * witness_weight * witness_weight / row["n"]
        rejected = witness_weight <= cutoff
        row.update({
            "d": witness_weight,
            "d_is_exact": False,
            "distance_trusted": False,
            "distance_status": "upper_bound",
            "distance_upper_bound": witness_weight,
            "distance_upper_bound_source": "low_weight_oracle",
            "fom": upper_fom,
            "fom_upper_bound": upper_fom,
            "fitness_distance_credit": 0.0,
            "stage": "low_weight_oracle_rejected",
            "search_status": "terminal_negative",
            "threshold_rejection_proven": rejected,
            "threshold_proof_source": "low_weight_oracle",
            "threshold_proof_distance": witness_weight,
            "threshold_proof_witness": witness,
            "fom_rejection_cutoff": cutoff,
            "challenge_rejection_cutoff": cutoff,
            "minimum_winning_distance": cutoff + 1,
            "fom_target_excluded_by_upper_bound": rejected,
            "final_gate_excluded_by_upper_bound": rejected,
            "search_final_gate_excluded_by_upper_bound": rejected,
            "candidate_persistence_lane": "negative_search_feedback",
            "candidate_persistence_reason": (
                "replayed_low_weight_logical_witness"
            ),
        })
    elif outcome == "UNSAT":
        lower_bound = evidence.get("distance_lower_bound")
        row.update({
            "distance_lower_bound_proven": isinstance(lower_bound, int),
            "distance_lower_bound_status": "search_oracle_proven",
            "fom_lower_bound": (
                row["k"] * lower_bound * lower_bound / row["n"]
                if isinstance(lower_bound, int)
                else None
            ),
            "low_weight_oracle_threshold": threshold,
            "search_status": "certified_lower_bound",
        })
    else:
        row.update({
            "distance_retry_required": True,
            "search_status": "unresolved",
        })


def _fitness(row: Mapping[str, Any]) -> float:
    """Score only exact/static facts and proof-safe distance evidence."""

    if (
        not row.get("static_legal")
        or row.get("k", 0) <= 0
        or row.get("threshold_rejected") is True
    ):
        return 0.0
    n = int(row["n"])
    k = int(row["k"])
    score = 0.10  # directly rebuilt static legality
    score += 0.25 * min(1.0, (k / n) / 0.25)  # exact rank-derived rate
    lower = row.get("distance_lower_bound")
    if isinstance(lower, int) and lower > 0:
        proven_fom = k * lower * lower / n
        score += 0.45 * min(1.0, proven_fom / TARGET_FOM)
    exact = row.get("exact_distance")
    if isinstance(exact, int) and exact > 0:
        exact_fom = k * exact * exact / n
        score += 0.20 * min(1.0, exact_fom / TARGET_FOM)
    return min(score, 1.0)


def _safe_json_row(row: Mapping[str, Any]) -> dict[str, Any]:
    record = {
        **dict(row["candidate"]),
        "construction": dict(row["construction"]),
        "candidate_sha256": row["candidate_sha256"],
        "n": row["n"],
        "k": row["k"],
        "rank_x": row["rank_x"],
        "rank_z": row["rank_z"],
        "css_commutation": row["css_commutation"],
        "max_check_weight": row["max_check_weight"],
        "max_qubit_degree": row["max_qubit_degree"],
        "tanner_components": row["tanner_components"],
        "static_legal": row["static_legal"],
        "subgroup_normal": row["subgroup_normal"],
        "support_orbit_bin": row["support_orbit_bin"],
        "low_weight_oracle_outcome": row.get("oracle_outcome", "NOT_RUN"),
        "low_weight_oracle_threshold": row.get("oracle_threshold"),
        "low_weight_oracle": row.get("low_weight_oracle"),
        "distance_lower_bound": row.get("distance_lower_bound"),
        "low_weight_witness": row.get("low_weight_witness"),
        "threshold_rejected": row.get("threshold_rejected", False),
        "fitness": row["fitness"],
        "distance_semantics": "proof-lower-bound-or-replayed-witness-only",
    }
    for field in (
        "d",
        "d_is_exact",
        "distance_trusted",
        "distance_status",
        "distance_upper_bound",
        "distance_upper_bound_source",
        "fom",
        "fom_upper_bound",
        "fitness_distance_credit",
        "distance_lower_bound_proven",
        "distance_lower_bound_status",
        "fom_lower_bound",
        "stage",
        "search_status",
        "distance_retry_required",
        "threshold_rejection_proven",
        "threshold_proof_source",
        "threshold_proof_distance",
        "threshold_proof_witness",
        "fom_rejection_cutoff",
        "challenge_rejection_cutoff",
        "minimum_winning_distance",
        "fom_target_excluded_by_upper_bound",
        "final_gate_excluded_by_upper_bound",
        "search_final_gate_excluded_by_upper_bound",
        "candidate_persistence_lane",
        "candidate_persistence_reason",
    ):
        if field in row:
            record[field] = row[field]
    return record


def _append_candidate_rows(rows: list[dict[str, Any]]) -> int:
    raw_path = os.environ.get(CANDIDATE_LOG_PATH_ENV)
    if raw_path is None:
        return 0
    path = Path(raw_path).expanduser()
    if not path.is_absolute():
        raise RuntimeError("coset candidate log path must be absolute")
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = bytearray()
    for row in rows:
        payload.extend(
            json.dumps(
                _safe_json_row(row),
                sort_keys=True,
                separators=(",", ":"),
                allow_nan=False,
            ).encode("utf-8")
        )
        payload.extend(b"\n")

    # Share the default evaluator's write-ahead log.  A process killed after a
    # partial os.write leaves a complete, fsynced intent that the next writer
    # finishes before appending, so no interior corrupt JSONL row can survive.
    from evolve.openevolve_evaluator import _append_candidate_jsonl

    _append_candidate_jsonl(path, payload)
    return len(rows)


def _entropy(values: list[Any]) -> float:
    if len(values) < 2:
        return 0.0
    counts = Counter(values)
    value = -sum(
        (count / len(values)) * math.log(count / len(values))
        for count in counts.values()
    )
    return value / math.log(len(values))


def _preflight_markers(
    *,
    evaluated: int,
    eligible: int,
    persisted: int,
    action_strata: int,
):
    contract_raw = os.environ.get(PREFLIGHT_CONTRACT_ID_ENV, "0")
    try:
        contract_id = int(contract_raw)
    except ValueError as exc:
        raise RuntimeError("invalid coset preflight contract ID") from exc
    if contract_id < 0:
        raise RuntimeError("invalid coset preflight contract ID")
    expected_strata = len(action_search_views())
    if action_strata != expected_strata:
        raise RuntimeError(
            "coset preflight did not evaluate every enabled action stratum"
        )
    return {
        "winner_preflight_contract_version": float(PREFLIGHT_CONTRACT_VERSION),
        "winner_preflight_contract_id": float(contract_id),
        "winner_preflight_complete": 1.0,
        "winner_preflight_incomplete": 0.0,
        PREFLIGHT_UNIT_KIND_ID_METRIC: PREFLIGHT_UNIT_KIND_ID,
        PREFLIGHT_UNITS_METRIC: float(action_strata),
        PREFLIGHT_ACTION_STRATA_METRIC: float(action_strata),
        "winner_preflight_candidate_definitions_evaluated": float(evaluated),
        "winner_preflight_winner_capable_eligible": float(eligible),
        "winner_preflight_winner_capable_persisted": float(persisted),
        "winner_preflight_winner_capable_omitted": 0.0,
        "winner_preflight_hard_timeout": 0.0,
        "winner_preflight_subprocess_failed": 0.0,
    }


def _evaluate(program_path: str):
    started = time.monotonic()
    generator, program_sha256, source_path = _load_program(program_path)
    raw = generator()
    if not isinstance(raw, (list, tuple)):
        raise ValueError("generate_candidates() must return a list or tuple")
    if len(raw) > MAX_GENERATED_CANDIDATES:
        raise ValueError("coset candidate pool exceeds immutable cap")
    normalized = []
    seen = set()
    invalid = 0
    for candidate in raw:
        try:
            item = normalize_candidate(candidate)
            digest = candidate_digest(item)
        except (TypeError, ValueError):
            invalid += 1
            continue
        if digest in seen:
            continue
        seen.add(digest)
        normalized.append(item)
    expected_action_ids = {
        view.action_id for view in action_search_views()
    }
    observed_action_ids = {
        item["action_id"] for item in normalized
    }
    if observed_action_ids != expected_action_ids:
        raise ValueError(
            "generate_candidates() must cover every search-enabled action"
        )
    rows = []
    build_errors = 0
    for candidate in normalized:
        try:
            rows.append(_static_candidate(candidate))
        except Exception:
            build_errors += 1
    built_action_ids = {row["action_id"] for row in rows}
    if built_action_ids != expected_action_ids:
        missing = sorted(expected_action_ids - built_action_ids)
        raise RuntimeError(
            "coset evaluator failed to build every enabled action stratum: "
            f"missing={missing}"
        )
    oracle_order = _oracle_probe_rows(rows)
    for row in rows:
        row.update({
            "oracle_outcome": "NOT_RUN",
            "oracle_threshold": None,
            "low_weight_oracle": None,
            "distance_lower_bound": None,
            "low_weight_witness": None,
            "threshold_rejected": False,
            "search_status": "unresolved",
        })
    for row in oracle_order:
        _run_oracle(row)
    for row in rows:
        row["fitness"] = _fitness(row)

    eligible_rows = [
        row for row in rows
        if row["static_legal"] and row["k"] > 0 and not row["threshold_rejected"]
    ]
    # Preserve terminal SAT witnesses in the transaction-bound candidate
    # stream so Humanize can replay concrete failure geometry.  These rows are
    # a negative-only advisory lane and do not count as winner-capable
    # preflight persistence or positive fitness.
    persistable_rows = [
        row for row in rows if row["static_legal"] and row["k"] > 0
    ]
    persisted = _append_candidate_rows(persistable_rows)
    if persisted != len(persistable_rows) and os.environ.get(CANDIDATE_LOG_PATH_ENV):
        raise RuntimeError("coset candidate persistence count is incomplete")
    winner_capable_persisted = (
        len(eligible_rows)
        if os.environ.get(CANDIDATE_LOG_PATH_ENV)
        and persisted == len(persistable_rows)
        else 0
    )

    action_diversity = _entropy([row["action_id"] for row in eligible_rows])
    normality_diversity = _entropy([
        row["subgroup_normal"] for row in eligible_rows
    ])
    orbit_diversity = _entropy([
        row["support_orbit_bin"] for row in eligible_rows
    ])
    diversity = (action_diversity + normality_diversity + orbit_diversity) / 3
    best = max(eligible_rows, key=lambda row: row["fitness"], default=None)
    best_fitness = 0.0 if best is None else float(best["fitness"])
    combined_score = min(0.999, 0.8 * best_fitness + 0.199 * diversity)
    metrics = {
        "combined_score": combined_score,
        "exact_k_best": float(0 if best is None else best["k"]),
        "static_legal_candidates": float(sum(row["static_legal"] for row in rows)),
        "unique_candidate_definitions": float(len(normalized)),
        "invalid_candidate_definitions": float(invalid),
        "build_errors": float(build_errors),
        "low_weight_rejections": float(sum(row["threshold_rejected"] for row in rows)),
        "candidate_log_records_persisted": float(persisted),
        "proven_lower_bound_candidates": float(sum(
            isinstance(row.get("distance_lower_bound"), int) for row in rows
        )),
        "action_coverage": float(len({row["action_id"] for row in rows})),
        "normality_coverage": float(len({row["subgroup_normal"] for row in rows})),
        "search_diversity": diversity,
        MAP_DESCRIPTOR_VERSION_METRIC: float(MAP_DESCRIPTOR_VERSION),
        COSET_MAP_SCHEMA_METRIC: float(COSET_MAP_SCHEMA_VERSION),
        EVALUATOR_KIND_ID_METRIC: EVALUATOR_KIND_ID,
        ACTION_CATALOG_ID_METRIC: _action_catalog_contract_id(),
        COSET_ACTION_FAMILY_METRIC: float(
            0 if best is None else best["action_family_bin"]
        ),
        COSET_SUBGROUP_NORMALITY_METRIC: float(
            0 if best is None else int(best["subgroup_normal"])
        ),
        COSET_SUPPORT_ORBIT_METRIC: float(
            0 if best is None else best["support_orbit_bin"]
        ),
        "evaluation_elapsed_s": time.monotonic() - started,
        **_preflight_markers(
            evaluated=len(normalized),
            eligible=len(eligible_rows),
            persisted=winner_capable_persisted,
            action_strata=len(built_action_ids),
        ),
    }
    oracle_failure_lines = []
    for row in sorted(
        (item for item in rows if item["threshold_rejected"]),
        key=lambda item: item["candidate_sha256"],
    )[:8]:
        witness = row.get("low_weight_witness")
        if not isinstance(witness, Mapping):
            continue
        oracle_failure_lines.append(
            "  action={action} side={side} weight={weight} support={support} "
            "left_support={left} right_support={right}".format(
                action=row["action_id"],
                side=witness.get("side"),
                weight=witness.get("weight"),
                support=witness.get("support"),
                left=row["candidate"]["left_support"],
                right=row["candidate"]["right_support"],
            )
        )
    artifacts = {
        "representation": "coset-two-block",
        "evaluator_kind": COSET_EVALUATOR_KIND,
        "program_path": str(source_path),
        "program_sha256": program_sha256,
        "distance_semantics": {
            "bp_upper_bound_positive_credit": False,
            "positive_distance_sources": [
                "replayed two-sector UNSAT lower bound",
                "independently replayed exact distance",
            ],
        },
        "best_candidates": [
            _safe_json_row(row)
            for row in sorted(
                eligible_rows,
                key=lambda item: (-item["fitness"], item["candidate_sha256"]),
            )[:12]
        ],
    }
    if oracle_failure_lines:
        artifacts["low_weight_oracle_failures"] = "\n".join([
            "Replayed short logical operators are negative-only evidence. "
            "Mutate the implicated action/orbit/support mechanism:",
            *oracle_failure_lines,
        ])
    try:
        from openevolve.evaluation_result import EvaluationResult

        return EvaluationResult(metrics=metrics, artifacts=artifacts)
    except ImportError:
        return metrics


def evaluate_stage1(program_path: str):
    return _evaluate(program_path)


def evaluate_stage2(program_path: str):
    # Stage 1 intentionally owns the only search signal for this new family.
    # The campaign config keeps the cascade threshold above every possible
    # score, so reaching this function is a configuration error.
    raise RuntimeError("coset Stage-2 cascade is disabled; use the five-stage pool")


def evaluate(program_path: str):
    return evaluate_stage1(program_path)


__all__ = [
    "evaluate",
    "evaluate_stage1",
    "evaluate_stage2",
]
