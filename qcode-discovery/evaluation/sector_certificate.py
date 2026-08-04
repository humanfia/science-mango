"""Typed exact CSS BB certificates from complete SAT sector decisions.

This certificate schema proves the exact distance ``d = R`` with two distinct
pieces of evidence:

* complete UNSAT decisions for every X/Z logical sector below weight ``R``;
* one algebraically replayable nontrivial logical operator of weight ``R``.

The lower-bound decisions may be either two global logical-OR instances or a
disjoint first-nonzero-logical partition in each sector.  They are never
presented as fictitious ``2k`` MILP optima.  Verification rebuilds the BB
matrices, replays the witness, and reruns every SAT decision.
"""

from __future__ import annotations

import hashlib
import inspect
import json
import math
import platform
import re
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Any, Callable, Mapping

import numpy as np

from evaluation.bb_code import build_bb_code
from evaluation.bb_sector_isometry import verify_bb_xz_sector_isometry
from evaluation.certificate import (
    _certificate_sha256,
    _file_sha256,
    _package_version,
    _validate_solver_workers,
)
from evaluation.challenge_gate import evaluate_challenge_gate
from evaluation.distance_milp import get_code_matrices
from evaluation.distance_sat import (
    SAT_ENCODINGS,
    SAT_EVIDENCE_KIND,
    SAT_EVIDENCE_SCHEMA_VERSION,
    SAT_FORMULATION,
    solve_css_threshold_sat,
    verify_css_threshold_sat_witness,
)
from evaluation.failure_disposition import incomplete_result_disposition
from evaluation.final_gate import (
    SECTOR_SAT_EXACT_PROOF_TYPE,
    _matrix_sha256,
    _rank_f2,
    minimum_winning_distance,
)
from evaluation.geometry import candidate_geometry
from evaluation.registry import check_code_novelty


SCHEMA_VERSION = 1
CERTIFICATE_TYPE = "qldpc-css-bb-sector-sat-exact"
FORMULATION = "css-bb-exact-distance-sector-sat-v1"
REQUEST_FIELD = "_exact_sector_certificate"
STAGE3_GATE = "qldpc-frontier-sat-sector-exact-screen"
GLOBAL_MODE = "global"
PARTITION_MODE = "first-nonzero"
SUPPORTED_MODES = frozenset({GLOBAL_MODE, PARTITION_MODE})
_SAT_FORMULATIONS = frozenset({
    SAT_FORMULATION,
    "css-first-nonzero-logical-threshold-cnf-v1",
})
_SAFE_SOLVER_NAME = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.+-]{0,63}")
_SAT_ENCODINGS = frozenset(SAT_ENCODINGS)

SectorSolver = Callable[..., dict[str, Any]]


def _canonical_sha256(value: Any, *, omit: str | None = None) -> str:
    payload = dict(value) if isinstance(value, Mapping) else value
    if omit is not None and isinstance(payload, dict):
        payload.pop(omit, None)
    encoded = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def _array_sha256(name: str, value: np.ndarray) -> str:
    array = np.ascontiguousarray(np.asarray(value, dtype=np.uint8) & 1)
    digest = hashlib.sha256()
    digest.update(name.encode())
    digest.update(b"\0")
    digest.update(json.dumps(list(array.shape), separators=(",", ":")).encode())
    digest.update(b"\0")
    digest.update(array.tobytes(order="C"))
    return digest.hexdigest()


def _default_solver() -> SectorSolver:
    """Resolve the optional partition-capable adapter when it is available."""

    try:
        from evaluation.distance_sat import solve_css_sector_sat
    except ImportError:
        return solve_css_threshold_sat
    return solve_css_sector_sat


def _strict_positive_timeout(value: float, label: str) -> float:
    timeout = float(value)
    if not math.isfinite(timeout) or timeout <= 0:
        raise ValueError(f"{label} must be a positive finite number")
    return timeout


def _run_parallel_decisions(
    decisions: list[Any],
    *,
    started: float,
    total_timeout: float,
    timeout_per_decision: float,
    workers: int,
    solve_one: Callable[[Any, float], dict[str, Any]],
) -> list[dict[str, Any]]:
    """Run independent SAT units with deterministic, bounded parallelism.

    ``workers`` is certificate-level concurrency: every task launches at most
    one single-threaded PySAT child.  A fixed per-wave budget prevents the
    first wave from consuming the total wall limit, while results are returned
    in proof order rather than completion order.
    """

    if not decisions:
        return []
    remaining = total_timeout - (time.monotonic() - started)
    if remaining <= 0:
        return []
    active_workers = min(workers, len(decisions))
    waves = math.ceil(len(decisions) / active_workers)
    unit_timeout = min(timeout_per_decision, remaining / waves)
    deadline = time.monotonic() + remaining

    def invoke(index: int, decision: Any) -> tuple[int, dict[str, Any] | None]:
        task_remaining = deadline - time.monotonic()
        if task_remaining <= 0:
            return index, None
        return index, solve_one(decision, min(unit_timeout, task_remaining))

    ordered: dict[int, dict[str, Any] | None] = {}
    with ThreadPoolExecutor(
        max_workers=active_workers,
        thread_name_prefix="qcode-sector-certificate",
    ) as executor:
        futures = {
            executor.submit(invoke, index, decision): index
            for index, decision in enumerate(decisions)
        }
        for future in as_completed(futures):
            index, result = future.result()
            ordered[index] = result
    return [
        ordered[index]
        for index in range(len(decisions))
        if ordered.get(index) is not None
    ]


def _request(claim: Mapping[str, Any]) -> dict[str, Any]:
    raw = claim.get(REQUEST_FIELD)
    if raw is None:
        return {"coverage_mode": GLOBAL_MODE}
    if not isinstance(raw, Mapping):
        raise ValueError(f"{REQUEST_FIELD} must be an object")
    request = dict(raw)
    mode = request.get("coverage_mode", GLOBAL_MODE)
    if mode not in SUPPORTED_MODES:
        raise ValueError(
            "exact-sector coverage_mode must be global or first-nonzero",
        )
    request["coverage_mode"] = mode
    return request


def _clean_claim(claim: Mapping[str, Any]) -> dict[str, Any]:
    cleaned = dict(claim)
    cleaned.pop(REQUEST_FIELD, None)
    cleaned.pop("exact_distance_proof", None)
    cleaned.pop("milp_details", None)
    cleaned.pop("milp_attempted", None)
    cleaned.pop("d_is_exact", None)
    geometry = candidate_geometry(cleaned)
    if geometry is None:
        cleaned.pop("geometry", None)
    else:
        cleaned["geometry"] = geometry
    return cleaned


def _matrices(claim: Mapping[str, Any]) -> tuple[Any, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    if claim.get("C_terms") or claim.get("D_terms"):
        raise ValueError("sector SAT certificates support CSS BB claims only")
    if isinstance(claim.get("construction"), Mapping):
        from evaluation.construction import build_css_code_from_claim

        code = build_css_code_from_claim(dict(claim))
    else:
        code = build_bb_code(
            int(claim["ell"]),
            int(claim["m"]),
            claim["A_terms"],
            claim["B_terms"],
            geometry=candidate_geometry(claim),
        )
    hx, hz, lx, lz = (
        np.asarray(value, dtype=np.uint8) & 1
        for value in get_code_matrices(code)
    )
    return code, hx, hz, lx, lz


def _sector_matrices(
    sector: str,
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
) -> tuple[np.ndarray, np.ndarray]:
    if sector == "Z":
        return hx, lx
    if sector == "X":
        return hz, lz
    raise ValueError("sector must be X or Z")


def _checkpoint_for(
    checkpoint_path: Path | str | None,
    *,
    phase: str,
    sector: str,
    partition_index: int | None,
    max_weight: int,
    anchor_cube: Mapping[str, Any] | None = None,
) -> Path | None:
    if checkpoint_path is None:
        return None
    base = Path(checkpoint_path)
    partition = "global" if partition_index is None else f"p{partition_index}"
    cube = (
        ""
        if anchor_cube is None
        else f".c{int(anchor_cube['cube_index'])}"
    )
    return base.with_name(
        f"{base.name}.{phase}.{sector}.{partition}{cube}.w{max_weight}.json",
    )


def _call_solver(
    solver: SectorSolver,
    checks: np.ndarray,
    logicals: np.ndarray,
    *,
    sector: str,
    max_weight: int,
    timeout: float,
    solver_workers: int,
    seed: int,
    partition_index: int | None,
    anchor_indices: tuple[int, ...],
    anchor_cube: Mapping[str, Any] | None,
    checkpoint_path: Path | None,
    resume: bool,
    checkpoint_identity: Mapping[str, Any],
    requested_solver: str = "auto",
    cardinality_encoding: str = "seqcounter",
) -> dict[str, Any]:
    kwargs: dict[str, Any] = {
        "max_weight": max_weight,
        "sector": sector,
        "hard_timeout_s": timeout,
        "timeout": timeout,
        "workers": solver_workers,
        "seed": seed,
        "partition_index": partition_index,
        "anchor_indices": anchor_indices,
        "zero_anchor_indices": (
            ()
            if anchor_cube is None
            else tuple(int(index) for index in anchor_cube["zero_anchor_indices"])
        ),
        "one_anchor_index": (
            None if anchor_cube is None else int(anchor_cube["one_anchor_index"])
        ),
        "anchor_cube_sha256": (
            None if anchor_cube is None else str(anchor_cube["cube_sha256"])
        ),
        "checkpoint_path": checkpoint_path,
        "resume": resume,
        "checkpoint_identity": checkpoint_identity,
        "solver": requested_solver,
        "cardinality_encoding": cardinality_encoding,
    }
    try:
        signature = inspect.signature(solver)
    except (TypeError, ValueError):
        filtered = kwargs
    else:
        variadic = any(
            parameter.kind == inspect.Parameter.VAR_KEYWORD
            for parameter in signature.parameters.values()
        )
        filtered = (
            kwargs
            if variadic
            else {name: value for name, value in kwargs.items() if name in signature.parameters}
        )
    if partition_index is not None and "partition_index" not in filtered:
        raise RuntimeError(
            "selected SAT backend does not support first-nonzero partitions",
        )
    if anchor_cube is not None and not all(
        name in filtered
        for name in (
            "zero_anchor_indices",
            "one_anchor_index",
            "anchor_cube_sha256",
        )
    ):
        raise RuntimeError(
            "selected SAT backend does not support anchor-cover cubes",
        )
    solver_started = time.monotonic()
    try:
        result = solver(checks, logicals, **filtered)
    except Exception as exc:
        # A backend/runtime failure is evidence of no mathematical fact.  Keep
        # it explicitly retryable and let the caller try the other independent
        # sectors/partitions in this attempt.  BaseException subclasses such
        # as KeyboardInterrupt and SystemExit deliberately still propagate.
        result = {
            "schema_version": SAT_EVIDENCE_SCHEMA_VERSION,
            "evidence_kind": SAT_EVIDENCE_KIND,
            "formulation": SAT_FORMULATION,
            "sector": sector,
            "max_weight": max_weight,
            "partition_index": partition_index,
            "anchor_indices": list(anchor_indices),
            "zero_anchor_indices": kwargs["zero_anchor_indices"],
            "one_anchor_index": kwargs["one_anchor_index"],
            "anchor_cube_sha256": kwargs["anchor_cube_sha256"],
            "backend": {
                "distribution": "python-sat",
                "version": "unknown",
                "solver": "wrapper-exception",
            },
            "instance": {
                "check_matrix_sha256": _array_sha256("checks", checks),
                "target_logicals_sha256": _array_sha256(
                    "logicals",
                    logicals,
                ),
                "partition_index": partition_index,
                "anchor_indices": list(anchor_indices),
                "zero_anchor_indices": list(kwargs["zero_anchor_indices"]),
                "one_anchor_index": kwargs["one_anchor_index"],
                "anchor_cube_sha256": kwargs["anchor_cube_sha256"],
            },
            "outcome": "solver_error",
            "decision_complete": False,
            "threshold_infeasible": False,
            "success": False,
            "retryable": True,
            "message": f"{type(exc).__name__}: {exc}",
            "operator": None,
            "objective": None,
            "logical_syndrome": None,
            "hard_timeout_s": timeout,
            "elapsed_s": time.monotonic() - solver_started,
        }
        result["evidence_sha256"] = _canonical_sha256(result)
    if not isinstance(result, dict):
        result = {
            "schema_version": SAT_EVIDENCE_SCHEMA_VERSION,
            "evidence_kind": SAT_EVIDENCE_KIND,
            "formulation": SAT_FORMULATION,
            "sector": sector,
            "max_weight": max_weight,
            "partition_index": partition_index,
            "anchor_indices": list(anchor_indices),
            "zero_anchor_indices": list(kwargs["zero_anchor_indices"]),
            "one_anchor_index": kwargs["one_anchor_index"],
            "anchor_cube_sha256": kwargs["anchor_cube_sha256"],
            "backend": {
                "distribution": "python-sat",
                "version": "unknown",
                "solver": "wrapper-protocol",
            },
            "instance": {
                "check_matrix_sha256": _array_sha256("checks", checks),
                "target_logicals_sha256": _array_sha256(
                    "logicals",
                    logicals,
                ),
                "partition_index": partition_index,
                "anchor_indices": list(anchor_indices),
                "zero_anchor_indices": list(kwargs["zero_anchor_indices"]),
                "one_anchor_index": kwargs["one_anchor_index"],
                "anchor_cube_sha256": kwargs["anchor_cube_sha256"],
            },
            "outcome": "solver_error",
            "decision_complete": False,
            "threshold_infeasible": False,
            "success": False,
            "retryable": True,
            "message": "SAT backend returned a non-object result",
            "operator": None,
            "objective": None,
            "logical_syndrome": None,
            "hard_timeout_s": timeout,
            "elapsed_s": time.monotonic() - solver_started,
        }
        result["evidence_sha256"] = _canonical_sha256(result)
    return result


def _attempt_summary(
    wrapper: Mapping[str, Any],
    *,
    phase: str,
    max_weight: int,
) -> dict[str, Any]:
    evidence = wrapper.get("solver_evidence")
    evidence = evidence if isinstance(evidence, Mapping) else {}
    return {
        "phase": phase,
        "sector": wrapper.get("sector"),
        "partition_index": wrapper.get("partition_index"),
        "anchor_cube_index": (
            wrapper.get("anchor_cube", {}).get("cube_index")
            if isinstance(wrapper.get("anchor_cube"), Mapping)
            else None
        ),
        "anchor_cube_sha256": (
            wrapper.get("anchor_cube", {}).get("cube_sha256")
            if isinstance(wrapper.get("anchor_cube"), Mapping)
            else None
        ),
        "max_weight": max_weight,
        "outcome": evidence.get("outcome"),
        "decision_complete": evidence.get("decision_complete") is True,
        "retryable": evidence.get("retryable") is True,
        "solver": (
            evidence.get("backend", {}).get("solver")
            if isinstance(evidence.get("backend"), Mapping)
            else None
        ),
        "cardinality_encoding": evidence.get("cardinality_encoding"),
        "evidence_sha256": evidence.get("evidence_sha256"),
    }


def _validated_replay_solver_config(
    wrapper: Mapping[str, Any],
) -> tuple[str, str]:
    """Extract a solver/CNF pair only from a fully bound terminal evidence.

    The caller first validates the complete UNSAT schema, evidence hash, and
    matrices.  This function additionally requires the concrete configuration
    to agree with the self-hashed instance binding.  Legacy or malformed
    evidence conservatively falls back to the standard independent replay.
    """

    evidence = wrapper.get("solver_evidence")
    if not isinstance(evidence, Mapping):
        return "auto", "seqcounter"
    instance = evidence.get("instance")
    backend = evidence.get("backend")
    if not isinstance(instance, Mapping) or not isinstance(backend, Mapping):
        return "auto", "seqcounter"
    binding_hash = instance.get("binding_sha256")
    try:
        binding_valid = binding_hash == _canonical_sha256(
            instance,
            omit="binding_sha256",
        )
    except (TypeError, ValueError):
        binding_valid = False
    solver_name = backend.get("solver")
    encoding = evidence.get("cardinality_encoding")
    if not (
        binding_valid
        and instance.get("formulation") == evidence.get("formulation")
        and instance.get("sector") == evidence.get("sector")
        and instance.get("max_weight") == evidence.get("max_weight")
        and instance.get("backend") == backend
        and instance.get("cardinality_encoding") == encoding
        and isinstance(solver_name, str)
        and _SAFE_SOLVER_NAME.fullmatch(solver_name) is not None
        and encoding in _SAT_ENCODINGS
    ):
        return "auto", "seqcounter"
    return solver_name, str(encoding)


def _evidence_hash_valid(evidence: Mapping[str, Any]) -> bool:
    try:
        return evidence.get("evidence_sha256") == _canonical_sha256(
            evidence,
            omit="evidence_sha256",
        )
    except (TypeError, ValueError):
        return False


def _complete_unsat(
    wrapper: Mapping[str, Any],
    *,
    sector: str,
    max_weight: int,
    checks: np.ndarray | None = None,
    logicals: np.ndarray | None = None,
    expected_anchors: tuple[int, ...] = (),
    expected_anchor_cube: Mapping[str, Any] | None = None,
) -> bool:
    evidence = wrapper.get("solver_evidence")
    backend = evidence.get("backend") if isinstance(evidence, Mapping) else None
    instance = evidence.get("instance") if isinstance(evidence, Mapping) else None
    partition = wrapper.get("partition_index")
    stored_cube = wrapper.get("anchor_cube")
    if expected_anchor_cube is None:
        if stored_cube is not None:
            return False
        expected_zero: list[int] = []
        expected_one: int | None = None
        expected_cube_sha: str | None = None
        expected_unit_clauses: list[list[int]] = []
    else:
        if not isinstance(stored_cube, Mapping) or dict(stored_cube) != dict(
            expected_anchor_cube,
        ):
            return False
        expected_zero = [
            int(index) for index in expected_anchor_cube["zero_anchor_indices"]
        ]
        expected_one = int(expected_anchor_cube["one_anchor_index"])
        expected_cube_sha = str(expected_anchor_cube["cube_sha256"])
        expected_unit_clauses = [
            *([[-(index + 1)] for index in expected_zero]),
            [expected_one + 1],
        ]
    instance_matches = True
    if checks is not None and logicals is not None:
        cube_binding_matches = True
        if expected_anchor_cube is not None:
            try:
                instance_without_hash = dict(instance)
                binding_sha256 = instance_without_hash.pop(
                    "binding_sha256",
                )
                cnf = evidence.get("cnf")
                cube_binding_matches = bool(
                    binding_sha256 == _canonical_sha256(instance_without_hash)
                    and evidence.get("zero_anchor_indices") == expected_zero
                    and evidence.get("one_anchor_index") == expected_one
                    and evidence.get("anchor_cube_sha256") == expected_cube_sha
                    and instance.get("zero_anchor_indices") == expected_zero
                    and instance.get("one_anchor_index") == expected_one
                    and instance.get("anchor_cube_sha256") == expected_cube_sha
                    and instance.get("anchor_constraint_formulation")
                    == "anchor-or-first-nonzero-unit-clauses-v1"
                    and instance.get("anchor_unit_clauses")
                    == expected_unit_clauses
                    and instance.get("anchor_unit_clauses_sha256")
                    == _canonical_sha256(expected_unit_clauses)
                    and isinstance(cnf, Mapping)
                    and cnf.get("anchor_unit_clauses_sha256")
                    == _canonical_sha256(expected_unit_clauses)
                )
            except (KeyError, TypeError, ValueError):
                cube_binding_matches = False
        else:
            # Legacy evidence predates cube fields.  New global-anchor evidence
            # uses their neutral values.  Either representation is safe, but a
            # non-neutral cube binding must never be treated as the legacy OR.
            cube_binding_matches = bool(
                evidence.get("zero_anchor_indices", []) == []
                and evidence.get("one_anchor_index") is None
                and evidence.get("anchor_cube_sha256") is None
                and (
                    not isinstance(instance, Mapping)
                    or (
                        instance.get("zero_anchor_indices", []) == []
                        and instance.get("one_anchor_index") is None
                        and instance.get("anchor_cube_sha256") is None
                    )
                )
            )
        instance_matches = bool(
            isinstance(instance, Mapping)
            and instance.get("check_matrix_sha256")
            == _array_sha256("checks", checks)
            and instance.get("target_logicals_sha256")
            == _array_sha256("logicals", logicals)
            and instance.get("partition_index") == partition
            and instance.get("anchor_indices") == list(expected_anchors)
            and evidence.get("partition_index") == partition
            and evidence.get("anchor_indices") == list(expected_anchors)
            and cube_binding_matches
        )
    return bool(
        wrapper.get("sector") == sector
        and isinstance(evidence, Mapping)
        and evidence.get("schema_version") == SAT_EVIDENCE_SCHEMA_VERSION
        and evidence.get("evidence_kind") == SAT_EVIDENCE_KIND
        and evidence.get("formulation") in _SAT_FORMULATIONS
        and evidence.get("sector") == sector
        and evidence.get("max_weight") == max_weight
        and evidence.get("outcome") == "unsat"
        and evidence.get("decision_complete") is True
        and evidence.get("threshold_infeasible") is True
        and evidence.get("operator") is None
        and evidence.get("objective") is None
        and isinstance(backend, Mapping)
        and backend.get("distribution") == "python-sat"
        and isinstance(backend.get("solver"), str)
        and bool(backend.get("solver"))
        and instance_matches
        and _evidence_hash_valid(evidence)
    )


def _valid_upper_witness(
    wrapper: Mapping[str, Any],
    *,
    distance: int,
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
    expected_anchors: tuple[int, ...] = (),
) -> bool:
    sector = wrapper.get("sector")
    evidence = wrapper.get("solver_evidence")
    if sector not in {"X", "Z"} or not isinstance(evidence, Mapping):
        return False
    if not (
        wrapper.get("anchor_cube") is None
        and evidence.get("zero_anchor_indices", []) == []
        and evidence.get("one_anchor_index") is None
        and evidence.get("anchor_cube_sha256") is None
        and evidence.get("schema_version") == SAT_EVIDENCE_SCHEMA_VERSION
        and evidence.get("evidence_kind") == SAT_EVIDENCE_KIND
        and evidence.get("formulation") in _SAT_FORMULATIONS
        and evidence.get("sector") == sector
        and evidence.get("max_weight") == distance
        and evidence.get("outcome") == "sat"
        and evidence.get("decision_complete") is True
        and evidence.get("objective") == distance
        and isinstance(evidence.get("instance"), Mapping)
        and evidence["instance"].get("check_matrix_sha256")
        == _array_sha256("checks", _sector_matrices(str(sector), hx, hz, lx, lz)[0])
        and evidence["instance"].get("target_logicals_sha256")
        == _array_sha256("logicals", _sector_matrices(str(sector), hx, hz, lx, lz)[1])
        and evidence["instance"].get("partition_index") is None
        and evidence["instance"].get("anchor_indices") == list(expected_anchors)
        and evidence["instance"].get("zero_anchor_indices", []) == []
        and evidence["instance"].get("one_anchor_index") is None
        and evidence["instance"].get("anchor_cube_sha256") is None
        and evidence.get("partition_index") is None
        and evidence.get("anchor_indices") == list(expected_anchors)
        and _evidence_hash_valid(evidence)
    ):
        return False
    checks, logicals = _sector_matrices(str(sector), hx, hz, lx, lz)
    return not verify_css_threshold_sat_witness(evidence, checks, logicals)


def _expected_decisions(
    mode: str,
    k: int,
    sectors: tuple[str, ...] = ("X", "Z"),
) -> list[tuple[str, int | None]]:
    if mode == GLOBAL_MODE:
        return [(sector, None) for sector in sectors]
    return [
        (sector, index)
        for sector in sectors
        for index in range(k)
    ]


def _rebuild_anchor_cover_cubes(
    stored: Any,
    *,
    anchors: tuple[int, ...],
) -> list[dict[str, Any]] | None:
    """Replay the typed disjoint/exhaustive cover of the anchor OR.

    ``None`` is the legacy single anchor-OR decision.  An explicit cover is
    accepted only when it is byte-for-byte the deterministic first-nonzero
    cover freshly rebuilt from the verified translation-orbit anchors.  This
    simultaneously checks cube hashes, order, uniqueness, disjointness, and
    exhaustiveness.
    """

    if stored is None:
        return None
    if not anchors or not isinstance(stored, list):
        raise ValueError("anchor_cover_cubes requires verified nonempty anchors")
    from scripts.screen_frontier_sat import build_anchor_cover_cubes

    rebuilt = build_anchor_cover_cubes(anchors)
    if stored != rebuilt:
        raise ValueError("stored anchor-cover cubes do not replay")
    return rebuilt


def _expected_solver_decisions(
    mode: str,
    k: int,
    sectors: tuple[str, ...],
    anchor_cover_cubes: list[dict[str, Any]] | None,
) -> list[tuple[str, int | None, dict[str, Any] | None]]:
    cubes: list[dict[str, Any] | None] = (
        [None] if anchor_cover_cubes is None else anchor_cover_cubes
    )
    return [
        (sector, partition, cube)
        for sector, partition in _expected_decisions(mode, k, sectors)
        for cube in cubes
    ]


def _solver_decision_key(
    sector: str,
    partition: int | None,
    anchor_cube: Mapping[str, Any] | None,
) -> tuple[str, int | None, str | None]:
    return (
        sector,
        partition,
        None if anchor_cube is None else str(anchor_cube["cube_sha256"]),
    )


def _completed_partition_count(
    records: list[dict[str, Any]],
    *,
    mode: str,
    k: int,
    sectors: tuple[str, ...],
    anchor_cover_cubes: list[dict[str, Any]] | None,
) -> int:
    expected_by_partition: dict[tuple[str, int | None], set[str | None]] = {}
    for sector, partition, cube in _expected_solver_decisions(
        mode,
        k,
        sectors,
        anchor_cover_cubes,
    ):
        expected_by_partition.setdefault((sector, partition), set()).add(
            None if cube is None else str(cube["cube_sha256"]),
        )
    observed_by_partition: dict[tuple[str, int | None], set[str | None]] = {}
    for item in records:
        if not isinstance(item, Mapping):
            continue
        cube = item.get("anchor_cube")
        observed_by_partition.setdefault(
            (str(item.get("sector")), item.get("partition_index")),
            set(),
        ).add(
            str(cube.get("cube_sha256")) if isinstance(cube, Mapping) else None,
        )
    return sum(
        observed_by_partition.get(partition_key, set()) == cube_hashes
        for partition_key, cube_hashes in expected_by_partition.items()
    )


def _stored_lower(
    request: Mapping[str, Any],
    *,
    mode: str,
    k: int,
    max_weight: int,
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
    expected_anchors: tuple[int, ...] = (),
    sectors: tuple[str, ...] = ("X", "Z"),
    anchor_cover_cubes: list[dict[str, Any]] | None = None,
) -> list[dict[str, Any]] | None:
    return _stored_unsat_decisions(
        request.get("lower_bound_decisions"),
        mode=mode,
        k=k,
        max_weight=max_weight,
        hx=hx,
        hz=hz,
        lx=lx,
        lz=lz,
        expected_anchors=expected_anchors,
        sectors=sectors,
        anchor_cover_cubes=anchor_cover_cubes,
    )


def _stored_unsat_decisions(
    records: Any,
    *,
    mode: str,
    k: int,
    max_weight: int,
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
    expected_anchors: tuple[int, ...] = (),
    require_complete: bool = True,
    sectors: tuple[str, ...] = ("X", "Z"),
    anchor_cover_cubes: list[dict[str, Any]] | None = None,
) -> list[dict[str, Any]] | None:
    """Validate typed UNSAT wrappers for one complete threshold layer.

    ``require_complete=False`` is used only while importing Stage-3 upper
    decisions.  A partial layer can save one repeated solve after resume, but
    it is never promoted to a distance lower bound until every required proof
    sector is present.
    """

    if not isinstance(records, list):
        return None
    expected_specs = _expected_solver_decisions(
        mode,
        k,
        sectors,
        anchor_cover_cubes,
    )
    expected = {
        _solver_decision_key(sector, partition, cube)
        for sector, partition, cube in expected_specs
    }
    cubes_by_hash = {
        str(cube["cube_sha256"]): cube
        for cube in (anchor_cover_cubes or [])
    }
    recovered: dict[tuple[str, int | None, str | None], dict[str, Any]] = {}
    for raw in records:
        if not isinstance(raw, Mapping):
            return None
        wrapper = dict(raw)
        sector = wrapper.get("sector")
        partition = wrapper.get("partition_index")
        raw_cube = wrapper.get("anchor_cube")
        if raw_cube is None:
            expected_cube = None
        elif isinstance(raw_cube, Mapping):
            raw_cube_sha = raw_cube.get("cube_sha256")
            expected_cube = cubes_by_hash.get(str(raw_cube_sha))
            if expected_cube is None or dict(raw_cube) != expected_cube:
                return None
        else:
            return None
        key = _solver_decision_key(str(sector), partition, expected_cube)
        if key not in expected or key in recovered:
            return None
        if not _complete_unsat(
            wrapper,
            sector=str(sector),
            max_weight=max_weight,
            checks=_sector_matrices(str(sector), hx, hz, lx, lz)[0],
            logicals=_sector_matrices(str(sector), hx, hz, lx, lz)[1],
            expected_anchors=expected_anchors,
            expected_anchor_cube=expected_cube,
        ):
            return None
        recovered[key] = wrapper
    if require_complete and set(recovered) != expected:
        return None
    return [
        recovered[_solver_decision_key(sector, partition, cube)]
        for sector, partition, cube in expected_specs
        if _solver_decision_key(sector, partition, cube) in recovered
    ]


def _xz_isometry_context(
    request: Mapping[str, Any],
    claim: Mapping[str, Any],
    *,
    hx: np.ndarray,
    hz: np.ndarray,
) -> tuple[dict[str, Any] | None, tuple[str, ...]]:
    """Replay an explicitly supplied BB X/Z-isometry report.

    Absence preserves the legacy two-sector proof.  Supplying a report is a
    request to reduce proof coverage, so a malformed, stale, unverified, or
    wrong-geometry report is rejected instead of silently falling back.
    """

    stored = request.get("xz_sector_isometry")
    if stored is None:
        return None, ("X", "Z")
    if not isinstance(stored, Mapping):
        raise ValueError("xz_sector_isometry must be an object or null")
    try:
        replayed = verify_bb_xz_sector_isometry(
            hx,
            hz,
            ell=int(claim["ell"]),
            m=int(claim["m"]),
            geometry=candidate_geometry(claim),
        )
    except (KeyError, TypeError, ValueError) as exc:
        raise ValueError("BB X/Z sector isometry replay failed") from exc
    if (
        replayed.get("verified") is not True
        or replayed.get("canonical_sector") != "X"
        or replayed.get("covered_sectors") != ["X", "Z"]
        or dict(stored) != replayed
    ):
        raise ValueError("stored BB X/Z sector isometry does not replay")
    return replayed, ("X",)


def _coverage_context(
    request: Mapping[str, Any],
    claim: Mapping[str, Any],
    *,
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
) -> tuple[dict[str, Any], dict[str, Any] | None, tuple[int, ...]]:
    """Recompute detector/symmetry reports before accepting anchored UNSAT."""

    from scripts.screen_frontier_sat import verify_css_logical_detectors

    detector = verify_css_logical_detectors(hx, hz, lx, lz)
    if detector.get("verified") is not True:
        raise ValueError("CSS logical detector replay failed")
    stored_detector = request.get("logical_detector")
    if stored_detector is not None and stored_detector != detector:
        raise ValueError("stored CSS logical detector report does not replay")

    records = request.get("lower_bound_decisions")
    used_anchors = {
        tuple(item.get("solver_evidence", {}).get("anchor_indices", []))
        for item in records or []
        if isinstance(item, Mapping)
        and isinstance(item.get("solver_evidence"), Mapping)
    }
    compact = isinstance(claim.get("construction"), Mapping)
    translation_flag = request.get("use_translation_anchors") is True
    construction_flag = request.get("use_construction_anchors") is True
    if translation_flag and construction_flag:
        raise ValueError("BB and compact-construction anchor flags cannot mix")
    if compact and (
        translation_flag or request.get("translation_symmetry") is not None
    ):
        raise ValueError("compact construction cannot use BB translation anchors")
    if not compact and (
        construction_flag or request.get("construction_symmetry") is not None
    ):
        raise ValueError("BB claim cannot use compact-construction anchors")
    use_anchors = bool(
        (construction_flag if compact else translation_flag)
        or any(used_anchors)
    )
    if not use_anchors:
        if any(used_anchors):
            raise ValueError("lower SAT decisions use inconsistent anchors")
        # A global portfolio lane may finish without using the available
        # construction automorphism.  Its UNSAT proof is stronger; ignore the
        # unused proposal rather than pretending it covered that decision.
        return detector, None, ()

    if compact:
        from scripts.screen_frontier_sat import verify_construction_symmetry

        symmetry = verify_construction_symmetry(dict(claim), hx, hz)
        if (
            symmetry.get("verified") is not True
            or symmetry.get("orbits_cover_all_qubits") is not True
        ):
            raise ValueError("compact-construction symmetry replay failed")
        stored_symmetry = request.get("construction_symmetry")
        if (
            not isinstance(stored_symmetry, Mapping)
            or dict(stored_symmetry) != symmetry
        ):
            raise ValueError(
                "stored compact-construction symmetry report does not replay"
            )
        if request.get("translation_symmetry") is not None:
            raise ValueError("compact construction cannot carry BB symmetry")
        anchors = tuple(
            int(index) for index in symmetry["orbit_representatives"]
        )
        if used_anchors and used_anchors != {anchors}:
            raise ValueError(
                "SAT lower decisions do not use the verified construction orbits"
            )
        return detector, symmetry, anchors

    from scripts.screen_frontier_xor import verify_bb_translation_symmetry

    symmetry = verify_bb_translation_symmetry(dict(claim))
    if symmetry.get("verified") is not True:
        raise ValueError("BB translation symmetry replay failed")
    stored_symmetry = request.get("translation_symmetry")
    if not isinstance(stored_symmetry, Mapping) or dict(stored_symmetry) != symmetry:
        raise ValueError("stored BB translation symmetry report does not replay")
    anchors = tuple(int(index) for index in symmetry["orbit_representatives"])
    if used_anchors and used_anchors != {anchors}:
        raise ValueError("SAT lower decisions do not use the verified orbit anchors")
    return detector, symmetry, anchors


def claim_from_sector_sat_artifact(
    artifact: Mapping[str, Any],
) -> dict[str, Any]:
    """Fail-closed Stage 3 to Stage 4 handoff for exact sector evidence."""

    if (
        artifact.get("schema_version") != 1
        or artifact.get("gate") != STAGE3_GATE
        or artifact.get("status") not in {"THRESHOLD_PROVEN", "EXACT_PROVEN"}
        or artifact.get("artifact_sha256")
        != _canonical_sha256(artifact, omit="artifact_sha256")
    ):
        raise ValueError("not a terminal Stage 3 sector-SAT proof artifact")
    candidate = artifact.get("candidate")
    if not isinstance(candidate, Mapping):
        raise ValueError("Stage 3 sector-SAT candidate must be an object")
    claim = dict(candidate)
    code, hx, hz, lx, lz = _matrices(claim)
    n = int(code.num_qudits)
    k = n - _rank_f2(hx) - _rank_f2(hz)
    required = minimum_winning_distance(n, k)
    if (
        artifact.get("required_distance") != required
        or claim.get("required_distance") != required
        or claim.get("n") != n
        or claim.get("k") != k
    ):
        raise ValueError("Stage 3 sector-SAT geometry/threshold mismatch")
    mode = artifact.get("coverage_mode")
    if mode not in SUPPORTED_MODES:
        raise ValueError("Stage 3 sector-SAT coverage_mode is invalid")
    raw_lower_threshold = artifact.get("lower_bound_threshold", required - 1)
    if (
        isinstance(raw_lower_threshold, bool)
        or not isinstance(raw_lower_threshold, int)
        or not required - 1 <= raw_lower_threshold <= n
    ):
        raise ValueError("Stage 3 sector-SAT lower threshold is invalid")
    lower_threshold = int(raw_lower_threshold)
    request = {
        "coverage_mode": mode,
        "lower_bound_threshold": lower_threshold,
        "lower_bound_decisions": artifact.get("lower_bound_decisions"),
        "upper_witness": artifact.get("upper_witness"),
        "translation_symmetry": artifact.get("translation_symmetry"),
        "construction_symmetry": artifact.get("construction_symmetry"),
        "logical_detector": artifact.get("logical_detector"),
        "xz_sector_isometry": artifact.get("xz_sector_isometry"),
        "anchor_cover_cubes": artifact.get("anchor_cover_cubes"),
    }
    xz_sector_isometry, proof_sectors = _xz_isometry_context(
        request,
        claim,
        hx=hx,
        hz=hz,
    )
    detector, symmetry, anchors = _coverage_context(
        request,
        claim,
        hx=hx,
        hz=hz,
        lx=lx,
        lz=lz,
    )
    anchor_cover_cubes = _rebuild_anchor_cover_cubes(
        request.get("anchor_cover_cubes"),
        anchors=anchors,
    )
    lower = _stored_lower(
        request,
        mode=str(mode),
        k=k,
        max_weight=lower_threshold,
        hx=hx,
        hz=hz,
        lx=lx,
        lz=lz,
        expected_anchors=anchors,
        sectors=proof_sectors,
        anchor_cover_cubes=anchor_cover_cubes,
    )
    witness = request["upper_witness"]
    witness_valid = bool(
        isinstance(witness, Mapping)
        and _valid_upper_witness(
            witness,
            distance=required,
            hx=hx,
            hz=hz,
            lx=lx,
            lz=lz,
            expected_anchors=anchors,
        )
    )
    if lower is None:
        raise ValueError("Stage 3 sector-SAT lower evidence is incomplete")
    expected_solver_decisions = len(_expected_solver_decisions(
        str(mode),
        k,
        proof_sectors,
        anchor_cover_cubes,
    ))
    expected_partitions = len(_expected_decisions(str(mode), k, proof_sectors))
    if anchor_cover_cubes is not None and (
        artifact.get("expected_lower_decisions") != expected_solver_decisions
        or artifact.get("completed_lower_decisions") != expected_solver_decisions
        or artifact.get("expected_lower_partitions") != expected_partitions
        or artifact.get("completed_lower_partitions") != expected_partitions
    ):
        raise ValueError("Stage 3 anchor-cover counters are incomplete")
    if artifact.get("status") == "EXACT_PROVEN" and (
        lower_threshold != required - 1 or not witness_valid
    ):
        raise ValueError(
            "EXACT_PROVEN Stage 3 artifact lacks the R-1 lower/R witness pair",
        )
    if artifact.get("status") == "THRESHOLD_PROVEN" and witness is not None:
        raise ValueError("THRESHOLD_PROVEN Stage 3 artifact must not claim a witness")

    # Stage 3 evaluates every required global proof sector at ``required``
    # while it proves the lower threshold.  Preserve validated UNSAT decisions
    # so Stage 4 can resume the upward exact-distance search.  A partial layer
    # is only a cache until every required sector is complete.
    escalation_by_sector: dict[str, dict[str, Any]] = {}
    units = artifact.get("units")
    if isinstance(units, list):
        for raw in units:
            if not isinstance(raw, Mapping) or raw.get("phase") != "upper":
                continue
            sector = raw.get("sector")
            if sector not in proof_sectors or raw.get("partition_index") is not None:
                continue
            wrapper = {
                "sector": sector,
                "partition_index": None,
                "solver_evidence": raw.get("solver_evidence"),
            }
            checks, logicals = _sector_matrices(str(sector), hx, hz, lx, lz)
            if not _complete_unsat(
                wrapper,
                sector=str(sector),
                max_weight=required,
                checks=checks,
                logicals=logicals,
                expected_anchors=anchors,
            ):
                continue
            if str(sector) in escalation_by_sector:
                raise ValueError("duplicate Stage 3 upper UNSAT sector decision")
            escalation_by_sector[str(sector)] = wrapper

    request["lower_bound_decisions"] = lower
    request["lower_bound_threshold"] = lower_threshold
    request["upper_witness"] = dict(witness) if witness_valid else None
    request["escalation_decisions"] = [
        escalation_by_sector[sector]
        for sector in proof_sectors
        if sector in escalation_by_sector
    ]
    request["required_distance"] = required
    request["logical_detector"] = detector
    if isinstance(claim.get("construction"), Mapping):
        request["translation_symmetry"] = None
        request["construction_symmetry"] = symmetry
        request["use_translation_anchors"] = False
        request["use_construction_anchors"] = bool(anchors)
    else:
        request["translation_symmetry"] = symmetry
        request["construction_symmetry"] = None
        request["use_translation_anchors"] = bool(anchors)
        request["use_construction_anchors"] = False
    request["xz_sector_isometry"] = xz_sector_isometry
    request["anchor_cover_cubes"] = anchor_cover_cubes
    request["stage3_artifact_sha256"] = _canonical_sha256(artifact)
    request["stage3_status"] = artifact.get("status")
    claim[REQUEST_FIELD] = request
    return claim


def _proof_payload(
    *,
    mode: str,
    required_distance: int,
    distance: int,
    lower: list[dict[str, Any]],
    witness: dict[str, Any],
    logical_detector: Mapping[str, Any],
    translation_symmetry: Mapping[str, Any] | None,
    xz_sector_isometry: Mapping[str, Any] | None,
    anchor_indices: tuple[int, ...],
    anchor_cover_cubes: list[dict[str, Any]] | None,
    expected_lower_decisions: int,
    expected_lower_partitions: int,
) -> dict[str, Any]:
    proof: dict[str, Any] = {
        "schema_version": 1,
        "proof_type": SECTOR_SAT_EXACT_PROOF_TYPE,
        "coverage_mode": mode,
        "exact": True,
        "required_distance": required_distance,
        "lower_bound_threshold": distance - 1,
        "lower_bound": distance,
        "upper_bound": distance,
        "distance": distance,
        "expected_lower_decisions": expected_lower_decisions,
        "completed_lower_decisions": len(lower),
        "expected_lower_partitions": expected_lower_partitions,
        "completed_lower_partitions": expected_lower_partitions,
        "lower_bound_decisions": lower,
        "upper_witness": witness,
        "logical_detector": dict(logical_detector),
        "translation_symmetry": (
            None if translation_symmetry is None else dict(translation_symmetry)
        ),
        "xz_sector_isometry": (
            None if xz_sector_isometry is None else dict(xz_sector_isometry)
        ),
        "anchor_indices": list(anchor_indices),
        "anchor_cover_cubes": (
            None
            if anchor_cover_cubes is None
            else [dict(cube) for cube in anchor_cover_cubes]
        ),
    }
    proof["proof_sha256"] = _canonical_sha256(proof)
    return proof


def build_sector_sat_certificate(
    claim: dict[str, Any],
    *,
    known_answer_artifact: Path | str,
    timeout_per_logical: float = 300,
    total_timeout: float = 7200,
    checkpoint_path: Path | str | None = None,
    resume: bool = False,
    solver_workers: int = 1,
    sector_solver: SectorSolver | None = None,
) -> dict[str, Any]:
    """Build an exact-distance certificate from typed SAT sector decisions."""

    workers = _validate_solver_workers(solver_workers)
    per_decision = _strict_positive_timeout(
        timeout_per_logical,
        "timeout_per_logical",
    )
    total = _strict_positive_timeout(total_timeout, "total_timeout")
    request = _request(claim)
    mode = str(request["coverage_mode"])
    seed = int(request.get("seed", 0))
    clean_claim = _clean_claim(claim)
    code, hx, hz, lx, lz = _matrices(clean_claim)
    n = int(code.num_qudits)
    k = n - _rank_f2(hx) - _rank_f2(hz)
    if k <= 0 or int(code.dimension) != k or len(lx) != k or len(lz) != k:
        raise ValueError("reconstructed CSS BB logical dimension is inconsistent")
    required = minimum_winning_distance(n, k)
    if int(clean_claim.get("required_distance", required)) != required:
        raise ValueError("required_distance does not match the challenge threshold")
    solve = _default_solver() if sector_solver is None else sector_solver
    xz_sector_isometry, proof_sectors = _xz_isometry_context(
        request,
        clean_claim,
        hx=hx,
        hz=hz,
    )
    logical_detector, translation_symmetry, anchors = _coverage_context(
        request,
        clean_claim,
        hx=hx,
        hz=hz,
        lx=lx,
        lz=lz,
    )
    anchor_cover_cubes = _rebuild_anchor_cover_cubes(
        request.get("anchor_cover_cubes"),
        anchors=anchors,
    )
    started = time.monotonic()
    raw_initial_threshold = request.get("lower_bound_threshold", required - 1)
    if (
        isinstance(raw_initial_threshold, bool)
        or not isinstance(raw_initial_threshold, int)
        or not required - 1 <= raw_initial_threshold <= n
    ):
        raise ValueError("sector SAT lower_bound_threshold is invalid")
    initial_threshold = int(raw_initial_threshold)
    lower = _stored_lower(
        request,
        mode=mode,
        k=k,
        max_weight=initial_threshold,
        hx=hx,
        hz=hz,
        lx=lx,
        lz=lz,
        expected_anchors=anchors,
        sectors=proof_sectors,
        anchor_cover_cubes=anchor_cover_cubes,
    )
    lower_resumed = lower is not None
    lower = [] if lower is None else lower
    completed_keys = {
        _solver_decision_key(
            str(item["sector"]),
            item.get("partition_index"),
            item.get("anchor_cube"),
        )
        for item in lower
    }
    decision_attempts: list[dict[str, Any]] = []
    pending_lower = [
        decision
        for decision in _expected_solver_decisions(
            mode,
            k,
            proof_sectors,
            anchor_cover_cubes,
        )
        if _solver_decision_key(*decision) not in completed_keys
    ]

    def solve_lower(
        decision: tuple[str, int | None, dict[str, Any] | None],
        decision_timeout: float,
    ) -> dict[str, Any]:
        sector, partition, anchor_cube = decision
        checks, logicals = _sector_matrices(sector, hx, hz, lx, lz)
        evidence = _call_solver(
            solve,
            checks,
            logicals,
            sector=sector,
            max_weight=initial_threshold,
            timeout=decision_timeout,
            solver_workers=1,
            seed=seed,
            partition_index=partition,
            anchor_indices=anchors,
            anchor_cube=anchor_cube,
            checkpoint_path=_checkpoint_for(
                checkpoint_path,
                phase="lower",
                sector=sector,
                partition_index=partition,
                max_weight=initial_threshold,
                anchor_cube=anchor_cube,
            ),
            resume=resume,
            checkpoint_identity={
                "certificate_type": CERTIFICATE_TYPE,
                "phase": "lower",
                "claim_sha256": _canonical_sha256(clean_claim),
                "coverage_mode": mode,
                "max_weight": initial_threshold,
                "partition_index": partition,
                "anchor_cube_sha256": (
                    None
                    if anchor_cube is None
                    else anchor_cube["cube_sha256"]
                ),
                **(
                    {}
                    if xz_sector_isometry is None
                    else {
                        "xz_sector_isometry_sha256": (
                            xz_sector_isometry["report_sha256"]
                        ),
                    }
                ),
            },
        )
        return {
            "sector": sector,
            "partition_index": partition,
            "anchor_cube": (
                None if anchor_cube is None else dict(anchor_cube)
            ),
            "solver_evidence": evidence,
        }

    lower_results = _run_parallel_decisions(
        pending_lower,
        started=started,
        total_timeout=total,
        timeout_per_decision=per_decision,
        workers=workers,
        solve_one=solve_lower,
    )
    for wrapper in lower_results:
        lower.append(wrapper)
        decision_attempts.append(
            _attempt_summary(
                wrapper,
                phase="lower",
                max_weight=initial_threshold,
            ),
        )
    # Do not stop on timeout/error.  Every independent unit gets its fair
    # share in this attempt; the all-UNSAT predicate below remains the only
    # way this layer can become a mathematical lower bound.

    lower_complete = bool(
        len(lower) == len(_expected_solver_decisions(
            mode,
            k,
            proof_sectors,
            anchor_cover_cubes,
        ))
        and all(
            _complete_unsat(
                item,
                sector=str(item.get("sector")),
                max_weight=initial_threshold,
                checks=_sector_matrices(
                    str(item.get("sector")), hx, hz, lx, lz,
                )[0],
                logicals=_sector_matrices(
                    str(item.get("sector")), hx, hz, lx, lz,
                )[1],
                expected_anchors=anchors,
                expected_anchor_cube=(
                    item.get("anchor_cube")
                    if isinstance(item.get("anchor_cube"), Mapping)
                    else None
                ),
            )
            for item in lower
        )
    )
    witness = request.get("upper_witness")
    initial_witness_distance = initial_threshold + 1
    upper_resumed = bool(
        isinstance(witness, Mapping)
        and _valid_upper_witness(
            witness,
            distance=initial_witness_distance,
            hx=hx,
            hz=hz,
            lx=lx,
            lz=lz,
            expected_anchors=anchors,
        )
    )
    witness = dict(witness) if upper_resumed else None
    exact_distance = initial_witness_distance if upper_resumed else 0
    current_lower = lower
    current_mode = mode
    current_anchor_cover_cubes = anchor_cover_cubes
    lower_threshold = initial_threshold if lower_complete else -1
    max_weight_attempted = initial_threshold
    completed_unsat_thresholds: list[int] = []
    reused_stage3_escalation_decisions = 0

    cached_initial_escalation = _stored_unsat_decisions(
        request.get("escalation_decisions"),
        mode=GLOBAL_MODE,
        k=k,
        max_weight=initial_witness_distance,
        hx=hx,
        hz=hz,
        lx=lx,
        lz=lz,
        expected_anchors=anchors,
        require_complete=False,
        sectors=proof_sectors,
    )
    cached_by_sector = {
        str(item["sector"]): item for item in (cached_initial_escalation or [])
    }

    # Once <=T is UNSAT in every required proof sector, d >= T+1.  A verified
    # BB isometry lets canonical X cover Z; otherwise both sectors are needed.
    # The first SAT witness at T+1 then has weight exactly T+1.  Individual
    # decisions retain threshold/sector-specific atomic checkpoints.
    threshold = initial_witness_distance
    while lower_complete and witness is None and threshold <= n:
        layer_by_sector: dict[str, dict[str, Any]] = {}
        if threshold == initial_witness_distance:
            layer_by_sector.update(cached_by_sector)
            reused_stage3_escalation_decisions = len(layer_by_sector)
        layer_sectors = proof_sectors
        pending_sectors = [
            sector for sector in layer_sectors if sector not in layer_by_sector
        ]

        def solve_escalation(
            sector: str,
            decision_timeout: float,
        ) -> dict[str, Any]:
            checks, logicals = _sector_matrices(sector, hx, hz, lx, lz)
            evidence = _call_solver(
                solve,
                checks,
                logicals,
                sector=sector,
                max_weight=threshold,
                timeout=decision_timeout,
                solver_workers=1,
                seed=seed,
                partition_index=None,
                anchor_indices=anchors,
                anchor_cube=None,
                checkpoint_path=_checkpoint_for(
                    checkpoint_path,
                    phase="escalation",
                    sector=sector,
                    partition_index=None,
                    max_weight=threshold,
                ),
                resume=resume,
                checkpoint_identity={
                    "certificate_type": CERTIFICATE_TYPE,
                    "phase": "escalation",
                    "claim_sha256": _canonical_sha256(clean_claim),
                    "sector": sector,
                    "max_weight": threshold,
                    **(
                        {}
                        if xz_sector_isometry is None
                        else {
                            "xz_sector_isometry_sha256": (
                                xz_sector_isometry["report_sha256"]
                            ),
                        }
                    ),
                },
            )
            return {
                "sector": sector,
                "partition_index": None,
                "solver_evidence": evidence,
            }

        for wrapper in _run_parallel_decisions(
            pending_sectors,
            started=started,
            total_timeout=total,
            timeout_per_decision=per_decision,
            workers=workers,
            solve_one=solve_escalation,
        ):
            layer_by_sector[str(wrapper["sector"])] = wrapper
            decision_attempts.append(
                _attempt_summary(
                    wrapper,
                    phase="escalation",
                    max_weight=threshold,
                ),
            )

        layer_failed = False
        for sector in layer_sectors:
            wrapper = layer_by_sector.get(sector)
            if wrapper is None:
                layer_failed = True
                continue
            max_weight_attempted = max(max_weight_attempted, threshold)
            if _valid_upper_witness(
                wrapper,
                distance=threshold,
                hx=hx,
                hz=hz,
                lx=lx,
                lz=lz,
                expected_anchors=anchors,
            ):
                witness = wrapper
                exact_distance = threshold
                break
            checks, logicals = _sector_matrices(sector, hx, hz, lx, lz)
            if not _complete_unsat(
                wrapper,
                sector=sector,
                max_weight=threshold,
                checks=checks,
                logicals=logicals,
                expected_anchors=anchors,
            ):
                # A timeout, backend error, or a SAT result inconsistent with
                # the already-proved lower layer must remain retryable.
                layer_failed = True
                continue
        if witness is not None or layer_failed:
            break
        if set(layer_by_sector) != set(proof_sectors):
            break
        current_lower = [layer_by_sector[sector] for sector in proof_sectors]
        current_mode = GLOBAL_MODE
        current_anchor_cover_cubes = None
        lower_threshold = threshold
        completed_unsat_thresholds.append(threshold)
        threshold += 1

    exact = bool(
        lower_complete
        and witness is not None
        and exact_distance > 0
        and lower_threshold == exact_distance - 1
    )
    proof = (
        _proof_payload(
            mode=current_mode,
            required_distance=required,
            distance=exact_distance,
            lower=current_lower,
            witness=witness,
            logical_detector=logical_detector,
            translation_symmetry=translation_symmetry,
            xz_sector_isometry=xz_sector_isometry,
            anchor_indices=anchors,
            anchor_cover_cubes=current_anchor_cover_cubes,
            expected_lower_decisions=len(_expected_solver_decisions(
                current_mode,
                k,
                proof_sectors,
                current_anchor_cover_cubes,
            )),
            expected_lower_partitions=len(_expected_decisions(
                current_mode,
                k,
                proof_sectors,
            )),
        )
        if exact and witness is not None
        else None
    )
    current_evidence_threshold = (
        lower_threshold if lower_threshold >= 0 else initial_threshold
    )
    validated_current_lower: list[dict[str, Any]] = []
    for current_item in current_lower:
        recovered_item = _stored_unsat_decisions(
            [current_item],
            mode=current_mode,
            k=k,
            max_weight=current_evidence_threshold,
            hx=hx,
            hz=hz,
            lx=lx,
            lz=lz,
            expected_anchors=anchors,
            require_complete=False,
            sectors=proof_sectors,
            anchor_cover_cubes=current_anchor_cover_cubes,
        )
        if recovered_item:
            validated_current_lower.extend(recovered_item)
    completed_current_lower = len(validated_current_lower)
    expected_current_lower = len(_expected_solver_decisions(
        current_mode,
        k,
        proof_sectors,
        current_anchor_cover_cubes,
    ))
    expected_current_partitions = len(_expected_decisions(
        current_mode,
        k,
        proof_sectors,
    ))
    completed_current_partitions = _completed_partition_count(
        validated_current_lower,
        mode=current_mode,
        k=k,
        sectors=proof_sectors,
        anchor_cover_cubes=current_anchor_cover_cubes,
    )
    novelty = check_code_novelty(code, code_type="css")
    normalized_claim = {
        **clean_claim,
        "n": n,
        "k": k,
        "d": exact_distance if exact else 0,
        "fom": k * exact_distance * exact_distance / n if exact else 0.0,
        "d_is_exact": exact,
        "structural_novelty": novelty,
    }
    if proof is not None:
        normalized_claim["exact_distance_proof"] = proof
    final_gate = evaluate_challenge_gate(
        normalized_claim,
        known_answer_artifact=known_answer_artifact,
    )
    passed = bool(exact and final_gate.get("accepted") is True)
    certificate: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "certificate_type": CERTIFICATE_TYPE,
        "formulation": FORMULATION,
        "claim": normalized_claim,
        "matrix_sha256": {
            "hx": _matrix_sha256(hx),
            "hz": _matrix_sha256(hz),
        },
        "known_answer": {
            "artifact_sha256": _file_sha256(known_answer_artifact),
        },
        "xz_sector_isometry": (
            None
            if xz_sector_isometry is None
            else dict(xz_sector_isometry)
        ),
        "anchor_cover_cubes": (
            None
            if current_anchor_cover_cubes is None
            else [dict(cube) for cube in current_anchor_cover_cubes]
        ),
        "solver": {
            "interface": "evaluation.distance_sat",
            "backend": "python-sat",
            "python_sat_version": _package_version("python-sat"),
            "coverage_mode": current_mode,
            "solver_workers": workers,
            "timeout_per_decision_s": per_decision,
            "total_timeout_s": total,
            "seed": seed,
        },
        "environment": {
            "python": platform.python_version(),
            "numpy": _package_version("numpy"),
            "qldpc": _package_version("qldpc"),
        },
        "sector_exact": {
            "exact": exact,
            "coverage_mode": current_mode,
            "initial_coverage_mode": mode,
            "required_distance": required,
            "initial_lower_bound_threshold": initial_threshold,
            "exact_lower_bound_threshold": lower_threshold,
            "expected_lower_decisions": expected_current_lower,
            "completed_lower_decisions": completed_current_lower,
            "expected_lower_partitions": expected_current_partitions,
            "completed_lower_partitions": completed_current_partitions,
            "lower_bound": lower_threshold + 1 if lower_threshold >= 0 else 0,
            "upper_bound": exact_distance if witness is not None else None,
            "distance": exact_distance if exact else 0,
            "max_weight_attempted": max_weight_attempted,
            "completed_unsat_thresholds": completed_unsat_thresholds,
            "reused_stage3_escalation_decisions": (
                reused_stage3_escalation_decisions
            ),
            "decision_attempts": decision_attempts,
            "retryable_decisions": sum(
                item["retryable"] is True for item in decision_attempts
            ),
            "lower_resumed_from_stage3": lower_resumed,
            "upper_resumed_from_stage3": upper_resumed,
            "elapsed_s": time.monotonic() - started,
            "proof": proof,
            "xz_sector_isometry": (
                None
                if xz_sector_isometry is None
                else dict(xz_sector_isometry)
            ),
            "anchor_cover_cubes": (
                None
                if current_anchor_cover_cubes is None
                else [dict(cube) for cube in current_anchor_cover_cubes]
            ),
        },
        "final_gate": final_gate,
        "passed": passed,
    }
    if not passed:
        certificate["failure_disposition"] = incomplete_result_disposition(
            domain="solver" if not exact else "evidence",
            code=(
                "SECTOR_SAT_EXACT_PROOF_INCOMPLETE"
                if not exact
                else "SECTOR_SAT_FINAL_GATE_REJECTED"
            ),
        )
    certificate["certificate_sha256"] = _certificate_sha256(certificate)
    return certificate


def verify_sector_sat_certificate(
    certificate: dict[str, Any],
    *,
    known_answer_artifact: Path | str,
    rerun_milp: bool = True,
    timeout_per_logical: float | None = None,
    checkpoint_path: Path | str | None = None,
    resume: bool = False,
    total_timeout: float | None = None,
    solver_workers: int = 1,
    sector_solver: SectorSolver | None = None,
) -> dict[str, Any]:
    """Independently rebuild, replay, and rerun a sector-SAT certificate."""

    workers = _validate_solver_workers(solver_workers)
    started = time.monotonic()
    checks: dict[str, bool] = {}
    failures: list[str] = []
    replay_complete = True
    checks["schema"] = bool(
        certificate.get("schema_version") == SCHEMA_VERSION
        and certificate.get("certificate_type") == CERTIFICATE_TYPE
        and certificate.get("formulation") == FORMULATION
    )
    checks["certificate_sha256"] = bool(
        certificate.get("certificate_sha256") == _certificate_sha256(certificate)
    )
    try:
        checks["known_answer_sha256"] = bool(
            certificate["known_answer"]["artifact_sha256"]
            == _file_sha256(known_answer_artifact)
        )
        claim = certificate["claim"]
        if not isinstance(claim, dict):
            raise TypeError("claim must be an object")
        code, hx, hz, lx, lz = _matrices(claim)
        n = int(code.num_qudits)
        k = n - _rank_f2(hx) - _rank_f2(hz)
        required = minimum_winning_distance(n, k)
        proof = claim["exact_distance_proof"]
        if not isinstance(proof, dict):
            raise TypeError("exact_distance_proof must be an object")
        distance = int(claim["d"])
        if (
            distance < required
            or int(claim.get("required_distance", required)) != required
            or proof.get("required_distance") != required
            or proof.get("lower_bound_threshold") != distance - 1
        ):
            raise ValueError("exact proof threshold/distance metadata mismatch")
        mode = str(proof["coverage_mode"])
        if mode not in SUPPORTED_MODES:
            raise ValueError("exact proof coverage_mode is unsupported")
        lower = proof["lower_bound_decisions"]
        witness = proof["upper_witness"]
        if not isinstance(lower, list) or not isinstance(witness, dict):
            raise TypeError("typed proof evidence is malformed")
        coverage_request = {
            "coverage_mode": mode,
            "lower_bound_decisions": lower,
            "upper_witness": witness,
            "logical_detector": proof.get("logical_detector"),
            "translation_symmetry": proof.get("translation_symmetry"),
            "xz_sector_isometry": proof.get("xz_sector_isometry"),
            "anchor_cover_cubes": proof.get("anchor_cover_cubes"),
            "use_translation_anchors": bool(proof.get("anchor_indices")),
        }
        xz_sector_isometry, proof_sectors = _xz_isometry_context(
            coverage_request,
            claim,
            hx=hx,
            hz=hz,
        )
        logical_detector, translation_symmetry, anchors = _coverage_context(
            coverage_request,
            claim,
            hx=hx,
            hz=hz,
            lx=lx,
            lz=lz,
        )
        anchor_cover_cubes = _rebuild_anchor_cover_cubes(
            proof.get("anchor_cover_cubes"),
            anchors=anchors,
        )
    except (KeyError, OSError, TypeError, ValueError) as exc:
        return {
            "passed": False,
            "replay_complete": False,
            "checks": checks,
            "failures": [f"certificate reconstruction failed: {exc}"],
            "failure_disposition": incomplete_result_disposition(
                domain="schema",
                code="SECTOR_SAT_CERTIFICATE_RECONSTRUCTION_FAILED",
            ),
        }

    checks["matrix_sha256"] = certificate.get("matrix_sha256") == {
        "hx": _matrix_sha256(hx),
        "hz": _matrix_sha256(hz),
    }
    checks["logical_detector"] = proof.get("logical_detector") == logical_detector
    checks["translation_symmetry"] = bool(
        proof.get("translation_symmetry") == translation_symmetry
        and proof.get("anchor_indices") == list(anchors)
    )
    expected_partitions = _expected_decisions(mode, k, proof_sectors)
    expected = _expected_solver_decisions(
        mode,
        k,
        proof_sectors,
        anchor_cover_cubes,
    )
    validated_lower = _stored_unsat_decisions(
        lower,
        mode=mode,
        k=k,
        max_weight=distance - 1,
        hx=hx,
        hz=hz,
        lx=lx,
        lz=lz,
        expected_anchors=anchors,
        sectors=proof_sectors,
        anchor_cover_cubes=anchor_cover_cubes,
    )
    checks["typed_lower_evidence"] = bool(
        proof.get("required_distance") == required
        and proof.get("lower_bound_threshold") == distance - 1
        and validated_lower is not None
        and validated_lower == lower
    )
    checks["upper_witness"] = _valid_upper_witness(
        witness,
        distance=distance,
        hx=hx,
        hz=hz,
        lx=lx,
        lz=lz,
        expected_anchors=anchors,
    )
    proof_without_hash = dict(proof)
    proof_without_hash.pop("proof_sha256", None)
    checks["proof_sha256"] = proof.get("proof_sha256") == _canonical_sha256(
        proof_without_hash,
    )
    stored_exact = certificate.get("sector_exact")
    expected_count = len(expected)
    expected_partition_count = len(expected_partitions)
    legacy_single_or = anchor_cover_cubes is None
    proof_expected_decisions_valid = bool(
        proof.get("expected_lower_decisions") == expected_count
        or (
            legacy_single_or
            and "expected_lower_decisions" not in proof
        )
    )
    proof_partition_counts_valid = bool(
        (
            proof.get("expected_lower_partitions") == expected_partition_count
            and proof.get("completed_lower_partitions")
            == expected_partition_count
        )
        or (
            legacy_single_or
            and "expected_lower_partitions" not in proof
            and "completed_lower_partitions" not in proof
        )
    )
    checks["anchor_cover_cubes"] = bool(
        proof.get("anchor_cover_cubes") == anchor_cover_cubes
        and certificate.get("anchor_cover_cubes") == anchor_cover_cubes
        and isinstance(stored_exact, Mapping)
        and stored_exact.get("anchor_cover_cubes") == anchor_cover_cubes
    )
    checks["xz_sector_isometry"] = bool(
        proof.get("xz_sector_isometry") == xz_sector_isometry
        and certificate.get("xz_sector_isometry") == xz_sector_isometry
        and isinstance(stored_exact, Mapping)
        and stored_exact.get("xz_sector_isometry") == xz_sector_isometry
    )
    checks["proof_metadata"] = bool(
        proof.get("schema_version") == 1
        and proof.get("proof_type") == SECTOR_SAT_EXACT_PROOF_TYPE
        and proof.get("coverage_mode") == mode
        and proof.get("required_distance") == required
        and proof.get("lower_bound_threshold") == distance - 1
        and type(proof.get("completed_lower_decisions")) is int
        and proof_expected_decisions_valid
        and proof.get("completed_lower_decisions") == expected_count
        and proof_partition_counts_valid
    )
    checks["sector_exact_coverage_mode"] = bool(
        isinstance(stored_exact, Mapping)
        and stored_exact.get("coverage_mode") == mode
    )
    checks["sector_exact_counts"] = bool(
        isinstance(stored_exact, Mapping)
        and type(stored_exact.get("expected_lower_decisions")) is int
        and type(stored_exact.get("completed_lower_decisions")) is int
        and stored_exact.get("expected_lower_decisions") == expected_count
        and stored_exact.get("completed_lower_decisions") == expected_count
        and (
            (
                type(stored_exact.get("expected_lower_partitions")) is int
                and type(stored_exact.get("completed_lower_partitions")) is int
                and stored_exact.get("expected_lower_partitions")
                == expected_partition_count
                and stored_exact.get("completed_lower_partitions")
                == expected_partition_count
            )
            or (
                legacy_single_or
                and "expected_lower_partitions" not in stored_exact
                and "completed_lower_partitions" not in stored_exact
            )
        )
        and len(lower) == expected_count
    )
    checks["sector_exact_proof_binding"] = bool(
        isinstance(stored_exact, Mapping)
        and stored_exact.get("proof") == proof
    )
    checks["distance_recomputed"] = bool(
        isinstance(stored_exact, Mapping)
        and stored_exact.get("exact") is True
        and stored_exact.get("distance") == distance
        and stored_exact.get("required_distance") == required
        and stored_exact.get("exact_lower_bound_threshold") == distance - 1
        and stored_exact.get("lower_bound") == distance
        and stored_exact.get("upper_bound") == distance
        and proof.get("exact") is True
        and proof.get("distance") == distance
        and proof.get("lower_bound") == distance
        and proof.get("upper_bound") == distance
    )

    rerun_matches = bool(rerun_milp and expected)
    rerun_completed = 0
    rerun_results: list[dict[str, Any]] = []
    solve = _default_solver() if sector_solver is None else sector_solver
    per_decision = timeout_per_logical
    if per_decision is None:
        per_decision = certificate.get("solver", {}).get(
            "timeout_per_decision_s",
            300,
        )
    try:
        per_decision = _strict_positive_timeout(
            float(per_decision),
            "timeout_per_logical",
        )
        total = (
            math.inf
            if total_timeout is None
            else _strict_positive_timeout(total_timeout, "total_timeout")
        )
    except (TypeError, ValueError, OverflowError):
        per_decision = 0.0
        total = 0.0
        rerun_matches = False
        replay_complete = False

    if rerun_milp and checks["typed_lower_evidence"]:
        by_key = {
            _solver_decision_key(
                str(item["sector"]),
                item.get("partition_index"),
                item.get("anchor_cube"),
            ): item
            for item in lower
        }
        rerun_attempts: list[dict[str, Any]] = []

        def solve_verification(
            decision: tuple[str, int | None, dict[str, Any] | None],
            decision_timeout: float,
        ) -> dict[str, Any]:
            sector, partition, anchor_cube = decision
            key = _solver_decision_key(sector, partition, anchor_cube)
            requested_solver, requested_encoding = (
                _validated_replay_solver_config(by_key[key])
            )
            stabilizers, logicals = _sector_matrices(sector, hx, hz, lx, lz)
            evidence = _call_solver(
                solve,
                stabilizers,
                logicals,
                sector=sector,
                max_weight=distance - 1,
                timeout=decision_timeout,
                solver_workers=1,
                seed=int(certificate.get("solver", {}).get("seed", 0)),
                partition_index=partition,
                anchor_indices=anchors,
                anchor_cube=anchor_cube,
                checkpoint_path=_checkpoint_for(
                    checkpoint_path,
                    phase="verify-lower",
                    sector=sector,
                    partition_index=partition,
                    max_weight=distance - 1,
                    anchor_cube=anchor_cube,
                ),
                resume=resume,
                checkpoint_identity={
                    "certificate_sha256": certificate.get("certificate_sha256"),
                    "phase": "verify-lower",
                    "partition_index": partition,
                    "anchor_cube_sha256": (
                        None
                        if anchor_cube is None
                        else anchor_cube["cube_sha256"]
                    ),
                    **(
                        {}
                        if xz_sector_isometry is None
                        else {
                            "xz_sector_isometry_sha256": (
                                xz_sector_isometry["report_sha256"]
                            ),
                        }
                    ),
                },
                requested_solver=requested_solver,
                cardinality_encoding=requested_encoding,
            )
            return {
                "sector": sector,
                "partition_index": partition,
                "anchor_cube": (
                    None if anchor_cube is None else dict(anchor_cube)
                ),
                "solver_evidence": evidence,
            }

        rerun_results = _run_parallel_decisions(
            expected,
            started=started,
            total_timeout=total,
            timeout_per_decision=per_decision,
            workers=workers,
            solve_one=solve_verification,
        )
        if len(rerun_results) != len(expected):
            rerun_matches = False
            replay_complete = False
        for wrapper in rerun_results:
            sector = str(wrapper["sector"])
            partition = wrapper.get("partition_index")
            anchor_cube = wrapper.get("anchor_cube")
            stabilizers, logicals = _sector_matrices(sector, hx, hz, lx, lz)
            rerun_attempts.append(
                _attempt_summary(
                    wrapper,
                    phase="verify-lower",
                    max_weight=distance - 1,
                ),
            )
            if not _complete_unsat(
                wrapper,
                sector=sector,
                max_weight=distance - 1,
                checks=stabilizers,
                logicals=logicals,
                expected_anchors=anchors,
                expected_anchor_cube=(
                    anchor_cube if isinstance(anchor_cube, Mapping) else None
                ),
            ):
                rerun_matches = False
                replay_complete = False
                continue
            # The independent decision need not reproduce timings or a solver
            # model; complete UNSAT for the same reconstructed instance is the
            # mathematical statement being replayed.
            del by_key[_solver_decision_key(
                sector,
                partition,
                anchor_cube if isinstance(anchor_cube, Mapping) else None,
            )]
            rerun_completed += 1
        if by_key:
            rerun_matches = False
    elif rerun_milp:
        rerun_matches = False
        replay_complete = False
        rerun_attempts = []
    else:
        rerun_attempts = []
    checks["sat_rerun"] = rerun_matches
    rerun_verified_partitions = _completed_partition_count(
        [
            wrapper
            for wrapper in rerun_results
            if isinstance(wrapper, dict)
            and _complete_unsat(
                wrapper,
                sector=str(wrapper.get("sector")),
                max_weight=distance - 1,
                checks=_sector_matrices(
                    str(wrapper.get("sector")), hx, hz, lx, lz,
                )[0],
                logicals=_sector_matrices(
                    str(wrapper.get("sector")), hx, hz, lx, lz,
                )[1],
                expected_anchors=anchors,
                expected_anchor_cube=(
                    wrapper.get("anchor_cube")
                    if isinstance(wrapper.get("anchor_cube"), Mapping)
                    else None
                ),
            )
        ]
        if rerun_milp
        else [],
        mode=mode,
        k=k,
        sectors=proof_sectors,
        anchor_cover_cubes=anchor_cover_cubes,
    )

    gate = evaluate_challenge_gate(
        claim,
        known_answer_artifact=known_answer_artifact,
    )
    checks["final_gate"] = gate.get("accepted") is True
    checks["certificate_passed_flag"] = certificate.get("passed") is True
    for name, passed in checks.items():
        if passed is not True:
            failures.append(name)
    passed = not failures
    result: dict[str, Any] = {
        "passed": passed,
        "replay_complete": replay_complete,
        "checks": checks,
        "failures": failures,
        "distance": distance,
        "sector_decisions_verified": rerun_completed,
        "sector_decisions_total": len(expected),
        "logical_partitions_verified": rerun_verified_partitions,
        "logical_partitions_total": expected_partition_count,
        "sector_decision_attempts": rerun_attempts,
        "rerun_elapsed_s": time.monotonic() - started,
        "solver_workers": workers,
        "final_gate": gate,
    }
    if not passed:
        result["failure_disposition"] = incomplete_result_disposition(
            domain="solver" if not replay_complete else "evidence",
            code=(
                "SECTOR_SAT_REPLAY_INCOMPLETE"
                if not replay_complete
                else "SECTOR_SAT_REPLAY_MISMATCH"
            ),
        )
    return result


__all__ = [
    "CERTIFICATE_TYPE",
    "FORMULATION",
    "GLOBAL_MODE",
    "PARTITION_MODE",
    "REQUEST_FIELD",
    "STAGE3_GATE",
    "build_sector_sat_certificate",
    "claim_from_sector_sat_artifact",
    "verify_sector_sat_certificate",
]
