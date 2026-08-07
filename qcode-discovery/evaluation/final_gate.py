"""Fail-closed final acceptance gate for the qLDPC challenge.

Discovery records are untrusted inputs.  This module rebuilds every CSS BB
candidate, recomputes its static parameters, reruns the structural-novelty
audit, and accepts a challenge claim only when:

* the frozen known-answer artifact passed all three required baselines;
* the candidate is a valid, connected CSS code with check weight and qubit
  degree at most six;
* its reported ``n`` and ``k`` agree with independent recomputation;
* exact distance follows either from all ``2k`` MILP optima or from a typed
  complete X/Z SAT lower bound plus an algebraically checked upper witness;
* it is structurally novel against the known CSS registry; and
* it beats the scalar threshold or one of the stated Pareto fronts.

Missing or malformed evidence is always a rejection, never a warning.
"""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path
from typing import Any, Mapping

import numpy as np

from evaluation.bb_sector_isometry import verify_bb_xz_sector_isometry
from evaluation.bb_code import build_bb_code, validate_terms
from evaluation.geometry import candidate_geometry
from evaluation.distance_milp import get_code_matrices
from evaluation.registry import check_code_novelty
from evaluation.structural_dedup import (
    check_css_code_structural_novelty,
    check_css_structural_novelty,
)
from evaluation.target_policy import (
    DEFAULT_TARGET_MODE,
    FOM_THRESHOLD,
    KNOWN_PARETO_REFERENCES,
    SUPPORTED_TARGET_MODES,
    TARGET_MODE_GIST,
    TARGET_MODE_SCALAR,
    classify_target_win,
    minimum_target_distance,
    target_binding,
    validate_target_binding,
    validate_target_mode,
)


REQUIRED_BASELINES = {
    "[[72,12,6]]": (72, 12, 6),
    "[[90,8,10]]": (90, 8, 10),
    "[[144,12,12]]": (144, 12, 12),
}


def _rank_f2(matrix: np.ndarray) -> int:
    work = np.asarray(matrix, dtype=np.uint8).copy() & 1
    rows, cols = work.shape
    rank = 0
    for col in range(cols):
        pivots = np.flatnonzero(work[rank:, col])
        if not pivots.size:
            continue
        pivot = rank + int(pivots[0])
        if pivot != rank:
            work[[rank, pivot]] = work[[pivot, rank]]
        other = np.flatnonzero(work[:, col])
        other = other[other != rank]
        if other.size:
            work[other] ^= work[rank]
        rank += 1
        if rank == rows:
            break
    return rank


def _matrix_sha256(matrix: np.ndarray) -> str:
    binary = np.ascontiguousarray(np.asarray(matrix, dtype=np.uint8) & 1)
    digest = hashlib.sha256()
    digest.update(f"{binary.shape[0]}x{binary.shape[1]}:".encode())
    digest.update(np.packbits(binary, axis=None, bitorder="little").tobytes())
    return digest.hexdigest()


def _connected(checks: np.ndarray) -> tuple[bool, int]:
    matrix = np.asarray(checks, dtype=np.uint8) & 1
    num_checks, num_qubits = matrix.shape
    adjacency = [[] for _ in range(num_checks + num_qubits)]
    for check_idx, qubit_idx in np.argwhere(matrix):
        left = int(check_idx)
        right = num_checks + int(qubit_idx)
        adjacency[left].append(right)
        adjacency[right].append(left)
    unseen = set(range(len(adjacency)))
    components = 0
    while unseen:
        components += 1
        stack = [unseen.pop()]
        while stack:
            node = stack.pop()
            for neighbor in adjacency[node]:
                if neighbor in unseen:
                    unseen.remove(neighbor)
                    stack.append(neighbor)
    return components == 1, components


def validate_known_answer_artifact(path: Path | str) -> dict[str, Any]:
    """Validate the baseline artifact without trusting its top-level flag."""
    path = Path(path)
    failures: list[str] = []
    try:
        artifact = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        return {
            "passed": False,
            "path": str(path),
            "failures": [f"known-answer artifact unavailable or invalid: {exc}"],
        }

    if artifact.get("schema_version") != 1:
        failures.append("known-answer schema_version must be 1")
    if artifact.get("gate") != "qldpc-known-answer-baselines":
        failures.append("unexpected known-answer gate identifier")
    records = artifact.get("baselines")
    if not isinstance(records, list):
        records = []
        failures.append("known-answer baselines must be a list")

    by_label = {
        row.get("label"): row for row in records if isinstance(row, dict)
    }
    if set(by_label) != set(REQUIRED_BASELINES):
        failures.append("known-answer artifact must contain exactly the three required baselines")
    for label, expected in REQUIRED_BASELINES.items():
        row = by_label.get(label)
        if not row:
            continue
        observed = row.get("observed") or {}
        if tuple(observed.get(name) for name in ("n", "k", "d")) != expected:
            failures.append(f"{label}: observed parameters do not match {expected}")
        checks = row.get("checks")
        if (
            row.get("status") != "passed"
            or not isinstance(checks, dict)
            or not checks
            or not all(value is True for value in checks.values())
        ):
            failures.append(f"{label}: one or more baseline checks failed")
        milp = row.get("milp") or {}
        total = 2 * expected[1]
        if not (
            milp.get("exact") is True
            and int(milp.get("total_logicals", 0)) == total
            and int(milp.get("num_logicals_checked", 0)) == total
            and int(milp.get("logicals_optimal", 0)) == total
            and int(milp.get("logicals_incumbent", 0)) == 0
        ):
            failures.append(f"{label}: MILP did not prove all 2k directions optimal")

    if artifact.get("passed") is not True:
        failures.append("known-answer top-level result is not passed")
    summary = artifact.get("summary") or {}
    if summary.get("passed") != 3 or summary.get("total") != 3:
        failures.append("known-answer summary is not 3/3")
    return {
        "passed": not failures,
        "path": str(path.resolve()),
        "generated_at": artifact.get("generated_at"),
        "failures": failures,
    }


def _exact_milp_check(row: dict[str, Any], k: int) -> bool:
    details = row.get("milp_details")
    total = 2 * k
    return bool(
        row.get("milp_attempted") is True
        and row.get("d_is_exact") is True
        and isinstance(details, dict)
        and details.get("exact") is True
        and int(details.get("total_logicals", 0)) == total
        and int(details.get("num_logicals_checked", 0)) == total
        and int(details.get("logicals_optimal", 0)) == total
        and int(details.get("logicals_incumbent", 0)) == 0
    )


SECTOR_SAT_EXACT_PROOF_TYPE = "qldpc-css-sector-sat-exact-proof-v1"
TWOBGA_EXACT_PROOF_TYPE = "qldpc-css-twobga-subsystem-exact-proof-v1"


def _canonical_sha256(value: Any, *, omit: str | None = None) -> str:
    payload = dict(value) if isinstance(value, dict) else value
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


def _sat_array_sha256(name: str, value: np.ndarray) -> str:
    array = np.ascontiguousarray(np.asarray(value, dtype=np.uint8) & 1)
    digest = hashlib.sha256()
    digest.update(name.encode())
    digest.update(b"\0")
    digest.update(json.dumps(list(array.shape), separators=(",", ":")).encode())
    digest.update(b"\0")
    digest.update(array.tobytes(order="C"))
    return digest.hexdigest()


def _complete_sat_unsat_evidence(
    wrapper: Any,
    *,
    sector: str,
    max_weight: int,
    partition_index: int | None,
    check_matrix: np.ndarray,
    target_logicals: np.ndarray,
    expected_anchors: tuple[int, ...],
    expected_anchor_cube: dict[str, Any] | None = None,
) -> bool:
    """Validate one typed complete SAT decision without inventing MILP data."""

    if not isinstance(wrapper, dict) or wrapper.get("sector") != sector:
        return False
    evidence = wrapper.get("solver_evidence")
    if not isinstance(evidence, dict):
        return False
    try:
        evidence_hash_valid = evidence.get("evidence_sha256") == _canonical_sha256(
            evidence,
            omit="evidence_sha256",
        )
    except (TypeError, ValueError):
        return False
    backend = evidence.get("backend")
    instance = evidence.get("instance")
    stored_cube = wrapper.get("anchor_cube")
    if expected_anchor_cube is None:
        cube_binding_valid = bool(
            stored_cube is None
            and evidence.get("zero_anchor_indices", []) == []
            and evidence.get("one_anchor_index") is None
            and evidence.get("anchor_cube_sha256") is None
            and (
                not isinstance(instance, dict)
                or (
                    instance.get("zero_anchor_indices", []) == []
                    and instance.get("one_anchor_index") is None
                    and instance.get("anchor_cube_sha256") is None
                )
            )
        )
    else:
        zero_indices = [
            int(index) for index in expected_anchor_cube["zero_anchor_indices"]
        ]
        one_index = int(expected_anchor_cube["one_anchor_index"])
        cube_sha256 = str(expected_anchor_cube["cube_sha256"])
        unit_clauses = [
            *([[-(index + 1)] for index in zero_indices]),
            [one_index + 1],
        ]
        try:
            unsigned_instance = dict(instance)
            binding_sha256 = unsigned_instance.pop("binding_sha256")
            cnf = evidence.get("cnf")
            cube_binding_valid = bool(
                isinstance(stored_cube, dict)
                and stored_cube == expected_anchor_cube
                and evidence.get("zero_anchor_indices") == zero_indices
                and evidence.get("one_anchor_index") == one_index
                and evidence.get("anchor_cube_sha256") == cube_sha256
                and instance.get("zero_anchor_indices") == zero_indices
                and instance.get("one_anchor_index") == one_index
                and instance.get("anchor_cube_sha256") == cube_sha256
                and instance.get("anchor_constraint_formulation")
                == "anchor-or-first-nonzero-unit-clauses-v1"
                and instance.get("anchor_unit_clauses") == unit_clauses
                and instance.get("anchor_unit_clauses_sha256")
                == _canonical_sha256(unit_clauses)
                and isinstance(cnf, dict)
                and cnf.get("anchor_unit_clauses_sha256")
                == _canonical_sha256(unit_clauses)
                and binding_sha256 == _canonical_sha256(unsigned_instance)
            )
        except (KeyError, TypeError, ValueError):
            cube_binding_valid = False
    return bool(
        evidence.get("schema_version") == 1
        and evidence.get("evidence_kind")
        == "qcode-css-threshold-sat-evidence"
        and evidence.get("formulation")
        in {
            "css-global-logical-threshold-cnf-v1",
            "css-first-nonzero-logical-threshold-cnf-v1",
        }
        and evidence.get("sector") == sector
        and evidence.get("max_weight") == max_weight
        and evidence.get("outcome") == "unsat"
        and evidence.get("decision_complete") is True
        and evidence.get("threshold_infeasible") is True
        and evidence.get("operator") is None
        and evidence.get("objective") is None
        and isinstance(backend, dict)
        and backend.get("distribution") == "python-sat"
        and isinstance(backend.get("solver"), str)
        and bool(backend.get("solver"))
        and isinstance(instance, dict)
        and instance.get("check_matrix_sha256")
        == _sat_array_sha256("checks", check_matrix)
        and instance.get("target_logicals_sha256")
        == _sat_array_sha256("logicals", target_logicals)
        and instance.get("partition_index") == partition_index
        and instance.get("anchor_indices") == list(expected_anchors)
        and evidence.get("partition_index") == partition_index
        and evidence.get("anchor_indices") == list(expected_anchors)
        and cube_binding_valid
        and evidence_hash_valid
    )


def _typed_exact_sector_check(
    row: dict[str, Any],
    *,
    distance: int,
    k: int,
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
) -> bool:
    """Replay the shape and upper witness of a typed exact-sector proof.

    The complete UNSAT decisions are independently rerun by the certificate
    verifier.  This gate still checks their immutable SAT schema/backend
    binding and algebraically replays the weight-``distance`` witness.  It
    deliberately does not set ``all_2k_milp_directions_optimal``: a global or
    disjoint-sector SAT proof is a different mathematical proof object.
    """

    proof = row.get("exact_distance_proof")
    if not isinstance(proof, dict):
        return False
    try:
        proof_hash_valid = proof.get("proof_sha256") == _canonical_sha256(
            proof,
            omit="proof_sha256",
        )
    except (TypeError, ValueError):
        return False
    mode = proof.get("coverage_mode")
    lower = proof.get("lower_bound_decisions")
    try:
        n = int(hx.shape[1])
        supplied_mode = row.get("target_mode")
        if "target" not in row:
            target_mode = validate_target_mode(
                DEFAULT_TARGET_MODE if supplied_mode is None else supplied_mode
            )
            if (
                target_mode != DEFAULT_TARGET_MODE
                or row.get("target_binding_sha256") is not None
            ):
                return False
            selected_target = None
            required_distance = minimum_winning_distance(n, k)
            proof_target_valid = bool(
                proof.get("target") is None
                and proof.get("target_binding_sha256") is None
                and (
                    proof.get("target_mode") is None
                    or validate_target_mode(proof.get("target_mode"))
                    == DEFAULT_TARGET_MODE
                )
            )
            target_win = distance >= required_distance
        else:
            selected_target = validate_target_binding(
                row.get("target"),
                n=n,
                k=k,
                mode=supplied_mode,
            )
            target_mode = str(selected_target["mode"])
            required_distance = int(selected_target["required_distance"])
            proof_target_valid = bool(
                row.get("target_mode") == target_mode
                and row.get("target_binding_sha256")
                == selected_target["binding_sha256"]
                and proof.get("target_mode") == target_mode
                and proof.get("target") == selected_target
                and proof.get("target_binding_sha256")
                == selected_target["binding_sha256"]
            )
            target_win = classify_target_win(
                n,
                k,
                distance,
                target_mode,
            )["passed"] is True
            reported_required = row.get("required_distance")
        if selected_target is None:
            reported_required = row.get(
                "required_distance",
                required_distance,
            )
    except (TypeError, ValueError):
        return False
    if (
        proof.get("schema_version") != 1
        or proof.get("proof_type") != SECTOR_SAT_EXACT_PROOF_TYPE
        or proof.get("exact") is not True
        or not proof_target_valid
        or isinstance(reported_required, bool)
        or not isinstance(reported_required, int)
        or reported_required != required_distance
        or proof.get("required_distance") != required_distance
        or distance < required_distance
        or not target_win
        or proof.get("lower_bound_threshold") != distance - 1
        or proof.get("distance") != distance
        or proof.get("lower_bound") != distance
        or proof.get("upper_bound") != distance
        or mode not in {"global", "first-nonzero"}
        or not isinstance(lower, list)
        or not proof_hash_valid
    ):
        return False

    try:
        raw_anchors = proof.get("anchor_indices")
        if not isinstance(raw_anchors, list) or any(
            isinstance(index, bool) or not isinstance(index, int)
            for index in raw_anchors
        ):
            return False
        anchors = tuple(raw_anchors)
        from scripts.screen_frontier_sat import (
            build_anchor_cover_cubes,
            verify_css_logical_detectors,
        )

        detector = verify_css_logical_detectors(hx, hz, lx, lz)
        if (
            detector.get("verified") is not True
            or proof.get("logical_detector") != detector
        ):
            return False
        if anchors:
            from scripts.screen_frontier_xor import verify_bb_translation_symmetry

            symmetry = verify_bb_translation_symmetry(row)
            if (
                symmetry.get("verified") is not True
                or proof.get("translation_symmetry") != symmetry
                or anchors
                != tuple(int(index) for index in symmetry["orbit_representatives"])
            ):
                return False
        elif proof.get("translation_symmetry") is not None:
            return False
        stored_cubes = proof.get("anchor_cover_cubes")
        if stored_cubes is None:
            anchor_cover_cubes = None
        else:
            if not anchors or not isinstance(stored_cubes, list):
                return False
            anchor_cover_cubes = build_anchor_cover_cubes(anchors)
            if stored_cubes != anchor_cover_cubes:
                return False
    except (ImportError, KeyError, TypeError, ValueError):
        return False
    stored_isometry = proof.get("xz_sector_isometry")
    if stored_isometry is None:
        proof_sectors = ("X", "Z")
    elif not isinstance(stored_isometry, dict):
        return False
    else:
        try:
            replayed_isometry = verify_bb_xz_sector_isometry(
                hx,
                hz,
                ell=int(row["ell"]),
                m=int(row["m"]),
                geometry=candidate_geometry(row),
            )
        except (KeyError, TypeError, ValueError):
            return False
        if (
            replayed_isometry.get("verified") is not True
            or replayed_isometry.get("canonical_sector") != "X"
            or replayed_isometry.get("covered_sectors") != ["X", "Z"]
            or stored_isometry != replayed_isometry
        ):
            return False
        proof_sectors = ("X",)

    expected_partitions = 1 if mode == "global" else k
    expected_partition_keys = {
        (sector, None if mode == "global" else index)
        for sector in proof_sectors
        for index in range(expected_partitions)
    }
    cubes: list[dict[str, Any] | None] = (
        [None] if anchor_cover_cubes is None else anchor_cover_cubes
    )
    expected_keys = {
        (
            sector,
            partition,
            None if cube is None else str(cube["cube_sha256"]),
        )
        for sector, partition in expected_partition_keys
        for cube in cubes
    }
    cubes_by_hash = {
        str(cube["cube_sha256"]): cube
        for cube in (anchor_cover_cubes or [])
    }
    expected_decision_count = len(expected_keys)
    expected_partition_count = len(expected_partition_keys)
    if not (
        proof.get("completed_lower_decisions") == expected_decision_count
        and proof.get("expected_lower_decisions", expected_decision_count)
        == expected_decision_count
        and proof.get("expected_lower_partitions", expected_partition_count)
        == expected_partition_count
        and proof.get("completed_lower_partitions", expected_partition_count)
        == expected_partition_count
    ):
        return False
    observed: set[tuple[str, int | None, str | None]] = set()
    for wrapper in lower:
        if not isinstance(wrapper, dict):
            return False
        sector = wrapper.get("sector")
        partition = wrapper.get("partition_index")
        if mode == "global":
            if partition is not None:
                return False
        elif isinstance(partition, bool) or not isinstance(partition, int):
            return False
        raw_cube = wrapper.get("anchor_cube")
        if raw_cube is None:
            expected_cube = None
        elif isinstance(raw_cube, dict):
            expected_cube = cubes_by_hash.get(str(raw_cube.get("cube_sha256")))
            if expected_cube is None or raw_cube != expected_cube:
                return False
        else:
            return False
        key = (
            str(sector),
            partition,
            None if expected_cube is None else str(expected_cube["cube_sha256"]),
        )
        if key not in expected_keys or key in observed:
            return False
        if not _complete_sat_unsat_evidence(
            wrapper,
            sector=str(sector),
            max_weight=distance - 1,
            partition_index=partition,
            check_matrix=hx if sector == "Z" else hz,
            target_logicals=lx if sector == "Z" else lz,
            expected_anchors=anchors,
            expected_anchor_cube=expected_cube,
        ):
            return False
        observed.add(key)
    if observed != expected_keys:
        return False

    witness = proof.get("upper_witness")
    if (
        not isinstance(witness, dict)
        or witness.get("sector") not in set(proof_sectors)
        or witness.get("anchor_cube") is not None
    ):
        return False
    evidence = witness.get("solver_evidence")
    if not isinstance(evidence, dict):
        return False
    try:
        evidence_hash_valid = evidence.get("evidence_sha256") == _canonical_sha256(
            evidence,
            omit="evidence_sha256",
        )
    except (TypeError, ValueError):
        return False
    if not (
        evidence.get("schema_version") == 1
        and evidence.get("evidence_kind")
        == "qcode-css-threshold-sat-evidence"
        and evidence.get("sector") == witness.get("sector")
        and evidence.get("max_weight") == distance
        and evidence.get("outcome") == "sat"
        and evidence.get("decision_complete") is True
        and evidence.get("objective") == distance
        and evidence.get("zero_anchor_indices", []) == []
        and evidence.get("one_anchor_index") is None
        and evidence.get("anchor_cube_sha256") is None
        and isinstance(evidence.get("instance"), dict)
        and evidence["instance"].get("check_matrix_sha256")
        == _sat_array_sha256(
            "checks", hx if witness.get("sector") == "Z" else hz,
        )
        and evidence["instance"].get("target_logicals_sha256")
        == _sat_array_sha256(
            "logicals", lx if witness.get("sector") == "Z" else lz,
        )
        and evidence["instance"].get("partition_index") is None
        and evidence["instance"].get("anchor_indices") == list(anchors)
        and evidence["instance"].get("zero_anchor_indices", []) == []
        and evidence["instance"].get("one_anchor_index") is None
        and evidence["instance"].get("anchor_cube_sha256") is None
        and evidence.get("partition_index") is None
        and evidence.get("anchor_indices") == list(anchors)
        and evidence_hash_valid
    ):
        return False
    try:
        from evaluation.distance_sat import verify_css_threshold_sat_witness

        matrices = {
            "Z": (hx, lx),
            "X": (hz, lz),
        }
        stabilizers, logicals = matrices[str(witness["sector"])]
        return not verify_css_threshold_sat_witness(
            evidence,
            stabilizers,
            logicals,
        )
    except (ImportError, KeyError, TypeError, ValueError):
        return False


def _typed_exact_twobga_check(
    row: dict[str, Any],
    *,
    distance: int,
    k: int,
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
) -> bool:
    """Replay a typed exact proof bridged by a dressed 2BGA subsystem.

    The certificate verifier independently reruns both auxiliary UNSAT
    decisions.  The final gate still rebuilds the rank-defect theorem
    hypotheses, quotient detectors, evidence bindings, and the original-code
    upper witness.  Importing lazily avoids a module cycle because the typed
    certificate builder itself calls this final gate.
    """

    try:
        if candidate_geometry(row) is not None:
            return False
    except (KeyError, TypeError, ValueError):
        return False
    proof = row.get("exact_distance_proof")
    if (
        not isinstance(proof, dict)
        or proof.get("proof_type") != TWOBGA_EXACT_PROOF_TYPE
        or distance <= 0
    ):
        return False
    try:
        from evaluation.twobga_certificate import validate_twobga_exact_proof

        context = validate_twobga_exact_proof(row)
        rebuilt = context["code"]
        return bool(
            int(rebuilt.num_qudits) == int(hx.shape[1])
            and int(rebuilt.dimension) == k
            and int(context["required_distance"]) == distance
            and np.array_equal(context["hx"], hx)
            and np.array_equal(context["hz"], hz)
            and np.array_equal(context["lx"], lx)
            and np.array_equal(context["lz"], lz)
        )
    except (
        ImportError,
        KeyError,
        OverflowError,
        RuntimeError,
        TypeError,
        ValueError,
    ):
        return False


def classify_win(n: int, k: int, d: int) -> dict[str, Any]:
    """Apply the scalar and explicit fixed-coordinate Pareto win rules."""
    fom = k * d * d / n if n > 0 else 0.0
    reasons: list[str] = []
    if fom > FOM_THRESHOLD:
        reasons.append("fom_strictly_above_12")
    for ref_n, ref_k, ref_d in KNOWN_PARETO_REFERENCES:
        ref_fom = ref_k * ref_d * ref_d / ref_n
        label = f"[[{ref_n},{ref_k},{ref_d}]]"
        if math.isclose(fom, ref_fom, rel_tol=0.0, abs_tol=1e-12) and n < ref_n:
            reasons.append(f"same_fom_smaller_n_than_{label}")
        if n == ref_n and d == ref_d and k > ref_k:
            reasons.append(f"higher_k_than_{label}_with_n_d_fixed")
        if n == ref_n and k == ref_k and d > ref_d:
            reasons.append(f"higher_d_than_{label}_with_n_k_fixed")
    return {"passed": bool(reasons), "fom": fom, "reasons": reasons}


def minimum_winning_distance(n: int, k: int) -> int:
    """Return the smallest distance that satisfies any scalar or Pareto win rule."""
    if n <= 0 or k <= 0:
        raise ValueError("n and k must be positive")
    for distance in range(1, n + 1):
        if classify_win(n, k, distance)["passed"]:
            return distance
    raise ValueError(f"no winning distance exists for n={n}, k={k}")


def evaluate_final_gate(
    row: dict[str, Any],
    *,
    known_answer_artifact: Path | str,
) -> dict[str, Any]:
    """Rebuild and structurally evaluate one CSS BB discovery record.

    Typed SAT ``UNSAT`` rows are schema- and instance-bound here, but they are
    not proof-carrying LRAT objects.  A production acceptance must therefore
    also pass the dispatched certificate verifier's fresh solver replay; this
    function alone is not a release authorization.
    """
    baseline = validate_known_answer_artifact(known_answer_artifact)
    checks: dict[str, bool] = {"known_answer_gate": baseline["passed"]}
    failures = list(baseline["failures"])
    result: dict[str, Any] = {
        "schema_version": 1,
        "gate": "qldpc-challenge-final",
        "accepted": False,
        "checks": checks,
        "failures": failures,
        "known_answer": baseline,
    }

    compact_construction = isinstance(row.get("construction"), Mapping)
    try:
        if compact_construction:
            from evaluation.construction import (
                build_css_code_from_claim,
                construction_identity,
                construction_source_fingerprint,
                normalize_construction_claim,
            )

            normalized_claim = normalize_construction_claim(dict(row))
            if not (
                isinstance(normalized_claim, Mapping)
                and isinstance(normalized_claim.get("construction"), Mapping)
            ):
                normalized_claim = {
                    "construction": dict(normalized_claim),
                }
            code = build_css_code_from_claim(dict(normalized_claim))
            construction = dict(normalized_claim["construction"])
            construction_identity_value = construction_identity(
                dict(normalized_claim)
            )
            construction_source = construction_source_fingerprint()
            ell = m = None
            a_terms = b_terms = None
            geometry = None
        else:
            ell, m = int(row["ell"]), int(row["m"])
            a_terms, b_terms = row["A_terms"], row["B_terms"]
            validate_terms(ell, m, a_terms, "A")
            validate_terms(ell, m, b_terms, "B")
            geometry = candidate_geometry(row)
            code = build_bb_code(
                ell, m, a_terms, b_terms, geometry=geometry,
            )
            construction = None
            construction_identity_value = None
            construction_source = None
    except (ImportError, KeyError, TypeError, ValueError) as exc:
        checks["candidate_rebuild"] = False
        failures.append(f"candidate cannot be rebuilt: {exc}")
        return result

    checks["candidate_rebuild"] = True
    hx, hz, lx, lz = get_code_matrices(code)
    hx = np.asarray(hx, dtype=np.uint8) & 1
    hz = np.asarray(hz, dtype=np.uint8) & 1
    lx = np.asarray(lx, dtype=np.uint8) & 1
    lz = np.asarray(lz, dtype=np.uint8) & 1
    stacked = np.vstack((hx, hz))
    n = int(code.num_qudits)
    rank_hx, rank_hz = _rank_f2(hx), _rank_f2(hz)
    k = n - rank_hx - rank_hz
    max_row_weight = int(stacked.sum(axis=1).max(initial=0))
    max_qubit_degree = int(stacked.sum(axis=0).max(initial=0))
    connected, components = _connected(stacked)

    checks.update({
        "css_commutation": int(np.count_nonzero((hx @ hz.T) & 1)) == 0,
        "weight_and_degree_at_most_6": max_row_weight <= 6 and max_qubit_degree <= 6,
        "connected_tanner_graph": connected,
        "reported_n_matches": int(row.get("n", -1)) == n,
        "reported_k_matches": int(row.get("k", -1)) == k,
        "qldpc_k_crosscheck": int(code.dimension) == k,
    })

    d = int(row.get("d", 0) or 0)
    checks["positive_reported_distance"] = d > 0
    exact_proof = row.get("exact_distance_proof")
    if exact_proof is not None:
        if (
            isinstance(exact_proof, dict)
            and exact_proof.get("proof_type") == TWOBGA_EXACT_PROOF_TYPE
        ):
            checks["typed_exact_twobga_subsystem_proof"] = (
                _typed_exact_twobga_check(
                    row,
                    distance=d,
                    k=k,
                    hx=hx,
                    hz=hz,
                    lx=lx,
                    lz=lz,
                )
            )
        else:
            checks["typed_exact_sector_sat_proof"] = _typed_exact_sector_check(
                row,
                distance=d,
                k=k,
                hx=hx,
                hz=hz,
                lx=lx,
                lz=lz,
            )
    else:
        checks["all_2k_milp_directions_optimal"] = _exact_milp_check(row, k)

    reported_audit = row.get("structural_novelty")
    recomputed_audit = (
        check_css_code_structural_novelty(code)
        if compact_construction
        else check_css_structural_novelty(
            ell, m, a_terms, b_terms, geometry=geometry,
        )
    )
    expanded_audit = check_code_novelty(code, code_type="css")
    checks["structural_audit_present"] = bool(
        isinstance(reported_audit, dict)
        and reported_audit.get("checked") is True
        and reported_audit.get("novel") is True
    )
    checks["structural_audit_reproduced"] = bool(
        recomputed_audit.get("novel") is True
        and isinstance(reported_audit, dict)
        and reported_audit.get("canonical_digest") == recomputed_audit.get("canonical_digest")
    )
    checks["expanded_registry_novel"] = bool(
        expanded_audit.get("novel") is True
        and isinstance(reported_audit, dict)
        and reported_audit.get("registry_sha256") == expanded_audit.get("registry_sha256")
    )

    win = classify_win(n, k, d)
    checks["challenge_win"] = win["passed"]
    reported_fom = row.get("fom")
    checks["reported_fom_matches"] = bool(
        isinstance(reported_fom, (int, float))
        and math.isclose(float(reported_fom), win["fom"], rel_tol=0.0, abs_tol=1e-9)
    )

    for name, passed in checks.items():
        if not passed and name != "known_answer_gate":
            failures.append(name)
    result.update({
        "accepted": not failures,
        "candidate": {
            "n": n,
            "k": k,
            "d": d,
            "fom": win["fom"],
            "rank_hx": rank_hx,
            "rank_hz": rank_hz,
            "max_row_weight": max_row_weight,
            "max_qubit_degree": max_qubit_degree,
            "tanner_components": components,
            "matrix_sha256": {
                "hx": _matrix_sha256(hx),
                "hz": _matrix_sha256(hz),
            },
        },
        "structural_novelty": recomputed_audit,
        "expanded_structural_novelty": expanded_audit,
        "win": win,
    })
    if compact_construction:
        result["candidate"].update({
            "construction": construction,
            "construction_identity": construction_identity_value,
            "construction_source_fingerprint": construction_source,
        })
    else:
        result["candidate"].update({
            "ell": ell,
            "m": m,
            "A_terms": a_terms,
            "B_terms": b_terms,
        })
    if not compact_construction and geometry is not None:
        result["candidate"]["geometry"] = geometry
    return result
