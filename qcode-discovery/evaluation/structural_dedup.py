"""Structural novelty gate for CSS bivariate-bicycle codes.

BLISS supplies a colored-Tanner-graph canonical form and a candidate
isomorphism.  A match is accepted only after replaying the full qubit and
X/Z-check permutations directly against both parity-check matrices.
"""

from __future__ import annotations

import hashlib
from functools import lru_cache

import numpy as np

from evaluation.bb_code import build_bb_code, get_code_params_fast, validate_terms
from evaluation.tanner_equivalence import (
    canonical_hash,
    extract_full_vertex_isomorphism,
)


KNOWN_CSS_REFERENCES = (
    ("Bravyi [[72,12,6]]", 6, 6,
     [(3, 0), (0, 1), (0, 2)], [(0, 3), (1, 0), (2, 0)]),
    ("Bravyi [[90,8,10]]", 15, 3,
     [(9, 0), (0, 1), (0, 2)], [(0, 0), (2, 0), (7, 0)]),
    ("Bravyi [[108,8,10]]", 9, 6,
     [(3, 0), (0, 1), (0, 2)], [(0, 3), (1, 0), (2, 0)]),
    ("Gross [[144,12,12]]", 12, 6,
     [(3, 0), (0, 1), (0, 2)], [(0, 3), (1, 0), (2, 0)]),
    ("Bravyi [[288,12,18]]", 12, 12,
     [(3, 0), (0, 2), (0, 7)], [(0, 3), (1, 0), (2, 0)]),
    ("Bravyi [[360,12,<=24]]", 30, 6,
     [(9, 0), (0, 1), (0, 2)], [(0, 3), (25, 0), (26, 0)]),
)


def _matrices(code):
    hx = np.asarray(
        code.matrix_x.toarray() if hasattr(code.matrix_x, "toarray")
        else code.matrix_x, dtype=np.uint8,
    ) & 1
    hz = np.asarray(
        code.matrix_z.toarray() if hasattr(code.matrix_z, "toarray")
        else code.matrix_z, dtype=np.uint8,
    ) & 1
    return hx, hz


def _component_sizes(checks: np.ndarray) -> list[int]:
    """Return Tanner-component sizes using the final gate's graph definition."""
    matrix = np.asarray(checks, dtype=np.uint8) & 1
    num_checks, num_qubits = matrix.shape
    adjacency = [[] for _ in range(num_checks + num_qubits)]
    for check_index, qubit_index in np.argwhere(matrix):
        left = int(check_index)
        right = num_checks + int(qubit_index)
        adjacency[left].append(right)
        adjacency[right].append(left)

    unseen = set(range(len(adjacency)))
    sizes = []
    while unseen:
        start = unseen.pop()
        size = 0
        stack = [start]
        while stack:
            node = stack.pop()
            size += 1
            for neighbor in adjacency[node]:
                if neighbor in unseen:
                    unseen.remove(neighbor)
                    stack.append(neighbor)
        sizes.append(size)
    return sorted(sizes, reverse=True)


def check_css_static_eligibility(
    ell, m, a_terms, b_terms, *, reported_n=None, reported_k=None,
) -> dict:
    """Run cheap, fail-closed challenge gates before BLISS or distance MILP.

    The code is rebuilt, then commutation, check weight, qubit degree, positive
    dimension, and connectedness are recomputed from H_X/H_Z. Optional reported
    n/k values are cross-checked but never trusted as inputs to those checks.
    """
    try:
        ell, m = int(ell), int(m)
        a_terms = [tuple(map(int, term)) for term in a_terms]
        b_terms = [tuple(map(int, term)) for term in b_terms]
        validate_terms(ell, m, a_terms, "A")
        validate_terms(ell, m, b_terms, "B")
        code = build_bb_code(ell, m, a_terms, b_terms)
        hx, hz = _matrices(code)
    except (TypeError, ValueError) as exc:
        return {
            "checked": True,
            "eligible": False,
            "checks": {"candidate_rebuild": False},
            "failures": [f"candidate_rebuild: {exc}"],
        }

    stacked = np.vstack((hx, hz))
    component_sizes = _component_sizes(stacked)
    max_row_weight = int(stacked.sum(axis=1).max(initial=0))
    max_qubit_degree = int(stacked.sum(axis=0).max(initial=0))
    n, k = get_code_params_fast(code)
    checks = {
        "candidate_rebuild": True,
        "positive_dimension": int(k) > 0,
        "css_commutation": int(np.count_nonzero((hx @ hz.T) & 1)) == 0,
        "weight_and_degree_at_most_6": (
            max_row_weight <= 6 and max_qubit_degree <= 6
        ),
        "connected_tanner_graph": len(component_sizes) == 1,
    }
    if reported_n is not None:
        checks["reported_n_matches"] = int(reported_n) == int(n)
    if reported_k is not None:
        checks["reported_k_matches"] = int(reported_k) == int(k)
    failures = [name for name, passed in checks.items() if not passed]
    return {
        "checked": True,
        "eligible": not failures,
        "checks": checks,
        "failures": failures,
        "n": int(n),
        "k": int(k),
        "max_row_weight": max_row_weight,
        "max_qubit_degree": max_qubit_degree,
        "tanner_components": len(component_sizes),
        "tanner_component_sizes": component_sizes,
    }


def canonical_digest(code) -> str:
    """Compact, stable digest of the BLISS canonical edge representation."""
    canonical = canonical_hash(code)
    digest = hashlib.sha256()
    for left, right in canonical:
        digest.update(int(left).to_bytes(4, "little"))
        digest.update(int(right).to_bytes(4, "little"))
    return digest.hexdigest()


def replay_css_isomorphism(code_a, code_b, mapping) -> dict:
    """Replay a BLISS mapping directly on H_X and H_Z."""
    hx_a, hz_a = _matrices(code_a)
    hx_b, hz_b = _matrices(code_b)
    n = hx_a.shape[1]
    rx, rz = hx_a.shape[0], hz_a.shape[0]
    if (
        hx_b.shape != hx_a.shape
        or hz_b.shape != hz_a.shape
        or len(mapping) != n + rx + rz
    ):
        return {"verified": False, "reason": "matrix or mapping shape mismatch"}

    qubits = np.asarray(mapping[:n], dtype=int)
    x_rows = np.asarray(mapping[n:n + rx], dtype=int) - n
    z_rows = np.asarray(mapping[n + rx:], dtype=int) - n - rx
    valid = (
        sorted(qubits.tolist()) == list(range(n))
        and sorted(x_rows.tolist()) == list(range(rx))
        and sorted(z_rows.tolist()) == list(range(rz))
    )
    if not valid:
        return {"verified": False, "reason": "mapping violates color partitions"}

    hx_ok = np.array_equal(hx_a, hx_b[np.ix_(x_rows, qubits)])
    hz_ok = np.array_equal(hz_a, hz_b[np.ix_(z_rows, qubits)])
    return {
        "verified": bool(hx_ok and hz_ok),
        "hx_preserved": bool(hx_ok),
        "hz_preserved": bool(hz_ok),
        "qubit_permutation": qubits.tolist(),
        "x_check_permutation": x_rows.tolist(),
        "z_check_permutation": z_rows.tolist(),
    }


@lru_cache(maxsize=1)
def known_reference_registry():
    """Build canonical forms for the literature registry once per process."""
    registry = []
    for name, ell, m, a_terms, b_terms in KNOWN_CSS_REFERENCES:
        code = build_bb_code(ell, m, a_terms, b_terms)
        n, k = get_code_params_fast(code)
        registry.append({
            "name": name,
            "ell": ell,
            "m": m,
            "A_terms": a_terms,
            "B_terms": b_terms,
            "n": int(n),
            "k": int(k),
            "canonical_hash": canonical_hash(code),
            "canonical_digest": canonical_digest(code),
            "code": code,
        })
    return tuple(registry)


def check_css_structural_novelty(ell, m, a_terms, b_terms) -> dict:
    """Classify a CSS BB candidate against known literature structures."""
    candidate = build_bb_code(ell, m, a_terms, b_terms)
    n, k = get_code_params_fast(candidate)
    candidate_hash = canonical_hash(candidate)
    candidate_digest = canonical_digest(candidate)

    for reference in known_reference_registry():
        if reference["n"] != n or reference["k"] != k:
            continue
        if reference["canonical_hash"] != candidate_hash:
            continue
        mapping = extract_full_vertex_isomorphism(candidate, reference["code"])
        if mapping is None:
            raise RuntimeError("canonical match did not yield an isomorphism")
        replay = replay_css_isomorphism(candidate, reference["code"], mapping)
        if not replay["verified"]:
            raise RuntimeError("BLISS isomorphism failed explicit matrix replay")
        return {
            "checked": True,
            "novel": False,
            "relation": "css_tanner_permutation_equivalent",
            "canonical_digest": candidate_digest,
            "matched_reference": reference["name"],
            "reference_digest": reference["canonical_digest"],
            "explicit_isomorphism": replay,
        }

    return {
        "checked": True,
        "novel": True,
        "relation": None,
        "canonical_digest": candidate_digest,
        "matched_reference": None,
        "reference_digest": None,
        "explicit_isomorphism": None,
    }


def annotate_css_result(result: dict) -> dict:
    """Return a result copy carrying static and structural eligibility audits."""
    annotated = dict(result)
    static = check_css_static_eligibility(
        int(result["ell"]),
        int(result["m"]),
        result["A_terms"],
        result["B_terms"],
        reported_n=result.get("n"),
        reported_k=result.get("k"),
    )
    annotated["static_eligibility"] = static
    if not static["eligible"]:
        annotated["structural_novelty"] = {
            "checked": False,
            "novel": False,
            "relation": "static_ineligible",
            "canonical_digest": None,
            "matched_reference": None,
            "reference_digest": None,
            "explicit_isomorphism": None,
        }
        annotated["structural_rejection"] = "static_ineligible"
        return annotated
    annotated["structural_novelty"] = check_css_structural_novelty(
        int(result["ell"]),
        int(result["m"]),
        result["A_terms"],
        result["B_terms"],
    )
    return annotated


def deduplicate_css_results(results: list[dict]) -> tuple[list[dict], list[dict]]:
    """Reject known references and within-run permutation duplicates.

    Canonical equality is only the index.  Every within-run match is replayed
    against H_X/H_Z before the later candidate is rejected.
    """
    kept: list[dict] = []
    rejected: list[dict] = []
    representatives: dict[tuple[int, int, str], tuple[dict, object]] = {}
    for result in results:
        annotated = annotate_css_result(result)
        static = annotated["static_eligibility"]
        if not static["eligible"]:
            rejected.append(annotated)
            continue
        audit = annotated["structural_novelty"]
        if not audit["novel"]:
            annotated["structural_rejection"] = "known_reference"
            rejected.append(annotated)
            continue

        candidate = build_bb_code(
            int(result["ell"]), int(result["m"]),
            result["A_terms"], result["B_terms"],
        )
        n, k = get_code_params_fast(candidate)
        key = (int(n), int(k), audit["canonical_digest"])
        previous = representatives.get(key)
        if previous is None:
            representatives[key] = (annotated, candidate)
            kept.append(annotated)
            continue

        representative, representative_code = previous
        mapping = extract_full_vertex_isomorphism(candidate, representative_code)
        if mapping is None:
            raise RuntimeError("within-run canonical match lacked isomorphism")
        replay = replay_css_isomorphism(candidate, representative_code, mapping)
        if not replay["verified"]:
            raise RuntimeError("within-run isomorphism failed matrix replay")
        annotated["structural_novelty"] = {
            **audit,
            "novel": False,
            "relation": "within_run_css_tanner_permutation_equivalent",
            "matched_reference": representative.get("label") or (
                f"[[{representative.get('n')},{representative.get('k')},"
                f"{representative.get('d')}]]"
            ),
            "reference_digest": key[2],
            "explicit_isomorphism": replay,
        }
        annotated["structural_rejection"] = "within_run_duplicate"
        rejected.append(annotated)
    return kept, rejected
