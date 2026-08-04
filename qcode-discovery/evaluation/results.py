"""JSON persistence for discovered codes and Pareto front tracking.

Exact discovered codes are stored in a JSON file (default
``results/discovered_codes.json``) and deduplicated by their defining
parameters ``(ell, m, A_terms, B_terms)``.  Heuristic upper bounds and
certified lower bounds are deliberately excluded from this compatibility
store because its historical ``d`` field is consumed as an exact distance.

A Pareto front is maintained in a separate file (default
``results/pareto_front.json``).  A code is Pareto-optimal if no other
code dominates it in the three-dimensional space of ``(k/n, d, 1/n)`` --
i.e., no other code has both higher encoding rate *and* higher distance
at the same or smaller block size.  The front is incrementally updated:
each call merges new results with the existing front on disk, deduplicates,
and recomputes the non-dominated set.

Public API
----------
* :func:`save_code` -- append a single code to the discovered-codes file.
* :func:`load_codes` -- read all codes from the file.
* :func:`update_pareto_front` -- merge new results into the Pareto front.
"""

from __future__ import annotations

import json
import logging
from pathlib import Path
from typing import Any

from evaluation.geometry import normalize_geometry

logger = logging.getLogger(__name__)

RESULTS_DIR = Path(__file__).parent.parent / "results"


def _strict_positive_int(value: Any) -> int | None:
    """Return ``value`` only when it is a strict positive integer."""
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        return None
    return value


def _canonical_exact_result(result: Any) -> dict | None:
    """Return a normalized exact-distance row, or ``None`` fail closed.

    ``results/`` is a positive-discovery compatibility store, not a cache of
    search observations.  A BP/OSD result, feasible MILP incumbent, unresolved
    timeout, or certified lower bound therefore cannot enter it under the
    legacy ``d`` field, which consumers historically interpret as exact.
    """
    if not isinstance(result, dict):
        return None
    if (
        result.get("d_is_exact") is not True
        or result.get("distance_status") != "exact"
        or result.get("d_is_upper_bound") is True
        or result.get("d_represents_certified_lower_bound") is True
        or result.get("search_status") not in {"exact", "terminal_negative"}
    ):
        return None

    n = _strict_positive_int(result.get("n"))
    k = _strict_positive_int(result.get("k"))
    distance = _strict_positive_int(result.get("d"))
    exact_distance = _strict_positive_int(result.get("exact_distance"))
    if (
        n is None
        or k is None
        or distance is None
        or exact_distance != distance
        or k > n
        or distance > n
    ):
        return None

    # A row explicitly carrying only lower-bound semantics must never be
    # upgraded merely because stale exact-looking fields were also present.
    if (
        result.get("distance_lower_bound_proven") is True
        or result.get("distance_lower_bound_status") in {
            "proven",
            "certified",
        }
        or result.get("distance_status") == "certified_lower_bound"
    ):
        return None

    normalized = dict(result)
    exact_fom = k * distance * distance / n
    normalized.update({
        "n": n,
        "k": k,
        "d": distance,
        "d_is_exact": True,
        "distance_status": "exact",
        "exact_distance": distance,
        "exact_fom": exact_fom,
        "fom": exact_fom,
    })
    return normalized


def _load_result_array_for_update(path: Path, label: str) -> list[dict]:
    """Read an existing result array without treating corruption as empty."""
    if not path.exists():
        return []
    try:
        with path.open() as stream:
            value = json.load(stream)
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        raise ValueError(f"{label} is unavailable or invalid: {path}") from exc
    if not isinstance(value, list) or any(
        not isinstance(row, dict) for row in value
    ):
        raise ValueError(f"{label} must be a JSON array of objects: {path}")
    return value


def save_code(result: dict, filepath: Path | str | None = None) -> None:
    """Persist one explicitly exact discovered code.

    Args:
        result: Exact evaluation result from a proof-producing evaluator.
        filepath: Path to JSON file. Defaults to results/discovered_codes.json.

    Raises:
        ValueError: If ``result`` is upper-bound-only, unresolved, lower-bound
            only, malformed, or the existing store is corrupt.
    """
    filepath = Path(filepath or RESULTS_DIR / "discovered_codes.json")
    filepath.parent.mkdir(parents=True, exist_ok=True)

    exact = _canonical_exact_result(result)
    if exact is None:
        raise ValueError(
            "discovered-code persistence requires explicit exact-distance "
            "evidence"
        )
    existing = _load_result_array_for_update(
        filepath,
        "discovered-code store",
    )

    # Rebuild the positive store from exact rows only.  This simultaneously
    # removes legacy BP/incumbent pollution and ensures a later exact result
    # replaces an older upper-bound row with the same defining key.
    exact_by_key: dict[tuple, dict] = {}
    for row in existing:
        normalized = _canonical_exact_result(row)
        if normalized is not None:
            exact_by_key[_code_key(normalized)] = normalized
    exact_by_key[_code_key(exact)] = exact
    cleaned = list(exact_by_key.values())

    with open(filepath, "w") as f:
        json.dump(cleaned, f, indent=2, default=str)


def load_codes(filepath: Path | str | None = None) -> list[dict]:
    """Load discovered codes from JSON file.

    Args:
        filepath: Path to JSON file. Defaults to results/discovered_codes.json.

    Returns:
        List of result dicts.
    """
    filepath = Path(filepath or RESULTS_DIR / "discovered_codes.json")
    if not filepath.exists():
        return []
    try:
        with open(filepath) as f:
            return json.load(f)
    except (json.JSONDecodeError, ValueError) as e:
        logger.warning("Corrupted codes file %s: %s", filepath, e)
        return []


def update_pareto_front(
    results: list[dict], filepath: Path | str | None = None
) -> list[dict]:
    """Update the exact-distance Pareto front of discovered codes.

    Merges exact new results with exact rows from the existing front, cleaning
    legacy BP/OSD upper bounds, MILP incumbents, unresolved rows, and
    lower-bound-only claims before recomputing.
    A code is Pareto-optimal if no other code has both higher k/n AND
    higher d (at the same or smaller n).

    Args:
        results: List of evaluation result dicts.
        filepath: Path to save the front. Defaults to results/pareto_front.json.

    Returns:
        The Pareto-optimal codes.
    """
    filepath = Path(filepath or RESULTS_DIR / "pareto_front.json")
    filepath.parent.mkdir(parents=True, exist_ok=True)

    if not isinstance(results, list):
        raise TypeError("Pareto update results must be a list")
    existing_front = _load_result_array_for_update(
        filepath,
        "Pareto-front store",
    )

    # Later exact evidence replaces an older row with the same definition.
    # Non-exact rows are deliberately absent rather than being assigned a low
    # rank: even one loose upper bound can incorrectly dominate the real front.
    exact_by_key: dict[tuple, dict] = {}
    for row in [*existing_front, *results]:
        normalized = _canonical_exact_result(row)
        if normalized is not None:
            exact_by_key[_code_key(normalized)] = normalized
    valid = list(exact_by_key.values())

    # Sort by FOM descending
    valid.sort(key=lambda r: r["fom"], reverse=True)

    # Compute Pareto front: non-dominated in (k/n, d, 1/n) space
    front = []
    for candidate in valid:
        dominated = False
        n = candidate["n"]
        k = candidate["k"]
        d = candidate["d"]
        rate = k / n if n > 0 else 0

        for existing in front:
            en, ek, ed = existing["n"], existing["k"], existing["d"]
            e_rate = ek / en if en > 0 else 0
            # existing dominates candidate if it's at least as good in all
            # dimensions and strictly better in at least one
            if e_rate >= rate and ed >= d and en <= n:
                if e_rate > rate or ed > d or en < n:
                    dominated = True
                    break

        if not dominated:
            # Remove any codes in front that this candidate dominates
            front = [
                existing for existing in front
                if not (
                    rate >= (existing["k"] / existing["n"]) and
                    d >= existing["d"] and
                    n <= existing["n"] and
                    (rate > (existing["k"] / existing["n"]) or
                     d > existing["d"] or n < existing["n"])
                )
            ]
            front.append(candidate)

    with open(filepath, "w") as f:
        json.dump(front, f, indent=2, default=str)

    return front


def _code_key(result: dict) -> tuple:
    """Unique key for a code based on its defining parameters.

    For PBB (non-CSS) codes, also includes C_terms and D_terms so that
    codes with the same (A, B) base but different perturbations are
    stored separately.
    """
    def canonical_terms(terms):
        return tuple(sorted(tuple(t) for t in (terms or [])))

    ell = result.get("ell")
    m = result.get("m")
    key = (
        ell,
        m,
        canonical_terms(result.get("A_terms", [])),
        canonical_terms(result.get("B_terms", [])),
    )
    geometry = normalize_geometry(ell, m, result.get("geometry"))
    if geometry is not None:
        key += (
            json.dumps(geometry, sort_keys=True, separators=(",", ":")),
        )
    c_terms = result.get("C_terms")
    d_terms = result.get("D_terms")
    if c_terms or d_terms:
        key += (
            canonical_terms(c_terms),
            canonical_terms(d_terms),
        )
    return key
