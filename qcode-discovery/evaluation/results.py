"""JSON persistence for discovered codes and Pareto front tracking.

Discovered codes are appended to a JSON file (default
``results/discovered_codes.json``) and deduplicated by their defining
parameters ``(ell, m, A_terms, B_terms)``.

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

logger = logging.getLogger(__name__)

RESULTS_DIR = Path(__file__).parent.parent / "results"


def save_code(result: dict, filepath: Path | str | None = None) -> None:
    """Append a discovered code to the results JSON file.

    Args:
        result: Evaluation result dict from evaluate_candidate.
        filepath: Path to JSON file. Defaults to results/discovered_codes.json.
    """
    filepath = Path(filepath or RESULTS_DIR / "discovered_codes.json")
    filepath.parent.mkdir(parents=True, exist_ok=True)

    existing = load_codes(filepath)

    # Avoid duplicates by (ell, m, A_terms, B_terms) key
    key = _code_key(result)
    existing_keys = {_code_key(r) for r in existing}
    if key not in existing_keys:
        existing.append(result)

    with open(filepath, "w") as f:
        json.dump(existing, f, indent=2, default=str)


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
    """Update the Pareto front of discovered codes.

    Merges new results with the existing front on disk, then recomputes.
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

    # Merge with existing front on disk
    existing_front = []
    if filepath.exists():
        try:
            with open(filepath) as f:
                existing_front = json.load(f)
        except (json.JSONDecodeError, ValueError) as e:
            logger.warning("Corrupted pareto front file %s: %s", filepath, e)

    # Deduplicate by code key before computing front
    all_results = existing_front + results
    seen_keys = set()
    deduped = []
    for r in all_results:
        key = _code_key(r)
        if key not in seen_keys:
            seen_keys.add(key)
            deduped.append(r)

    # Filter to valid codes only
    valid = [r for r in deduped if r.get("k", 0) > 0 and r.get("d", 0) > 0]

    # Sort by FOM descending
    valid.sort(key=lambda r: r.get("fom", 0), reverse=True)

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

    key = (
        result.get("ell"),
        result.get("m"),
        canonical_terms(result.get("A_terms", [])),
        canonical_terms(result.get("B_terms", [])),
    )
    c_terms = result.get("C_terms")
    d_terms = result.get("D_terms")
    if c_terms or d_terms:
        key += (
            canonical_terms(c_terms),
            canonical_terms(d_terms),
        )
    return key
