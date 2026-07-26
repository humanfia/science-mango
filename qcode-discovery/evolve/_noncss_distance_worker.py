"""Standalone distance worker for non-CSS PBB code evaluation.

Extracted to a top-level importable module so that ProcessPoolExecutor
can pickle the function reference regardless of how OpenEvolve loads
the evaluator (dynamic import changes the module path, breaking pickle
for functions defined inside the evaluator).
"""

from __future__ import annotations

import time


def _trust_level(d: int, n: int, *, exact: bool) -> str:
    if exact:
        return "EXACT"
    ratio = d / (n ** 0.5) if n > 0 else 0.0
    if ratio < 1.5:
        return "TRUSTED"
    if ratio < 2.5:
        return "PARTIAL"
    return "UNTRUSTED"


def distance_worker(task: tuple) -> dict:
    """Worker for parallel distance estimation.

    Rebuilds the code in the worker process (QuditCode isn't picklable).

    Pipeline (adaptive based on n):
      1. Hash-based exact low-weight check:
         - n≤216: max_weight=6 (exact d≤6, O(n³), ~5s@n=72, ~2min@n=216)
         - n>216: max_weight=4 (exact d≤4 only, <1s)
         → d≤4: return d, fom=0 (reject)
         → d=5 or d=6 (if max_weight≥5): return exact d, compute real FOM
      2. MILP symplectic (adaptive timeout based on n):
         - n≤108: 15s/logical, 90s total
         - n≤216: 30s/logical, 180s total
         - n>216: 60s/logical, 360s total
         Partial results valid -- min over solved logicals.
      3. BP-OSD fallback only if MILP yields nothing useful
    """
    ell, m, A_terms, B_terms, C_terms, D_terms, num_trials = task

    # Import in worker to handle "spawn" start method (macOS, some Linux)
    from evaluation.pbb_code import build_pbb_code as _build
    from evaluation.pbb_code import get_pbb_params_fast as _params

    code = _build(ell, m, A_terms, B_terms, C_terms, D_terms)
    n, k = _params(code)

    t0 = time.time()
    base_result = {
        "ell": ell, "m": m, "n": n, "k": k,
        "A_terms": A_terms, "B_terms": B_terms,
        "C_terms": C_terms, "D_terms": D_terms,
        "encoding_rate": k / n if n > 0 else 0.0,
    }

    # --- Stage 1: Hash-based exact low-weight check ---
    # Covers full symplectic weight (X, Z, and mixed Y-type logicals).
    # Adaptive max_weight based on n: the O(n³) triple loop for weight-5/6
    # becomes too slow at large n (~10min for n=360). Memory is fine (251GB).
    # n≤216: max_weight=6 (exact d≤6, up to ~2min, ≤19GB)
    # n>216: max_weight=4 (exact d≤4 only, <1s -- MILP handles d≥5)
    from evaluation.distance_bposd_noncss import has_low_weight_logical as _lwl_fast

    if n <= 216:
        max_weight = 6
    else:
        max_weight = 4

    found, d_exact = _lwl_fast(code, max_weight=max_weight)
    if found:
        elapsed = time.time() - t0
        fom = 0.0 if d_exact <= 4 else (k * d_exact * d_exact / n if n > 0 else 0.0)
        return {
            **base_result,
            "d": d_exact, "d_method": f"exact_w{d_exact}",
            "d_is_exact": True, "d_is_upper_bound": False,
            "trust_level": "EXACT",
            "d_over_sqrtn": round(d_exact / (n ** 0.5), 3) if n > 0 else 0.0,
            "fom": round(fom, 2), "time_s": round(elapsed, 1),
        }

    # --- Stage 2: MILP symplectic (for codes beyond hash check range) ---
    # Adaptive MILP timeouts: larger codes need more solver time per logical.
    # At n=360, each ILP has ~720 binary vars -- HiGHS needs 30-120s per solve.
    # Partial results are valid upper bounds (min over solved logicals).
    # early_stop=None iterates every logical, which is required when the goal
    # is to certify exactness rather than reject high-d candidates.
    if n <= 108:
        milp_tpl, milp_total = 15, 90
    elif n <= 216:
        milp_tpl, milp_total = 30, 180
    else:
        milp_tpl, milp_total = 60, 360

    try:
        from evaluation.distance_milp import compute_distance_milp_symplectic as _milp

        d_milp, details = _milp(
            code,
            timeout_per_logical=milp_tpl,
            total_timeout=milp_total,
            early_stop=None,
            verbose=False,
        )
        milp_exact = details.get("exact", False)
        milp_worked = d_milp < n  # True only when a real solution was found
    except Exception:
        d_milp = n
        milp_exact = False
        milp_worked = False

    # --- Stage 3: BP-OSD fallback ---
    # Skip if MILP already gave an exact answer (saves ~2-5s).
    if milp_exact:
        d_best = d_milp
        elapsed = time.time() - t0
        return {
            **base_result,
            "d": d_best, "d_method": "milp_exact",
            "d_milp": d_milp, "d_bposd": None,
            "milp_exact": True,
            "d_is_exact": True, "d_is_upper_bound": False,
            "trust_level": "EXACT",
            "d_over_sqrtn": round(d_best / (n ** 0.5), 3) if n > 0 else 0.0,
            "fom": round(k * d_best * d_best / n if n > 0 else 0.0, 2),
            "time_s": round(elapsed, 1),
        }

    from evaluation.distance_bposd_noncss import estimate_distance_noncss as _est

    d_bp1 = _est(code, num_trials=num_trials, seed=42)
    d_bp2 = _est(code, num_trials=max(num_trials // 2, 100), seed=137)
    d_bp = min(d_bp1, d_bp2)

    # Take best across all methods (both are valid upper bounds)
    d_best = min(d_milp, d_bp) if milp_worked else d_bp
    elapsed = time.time() - t0

    fom = k * d_best * d_best / n if d_best > 0 and n > 0 else 0.0

    method = "milp+bposd" if milp_worked else "bposd"
    trust_level = _trust_level(d_best, n, exact=False)

    return {
        **base_result,
        "d": d_best, "d_method": method,
        "d_milp": d_milp if milp_worked else None,
        "d_bposd": d_bp,
        "milp_exact": False,
        "d_is_exact": False,
        "d_is_upper_bound": True,
        "trust_level": trust_level,
        "d_over_sqrtn": round(d_best / (n ** 0.5), 3) if n > 0 else 0.0,
        "fom": round(fom, 2), "time_s": round(elapsed, 1),
    }
