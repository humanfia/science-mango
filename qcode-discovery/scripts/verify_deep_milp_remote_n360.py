#!/usr/bin/env python3
"""Self-contained deep MILP verification for 30 (30,6) n=360 PBB codes.

Copy-paste this entire file onto a remote server and run:

    pip install numpy scipy sympy qldpc
    nohup python verify_deep_milp_remote_n360.py > verify_n360.log 2>&1 &

Output: campaign7_deep_milp_n360.jsonl (same format as campaign7_deep_milp.jsonl)
Merge:  cat campaign7_deep_milp_n360.jsonl >> campaign7_deep_milp.jsonl

Requirements: numpy, scipy, sympy, qldpc
Hardware: 60+ cores recommended, ~45GB RAM for n=360 codes
"""

from __future__ import annotations

import json
import os
import sys
import time
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed
from datetime import datetime, timezone

import numpy as np
import sympy
from sympy.abc import x, y
from scipy.optimize import milp, LinearConstraint, Bounds
from qldpc import codes
from qldpc.codes import QuditCode

# ============================================================================
# Configuration
# ============================================================================
WORKERS = int(os.environ.get("WORKERS", "60"))
TIMEOUT_PER_LOGICAL = 7200  # seconds
OUTPUT_FILE = "campaign7_deep_milp_n360.jsonl"

# ============================================================================
# 30 (30,6) deep-MILP worklist rows -- selected from then-TRUSTED publication rows
# ============================================================================
CODES_DATA = [
    {"A": [[4,1],[21,1],[8,4]], "B": [[0,0],[25,1],[8,5]], "C": [[4,5],[21,2]], "D": [[4,4],[21,1],[21,4]], "ell": 30, "m": 6, "n": 360, "k": 10, "d": 24, "fom": 16.0},
    {"A": [[13,4],[22,3],[22,2]], "B": [[0,0],[13,1],[5,2]], "C": [[13,1],[22,1]], "D": [[13,3],[22,3]], "ell": 30, "m": 6, "n": 360, "k": 12, "d": 20, "fom": 13.3333},
    {"A": [[1,2],[4,3],[4,4]], "B": [[0,0],[1,5],[5,4]], "C": [[1,4],[4,0]], "D": [[1,2],[4,4]], "ell": 30, "m": 6, "n": 360, "k": 10, "d": 20, "fom": 11.1111},
    {"A": [[29,2],[26,3],[26,4]], "B": [[0,0],[29,5],[25,4]], "C": [[26,1],[29,3]], "D": [[26,5],[29,1]], "ell": 30, "m": 6, "n": 360, "k": 10, "d": 20, "fom": 11.1111},
    {"A": [[29,2],[26,3],[26,4]], "B": [[0,0],[29,5],[25,4]], "C": [[26,5],[29,5]], "D": [[26,1],[29,4]], "ell": 30, "m": 6, "n": 360, "k": 10, "d": 20, "fom": 11.1111},
    {"A": [[11,2],[14,3],[14,4]], "B": [[0,0],[11,5],[25,4]], "C": [[11,4],[14,0]], "D": [[14,3]], "ell": 30, "m": 6, "n": 360, "k": 10, "d": 20, "fom": 11.1111},
    {"A": [[11,2],[14,3],[14,4]], "B": [[0,0],[11,5],[25,4]], "C": [[11,5]], "D": [[0,4],[25,2]], "ell": 30, "m": 6, "n": 360, "k": 10, "d": 20, "fom": 11.1111},
    {"A": [[7,2],[28,3],[28,4]], "B": [[0,0],[7,5],[5,4]], "C": [[0,5],[5,5]], "D": [[0,3],[5,3]], "ell": 30, "m": 6, "n": 360, "k": 10, "d": 20, "fom": 11.1111},
    {"A": [[14,1],[21,4],[28,4]], "B": [[0,0],[5,1],[28,5]], "C": [[14,5],[21,2]], "D": [[14,4],[21,4]], "ell": 30, "m": 6, "n": 360, "k": 10, "d": 20, "fom": 11.1111},
    {"A": [[26,1],[9,1],[22,4]], "B": [[0,0],[5,1],[22,5]], "C": [[9,5],[26,2]], "D": [[9,4],[22,4]], "ell": 30, "m": 6, "n": 360, "k": 10, "d": 18, "fom": 9.0},
    {"A": [[14,1],[21,1],[28,4]], "B": [[0,0],[5,1],[28,5]], "C": [[14,5],[21,2]], "D": [[21,4],[28,1]], "ell": 30, "m": 6, "n": 360, "k": 10, "d": 18, "fom": 9.0},
    {"A": [[21,0],[0,1],[0,2]], "B": [[0,3],[14,0],[28,0]], "C": [[21,0],[21,3]], "D": [[0,0],[0,3]], "ell": 30, "m": 6, "n": 360, "k": 8, "d": 20, "fom": 8.8889},
    {"A": [[28,1],[27,4],[26,4]], "B": [[0,0],[25,1],[26,5]], "C": [[27,1],[28,0]], "D": [[27,0],[28,5]], "ell": 30, "m": 6, "n": 360, "k": 12, "d": 16, "fom": 8.5333},
    {"A": [[3,2],[25,3],[25,4]], "B": [[0,0],[3,5],[28,4]], "C": [[3,5],[25,5]], "D": [[3,3],[25,3]], "ell": 30, "m": 6, "n": 360, "k": 4, "d": 26, "fom": 7.5111},
    {"A": [[0,1],[3,2],[14,1]], "B": [[3,1],[14,0],[14,1]], "C": [[0,0],[14,1]], "D": [[0,1],[14,2]], "ell": 30, "m": 6, "n": 360, "k": 4, "d": 26, "fom": 7.5111},
    {"A": [[0,1],[27,2],[16,1]], "B": [[27,1],[16,0],[16,1]], "C": [[0,2],[16,5]], "D": [[0,3],[16,0]], "ell": 30, "m": 6, "n": 360, "k": 4, "d": 26, "fom": 7.5111},
    {"A": [[8,2],[10,3],[10,4]], "B": [[0,0],[8,5],[18,4]], "C": [[8,5],[10,5]], "D": [[8,3],[10,3]], "ell": 30, "m": 6, "n": 360, "k": 8, "d": 18, "fom": 7.2},
    {"A": [[8,2],[12,3],[12,4]], "B": [[0,0],[8,5],[20,4]], "C": [[8,5],[12,5]], "D": [[8,3],[12,3]], "ell": 30, "m": 6, "n": 360, "k": 8, "d": 18, "fom": 7.2},
    {"A": [[7,2],[19,3],[19,4]], "B": [[0,0],[7,5],[26,4]], "C": [[7,5],[19,5]], "D": [[7,3],[19,3]], "ell": 30, "m": 6, "n": 360, "k": 8, "d": 18, "fom": 7.2},
    {"A": [[26,1],[9,1],[22,4]], "B": [[0,0],[5,1],[22,5]], "C": [[9,3],[26,4]], "D": [[9,3],[22,2]], "ell": 30, "m": 6, "n": 360, "k": 10, "d": 16, "fom": 7.1111},
    {"A": [[22,1],[3,4],[14,4]], "B": [[0,0],[25,1],[14,5]], "C": [[3,3],[22,4]], "D": [[3,2],[22,3]], "ell": 30, "m": 6, "n": 360, "k": 10, "d": 16, "fom": 7.1111},
    {"A": [[26,1],[9,4],[22,4]], "B": [[0,0],[5,1],[22,5]], "C": [[9,5],[26,2]], "D": [[9,4],[26,1]], "ell": 30, "m": 6, "n": 360, "k": 10, "d": 16, "fom": 7.1111},
    {"A": [[26,1],[9,4],[22,4]], "B": [[0,0],[5,1],[22,5]], "C": [[9,5],[26,2]], "D": [[22,4]], "ell": 30, "m": 6, "n": 360, "k": 10, "d": 16, "fom": 7.1111},
    {"A": [[4,2],[22,3],[22,4]], "B": [[0,0],[4,5],[26,4]], "C": [[4,5],[22,5]], "D": [[4,3],[22,3]], "ell": 30, "m": 6, "n": 360, "k": 16, "d": 12, "fom": 6.4},
    {"A": [[3,0],[0,2],[0,4]], "B": [[0,3],[2,0],[4,0]], "C": [[18,0]], "D": [[15,3]], "ell": 30, "m": 6, "n": 360, "k": 8, "d": 16, "fom": 5.6889},
    {"A": [[27,0],[0,1],[0,2]], "B": [[0,3],[19,0],[8,0]], "C": [[0,0],[27,0]], "D": [[0,4],[27,4]], "ell": 30, "m": 6, "n": 360, "k": 12, "d": 12, "fom": 4.8},
    {"A": [[3,2],[11,3],[11,4]], "B": [[0,0],[3,5],[14,4]], "C": [[3,5],[11,5]], "D": [[3,3],[11,3]], "ell": 30, "m": 6, "n": 360, "k": 4, "d": 20, "fom": 4.4444},
    {"A": [[1,2],[20,3],[20,4]], "B": [[0,0],[1,5],[21,4]], "C": [[1,5],[20,5]], "D": [[1,3],[20,3]], "ell": 30, "m": 6, "n": 360, "k": 4, "d": 16, "fom": 2.8444},
    {"A": [[4,2],[19,3],[19,4]], "B": [[0,0],[4,5],[23,4]], "C": [[4,5],[19,5]], "D": [[4,3],[19,3]], "ell": 30, "m": 6, "n": 360, "k": 12, "d": 6, "fom": 1.2},
    {"A": [[1,2],[15,3],[15,4]], "B": [[0,0],[1,5],[16,4]], "C": [[1,5],[15,5]], "D": [[1,3],[15,3]], "ell": 30, "m": 6, "n": 360, "k": 4, "d": 10, "fom": 1.1111},
]

# ============================================================================
# Inlined: terms_to_poly (from evaluation/bb_code.py)
# ============================================================================
def terms_to_poly(terms):
    """Convert exponent pairs to a sympy expression."""
    return sum(x ** xe * y ** ye for xe, ye in terms)


# ============================================================================
# Inlined: PBB code construction (from evaluation/pbb_code.py)
# ============================================================================
def _terms_to_sympy_poly(terms):
    expr = sum(x ** xe * y ** ye for xe, ye in terms)
    return sympy.Poly(expr, x, y)


def _poly_to_matrix(bb_code, terms):
    poly = _terms_to_sympy_poly(terms)
    mat = np.array(bb_code.eval(poly).lift().T, dtype=int) % 2
    return mat


def check_commutativity(A, B, C, D):
    M = (A @ C.T + B @ D.T) % 2
    return np.array_equal(M, M.T)


def build_pbb_code(ell, m, A_terms, B_terms, C_terms, D_terms):
    """Construct a non-CSS PBB qubit stabilizer code (qldpc ``QuditCode``)."""
    poly_a = terms_to_poly(A_terms)
    poly_b = terms_to_poly(B_terms)
    bb = codes.BBCode({x: ell, y: m}, poly_a, poly_b)

    mat_A = _poly_to_matrix(bb, A_terms)
    mat_B = _poly_to_matrix(bb, B_terms)
    mat_C = _poly_to_matrix(bb, C_terms)
    mat_D = _poly_to_matrix(bb, D_terms)

    if not check_commutativity(mat_A, mat_B, mat_C, mat_D):
        raise ValueError("Commutativity violated")

    dim = ell * m
    2 * dim
    zero = np.zeros((dim, dim), dtype=int)

    block1_x = np.hstack([mat_A, mat_B])
    block1_z = np.hstack([mat_C, mat_D])
    block2_x = np.hstack([zero, zero])
    block2_z = np.hstack([mat_B.T % 2, mat_A.T % 2])

    top = np.hstack([block1_x, block1_z])
    bottom = np.hstack([block2_x, block2_z])
    symplectic = np.vstack([top, bottom]) % 2

    return QuditCode(symplectic)


# ============================================================================
# Inlined: GF(2) logical operators (from evaluation/pbb_code.py)
# ============================================================================
def _gf2_rref(mat):
    M = mat.copy() % 2
    rows, cols = M.shape
    pivots = []
    r = 0
    for c in range(cols):
        found = None
        for i in range(r, rows):
            if M[i, c]:
                found = i
                break
        if found is None:
            continue
        M[[r, found]] = M[[found, r]]
        pivots.append(c)
        for i in range(rows):
            if i != r and M[i, c]:
                M[i] = (M[i] + M[r]) % 2
        r += 1
    return M, pivots


def _gf2_nullspace(mat):
    M, pivots = _gf2_rref(mat)
    rows, cols = M.shape
    free_cols = [c for c in range(cols) if c not in pivots]
    if not free_cols:
        return np.zeros((0, cols), dtype=int)
    null_vecs = []
    for fc in free_cols:
        vec = np.zeros(cols, dtype=int)
        vec[fc] = 1
        for i, pc in enumerate(pivots):
            vec[pc] = M[i, fc]
        null_vecs.append(vec)
    return np.array(null_vecs, dtype=int) % 2


def get_symplectic_logicals(code):
    stab = np.array(code.matrix, dtype=int) % 2
    num_stabs, two_n = stab.shape
    n = two_n // 2
    k = code.dimension
    if k == 0:
        return np.zeros((0, two_n), dtype=int)

    omega_stab = np.hstack([stab[:, n:], stab[:, :n]])
    complement = _gf2_nullspace(omega_stab)
    if complement.shape[0] == 0:
        return np.zeros((0, two_n), dtype=int)

    stab_rref, stab_pivots = _gf2_rref(stab)
    stab_rank = len(stab_pivots)
    working = stab_rref[:stab_rank].copy()
    current_rank = stab_rank
    logicals = []

    for row in complement:
        aug = np.vstack([working, row.reshape(1, -1)]) % 2
        aug_rref, aug_pivots = _gf2_rref(aug)
        if len(aug_pivots) > current_rank:
            logicals.append(row)
            working = aug_rref[:len(aug_pivots)]
            current_rank = len(aug_pivots)
            if len(logicals) >= 2 * k:
                break

    if not logicals:
        return np.zeros((0, two_n), dtype=int)
    return np.array(logicals, dtype=int) % 2


# ============================================================================
# Inlined: MILP solver (from evaluation/distance_milp.py)
# ============================================================================
def ilp_min_weight_symplectic(stabilizer_matrix, logical_op, timeout=30):
    """Find minimum symplectic-weight Pauli in the coset logical_op + stabilizers."""
    num_stabs, two_n = stabilizer_matrix.shape
    n = two_n // 2

    num_vars = 2 * n + n + num_stabs + 1
    idx_x = slice(0, n)
    idx_z = slice(n, 2 * n)
    idx_w = slice(2 * n, 3 * n)
    idx_t = 3 * n + num_stabs

    c = np.zeros(num_vars)
    c[idx_w] = 1.0

    rows = []
    row_lb = []
    row_ub = []

    for j in range(n):
        row = np.zeros(num_vars)
        row[2 * n + j] = 1
        row[j] = -1
        rows.append(row)
        row_lb.append(0)
        row_ub.append(np.inf)

    for j in range(n):
        row = np.zeros(num_vars)
        row[2 * n + j] = 1
        row[n + j] = -1
        rows.append(row)
        row_lb.append(0)
        row_ub.append(np.inf)

    for r in range(num_stabs):
        row = np.zeros(num_vars)
        s_x = stabilizer_matrix[r, :n]
        s_z = stabilizer_matrix[r, n:]
        row[idx_z] = s_x
        row[idx_x] = s_z
        row[3 * n + r] = -2
        rows.append(row)
        row_lb.append(0)
        row_ub.append(0)

    row = np.zeros(num_vars)
    L_x = logical_op[:n]
    L_z = logical_op[n:]
    row[idx_z] = L_x
    row[idx_x] = L_z
    row[idx_t] = -2
    rows.append(row)
    row_lb.append(1)
    row_ub.append(1)

    A_mat = np.array(rows)
    constraints = LinearConstraint(A_mat, row_lb, row_ub)

    lb = np.zeros(num_vars)
    ub = np.ones(num_vars)
    for r in range(num_stabs):
        ub[3 * n + r] = np.ceil(np.sum(stabilizer_matrix[r]) / 2)
    ub[idx_t] = np.ceil(np.sum(logical_op) / 2)

    bounds = Bounds(lb, ub)
    integrality = np.ones(num_vars)

    opts = {"presolve": True}
    if 0 < timeout < 1e9:
        opts["time_limit"] = timeout

    result = milp(
        c=c,
        constraints=constraints,
        integrality=integrality,
        bounds=bounds,
        options=opts,
    )

    if result.x is not None:
        w = int(round(result.fun))
        return w, result.success
    return None, False


# ============================================================================
# Worker function (runs in subprocess)
# ============================================================================
def solve_single_logical(args):
    stab_matrix, logical_vec, timeout, code_idx, logical_idx = args
    t0 = time.monotonic()
    try:
        w, optimal = ilp_min_weight_symplectic(stab_matrix, logical_vec, timeout=timeout)
        elapsed = time.monotonic() - t0
        return {
            "code_idx": code_idx,
            "logical_idx": logical_idx,
            "weight": w,
            "optimal": optimal,
            "time_s": round(elapsed, 1),
            "error": None,
        }
    except Exception as e:
        elapsed = time.monotonic() - t0
        return {
            "code_idx": code_idx,
            "logical_idx": logical_idx,
            "weight": None,
            "optimal": False,
            "time_s": round(elapsed, 1),
            "error": str(e),
        }


# ============================================================================
# Main
# ============================================================================
def main():
    print("=" * 70)
    print("Deep MILP Verification -- (30,6) n=360 PBB codes")
    print(f"Server: {os.uname().nodename}")
    print(f"Cores:  {os.cpu_count()}")
    print(f"Workers: {WORKERS}")
    print(f"Timeout/logical: {TIMEOUT_PER_LOGICAL}s")
    print(f"Output: {OUTPUT_FILE}")
    print(f"Started: {datetime.now()}")
    print("=" * 70)

    # Resume support: skip already-completed codes
    done_keys = set()
    if os.path.exists(OUTPUT_FILE):
        with open(OUTPUT_FILE) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                r = json.loads(line)
                key = (str(r["A_terms"]), str(r["B_terms"]),
                       str(r["C_terms"]), str(r["D_terms"]), r["ell"], r["m"])
                done_keys.add(key)
        print(f"Resuming: {len(done_keys)} already verified")

    # Build codes and prepare tasks
    todo = []
    for c in CODES_DATA:
        key = (str(c["A"]), str(c["B"]), str(c["C"]), str(c["D"]), c["ell"], c["m"])
        if key not in done_keys:
            todo.append(c)

    print(f"\nCodes to verify: {len(todo)} (of {len(CODES_DATA)} total)")
    print(f"Building codes and extracting logicals...\n")

    all_tasks = []
    code_metadata = []
    code_results = defaultdict(dict)

    for ci, c in enumerate(todo):
        ell, m = c["ell"], c["m"]
        A = [tuple(t) for t in c["A"]]
        B = [tuple(t) for t in c["B"]]
        C = [tuple(t) for t in c["C"]]
        D = [tuple(t) for t in c["D"]]

        code = build_pbb_code(ell, m, A, B, C, D)
        n = code.num_qudits
        k = code.dimension

        stab_matrix = np.array(code.matrix, dtype=int) % 2
        logicals = get_symplectic_logicals(code)
        num_logicals = logicals.shape[0]

        code_metadata.append({
            "entry": c, "n": n, "k": k,
            "num_logicals": num_logicals, "code_idx": ci,
        })

        for li in range(num_logicals):
            all_tasks.append((stab_matrix, logicals[li], TIMEOUT_PER_LOGICAL, ci, li))

        print(f"  Code {ci+1}: [[{n},{k},{c['d']}]] FOM={c['fom']:.2f} -- {num_logicals} logicals")

    total_logicals = len(all_tasks)
    print(f"\nTotal logicals to solve: {total_logicals}")
    print(f"Submitting all to pool with {WORKERS} workers...\n")

    header = (f"{'#':>3} {'lattice':>8} {'n':>4} {'k':>3} {'old_d':>5} "
              f"{'new_d':>5} {'FOM':>8} {'solved':>8} {'status':>8} {'time':>8}")
    print(header)
    print("-" * 75)
    sys.stdout.flush()

    code_start_times = {}
    codes_done = set()
    pushed_to_exact = 0
    improved = 0
    output_order = 0
    t_global = time.monotonic()

    with ProcessPoolExecutor(max_workers=WORKERS) as pool:
        futures = {}
        for task in all_tasks:
            ci = task[3]
            if ci not in code_start_times:
                code_start_times[ci] = time.monotonic()
            f = pool.submit(solve_single_logical, task)
            futures[f] = (task[3], task[4])

        for future in as_completed(futures):
            ci, li = futures[future]
            try:
                result = future.result()
            except Exception as e:
                result = {
                    "code_idx": ci, "logical_idx": li,
                    "weight": None, "optimal": False,
                    "time_s": 0, "error": str(e),
                }

            code_results[ci][li] = result

            meta = code_metadata[ci]
            if ci not in codes_done and len(code_results[ci]) == meta["num_logicals"]:
                codes_done.add(ci)
                elapsed = time.monotonic() - code_start_times[ci]

                c = meta["entry"]
                n = meta["n"]
                k = meta["k"]
                old_d = c["d"]
                num_log = meta["num_logicals"]

                d_best = n
                all_optimal = True
                logicals_optimal = 0
                logicals_incumbent = 0
                logicals_failed = 0
                any_found = False
                per_logical_detail = []

                for idx in range(num_log):
                    r = code_results[ci].get(idx)
                    if r is None:
                        logicals_failed += 1
                        all_optimal = False
                        per_logical_detail.append({"w": None, "opt": False})
                        continue
                    w = r["weight"]
                    opt = r["optimal"]
                    per_logical_detail.append({"w": w, "opt": opt, "t": r["time_s"]})
                    if w is not None:
                        d_best = min(d_best, w)
                        any_found = True
                        if opt:
                            logicals_optimal += 1
                        else:
                            logicals_incumbent += 1
                            all_optimal = False
                    else:
                        logicals_failed += 1
                        all_optimal = False

                exact = all_optimal and any_found
                new_d = d_best if any_found else old_d
                new_fom = round(k * new_d * new_d / n, 4) if n > 0 and k > 0 else 0

                if exact:
                    pushed_to_exact += 1
                if new_d != old_d:
                    improved += 1

                status = "EXACT" if exact else "partial"
                marker = " ***" if exact else (" !" if new_d != old_d else "")
                solved_str = f"{logicals_optimal}/{num_log}"
                lat_str = f"({c['ell']},{c['m']})"

                output_order += 1
                print(f"{output_order:3d} {lat_str:>8} {n:4d} {k:3d} {old_d:5d} "
                      f"{new_d:5d} {new_fom:8.2f} {solved_str:>8} {status:>8} "
                      f"{elapsed:7.0f}s{marker}")
                sys.stdout.flush()

                # Write result -- same format as campaign7_deep_milp.jsonl
                deep_method = "deep_milp" if new_d < old_d or exact else c.get("d_method", "deep_milp")
                out_record = {
                    "ell": c["ell"],
                    "m": c["m"],
                    "n": n,
                    "k": k,
                    "A_terms": c["A"],
                    "B_terms": c["B"],
                    "C_terms": c["C"],
                    "D_terms": c["D"],
                    "d": new_d,
                    "d_method": deep_method,
                    "d_is_exact": exact,
                    "d_is_upper_bound": not exact,
                    "fom": new_fom,
                    "d_deep_milp": new_d,
                    "d_original": old_d,
                    "fom_deep": new_fom,
                    "milp_exact_deep": exact,
                    "per_logical": per_logical_detail,
                    "logicals_optimal": logicals_optimal,
                    "logicals_incumbent": logicals_incumbent,
                    "logicals_failed": logicals_failed,
                    "total_logicals": num_log,
                    "deep_milp_time_s": round(elapsed, 1),
                    "timeout_per_logical": TIMEOUT_PER_LOGICAL,
                    "trust_level": "EXACT" if exact else c.get("trust_level", "TRUSTED"),
                    "publication_quality": exact,
                    "verified_at": datetime.now(timezone.utc).isoformat(),
                }
                with open(OUTPUT_FILE, "a") as f:
                    f.write(json.dumps(out_record) + "\n")

    total_elapsed = time.monotonic() - t_global
    print()
    print(f"Done in {total_elapsed/3600:.1f} hours ({total_elapsed/60:.0f} min).")
    print(f"  Pushed to EXACT: {pushed_to_exact}")
    print(f"  Distance changed: {improved}")
    print(f"  Results in {OUTPUT_FILE}")


if __name__ == "__main__":
    main()
