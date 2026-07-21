"""Extract and verify explicit logical operator witnesses for top codes.

For each code, runs BP-OSD and captures the actual low-weight operator.
Then verifies it algebraically:
  1. Commutes with all stabilizers (zero syndrome)
  2. Non-trivial logical action (anticommutes with ≥1 logical)
  3. Reports the explicit qubit support and Pauli type

This turns stochastic distance claims into verifiable proofs of d ≤ w.
"""

import sys
import time
import numpy as np
sys.path.insert(0, "/root/qcode-discovery")

from ldpc import BpOsdDecoder
from evaluation.pbb_code import (
    build_pbb_code, get_pbb_params_fast,
    get_symplectic_logicals, symplectic_weight,
)
from evaluation.distance_bposd_noncss import (
    _compute_achievable_basis, _safe_for_bposd,
)


def symplectic_inner_product(a: np.ndarray, b: np.ndarray) -> int:
    """Symplectic inner product ⟨a, b⟩ = a_x·b_z + a_z·b_x mod 2."""
    n = len(a) // 2
    return int((np.dot(a[:n], b[n:]) + np.dot(a[n:], b[:n])) % 2)


def verify_logical(operator: np.ndarray, stab: np.ndarray,
                   logicals: np.ndarray) -> dict:
    """Verify that operator is a valid non-trivial logical.

    Returns dict with verification results.
    """
    n = len(operator) // 2
    sw = symplectic_weight(operator)

    # Check 1: commutes with all stabilizers (syndrome = 0)
    syndromes = []
    for i in range(stab.shape[0]):
        s = symplectic_inner_product(operator, stab[i])
        syndromes.append(s)
    commutes_with_all_stabs = all(s == 0 for s in syndromes)
    num_anticommuting_stabs = sum(syndromes)

    # Check 2: non-trivial logical action
    logical_actions = []
    for i in range(logicals.shape[0]):
        a = symplectic_inner_product(operator, logicals[i])
        logical_actions.append(a)
    has_nontrivial_action = any(a == 1 for a in logical_actions)
    num_anticommuting_logicals = sum(logical_actions)

    # Check 3: describe the Pauli support
    x_part = operator[:n]
    z_part = operator[n:]
    x_only = []  # X on qubit i
    z_only = []  # Z on qubit i
    y_sites = []  # Y on qubit i (both X and Z)
    for i in range(n):
        if x_part[i] and z_part[i]:
            y_sites.append(i)
        elif x_part[i]:
            x_only.append(i)
        elif z_part[i]:
            z_only.append(i)

    return {
        "symplectic_weight": sw,
        "commutes_with_all_stabs": commutes_with_all_stabs,
        "num_anticommuting_stabs": num_anticommuting_stabs,
        "has_nontrivial_action": has_nontrivial_action,
        "num_anticommuting_logicals": num_anticommuting_logicals,
        "x_sites": x_only,
        "z_sites": z_only,
        "y_sites": y_sites,
        "pauli_string_compact": (
            "".join(f"X{i}" for i in x_only) +
            "".join(f"Y{i}" for i in y_sites) +
            "".join(f"Z{i}" for i in z_only)
        ),
    }


def extract_witness_symplectic(code, num_trials=50000, seeds=None):
    """Extract best witness using full symplectic BP-OSD.

    Returns (best_operator, best_weight, all_found_weights).
    """
    if seeds is None:
        seeds = [42, 137, 2024, 7777, 31415, 99991, 54321, 11111, 77777, 33333]

    n = code.num_qudits
    stab = np.array(code.matrix, dtype=int) % 2
    logicals = get_symplectic_logicals(code)

    effective_H = np.vstack([stab, logicals]).astype(np.uint8)
    num_stabs = stab.shape[0]
    num_logicals = logicals.shape[0]

    if not _safe_for_bposd(effective_H):
        print("    WARNING: effective_H not safe for BP-OSD")
        return None, n, []

    best_operator = None
    best_weight = n
    all_found = []

    for seed in seeds:
        rng = np.random.default_rng(seed)
        decoder = BpOsdDecoder(
            effective_H,
            error_rate=0.05,
            bp_method="product_sum",
            osd_method="osd_0",
            osd_order=0,
            max_iter=100,
        )

        t0 = time.time()
        found_this_seed = []

        for trial in range(num_trials):
            logical_bits = np.zeros(num_logicals, dtype=np.uint8)
            while not logical_bits.any():
                logical_bits = rng.integers(0, 2, size=num_logicals, dtype=np.uint8)

            syndrome = np.zeros(num_stabs + num_logicals, dtype=np.uint8)
            syndrome[:num_stabs] = 0
            syndrome[num_stabs:] = logical_bits

            result = decoder.decode(syndrome)
            actual = effective_H @ result % 2
            if np.array_equal(actual, syndrome):
                sw = symplectic_weight(result)
                if sw > 0:
                    found_this_seed.append(sw)
                    if sw < best_weight:
                        best_weight = sw
                        best_operator = result.copy()

        elapsed = time.time() - t0
        if found_this_seed:
            print(f"    seed={seed:5d}: best_sw={min(found_this_seed):2d}  "
                  f"found={len(found_this_seed)} operators  ({elapsed:.1f}s)")
        else:
            print(f"    seed={seed:5d}: no valid operators  ({elapsed:.1f}s)")
        all_found.extend(found_this_seed)
        sys.stdout.flush()

    return best_operator, best_weight, all_found


def extract_witness_mixed_channels(code, num_trials=50000, seeds=None):
    """Extract best witness using mixed-channel BP-OSD with symplectic lifting.

    For each mixed channel mask, BP-OSD finds a channel-projected operator.
    We lift it to a full symplectic operator and compute symplectic weight.
    """
    if seeds is None:
        seeds = [42, 137, 2024, 7777, 31415, 99991, 54321, 11111, 77777, 33333]

    n = code.num_qudits
    stab = np.array(code.matrix, dtype=int) % 2
    logicals = get_symplectic_logicals(code)

    S_x = stab[:, :n]
    S_z = stab[:, n:]
    L_x = logicals[:, :n]
    L_z = logicals[:, n:]

    best_operator = None
    best_weight = n
    all_found = []

    for seed in seeds:
        rng = np.random.default_rng(seed)
        t0 = time.time()
        found_this_seed = []

        # Also do pure X, Z, Y channels
        channels = []
        # X channel: errors are pure X, detected by Z-stabilizers
        channels.append(("X", S_z, L_z, np.zeros(n, dtype=np.uint8)))
        # Z channel: errors are pure Z, detected by X-stabilizers
        channels.append(("Z", S_x, L_x, np.ones(n, dtype=np.uint8)))
        # Y channel
        S_y = (S_x + S_z) % 2
        L_y = (L_x + L_z) % 2
        # Y mask is special -- both X and Z on every qubit
        channels.append(("Y", S_y, L_y, "Y"))

        # Mixed channels: ~100 random masks
        num_mixed = 100
        for i in range(num_mixed):
            mask = rng.integers(0, 2, size=n).astype(np.uint8)
            if not mask.any() or mask.all():
                mask[0] = 1 - mask[0]
            S_mixed = (S_z * (1 - mask) + S_x * mask) % 2
            L_mixed = (L_z * (1 - mask) + L_x * mask) % 2
            channels.append((f"M{i}", S_mixed, L_mixed, mask))

        trials_per_channel = max(num_trials // len(channels), 50)

        for ch_name, check_matrix, logical_matrix, mask_or_type in channels:
            nonzero_mask = logical_matrix.any(axis=1)
            active_logicals = logical_matrix[nonzero_mask]
            if active_logicals.shape[0] == 0:
                continue

            nonzero_checks = check_matrix[check_matrix.any(axis=1)]
            effective_H = np.vstack([nonzero_checks, active_logicals]).astype(np.uint8)
            num_checks = nonzero_checks.shape[0]
            num_active = active_logicals.shape[0]

            if not _safe_for_bposd(effective_H):
                continue

            achievable_basis = _compute_achievable_basis(nonzero_checks, active_logicals)

            decoder = BpOsdDecoder(
                effective_H,
                error_rate=0.05,
                bp_method="product_sum",
                osd_method="osd_0",
                osd_order=0,
                max_iter=100,
            )

            syndrome = np.zeros(num_checks + num_active, dtype=np.uint8)

            for _ in range(trials_per_channel):
                if achievable_basis is not None:
                    num_basis = achievable_basis.shape[0]
                    coeffs = np.zeros(num_basis, dtype=np.uint8)
                    while not coeffs.any():
                        coeffs = rng.integers(0, 2, size=num_basis, dtype=np.uint8)
                    logical_bits = np.zeros(num_active, dtype=np.uint8)
                    for j in range(num_basis):
                        if coeffs[j]:
                            logical_bits ^= achievable_basis[j]
                else:
                    logical_bits = np.zeros(num_active, dtype=np.uint8)
                    while not logical_bits.any():
                        logical_bits = rng.integers(0, 2, size=num_active, dtype=np.uint8)

                syndrome[:num_checks] = 0
                syndrome[num_checks:] = logical_bits

                result = decoder.decode(syndrome)
                actual = effective_H @ result % 2
                if np.array_equal(actual, syndrome):
                    hw = int(np.sum(result))
                    if hw == 0:
                        continue

                    # Lift channel-projected result to full symplectic operator
                    symp_op = np.zeros(2 * n, dtype=np.uint8)
                    if isinstance(mask_or_type, str) and mask_or_type == "Y":
                        # Y channel: both X and Z
                        symp_op[:n] = result
                        symp_op[n:] = result
                    elif isinstance(mask_or_type, np.ndarray):
                        # Mixed channel: mask=0 → X, mask=1 → Z
                        symp_op[:n] = result * (1 - mask_or_type)  # X part
                        symp_op[n:] = result * mask_or_type          # Z part
                    else:
                        # Pure X channel (mask all zeros)
                        symp_op[:n] = result

                    sw = symplectic_weight(symp_op)
                    if sw > 0:
                        found_this_seed.append(sw)
                        if sw < best_weight:
                            best_weight = sw
                            best_operator = symp_op.copy()

        elapsed = time.time() - t0
        if found_this_seed:
            print(f"    seed={seed:5d}: best_sw={min(found_this_seed):2d}  "
                  f"found={len(found_this_seed)} operators  ({elapsed:.1f}s)")
        else:
            print(f"    seed={seed:5d}: no valid operators  ({elapsed:.1f}s)")
        all_found.extend(found_this_seed)
        sys.stdout.flush()

    return best_operator, best_weight, all_found


CODES = [
    {
        "name": "[[72,40,≤8]] Code6v2",
        "ell": 6, "m": 6,
        "A": [(0, 1), (2, 3), (4, 5)], "B": [(1, 0), (3, 2), (5, 4)],
        "C": [(0, 2), (0, 5)], "D": [(1, 2), (3, 1), (5, 3)],
    },
    {
        "name": "[[72,40,≤8]] Code5",
        "ell": 6, "m": 6,
        "A": [(0, 1), (2, 3), (4, 5)], "B": [(1, 0), (3, 2), (5, 4)],
        "C": [(0, 2), (2, 4), (4, 0)], "D": [(1, 2), (1, 5)],
    },
    {
        "name": "[[72,38,≤8]] Code8",
        "ell": 6, "m": 6,
        "A": [(0, 1), (2, 3), (4, 5)], "B": [(1, 0), (3, 2), (5, 4)],
        "C": [(0, 4), (3, 1)], "D": [(1, 1), (4, 4)],
    },
    {
        "name": "[[72,13,≤16]] Code1",
        "ell": 6, "m": 6,
        "A": [(0, 1), (2, 0), (4, 0)], "B": [(1, 0), (0, 1), (0, 2)],
        "C": [(4, 0)], "D": [(0, 5), (4, 2)],
    },
]


if __name__ == "__main__":
    print("=" * 70)
    print("LOGICAL WITNESS EXTRACTION AND VERIFICATION")
    print("=" * 70)

    for code_info in CODES:
        code = build_pbb_code(code_info["ell"], code_info["m"],
                              code_info["A"], code_info["B"],
                              code_info["C"], code_info["D"])
        n, k = get_pbb_params_fast(code)
        stab = np.array(code.matrix, dtype=int) % 2
        logicals = get_symplectic_logicals(code)

        print(f"\n{'='*70}")
        print(f"{code_info['name']}  n={n} k={k}")
        print(f"  A={code_info['A']}  B={code_info['B']}")
        print(f"  C={code_info['C']}  D={code_info['D']}")

        # Method 1: Mixed channel extraction (main method)
        print(f"\n  --- Mixed-channel extraction (50k trials × 10 seeds) ---")
        op_mixed, w_mixed, all_mixed = extract_witness_mixed_channels(
            code, num_trials=50000, seeds=[42, 137, 2024, 7777, 31415,
                                           99991, 54321, 11111, 77777, 33333])

        # Method 2: Full symplectic extraction
        print(f"\n  --- Symplectic extraction (20k trials × 5 seeds) ---")
        op_symp, w_symp, all_symp = extract_witness_symplectic(
            code, num_trials=20000, seeds=[42, 137, 2024, 7777, 31415])

        # Pick best overall
        best_op = None
        best_w = n
        if op_mixed is not None and w_mixed < best_w:
            best_op, best_w = op_mixed, w_mixed
        if op_symp is not None and w_symp < best_w:
            best_op, best_w = op_symp, w_symp

        print(f"\n  BEST WITNESS: symplectic weight = {best_w}")

        if best_op is not None:
            # Verify
            v = verify_logical(best_op, stab, logicals)
            print(f"  VERIFICATION:")
            print(f"    Commutes with all stabilizers: {v['commutes_with_all_stabs']}")
            if not v['commutes_with_all_stabs']:
                print(f"    WARNING: anticommutes with {v['num_anticommuting_stabs']} stabilizers!")
            print(f"    Non-trivial logical action: {v['has_nontrivial_action']}")
            print(f"    Anticommutes with {v['num_anticommuting_logicals']}/{logicals.shape[0]} logicals")
            print(f"    X sites ({len(v['x_sites'])}): {v['x_sites']}")
            print(f"    Z sites ({len(v['z_sites'])}): {v['z_sites']}")
            print(f"    Y sites ({len(v['y_sites'])}): {v['y_sites']}")
            total = len(v['x_sites']) + len(v['z_sites']) + len(v['y_sites'])
            print(f"    Total support = {total} qubits (symplectic weight)")
            print(f"    Compact: {v['pauli_string_compact']}")

            if v['commutes_with_all_stabs'] and v['has_nontrivial_action']:
                print(f"\n  ✓ VERIFIED: d ≤ {best_w} (explicit weight-{best_w} logical operator)")
            else:
                print(f"\n  ✗ VERIFICATION FAILED")

        # Weight distribution of found operators
        if all_mixed or all_symp:
            all_w = all_mixed + all_symp
            from collections import Counter
            wc = Counter(all_w)
            print(f"\n  Weight distribution of found operators (top 10):")
            for w, count in sorted(wc.items())[:10]:
                bar = "#" * min(count, 50)
                print(f"    w={w:2d}: {count:5d} {bar}")

        sys.stdout.flush()

    print(f"\n{'='*70}")
    print("DONE")
