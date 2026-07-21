#!/usr/bin/env python3
"""Investigate the d≤2 outlier on [[144,32,≤14]].

The 1.5M-trial extended verification found d=2 in a single batch
(OSD_CS10/minimum_sum, batch 5/10). Both reviewers flagged this as
needing resolution: is it a valid weight-2 logical operator, or a
decoder bug?

This script:
1. Builds the [[144,32]] code (A = B = x^4 + 1 + y^2 at (12,6))
2. Reimplements the core distance-bound loop to capture actual operators
3. Runs many trials with OSD_CS10/minimum_sum looking for low-weight ops
4. When found, validates:
   - Is it in ker(H_z)? (valid X-type operator)
   - Does it anti-commute with some Z-logical? (non-trivial)
   - What is its actual support?
5. Also checks: is weight-2 even possible in a 6-regular Tanner graph?
"""

import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from qldpc.codes import CSSCode
from qldpc.objects import Pauli
from qldpc import decoders

from evaluation.bb_code import build_bb_code


def get_random_array(field, length):
    """Generate a random nonzero binary vector."""
    while True:
        vec = np.random.randint(0, 2, size=length).astype(np.int32)
        if vec.any():
            return vec


def find_low_weight_operators(
    code: CSSCode,
    pauli: Pauli,
    num_trials: int,
    decoder_kwargs: dict,
    weight_threshold: int = 8,
) -> list[dict]:
    """Run distance-bound trials and capture operators below weight_threshold.

    This reimplements the core of CSSCode.get_distance_bound_with_decoder
    but stores the actual operators instead of just their weights.
    """
    # Follow the same logic as qldpc
    pauli_z = Pauli.Z if pauli is Pauli.X else Pauli.X
    matrix_z = code.get_matrix(pauli_z)
    logical_ops_z = code.get_logical_ops(pauli_z)

    # Convert to plain numpy for our validation checks
    matrix_z_np = np.array(matrix_z, dtype=np.int32)
    logical_ops_z_np = np.array(logical_ops_z, dtype=np.int32)

    effective_check_matrix = np.vstack([matrix_z, logical_ops_z])
    decoder = decoders.get_decoder(effective_check_matrix, **decoder_kwargs)
    effective_syndrome = np.zeros(len(effective_check_matrix), dtype=int)

    found_operators = []
    min_weight = code.num_qudits
    weights_found = []

    for trial in range(num_trials):
        # Random nonzero logical syndrome
        effective_syndrome[-code.dimension:] = get_random_array(code.field, code.dimension)

        # Decode
        candidate = decoder.decode(effective_syndrome)

        # Verify decode succeeded (using plain numpy)
        ecm_np = np.array(effective_check_matrix, dtype=np.int32)
        actual_syndrome = ecm_np @ candidate.astype(np.int32) % 2
        target_syndrome = np.array(effective_syndrome, dtype=np.int32) % 2
        if not np.array_equal(actual_syndrome, target_syndrome):
            continue  # decoding failure, skip

        weight = int(np.count_nonzero(candidate))
        weights_found.append(weight)
        min_weight = min(min_weight, weight)

        if weight <= weight_threshold:
            # Capture this operator for inspection
            support = np.where(candidate != 0)[0]

            # Validate: is it in ker(H_z)?
            hz_syndrome = matrix_z_np @ candidate.astype(np.int32) % 2
            in_kernel = not hz_syndrome.any()

            # Validate: does it anti-commute with some Z-logical?
            logical_syndrome = logical_ops_z_np @ candidate.astype(np.int32) % 2
            is_nontrivial = logical_syndrome.any()

            # Check: is it a stabilizer? (in row space of H_x)
            # A stabilizer would have zero logical syndrome
            is_stabilizer = not is_nontrivial

            found_operators.append({
                "trial": trial,
                "weight": weight,
                "support": support.tolist(),
                "in_kernel_hz": in_kernel,
                "is_nontrivial_logical": is_nontrivial,
                "is_stabilizer": is_stabilizer,
                "logical_syndrome": logical_syndrome.tolist(),
                "target_logical_syndrome": target_syndrome[-code.dimension:].tolist(),
                "operator": candidate.copy(),
            })

            print(f"  Trial {trial}: weight={weight}, support={support.tolist()}, "
                  f"ker(H_z)={in_kernel}, nontrivial={is_nontrivial}")

    return found_operators, weights_found, min_weight


def main():
    print("=" * 70)
    print("  INVESTIGATING d≤2 OUTLIER ON [[144,32,≤14]]")
    print("  Code: A = B = x^4 + 1 + y^2  at (12,6)")
    print("=" * 70)

    # Build the code
    ell, m = 12, 6
    A_terms = [(4, 0), (0, 0), (0, 2)]  # x^4 + 1 + y^2
    B_terms = [(0, 2), (0, 0), (4, 0)]  # y^2 + 1 + x^4 (same as A, self-dual)

    code = build_bb_code(ell, m, A_terms, B_terms)
    n = code.num_qudits
    k = code.dimension
    print(f"\n  Code parameters: n={n}, k={k}")
    print(f"  Self-dual: A_terms == B_terms (after sorting): "
          f"{sorted(A_terms) == sorted(B_terms)}")

    # Basic check: H_X H_Z^T = 0
    hx = code.get_matrix(Pauli.X)
    hz = code.get_matrix(Pauli.Z)
    # Matrices are GF(2) galois arrays -- arithmetic is already mod 2
    css_check = hx @ hz.T
    print(f"  CSS check H_X H_Z^T = 0: {not np.any(np.array(css_check))}")
    print(f"  H_X shape: {hx.shape}, H_Z shape: {hz.shape}")

    # Convert to plain numpy for easier manipulation
    hx_np = np.array(hx, dtype=np.int32)
    hz_np = np.array(hz, dtype=np.int32)

    # Check matrix properties
    print(f"\n  Check weight (row weights of H_X):")
    row_weights = np.count_nonzero(hx_np, axis=1)
    print(f"    min={row_weights.min()}, max={row_weights.max()}, "
          f"mean={row_weights.mean():.1f}")

    # Column weights (qubit degrees)
    col_weights = np.count_nonzero(hx_np, axis=0)
    print(f"  Qubit degree (column weights of H_X):")
    print(f"    min={col_weights.min()}, max={col_weights.max()}, "
          f"mean={col_weights.mean():.1f}")

    # Theoretical check: in a 6-regular Tanner graph, can a weight-2
    # operator be in ker(H)? A weight-2 vector has 2 nonzero positions.
    # For it to be in ker(H_z), every row of H_z must have even overlap
    # with these 2 positions. This means the two columns must be identical
    # in H_z, or their sum must be zero mod 2.
    print(f"\n  --- Checking if weight-2 ker(H_z) vectors exist ---")
    n_cols = hz_np.shape[1]
    found_identical_cols = False
    identical_pairs_hz = []
    for i in range(n_cols):
        for j in range(i + 1, n_cols):
            if np.array_equal(hz_np[:, i], hz_np[:, j]):
                identical_pairs_hz.append((i, j))

    if identical_pairs_hz:
        found_identical_cols = True
        print(f"  FOUND {len(identical_pairs_hz)} identical column pair(s) in H_z")
        logical_ops_z = np.array(code.get_logical_ops(Pauli.Z), dtype=np.int32)
        nontrivial_count = 0
        stabilizer_count = 0
        for i, j in identical_pairs_hz[:10]:  # show up to 10
            test_vec = np.zeros(n_cols, dtype=np.int32)
            test_vec[i] = 1
            test_vec[j] = 1
            log_syn = logical_ops_z @ test_vec % 2
            is_nontrivial = log_syn.any()
            if is_nontrivial:
                nontrivial_count += 1
                print(f"    Cols ({i},{j}): NONTRIVIAL logical of weight 2!")
            else:
                stabilizer_count += 1
                print(f"    Cols ({i},{j}): stabilizer (trivial)")
        if len(identical_pairs_hz) > 10:
            print(f"    ... and {len(identical_pairs_hz) - 10} more pairs")
        print(f"  Summary: {nontrivial_count} nontrivial, "
              f"{stabilizer_count} stabilizers out of "
              f"{min(len(identical_pairs_hz), 10)} checked")
    else:
        print(f"  No identical column pairs in H_z -> weight-2 ker(H_z) "
              f"vectors are IMPOSSIBLE")
        print(f"  Any d=2 finding for X-type ops is necessarily a DECODER BUG")

    # Also check H_x (for Z-type operators)
    print(f"\n  --- Checking if weight-2 ker(H_x) vectors exist ---")
    n_cols_x = hx_np.shape[1]
    found_identical_cols_x = False
    identical_pairs_hx = []
    for i in range(n_cols_x):
        for j in range(i + 1, n_cols_x):
            if np.array_equal(hx_np[:, i], hx_np[:, j]):
                identical_pairs_hx.append((i, j))

    if identical_pairs_hx:
        found_identical_cols_x = True
        print(f"  FOUND {len(identical_pairs_hx)} identical column pair(s) in H_x")
        logical_ops_x = np.array(code.get_logical_ops(Pauli.X), dtype=np.int32)
        nontrivial_count_x = 0
        stabilizer_count_x = 0
        for i, j in identical_pairs_hx[:10]:
            test_vec = np.zeros(n_cols_x, dtype=np.int32)
            test_vec[i] = 1
            test_vec[j] = 1
            log_syn = logical_ops_x @ test_vec % 2
            is_nontrivial = log_syn.any()
            if is_nontrivial:
                nontrivial_count_x += 1
                print(f"    Cols ({i},{j}): NONTRIVIAL Z-logical of weight 2!")
            else:
                stabilizer_count_x += 1
                print(f"    Cols ({i},{j}): stabilizer (trivial)")
        if len(identical_pairs_hx) > 10:
            print(f"    ... and {len(identical_pairs_hx) - 10} more pairs")
        print(f"  Summary: {nontrivial_count_x} nontrivial, "
              f"{stabilizer_count_x} stabilizers out of "
              f"{min(len(identical_pairs_hx), 10)} checked")
    else:
        found_identical_cols_x = False
        print(f"  No identical column pairs in H_x -> weight-2 ker(H_x) "
              f"vectors are IMPOSSIBLE")

    if not found_identical_cols and not found_identical_cols_x:
        print(f"\n  *** CONCLUSION: d >= 3 is PROVEN for this code ***")
        print(f"  *** The d=2 finding was definitively a decoder artifact ***")

    # Now run the decoder to try to reproduce the d=2 finding
    print(f"\n{'='*70}")
    print(f"  ATTEMPTING TO REPRODUCE d=2 WITH OSD_CS10/minimum_sum")
    print(f"  Running 10 batches x 5000 trials (same as 1.5M protocol)")
    print(f"{'='*70}")

    decoder_kwargs = {
        "bp_method": "minimum_sum",
        "osd_method": "osd_cs",
        "osd_order": 10,
    }

    all_low_weight_ops = []
    batch_mins = []

    for batch in range(10):
        print(f"\n  --- Batch {batch+1}/10 ---")

        # Search for X-type low-weight ops
        ops_x, weights_x, min_x = find_low_weight_operators(
            code, Pauli.X, 2500, decoder_kwargs, weight_threshold=8
        )

        # Search for Z-type low-weight ops
        ops_z, weights_z, min_z = find_low_weight_operators(
            code, Pauli.Z, 2500, decoder_kwargs, weight_threshold=8
        )

        batch_min = min(min_x, min_z)
        batch_mins.append(batch_min)
        all_low_weight_ops.extend(ops_x)
        all_low_weight_ops.extend(ops_z)

        print(f"  Batch {batch+1} min: d_x={min_x}, d_z={min_z}, "
              f"d={batch_min}")
        if weights_x:
            print(f"    X weights: min={min(weights_x)}, "
                  f"mean={sum(weights_x)/len(weights_x):.1f}, "
                  f"max={max(weights_x)}")
        if weights_z:
            print(f"    Z weights: min={min(weights_z)}, "
                  f"mean={sum(weights_z)/len(weights_z):.1f}, "
                  f"max={max(weights_z)}")

    # Summary
    print(f"\n{'='*70}")
    print(f"  SUMMARY")
    print(f"{'='*70}")
    print(f"  Batch minimum distances: {batch_mins}")
    print(f"  Global minimum: {min(batch_mins)}")
    print(f"  Total low-weight operators found (weight ≤ 8): {len(all_low_weight_ops)}")

    if all_low_weight_ops:
        weight_counts = {}
        for op in all_low_weight_ops:
            w = op["weight"]
            weight_counts[w] = weight_counts.get(w, 0) + 1
        print(f"  Weight distribution of low-weight operators:")
        for w in sorted(weight_counts):
            valid = sum(1 for op in all_low_weight_ops
                        if op["weight"] == w and op["in_kernel_hz"]
                        and op["is_nontrivial_logical"])
            total = weight_counts[w]
            print(f"    weight={w}: {total} found, {valid} valid nontrivial logicals")

    # Any decoder bugs?
    bugs = [op for op in all_low_weight_ops if not op["in_kernel_hz"]]
    if bugs:
        print(f"\n  *** DECODER BUGS: {len(bugs)} operators NOT in ker(H) ***")
        for op in bugs[:5]:
            print(f"    Trial {op['trial']}: weight={op['weight']}, "
                  f"support={op['support']}")

    print(f"\n  Done.")


if __name__ == "__main__":
    main()
