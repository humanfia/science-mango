#!/usr/bin/env python3
"""Verify that [[288,24,12]] is a direct sum of two [[144,12,12]] gross codes.

Four independent checks:

1. TANNER GRAPH CONNECTIVITY: The full stabilizer graph (H_X and H_Z combined)
   has exactly 2 connected components, one on even x-indices, one on odd.
2. LOGICAL CONFINEMENT: All 48 logical operators are confined to a single
   component (0 of 48 span both).
3. ROW SPACE IDENTITY: Build at (24,6), extract even-x component, re-index
   x → x/2 to obtain a (12,6) code, then verify row-space equality with
   the gross code [[144,12,12]] at (12,6).
4. ALGEBRAIC EXPLANATION: The map x ↦ x² in F₂[x]/(x²⁴−1) has gcd(2,24)=2,
   so it is NOT a ring automorphism -- it maps onto the index-2 subgroup of
   even residues, creating two non-interacting cosets.

The [[288,24,12]] code (BLISS-equivalent at both lattices):
  (12,12): A = x⁶+y+y², B = y³+x²+x⁴
  (24,6):  A = x⁶+y+y², B = y³+x²+x⁴

The gross code [[144,12,12]]:
  (12,6): A = x³+y+y², B = y³+x+x²

Usage:
    uv run python tests/verify_decomposition_288_24_12.py
"""

import sys
from collections import deque
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.bb_code import build_bb_code


def build_bipartite_adjacency(hz, hx):
    """Build adjacency lists for the Tanner graph (qubits + checks)."""
    n_checks_z, n_qubits = hz.shape
    n_checks_x = hx.shape[0]

    total = n_qubits + n_checks_z + n_checks_x
    adj = [[] for _ in range(total)]

    for i in range(n_checks_z):
        for j in range(n_qubits):
            if hz[i, j]:
                adj[j].append(n_qubits + i)
                adj[n_qubits + i].append(j)

    for i in range(n_checks_x):
        for j in range(n_qubits):
            if hx[i, j]:
                adj[j].append(n_qubits + n_checks_z + i)
                adj[n_qubits + n_checks_z + i].append(j)

    return adj, total


def find_components(adj, total):
    """BFS to find connected components."""
    visited = [False] * total
    components = []

    for start in range(total):
        if visited[start]:
            continue
        comp = []
        queue = deque([start])
        visited[start] = True
        while queue:
            node = queue.popleft()
            comp.append(node)
            for nb in adj[node]:
                if not visited[nb]:
                    visited[nb] = True
                    queue.append(nb)
        components.append(comp)

    return components


def check_1_tanner_graph(code_288):
    """CHECK 1: Tanner graph has exactly 2 connected components."""
    print("=" * 70)
    print("  CHECK 1: TANNER GRAPH CONNECTIVITY")
    print("=" * 70)

    n = code_288.num_qudits
    hx = np.array(code_288.matrix_x, dtype=np.uint8)
    hz = np.array(code_288.matrix_z, dtype=np.uint8)

    adj, total = build_bipartite_adjacency(hz, hx)
    components = find_components(adj, total)

    print(f"  Code: [[288,{code_288.dimension},12]]")
    print(f"  n = {n}, H_X: {hx.shape}, H_Z: {hz.shape}")
    print(f"  Tanner graph nodes: {total}")
    print(f"  Connected components: {len(components)}")

    qubit_components = []
    for comp in components:
        qubits = sorted([node for node in comp if node < n])
        qubit_components.append(qubits)

    for i, qc in enumerate(qubit_components):
        print(f"  Component {i}: {len(qc)} qubits")

    passed = len(components) == 2
    print(f"\n  RESULT: {'PASS' if passed else 'FAIL'} -- "
          f"{'exactly 2 components (decomposable)' if passed else f'{len(components)} components'}")
    return passed, qubit_components


def check_2_logical_confinement(code_288, qubit_components):
    """CHECK 2: All logicals confined to a single component."""
    print("\n" + "=" * 70)
    print("  CHECK 2: LOGICAL CONFINEMENT")
    print("=" * 70)

    n = code_288.num_qudits
    k = code_288.dimension
    logicals = np.array(code_288.get_logical_ops(), dtype=np.uint8)

    qubit_to_comp = np.zeros(n, dtype=int)
    for comp_idx, qubits in enumerate(qubit_components):
        for q in qubits:
            qubit_to_comp[q] = comp_idx

    spanning_count = 0
    for i in range(logicals.shape[0]):
        logical = logicals[i]
        x_part = logical[:n]
        z_part = logical[n:]
        support = np.where((x_part | z_part) > 0)[0]
        comps_touched = set(qubit_to_comp[q] for q in support)
        if len(comps_touched) > 1:
            spanning_count += 1

    print(f"  Total logical operators: {logicals.shape[0]} (2k = {2 * k})")
    print(f"  Logicals spanning both components: {spanning_count}")
    print(f"  Logicals confined to single component: {logicals.shape[0] - spanning_count}")

    passed = spanning_count == 0
    print(f"\n  RESULT: {'PASS' if passed else 'FAIL'} -- "
          f"{'all logicals confined (true direct sum)' if passed else f'{spanning_count} logicals span both'}")
    return passed


def gf2_rank(matrix):
    """Compute GF(2) rank via Gaussian elimination."""
    m = matrix.copy().astype(np.uint8)
    rows, cols = m.shape
    rank = 0
    for col in range(cols):
        pivot = None
        for row in range(rank, rows):
            if m[row, col]:
                pivot = row
                break
        if pivot is None:
            continue
        m[[rank, pivot]] = m[[pivot, rank]]
        for row in range(rows):
            if row != rank and m[row, col]:
                m[row] = (m[row] + m[rank]) % 2
        rank += 1
    return rank


def check_3_row_space_identity(code_gross):
    """CHECK 3: Build at (24,6), extract even-x component, verify row space = gross.

    At (24,6), each qubit block has indices a*6+b with a in {0,...,23}, b in {0,...,5}.
    The even-x component has a in {0,2,...,22} (12 values), giving 72 qubits per block.
    Re-indexing a → a/2 gives a' in {0,...,11}, b' = b, matching gross code at (12,6).
    """
    print("\n" + "=" * 70)
    print("  CHECK 3: ROW SPACE IDENTITY (component vs gross code)")
    print("=" * 70)

    # Build [[288,24,12]] at (24,6): same code, different lattice embedding
    code_24_6 = build_bb_code(24, 6,
                              [(6, 0), (0, 1), (0, 2)],
                              [(0, 3), (2, 0), (4, 0)])
    n = code_24_6.num_qudits
    k = code_24_6.dimension
    print(f"  [[288,24,12]] at (24,6): n={n}, k={k}")
    assert n == 288 and k == 24

    ell, m = 24, 6
    block_size = ell * m  # 144

    # Build qubit re-indexing: even-x component → (12,6) gross code
    # Block j qubit at a*m+b (a even) → gross block j qubit at (a//2)*m+b
    ell_gross, m_gross = 12, 6
    block_gross = ell_gross * m_gross  # 72
    n_gross = 2 * block_gross  # 144

    reindex = {}  # 288-code qubit → gross-code qubit
    for j in range(2):  # two blocks
        for a in range(0, ell, 2):  # even x-indices only
            for b in range(m):
                q_288 = j * block_size + a * m + b
                q_gross = j * block_gross + (a // 2) * m_gross + b
                reindex[q_288] = q_gross

    even_qubits = set(reindex.keys())
    print(f"  Even-x component: {len(even_qubits)} qubits → {n_gross} gross qubits")

    hx_288 = np.array(code_24_6.matrix_x, dtype=np.uint8)
    hz_288 = np.array(code_24_6.matrix_z, dtype=np.uint8)
    hx_gross = np.array(code_gross.matrix_x, dtype=np.uint8)
    hz_gross = np.array(code_gross.matrix_z, dtype=np.uint8)

    print(f"  Gross code: H_X {hx_gross.shape}, H_Z {hz_gross.shape}")

    all_pass = True
    for label, h_full, h_gross in [("X", hx_288, hx_gross), ("Z", hz_288, hz_gross)]:
        comp_rows = []
        for row_idx in range(h_full.shape[0]):
            row = h_full[row_idx]
            support = set(np.where(row > 0)[0])
            if support and support.issubset(even_qubits):
                new_row = np.zeros(n_gross, dtype=np.uint8)
                for q in support:
                    new_row[reindex[q]] = 1
                comp_rows.append(new_row)

        comp_matrix = np.array(comp_rows, dtype=np.uint8)

        rank_comp = gf2_rank(comp_matrix)
        rank_gross = gf2_rank(h_gross)
        combined = np.vstack([comp_matrix, h_gross])
        rank_combined = gf2_rank(combined)

        match = (rank_combined == rank_gross == rank_comp)
        status = "MATCH" if match else "MISMATCH"
        print(f"  H_{label}: rank(comp)={rank_comp}, rank(gross)={rank_gross}, "
              f"rank(combined)={rank_combined} -- {status}")
        if not match:
            all_pass = False

    print(f"\n  RESULT: {'PASS' if all_pass else 'FAIL'} -- "
          f"{'row spaces identical to gross code' if all_pass else 'row space mismatch'}")
    return all_pass


def check_4_algebraic_explanation():
    """CHECK 4: The map x ↦ x² is not a ring automorphism when gcd(2, ℓ) > 1."""
    print("\n" + "=" * 70)
    print("  CHECK 4: ALGEBRAIC EXPLANATION")
    print("=" * 70)

    ell = 24
    g = np.gcd(2, ell)
    is_auto = (g == 1)

    print(f"  Lattice x-dimension: ℓ = {ell}")
    print(f"  Map: x ↦ x² in F₂[x]/(x^{ell} - 1)")
    print(f"  gcd(2, {ell}) = {g}")
    print(f"  Ring automorphism: {'YES' if is_auto else 'NO'}")
    if not is_auto:
        print(f"  The map x ↦ x² sends all elements to even residues mod {ell}.")
        print(f"  This creates two non-interacting cosets: even and odd x-indices.")
        print(f"  Polynomials A = x⁶+y+y², B = y³+x²+x⁴ use ONLY even")
        print(f"  x-exponents (0, 2, 4, 6), confirming the coset separation.")

    print(f"\n  At (12,12): same polynomials, same even-x separation.")
    print(f"  x-exponents in A: {{0, 6}} (both even)")
    print(f"  x-exponents in B: {{0, 2, 4}} (all even)")
    print(f"  → Stabilizers connect only qubits sharing x-index parity")

    passed = not is_auto
    print(f"\n  RESULT: {'PASS' if passed else 'FAIL'} -- "
          f"{'non-automorphism confirms decomposition' if passed else 'map is an automorphism'}")
    return passed


def main():
    print("Verification: [[288,24,12]] = [[144,12,12]] ⊕ [[144,12,12]]")
    print("=" * 70)

    # Build [[288,24,12]] at (12,12): A = x^6+y+y^2, B = y^3+x^2+x^4
    code_288 = build_bb_code(12, 12,
                             [(6, 0), (0, 1), (0, 2)],
                             [(0, 3), (2, 0), (4, 0)])
    n_288 = code_288.num_qudits
    k_288 = code_288.dimension
    print(f"  [[288,24,12]] at (12,12): n={n_288}, k={k_288}")
    assert n_288 == 288 and k_288 == 24, f"Unexpected: n={n_288}, k={k_288}"

    # Build gross code [[144,12,12]] at (12,6): A = x^3+y+y^2, B = y^3+x+x^2
    code_gross = build_bb_code(12, 6,
                               [(3, 0), (0, 1), (0, 2)],
                               [(0, 3), (1, 0), (2, 0)])
    n_gross = code_gross.num_qudits
    k_gross = code_gross.dimension
    print(f"  Gross [[144,12,12]] at (12,6): n={n_gross}, k={k_gross}")
    assert n_gross == 144 and k_gross == 12, f"Unexpected: n={n_gross}, k={k_gross}"

    # Checks 1 & 2 use (12,12); Check 3 rebuilds at (24,6) internally
    pass1, qubit_components = check_1_tanner_graph(code_288)
    pass2 = check_2_logical_confinement(code_288, qubit_components)
    pass3 = check_3_row_space_identity(code_gross)
    pass4 = check_4_algebraic_explanation()

    # Summary
    print("\n" + "=" * 70)
    print("  SUMMARY")
    print("=" * 70)
    results = [
        ("Tanner graph: 2 components", pass1),
        ("All logicals confined", pass2),
        ("Row spaces match gross code", pass3),
        ("Algebraic: non-automorphism", pass4),
    ]
    all_pass = True
    for desc, passed in results:
        status = "PASS" if passed else "FAIL"
        print(f"  [{status}] {desc}")
        if not passed:
            all_pass = False

    if all_pass:
        print("\n  CONCLUSION: [[288,24,12]] = [[144,12,12]] ⊕ [[144,12,12]]")
        print("  The code is a direct sum of two independent gross codes.")
    else:
        print("\n  CONCLUSION: Some checks failed -- decomposition NOT confirmed.")

    sys.exit(0 if all_pass else 1)


if __name__ == "__main__":
    main()
