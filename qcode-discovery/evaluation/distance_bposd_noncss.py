"""BP-OSD distance estimation for non-CSS stabilizer codes.

Adapts the randomized decoder-based distance bound algorithm from
Bravyi et al. (arXiv:2308.07915) to the general (non-CSS) setting.

**Two-mode approach**:

1. **Channel mode** (preferred for CSS-like codes): Decomposes into
   X, Z, Y, and random mixed channels, each operating on n-column
   matrices.  This is exact for CSS codes and works well for codes
   with channel-decomposable logicals.

2. **Full symplectic mode** (fallback for strongly non-CSS codes):
   Uses the full (m+2k) × 2n symplectic-syndrome matrix derived from
   [stab; logicals].  Always finds solutions but gives looser bounds
   because BP-OSD minimizes Hamming weight of the 2n-vector, not
   symplectic weight.

**Achievable syndrome sampling**: For non-CSS codes, only a subspace
of logical syndromes is achievable via any given channel.  Random
syndromes miss this subspace with high probability (e.g. 1/4096).
We compute the achievable subspace via GF(2) null space projection
and sample only from it, turning 0% decode success into ~100%.

Usage::

    from evaluation.distance_bposd_noncss import estimate_distance_noncss
    code = build_pbb_code(6, 3, A, B, C, D)
    d_upper = estimate_distance_noncss(code, num_trials=500)
"""

from __future__ import annotations

import numpy as np
from ldpc import BpOsdDecoder
from qldpc.codes import QuditCode

from evaluation.pbb_code import get_symplectic_logicals, symplectic_weight


def has_low_weight_logical(
    code: QuditCode, max_weight: int = 6,
) -> tuple[bool, int]:
    """Hash-based full-symplectic-weight low-weight-logical check.

    Searches for any non-trivial Pauli operator of symplectic weight
    ``≤ max_weight`` that lies in the codespace (zero syndrome) but is
    not a stabilizer.  Each qubit can independently carry X, Z, or Y,
    so this catches mixed Y-type logicals that pure-channel enumeration
    misses -- a non-CSS code can have a low-weight Y-type logical
    invisible to scanning X- and Z-channels separately.

    BP-OSD completely misses these -- it reported d=8-12 for codes that
    actually have d=2, and d=10 for codes with d=4.

    Uses hash-table decomposition for O(n³) complexity (vs O(n⁴) naive):
        weight 1-2: O(n)   via hashing
        weight 3-4: O(n²)  via pair-XOR hashing
        weight 5-6: O(n³)  via triple-XOR hashing

    Performance: n=72 ~5s, n=108 ~15s, n=144 ~40s (all weights through 6).

    Args:
        code: A qubit stabilizer code, non-CSS or CSS (qldpc's ``QuditCode``).
        max_weight: Maximum symplectic weight to check (1-6).

    Returns:
        (found, min_weight) -- found=True if a non-trivial logical of
        symplectic weight ≤ max_weight exists. min_weight is the weight
        found (or n if none).
    """
    S = np.array(code.matrix, dtype=np.uint8) % 2
    n = S.shape[1] // 2
    Sx = S[:, :n]
    Sz = S[:, n:]

    # Get logicals for non-triviality verification
    logicals = get_symplectic_logicals(code)
    if logicals.shape[0] == 0:
        return False, n
    L_x = logicals[:, :n]
    L_z = logicals[:, n:]

    def _is_nontrivial(x_vec, z_vec) -> bool:
        """Check if operator [x|z] anticommutes with at least one logical."""
        # Symplectic inner product: L_x · z + L_z · x (mod 2)
        syndrome = (L_x @ z_vec + L_z @ x_vec) % 2
        return np.any(syndrome)

    # Build extended syndrome columns for each qubit.
    # For qubit i, X_i on qubit i produces syndrome Sz[:,i] (detected by Z stabs).
    # Z_i produces Sx[:,i]. Y_i = X_i XOR Z_i.
    # ext_cols[qubit_idx] = (X_syndrome, Z_syndrome, Y_syndrome)
    # All stored as bytes keys for O(1) hashing.
    ext_synd = []  # list of (qubit, pauli_type, syndrome_bytes, syndrome_array)
    col_dict: dict[bytes, list[tuple[int, int]]] = {}  # syndrome -> [(qubit, type)]

    for i in range(n):
        sx_col = Sz[:, i]  # syndrome of X on qubit i
        sz_col = Sx[:, i]  # syndrome of Z on qubit i
        sy_col = sx_col ^ sz_col  # syndrome of Y on qubit i

        for p_type, s_arr in enumerate((sx_col, sz_col, sy_col)):
            s_bytes = s_arr.tobytes()
            ext_synd.append((i, p_type, s_bytes, s_arr))
            col_dict.setdefault(s_bytes, []).append((i, p_type))

    # --- Weight 1 ---
    if max_weight >= 1:
        zero_key = np.zeros(Sx.shape[0], dtype=np.uint8).tobytes()
        if zero_key in col_dict:
            for qi, pt in col_dict[zero_key]:
                # Build the operator vector and check non-triviality
                x_vec = np.zeros(n, dtype=np.uint8)
                z_vec = np.zeros(n, dtype=np.uint8)
                if pt == 0:    x_vec[qi] = 1       # X
                elif pt == 1:  z_vec[qi] = 1       # Z
                else:          x_vec[qi] = 1; z_vec[qi] = 1  # Y
                if _is_nontrivial(x_vec, z_vec):
                    return True, 1

    # --- Weight 2 ---
    if max_weight >= 2:
        # Two qubits with Pauli ops whose syndromes cancel.
        # syndrome(P_i) == syndrome(Q_j) with i != j
        for s_bytes, entries in col_dict.items():
            if s_bytes == np.zeros(Sx.shape[0], dtype=np.uint8).tobytes():
                continue  # zero-syndrome singles handled above
            # Check if any two entries are from different qubits
            qubits_seen: dict[int, int] = {}  # qubit -> first pauli_type
            for qi, pt in entries:
                if qi in qubits_seen:
                    continue  # same qubit, different Pauli → weight 1 (Y=XZ)
                for qj, pt2 in entries:
                    if qj > qi:
                        # Build operator
                        x_vec = np.zeros(n, dtype=np.uint8)
                        z_vec = np.zeros(n, dtype=np.uint8)
                        for q, p in ((qi, pt), (qj, pt2)):
                            if p == 0:    x_vec[q] = 1
                            elif p == 1:  z_vec[q] = 1
                            else:         x_vec[q] = 1; z_vec[q] = 1
                        if _is_nontrivial(x_vec, z_vec):
                            return True, 2
                qubits_seen[qi] = pt

    # --- Weight 3 ---
    # pair XOR matches a single column (disjoint qubit)
    if max_weight >= 3:
        num_ext = len(ext_synd)
        for ii in range(num_ext):
            qi, pi, _, si = ext_synd[ii]
            for jj in range(ii + 1, num_ext):
                qj, pj, _, sj = ext_synd[jj]
                if qi == qj:
                    continue
                pair_xor = si ^ sj
                pair_key = pair_xor.tobytes()
                if pair_key in col_dict:
                    for qk, pk in col_dict[pair_key]:
                        if qk != qi and qk != qj:
                            x_vec = np.zeros(n, dtype=np.uint8)
                            z_vec = np.zeros(n, dtype=np.uint8)
                            for q, p in ((qi, pi), (qj, pj), (qk, pk)):
                                if p == 0:    x_vec[q] = 1
                                elif p == 1:  z_vec[q] = 1
                                else:         x_vec[q] = 1; z_vec[q] = 1
                            if _is_nontrivial(x_vec, z_vec):
                                return True, 3

    # --- Weight 4 ---
    # Two disjoint pairs with equal XOR syndrome
    if max_weight >= 4:
        pair_xor_dict: dict[bytes, list[tuple[int, int, int, int]]] = {}
        num_ext = len(ext_synd)
        for ii in range(num_ext):
            qi, pi, _, si = ext_synd[ii]
            for jj in range(ii + 1, num_ext):
                qj, pj, _, sj = ext_synd[jj]
                if qi == qj:
                    continue
                pair_key = (si ^ sj).tobytes()
                pair_xor_dict.setdefault(pair_key, []).append((qi, pi, qj, pj))

        for entries in pair_xor_dict.values():
            if len(entries) < 2:
                continue
            for a in range(len(entries)):
                qa1, pa1, qa2, pa2 = entries[a]
                for b in range(a + 1, len(entries)):
                    qb1, pb1, qb2, pb2 = entries[b]
                    if len({qa1, qa2, qb1, qb2}) == 4:
                        x_vec = np.zeros(n, dtype=np.uint8)
                        z_vec = np.zeros(n, dtype=np.uint8)
                        for q, p in ((qa1, pa1), (qa2, pa2), (qb1, pb1), (qb2, pb2)):
                            if p == 0:    x_vec[q] = 1
                            elif p == 1:  z_vec[q] = 1
                            else:         x_vec[q] = 1; z_vec[q] = 1
                        if _is_nontrivial(x_vec, z_vec):
                            return True, 4

    # --- Weight 5 ---
    # triple XOR matches a pair XOR (disjoint qubits)
    if max_weight >= 5:
        # pair_xor_dict was built in the weight-4 block above
        # (max_weight >= 5 implies max_weight >= 4, so it always runs first).

        # Iterate over triples
        for ii in range(num_ext):
            qi, pi, _, si = ext_synd[ii]
            for jj in range(ii + 1, num_ext):
                qj, pj, _, sj = ext_synd[jj]
                if qi == qj:
                    continue
                pair_ij = si ^ sj
                for kk in range(jj + 1, num_ext):
                    qk, pk, _, sk = ext_synd[kk]
                    if qk == qi or qk == qj:
                        continue
                    triple_key = (pair_ij ^ sk).tobytes()
                    if triple_key in pair_xor_dict:
                        triple_qubits = {qi, qj, qk}
                        for qp1, pp1, qp2, pp2 in pair_xor_dict[triple_key]:
                            if qp1 not in triple_qubits and qp2 not in triple_qubits:
                                x_vec = np.zeros(n, dtype=np.uint8)
                                z_vec = np.zeros(n, dtype=np.uint8)
                                for q, p in ((qi, pi), (qj, pj), (qk, pk),
                                             (qp1, pp1), (qp2, pp2)):
                                    if p == 0:    x_vec[q] = 1
                                    elif p == 1:  z_vec[q] = 1
                                    else:         x_vec[q] = 1; z_vec[q] = 1
                                if _is_nontrivial(x_vec, z_vec):
                                    return True, 5

    # --- Weight 6 ---
    # Two disjoint triples with equal XOR syndrome
    if max_weight >= 6:
        triple_xor_dict: dict[bytes, list[tuple]] = {}
        for ii in range(num_ext):
            qi, pi, _, si = ext_synd[ii]
            for jj in range(ii + 1, num_ext):
                qj, pj, _, sj = ext_synd[jj]
                if qi == qj:
                    continue
                pair_ij = si ^ sj
                for kk in range(jj + 1, num_ext):
                    qk, pk, _, sk = ext_synd[kk]
                    if qk == qi or qk == qj:
                        continue
                    triple_key = (pair_ij ^ sk).tobytes()
                    triple_xor_dict.setdefault(triple_key, []).append(
                        (qi, pi, qj, pj, qk, pk)
                    )

        for entries in triple_xor_dict.values():
            if len(entries) < 2:
                continue
            for a in range(len(entries)):
                qa = {entries[a][0], entries[a][2], entries[a][4]}
                for b in range(a + 1, len(entries)):
                    qb = {entries[b][0], entries[b][2], entries[b][4]}
                    if qa.isdisjoint(qb):
                        x_vec = np.zeros(n, dtype=np.uint8)
                        z_vec = np.zeros(n, dtype=np.uint8)
                        for idx in (a, b):
                            e = entries[idx]
                            for r in range(3):
                                q, p = e[2*r], e[2*r+1]
                                if p == 0:    x_vec[q] = 1
                                elif p == 1:  z_vec[q] = 1
                                else:         x_vec[q] = 1; z_vec[q] = 1
                        if _is_nontrivial(x_vec, z_vec):
                            return True, 6

    return False, n


def _compute_achievable_basis(
    check_matrix: np.ndarray,
    active_logicals: np.ndarray,
) -> np.ndarray | None:
    """Compute basis for achievable logical syndromes in a channel.

    For non-CSS codes, the kernel of check_matrix may project onto
    only a subspace of the logical syndrome space.  Random syndromes
    outside this subspace are unsolvable, wasting decoder trials.

    Returns:
        (rank, num_active) basis matrix, or None if full space is
        achievable (CSS-like) or computation fails.
    """
    try:
        from galois import GF2
    except ImportError:
        import warnings
        warnings.warn(
            "galois package not installed -- falling back to random syndrome "
            "sampling, which has very low success rate for non-CSS codes. "
            "Install galois for accurate distance estimation: pip install galois",
            stacklevel=2,
        )
        return None

    check_matrix.shape[1]
    num_active = active_logicals.shape[0]

    check_gf = GF2(check_matrix.astype(int))
    kernel = check_gf.null_space()
    if kernel.shape[0] == 0:
        return None

    # Project kernel onto logical syndrome space
    kernel_np = np.array(kernel, dtype=int)
    # Each column of syndrome_image is the logical syndrome of a kernel vector
    syndrome_image = (active_logicals @ kernel_np.T) % 2  # (num_active, dim_kernel)

    # Basis for the column space = row space of transpose
    img_gf = GF2(syndrome_image.T.astype(int))
    rref = img_gf.row_reduce()
    rref_np = np.array(rref, dtype=int)
    nonzero_rows = rref_np[np.any(rref_np != 0, axis=1)]

    if nonzero_rows.shape[0] == 0:
        return None

    # If achievable rank equals num_active, full space is reachable
    if nonzero_rows.shape[0] >= num_active:
        return None  # No restriction needed

    return nonzero_rows.astype(np.uint8)


def _safe_for_bposd(matrix: np.ndarray) -> bool:
    """Check if a matrix is safe to pass to BpOsdDecoder.

    BpOsdDecoder's C code segfaults on matrices with all-zero columns
    (no variable node connections in the Tanner graph).

    NOTE: Zero rows should be stripped before calling this function
    (they are degenerate constraints, not a segfault risk per se, but
    callers strip them for cleanliness).
    """
    if matrix.size == 0:
        return False
    # All-zero columns cause null dereference in BP message passing
    if not matrix.any(axis=0).all():
        return False
    return True


def _symplectic_syndrome_matrix(rows: np.ndarray) -> np.ndarray:
    """Return the binary matrix whose dot product gives symplectic syndrome.

    Rows are stored in standard stabilizer form [x | z], while an operator is
    also represented as [x | z].  The symplectic inner product is
    row_x . op_z + row_z . op_x, so the linear syndrome matrix is [z | x].
    """
    rows = np.asarray(rows, dtype=np.uint8) % 2
    n = rows.shape[1] // 2
    return np.hstack([rows[:, n:], rows[:, :n]]).astype(np.uint8)


def _decode_channel(
    check_matrix: np.ndarray,
    logical_matrix: np.ndarray,
    num_trials: int,
    *,
    osd_method: str = "osd_0",
    osd_order: int = 0,
    max_bp_iter: int = 100,
    error_rate: float = 0.05,
    rng: np.random.Generator,
) -> int:
    """Run BP-OSD on a single Pauli channel with achievable syndrome sampling.

    Args:
        check_matrix: (num_checks, n) binary matrix of stabilizer projections.
        logical_matrix: (num_logicals, n) binary matrix of logical projections.
            Only rows with at least one nonzero entry are used.
        num_trials: Number of decoding trials.

    Returns:
        Minimum Hamming weight found (upper bound on channel distance).
    """
    n = check_matrix.shape[1]

    # Filter to logicals with nonzero projection onto this channel
    nonzero_mask = logical_matrix.any(axis=1)
    active_logicals = logical_matrix[nonzero_mask]

    if active_logicals.shape[0] == 0:
        return n  # No logicals in this channel

    # Strip zero rows from check_matrix (e.g. CSS codes have zero X-part
    # in Z-stabilizers).  Zero rows are degenerate constraints that cause
    # BpOsdDecoder to segfault, but they carry no information.
    nonzero_checks = check_matrix[check_matrix.any(axis=1)]

    effective_H = np.vstack([nonzero_checks, active_logicals]).astype(np.uint8)
    num_checks = nonzero_checks.shape[0]
    num_active = active_logicals.shape[0]

    if not _safe_for_bposd(effective_H):
        # Matrix has zero columns -- BpOsdDecoder would segfault.
        # Return n (no useful bound from this channel). Do NOT use
        # channel-projected Hamming weights as fallback -- for mixed
        # channels, the projection can be 3-5x lighter than the true
        # symplectic weight, giving spuriously low distance estimates.
        return n

    decoder = BpOsdDecoder(
        effective_H,
        error_rate=error_rate,
        bp_method="product_sum",
        osd_method=osd_method,
        osd_order=osd_order,
        max_iter=max_bp_iter,
    )

    # Compute achievable syndrome basis for non-CSS codes
    achievable_basis = _compute_achievable_basis(nonzero_checks, active_logicals)

    syndrome = np.zeros(num_checks + num_active, dtype=np.uint8)
    min_weight = n

    for _ in range(num_trials):
        if achievable_basis is not None:
            # Sample from achievable subspace only
            num_basis = achievable_basis.shape[0]
            coeffs = np.zeros(num_basis, dtype=np.uint8)
            while not coeffs.any():
                coeffs = rng.integers(0, 2, size=num_basis, dtype=np.uint8)
            logical_bits = np.zeros(num_active, dtype=np.uint8)
            for j in range(num_basis):
                if coeffs[j]:
                    logical_bits ^= achievable_basis[j]
        else:
            # Full space is achievable (CSS-like)
            logical_bits = np.zeros(num_active, dtype=np.uint8)
            while not logical_bits.any():
                logical_bits = rng.integers(0, 2, size=num_active, dtype=np.uint8)

        syndrome[:num_checks] = 0
        syndrome[num_checks:] = logical_bits

        result = decoder.decode(syndrome)
        actual = effective_H @ result % 2
        if np.array_equal(actual, syndrome):
            w = int(np.sum(result))
            if 0 < w < min_weight:
                min_weight = w

    return min_weight


def _decode_symplectic(
    stab: np.ndarray,
    logicals: np.ndarray,
    num_trials: int,
    *,
    osd_method: str = "osd_0",
    osd_order: int = 0,
    max_bp_iter: int = 100,
    error_rate: float = 0.05,
    rng: np.random.Generator,
) -> int:
    """Run BP-OSD on the full 2n-column symplectic matrix.

    Fallback for strongly non-CSS codes where channel decomposition
    fails.  Returns min symplectic weight (not Hamming weight).
    """
    two_n = stab.shape[1]
    n = two_n // 2

    effective_H = _symplectic_syndrome_matrix(np.vstack([stab, logicals]))
    num_stabs = stab.shape[0]
    num_logicals = logicals.shape[0]

    if not _safe_for_bposd(effective_H):
        # Degenerate matrix -- return min symplectic weight of logicals directly
        weights = [symplectic_weight(logicals[i]) for i in range(num_logicals)]
        return min(w for w in weights if w > 0) if any(w > 0 for w in weights) else n

    decoder = BpOsdDecoder(
        effective_H,
        error_rate=error_rate,
        bp_method="product_sum",
        osd_method=osd_method,
        osd_order=osd_order,
        max_iter=max_bp_iter,
    )

    syndrome = np.zeros(num_stabs + num_logicals, dtype=np.uint8)
    min_sw = n

    for _ in range(num_trials):
        logical_bits = np.zeros(num_logicals, dtype=np.uint8)
        while not logical_bits.any():
            logical_bits = rng.integers(0, 2, size=num_logicals, dtype=np.uint8)
        syndrome[:num_stabs] = 0
        syndrome[num_stabs:] = logical_bits

        result = decoder.decode(syndrome)
        actual = effective_H @ result % 2
        if np.array_equal(actual, syndrome):
            sw = symplectic_weight(result)
            if 0 < sw < min_sw:
                min_sw = sw

    return min_sw


def estimate_distance_noncss(
    code: QuditCode,
    num_trials: int = 500,
    *,
    osd_method: str = "osd_0",
    osd_order: int = 0,
    max_bp_iter: int = 100,
    error_rate: float = 0.05,
    seed: int | None = None,
) -> int:
    """Estimate non-CSS code distance via multi-channel BP-OSD.

    Runs BP-OSD on X, Z, Y, and random mixed channels, plus a full
    symplectic fallback.  Uses achievable syndrome sampling to ensure
    high decode success rates even for strongly non-CSS codes.

    For CSS codes, this reproduces the standard CSS BP-OSD result.

    Args:
        code: A qubit stabilizer code, non-CSS or CSS (qldpc's ``QuditCode``).
        num_trials: Total trials, split across channels.
        osd_method: ``"osd_0"`` (fast) or ``"osd_cs"`` (tighter, slower).
        osd_order: OSD order (0 for osd_0, 10 for osd_cs).
        max_bp_iter: Maximum BP iterations.
        error_rate: Channel error rate for BP initialization.
        seed: Random seed for reproducibility.

    Returns:
        Upper bound on symplectic-weight code distance.
    """
    n = code.num_qudits
    k = code.dimension
    if k == 0:
        return n

    stab = np.array(code.matrix, dtype=int) % 2
    logicals = get_symplectic_logicals(code)

    if logicals.shape[0] == 0:
        return n

    S_x = stab[:, :n]   # X-parts of stabilizers
    S_z = stab[:, n:]    # Z-parts of stabilizers
    L_x = logicals[:, :n]
    L_z = logicals[:, n:]

    rng = np.random.default_rng(seed)
    decoder_kwargs = dict(
        osd_method=osd_method,
        osd_order=osd_order,
        max_bp_iter=max_bp_iter,
        error_rate=error_rate,
    )

    # Split trials: X, Z get 20% each; Y gets 10%; mixed gets 35%; symplectic 15%
    # Mixed channels are critical for non-CSS codes -- low-weight logicals often
    # have mixed X/Z support that pure channels miss entirely.
    trials_x = num_trials * 20 // 100
    trials_z = num_trials * 20 // 100
    trials_y = num_trials * 10 // 100
    trials_mixed = num_trials * 35 // 100
    trials_symplectic = num_trials - trials_x - trials_z - trials_y - trials_mixed

    d_best = n

    # X-channel: pure X errors, detected by Z-parts of stabilizers
    d_x = _decode_channel(
        S_z, L_z, trials_x, rng=rng, **decoder_kwargs,
    )
    d_best = min(d_best, d_x)

    # Z-channel: pure Z errors, detected by X-parts of stabilizers
    d_z = _decode_channel(
        S_x, L_x, trials_z, rng=rng, **decoder_kwargs,
    )
    d_best = min(d_best, d_z)

    # Y-channel: Y errors (e_x = e_z), detected by (S_x + S_z)
    S_y = (S_x + S_z) % 2
    L_y = (L_x + L_z) % 2
    d_y = _decode_channel(
        S_y, L_y, trials_y, rng=rng, **decoder_kwargs,
    )
    d_best = min(d_best, d_y)

    # Random mixed channels: for a random binary mask m, assign X (m_i=0)
    # or Z (m_i=1) to each qubit.  Use many diverse masks (~20 trials each)
    # to maximize the chance of hitting the support of low-weight logicals.
    num_mixed_channels = max(1, trials_mixed // 20)
    trials_per_mixed = trials_mixed // num_mixed_channels

    for _ in range(num_mixed_channels):
        mask = rng.integers(0, 2, size=n).astype(np.uint8)
        if not mask.any() or mask.all():
            mask[0] = 1 - mask[0]

        S_mixed = (S_z * (1 - mask) + S_x * mask) % 2
        L_mixed = (L_z * (1 - mask) + L_x * mask) % 2

        d_mixed = _decode_channel(
            S_mixed, L_mixed, trials_per_mixed, rng=rng, **decoder_kwargs,
        )
        d_best = min(d_best, d_mixed)

    # Full symplectic fallback: always run to catch strongly non-CSS codes
    # where channel decomposition fails (logicals require mixed Y support).
    d_symp = _decode_symplectic(
        stab, logicals, trials_symplectic, rng=rng, **decoder_kwargs,
    )
    d_best = min(d_best, d_symp)

    return d_best


def estimate_distance_noncss_osdcs(
    code: QuditCode,
    num_trials: int = 200,
    *,
    osd_order: int = 10,
    seed: int | None = None,
) -> int:
    """Estimate distance with OSD-CS (tighter bounds, slower).

    OSD-CS systematically searches order-w subsets of reliable bit
    positions, finding lower-weight solutions that OSD_0 misses.
    ~3-5x slower per trial but empirically tightens bounds.
    """
    return estimate_distance_noncss(
        code,
        num_trials=num_trials,
        osd_method="osd_cs",
        osd_order=osd_order,
        seed=seed,
    )
