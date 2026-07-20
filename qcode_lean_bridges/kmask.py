#!/usr/bin/env python3
"""kmask.py — compute H_X/H_Z F2 bitmask rows + logical dimension k for a BB code.

Convention (validated against qldpc in the prior session):
  G = [(a,b) for a in range(ell) for b in range(m)]     # index order
  circ_P[i][j] = 1  iff  (G[j] - G[i]) mod (ell,m) in supp(P)
  H_X = [cA | cB],  H_Z = [cBᵀ | cAᵀ]     (block circulants, ℓm x 2ℓm)
  k   = n - rank_F2(H_X) - rank_F2(H_Z),  n = 2ℓm
"""
from __future__ import annotations


def circ(P, ell, m):
    G = [(a, b) for a in range(ell) for b in range(m)]
    idx = {g: i for i, g in enumerate(G)}
    supp = {(a % ell, b % m) for a, b in P}
    N = ell * m
    rows = [[0] * N for _ in range(N)]
    for i, (ga, gb) in enumerate(G):
        for j, (ha, hb) in enumerate(G):
            if ((ha - ga) % ell, (hb - gb) % m) in supp:
                rows[i][j] = 1
    return rows


def transpose(mat):
    return [list(col) for col in zip(*mat)]


def hx_hz_rows(A, B, ell, m):
    cA, cB = circ(A, ell, m), circ(B, ell, m)
    cAt, cBt = transpose(cA), transpose(cB)
    Hx = [ra + rb for ra, rb in zip(cA, cB)]          # [cA | cB]
    Hz = [rbt + rat for rbt, rat in zip(cBt, cAt)]    # [cBᵀ | cAᵀ]
    return Hx, Hz


def rows_to_masks(rows):
    """Pack each 0/1 row (LSB = column 0) into a Python int bitmask."""
    return [sum((1 << j) for j, bit in enumerate(r) if bit) for r in rows]


def rankF2(masks):
    basis = []
    for v in masks:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
            basis.sort(reverse=True)
    return len(basis)


def k_of(A, B, ell, m):
    Hx, Hz = hx_hz_rows(A, B, ell, m)
    mx, mz = rows_to_masks(Hx), rows_to_masks(Hz)
    n = 2 * ell * m
    return n, rankF2(mx), rankF2(mz), n - rankF2(mx) - rankF2(mz)


if __name__ == "__main__":
    import json, re, sys
    cat = json.load(open(sys.argv[1] if len(sys.argv) > 1 else
                         "qcode-discovery/results/ilp_catalog.json"))
    ok = bad = 0
    for group, recs in cat.items():
        for r in recs:
            A = [tuple(t) for t in r["A"]]
            B = [tuple(t) for t in r["B"]]
            n, rx, rz, k = k_of(A, B, r["ell"], r["m"])
            claim = r.get("k")
            match = (claim is None) or (k == claim)
            ok += match
            bad += (not match)
            if not match:
                print(f"MISMATCH {group} {r['label']}: computed k={k}, catalog k={claim}"
                      f" (n={n} rx={rx} rz={rz})")
    print(f"k cross-check: {ok} match, {bad} mismatch")
