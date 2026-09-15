# Exact distance catalogue for the 56 `C_105` recipe classes

> **Re-certified from scratch (2026-08-25).** The earlier connected-cluster
> catalogue is permanently withdrawn: it supplied `dmin=claimed-1` and
> `noscan=1`, so 54 of 56 jobs assumed the bound they were meant to prove. The
> table below replaces it with a certificate that takes no claimed distance as
> input. See
> [`C105_CIRCUIT_DISTANCE_LABEL_INDEPENDENT_AUDIT.md`](C105_CIRCUIT_DISTANCE_LABEL_INDEPENDENT_AUDIT.md)
> for the audit that forced the recomputation.

> **Targeted follow-up audit (2026-08-25).** A separately written
> sequential-counter/CaDiCaL calculation has independently re-proved both
> `d_X` and `d_Z` for the six exact-`d=10` rows and the exact-`d=8` row used by
> the circuit headline. It does not constitute a third full 56-class pass. See
> [`C105_HEADLINE_CIRCUIT_INDEPENDENT_AUDIT.md`](C105_HEADLINE_CIRCUIT_INDEPENDENT_AUDIT.md).

## Result

Every one of the 56 connected weight-`(3,3)` cyclic two-block recipe classes on
`C_105` with `k=10` now has an exact quantum distance.

| exact distance | recipe classes |
|---:|---:|
| 2 | 2 |
| 4 | 2 |
| 6 | 3 |
| 8 | 2 |
| 10 | 34 |
| 12 | 5 |
| 14 | 5 |
| **16** | **3** |
| **total** | **56** |

The maximum is 16 and it is attained by exactly three classes, all with
`A={0,1,5}`:

```text
B={0,11,34}   (previously unreported)
B={0,11,76}   (released construction)
B={0,13,32}   (published construction, Liang et al.)
```

`C105_CODE_INEQUIVALENCE.md` proves these three are pairwise inequivalent even
under arbitrary qubit permutations combined with independent one-qubit Clifford
operations, so the exact `[[210,10,16]]` cohort of this fibre has exactly three
members.

## What changed against the revoked labels

The revoked labels were valid *upper* bounds — each came with a replayed
logical witness — so no exact distance could rise. Thirty-eight of the 56 were
strictly too large:

| claimed | exact | classes |
|---:|---:|---:|
| 2 | 2 | 2 |
| 4 | 4 | 2 |
| 8 | 6 | 2 |
| 8 | 8 | 1 |
| 10 | 6 | 1 |
| 10 | 10 | 6 |
| 12 | 10 | 9 |
| 12 | 12 | 1 |
| 14 | 8 | 1 |
| 14 | 10 | 19 |
| 14 | 12 | 4 |
| 14 | 14 | 3 |
| 16 | 14 | 2 |
| 16 | 16 | 3 |

Two of the five previously claimed maximizers, `B={0,10,44}` and `B={0,29,61}`,
are exactly `d=14`. The claim of a five-member `[[210,10,16]]` cohort is
therefore falsified. The published `B={0,13,32}` representative is confirmed at
exactly 16, which independently reproduces the distance reported in
[PRX Quantum 6, 020357 (2025)](https://journals.aps.org/prxquantum/abstract/10.1103/rmy6-9n89).

## Certificate method

Let `sigma` be the cyclic translation `z` acting simultaneously on both blocks.
It permutes the rows of `H_X` and of `H_Z`, so it preserves both row spaces and
`ker H_Z`, maps nontrivial `X` logicals to nontrivial `X` logicals, and
preserves weight. Every nonzero logical therefore has a translate in exactly one
of two disjoint, jointly exhaustive cases:

1. **left block empty.** Then `A^T w = 0`, so `w` lies in a small annihilator
   (dimension 5 for every class here). All `2^5-1` nonzero vectors are
   enumerated and tested for nontriviality.
2. **left block nonempty.** Some translate occupies left site `0`. This is
   imposed as `x_0 = 1` and the resulting integer program is solved to *proved*
   optimality by `scipy.optimize.milp`/HiGHS with `mip_rel_gap=0`.

`d_X` is the minimum over the two cases. Cyclic inversion followed by block
exchange maps `H_X` onto `H_Z`, so `d_Z = d_X` and the value is the quantum
distance. The anchor is what makes the calculation tractable: unanchored HiGHS
on `B={0,11,34}` still had a dual bound of 6 after 600 s, whereas the anchored
program proved optimality at 16 in 613 s.

Every lower bound is then re-proved by a logically distinct route. A CNF that
asks for a nontrivial `X` logical of weight at most `d-1` is refuted by
`python-sat`/glucose42 under both translation anchors, escalating to the ten
disjoint first-nonzero logical-syndrome sectors when a whole-anchor refutation
does not finish. All 112 refutations succeeded without sector splitting; none
returned satisfiable and none timed out. Their cost rises steeply with the
bound: at most 1.4 s at weight 9, 7.1 s at weight 11, 138 s at weight 13, and
264–718 s at weight 15.

The replay in `scripts/verify_c105_exact_distance_anchored.py` rebuilds the CSS
matrices, ranks, logical dimension, Tanner connectivity, and X/Z duality from
the supports alone; re-runs the left-empty enumeration; replays each witness
against the reconstructed matrices; requires that the anchored branch and bound
proved optimality; requires full anchored SAT coverage at `d-1`; and checks
every exact distance against the independently replayed weight-15 SAT witnesses
that predate this work.

## Artifacts

- `evidence/c105_exact_distance_anchored.jsonl`: 56 anchored certificates;
- `evidence/c105_exact_distance_sat_lower_bounds.jsonl`: independent SAT refutations at `d-1`;
- `evidence/c105_exact_distance_anchored_verification.json`: fail-closed replay;
- `data/c105_k10_exact_catalogue.jsonl`: canonical recipe records with exact distances;
- `data/c105_k10_exact_catalogue_summary.json`: counts and source hashes;
- `evidence/c105_exact_distance_m4ri.jsonl`: the revoked certificates, retained as provenance.

## Reproduction

```bash
python -B scripts/exact_distance_c105.py --jobs 56 --time-limit 5400
python -B scripts/lower_bound_c105_sat_ladder.py --jobs 48
python -B scripts/verify_c105_exact_distance_anchored.py
python -B scripts/build_c105_exact_catalogue.py
python -m pytest -q -o addopts='' tests/test_exact_distance_c105.py
```

Neither stage reads a claimed distance. The SAT ladder reads only the value to
be refuted below, which is the statement being checked.
