# Complete `k`-stratified catalogues for four cyclic weight-three fibres

## Claim, domain, and status

This constructor result closes one finite classification task for the declared
cyclic two-block grammar.  For each

```text
N in {35,45,63,105},
```

the raw domain is every ordered pair `(A,B)` of three-element subsets of
`C_N`.  The equivalence group is exactly

```text
G_N = C_N^2 semidirect (U(N) x C_2),
```

acting by independent translations, one common unit multiplier, and block
exchange.  These are recipe classes, not classes under arbitrary CSS,
qubit-permutation, or local-Clifford equivalence.  Because all four orders are
odd, every class has the exact parameter label

```text
k = 2 deg gcd(a,b,z^N-1).
```

The natural Tanner presentation is labelled connected exactly when the support
differences generate `C_N`, equivalently when the normalized supports satisfy
`gcd(N,supp(a),supp(b))=1`.

One traversal of each independently audited canonical quotient labels every
class with exact `k`, connectivity index, individual support divisors, a common
divisor, and a unit-orbit-invariant divisor-pair signature.  The four complete
catalogues contain 43,086 classes.  Their status is **independently audited and
accepted on 2026-08-26** (`docs/CYCLIC_WEIGHT3_K_STRATA_INDEPENDENT_AUDIT.md`):
every record was reproduced field by field by a route using literal rotation
necklaces, generator-closure unit orbits, and cyclotomic-coset factor incidence
instead of anchor normalization, full-unit minimization, and polynomial Euclid.
This remains exhaustive computation on four finite fibres, supported by the
previously audited uniform quotient theorem.  It is not a theorem about
uncomputed `N`, not a distance catalogue outside the four previously certified
target strata, and not a quality predictor.

## Complete finite spectra

Entries below are `k:number of recipe classes`.  The connected and disconnected
columns partition the complete quotient in each row.

| quotient | full classes | connected `k` strata | disconnected `k` strata |
|---|---:|---|---|
| `C35` | 770 | `0:735, 6:28` | `0:6, 30:1` |
| `C45` | 2,203 | `0:1958, 4:132, 8:23` | `0:74, 12:10, 20:2, 24:3, 60:1` |
| `C63` | 5,761 | `0:5039, 4:308, 6:174, 10:10, 12:14, 16:2` | `0:179, 12:20, 18:8, 28:2, 30:2, 36:1, 54:1, 84:1` |
| `C105` | 34,352 | `0:30182, 4:1764, 6:991, 8:289, 10:56, 12:16, 14:9, 24:1` | `0:970, 18:28, 20:20, 28:10, 30:8, 50:2, 56:3, 60:1, 90:1, 140:1` |

Thus the connected realizable-`k` spectra are, exactly on these finite fibres,

```text
C35:  {0,6}
C45:  {0,4,8}
C63:  {0,4,6,10,12,16}
C105: {0,4,6,8,10,12,14,24}.
```

This immediately separates lattice-size effects from within-lattice logical
sector variation for the next design-law search.  It also exposes exact,
nonmonotone forbidden regions on these finite fibres.  For example, connected
`C105` realizes `k=24` while `k=16,18,20,22` are absent, even though
disconnected classes exist at `k=18,20`; connected `C63` realizes `k=10,12,16`
but not `k=8,14`.  A simple threshold law in `k` is therefore already
falsified.  A future uniform law must explain these gapped spectra or fail on a
held-out quotient.

## Completeness and orbit certificates

The exact full-domain envelopes are reproduced:

| `N` | raw ordered words | necklaces | staged pairs | final classes | representative hash matches audit |
|---:|---:|---:|---:|---:|:---:|
| 35 | 42,837,025 | 187 | 17,578 | 770 | yes |
| 45 | 201,356,100 | 316 | 50,086 | 2,203 | yes |
| 63 | 1,576,963,521 | 631 | 199,396 | 5,761 | yes |
| 105 | 35,141,251,600 | 1,786 | 1,595,791 | 34,352 | yes |

For every individual class the catalogue retains:

- its canonical support pair and a deterministic, generally noncanonical raw
  staged witness;
- an explicit `(unit, swap, left shift, right shift)` action taking the raw
  witness to the representative, with forward and inverse replay flags;
- the exact two support divisors, common divisor, `k`, connectivity index, and
  coordinate-invariant divisor-orbit signature;
- translation stabilizers, the translation/exchange orbit and stabilizer, the
  residual unit orbit and stabilizer, and the full recipe orbit and stabilizer.

For each class both

```text
residual unit orbit * residual unit stabilizer = |U(N)|
full recipe orbit * full recipe stabilizer = 2 N^2 phi(N)
```

hold.  Summing residual orbit sizes gives the staged-pair count in each row;
summing full orbit sizes gives `binom(N,3)^2`.  Hence the labelled strata are
not merely a list of representatives: they carry an exact partition
certificate at both reduced and raw levels.  Deterministic hashes commit to
every staged input and to its representative assignment.

## Frozen catalogue recovery

The connected target strata reproduce all four pre-existing exact-distance
catalogues as exact sets, not only as counts:

| quotient | target | recovered classes | exact distance distribution | representative-set result |
|---|---:|---:|---|---|
| `C35` | `k=6` | 28 | `2:2, 4:5, 6:8, 8:13` | identical hash |
| `C45` | `k=8` | 23 | `2:2, 4:3, 6:14, 8:4` | identical hash |
| `C63` | `k=16` | 2 | `2:1, 4:1` | identical hash |
| `C105` | `k=10` | 56 | `2:2, 4:2, 6:3, 8:2, 10:34, 12:5, 14:5, 16:3` | identical set and hash |

The released and published `[[210,10,16]]` recipes are both recovered and
remain distinct recipe classes.  Exact distance is copied only from these 109
frozen target records; the remaining 42,977 classes receive no inferred
distance.  They are newly parameter-labelled classes in this repository, not
claims of novelty against the literature.

## Falsifiers and verdict

The preregistered falsifiers were: a duplicate or missing class; failure to
partition either the staged or raw domain; an orbit--stabilizer failure; a
forward or inverse reconstruction failure; a non-invariant `k`, connectivity,
or divisor-orbit label; disagreement with an independently audited full-space
count or representative hash; or disagreement with any frozen target
catalogue.  None fired.

The exact finite classification claim therefore passes as a constructor
result, and the subsequent independent audit accepted it with no falsifier
fired, adding a literal Tanner-component check on all 43,086 classes, a `GF(2)`
rank cross-check of `k` on 10,808 classes, six held-out literal raw-word
sweeps, and seven negative controls.  Gate G4 is **closed**.
G5--G8 do not change: these catalogues supply the cross-parameter substrate for
a design law but do not themselves predict distance, circuit distance,
locality, or another quality objective.

## Artifacts and reproduction

- preregistration:
  `evidence/PREREGISTRATION_cyclic_weight3_k_stratified_catalogues.md`;
- implementation: `scripts/catalogue_cyclic_weight3_k_strata.py`;
- summary: `evidence/cyclic_weight3_k_stratified_catalogues.json`;
- 43,086 per-class records:
  `evidence/cyclic_weight3_k_stratified_catalogues.jsonl`;
- focused checks: `tests/test_catalogue_cyclic_weight3_k_strata.py`;
- independent audit: `docs/CYCLIC_WEIGHT3_K_STRATA_INDEPENDENT_AUDIT.md`,
  `evidence/PREREGISTRATION_cyclic_weight3_k_strata_independent_audit.md`,
  `scripts/audit_cyclic_weight3_k_strata.py`,
  `evidence/cyclic_weight3_k_strata_independent_audit.json`,
  `tests/test_audit_cyclic_weight3_k_strata.py`.

```bash
python -B scripts/catalogue_cyclic_weight3_k_strata.py
python -m pytest -q -o addopts='' tests/test_catalogue_cyclic_weight3_k_strata.py
```

The generated catalogue SHA-256 is
`be3c7250eead2bee1d7cadaced66919e95b8c33d2b8628312b495493732cef80`.
