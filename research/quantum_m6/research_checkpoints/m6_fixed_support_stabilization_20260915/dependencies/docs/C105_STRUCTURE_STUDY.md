# Hidden structure of the `[[210,10,d]]` cyclic two-block codes

> **Distances re-certified (2026-08-25).** The 56 recipe classes and the
> algebraic decomposition were never in doubt; the connected-cluster distance
> catalogue was, and it has been replaced. All 56 classes now have exact
> distances computed without a claimed input, and 38 of the revoked labels were
> too large. Section 5 has been rewritten around the true three-member
> maximal cohort. See
> [`C105_EXACT_DISTANCE_CATALOGUE.md`](C105_EXACT_DISTANCE_CATALOGUE.md) and the
> audit that forced the recomputation,
> [`C105_CIRCUIT_DISTANCE_LABEL_INDEPENDENT_AUDIT.md`](C105_CIRCUIT_DISTANCE_LABEL_INDEPENDENT_AUDIT.md).

## Scope

This study classifies every connected weight-`(3,3)` two-block translation recipe on 105 sites, up to independent translations of the two supports, a common automorphism of `C_105`, and exchange of the two blocks. It studies the mathematics before attempting additional exact-distance certification.

The exhaustive enumeration contains:

- 1,786 translation classes of three-element supports;
- 2,544 connected support pairs with `k=10`;
- 56 elementary recipe-equivalence classes;
- two reciprocal algebraic sectors, containing 28 raw classes each before inversion identifies their structure.

## 1. Every index-105 quotient is cyclic

Because `105 = 3*5*7` is square-free, every abelian group of order 105 is cyclic. Consequently, every two-dimensional quotient lattice with 105 sites can be rewritten as

```text
C_105 = <z | z^105 = 1>,
R = GF(2)[z]/(z^105-1).
```

Different twisted lattice bases are coordinate systems on the same finite group. This removes lattice-basis duplication before comparing constructions.

## 2. The logical dimension comes from order-3 and order-7 sectors

The released construction has common annihilator

```text
h(z) = z^5 + z + 1
     = (z^2+z+1)(z^3+z^2+1).
```

The published construction has the reciprocal annihilator

```text
h*(z) = z^5 + z^4 + 1
      = (z^2+z+1)(z^3+z+1).
```

The quadratic factor is the nontrivial order-3 Fourier sector. The reciprocal cubic factors are the two Frobenius orbits of primitive order-7 roots. Therefore both constructions select one degree-2 sector and one degree-3 sector, giving

```text
k = 2 deg(h) = 2(2+3) = 10.
```

This explains the common `k=10` without referring to their Tanner graphs or distance.

## 3. Chinese-remainder picture: topology versus lift

The group decomposes as

```text
C_105 ~= C_3 x C_5 x C_7 ~= C_21 x C_5.
```

The annihilator `h` sees the `C_3` and `C_7` coordinates but contains no order-5 factor. Thus the `C_21` projection determines the logical-sector algebra, while the `C_5` coordinate acts as a five-fold lift that changes the sparse wiring without changing `k`.

For a trinomial `1+z^a+z^b` to be divisible by `h`, its two nonzero exponents modulo 21 must be one of

```text
(1,5), (2,10), (4,20), (8,19), (16,17), (11,13).
```

These six pairs form one Frobenius orbit under exponent doubling modulo 21. The remaining freedom is how the two terms are lifted through the five possible `C_5` coordinates. That lift changes short cycles, expansion, and logical-operator weight while leaving the order-3/order-7 homology fixed.

## 4. A common module normal form

For the 40 recipe classes whose canonical first support is exactly `h`, write

```text
A = h,    B = h q.
```

Then

```text
H_X = h [1 | q].
```

An invertible block shear over the group ring sends `[h | hq]` to `[h | 0]`. Hence `q` does not change the abstract module or homology: all these chain complexes share the same algebraic core. The shear is generally dense and does not preserve Hamming weight, so it does **not** imply that the quantum codes have the same distance or that their sparse Tanner presentations are equivalent.

This separates the structure cleanly:

- `h` determines the logical sectors and `k`;
- `q` determines the sparse embedding and much of the metric behavior;
- the `C_5` lift is a concrete geometric component of `q` that is invisible to `k`.

There is also a useful metric formula. After absorbing the transpose by the inversion `z -> z^-1`, an `X` logical representative can be written as

```text
(u, q*u + t),    t in Ann(h).
```

Adding an `X` stabilizer replaces `u` by `u+h*r`. Therefore the ten logical coordinates split canonically into

```text
[u] in R/(h)       (dimension 5),
t   in Ann(h)      (dimension 5).
```

For a fixed sparse embedding `q`, the distance is the branch metric

```text
min over ([u],t) != (0,0), then over r in R:
    wt(u+h*r) + wt(q*(u+h*r)+t).
```

This formula makes the separation precise: `h` fixes the two five-dimensional logical-coordinate spaces, while `q` controls how difficult it is for a nonzero logical pair to have a sparse physical representative. It also suggests a structural route to distance—study the branch profile of `q`—without beginning with a black-box lower-bound proof.

## 5. The exact distance-optimal cohort

Exact certification gives a maximum distance of 16 attained by exactly three
classes. In the common `A=h` normal form, the certified `B` supports are

| Class | exact `d` | `B` support in `C_105` | `(mod 21, mod 5)` coordinates |
|---|---:|---|---|
| new candidate `{0,11,34}` | **16** | `{0,11,34}` | `(0,0),(11,1),(13,4)` |
| released | **16** | `{0,11,76}` | `(0,0),(11,1),(13,1)` |
| published | **16** | `{0,13,32}` | `(0,0),(13,3),(11,2)` |
| former candidate `{0,10,44}` | 14 | `{0,10,44}` | `(0,0),(10,0),(2,4)` |
| former candidate `{0,29,61}` | 14 | `{0,29,61}` | `(0,0),(8,4),(19,1)` |

All five satisfy:

- `A` is the minimal degree-five annihilator itself;
- `B` has exactly the same annihilator factors and no additional factor of `z^105-1`;
- `q=B/h` is a unit on the complementary Fourier sectors;
- `q` has multiplicative order 4095 on that complement;
- their combined Tanner singular spectra are pairwise different.

None of those properties separates the exact maximizers from the two classes
that fall to 14, so they are necessary at best. The order-4095 property is
weaker still: 33 of the 40 `A=h` classes have it, including classes of exact
distance 10. No structural predictor in this repository currently reproduces
the certified distance ordering.

The certified distribution is `2:2`, `4:2`, `6:3`, `8:2`, `10:34`, `12:5`,
`14:5`, `16:3`, against the revoked `2:2`, `4:2`, `8:3`, `10:7`, `12:10`,
`14:27`, `16:5`. The fibre is far more concentrated at low distance than the
revoked labels suggested: 34 of 56 classes are exactly `[[210,10,10]]`. See
[`C105_EXACT_DISTANCE_CATALOGUE.md`](C105_EXACT_DISTANCE_CATALOGUE.md).

## 6. The constructions are voltage-graph lifts

Projecting `C_105` onto `C_21` turns each construction into a five-fold voltage-graph lift. Every base Tanner edge carries its exponent modulo 5 as a voltage. A base cycle with total voltage zero lifts to five cycles of the same length; a cycle with nonzero voltage winds through all five fibers before closing and becomes five times longer.

This gives a concrete mechanism by which the same base homology produces different sparse geometry. Every one of the five strong recipes has the unavoidable baseline of 189 zero-voltage four-cycles in the 84-node base graph, corresponding to 945 four-cycles after lifting. Four of the five have 840 zero-voltage six-cycles; one has 1,050. The released construction and new candidate `{0,11,34}` also jointly minimize the observed zero-voltage eight-cycle count at 10,836 and have identical third and fourth closed-walk moments, although their full Tanner spectra remain different.

Short-cycle suppression alone is not sufficient for high distance, but the voltage description identifies the right finite mathematical object: classify lift voltages by which short homological relations receive zero total voltage.

## 7. Structural hypothesis

The evidence supports the following working model:

> The reciprocal degree-`2+3` annihilator fixes a common five-dimensional anyon/logical sector, while the order-5 lift chooses a sparse metric embedding of that sector. High-distance realizations occur when the complementary multiplier `q` is algebraically mixing and its lift avoids short additive relations.

This model explains how multiple visibly different sparse codes can share `[[210,10,*]]`: they have the same homology but different systolic geometry. The next mathematical task is to enumerate nontrivial relations in the 42-qubit `C_21` base complex, attach their linear `C_5` voltage conditions, and solve the resulting finite avoidance problem. That could replace solver-based screening with a theorem or a small combinatorial test and directly enumerate every promising lift.

## 8. Possible deployment advantages

All five recipes below have the same first-order hardware cost: 210 physical qubits, weight-six checks, qubit degree six, and a regular two-block translation structure. Only the first three are exact `[[210,10,16]]`. None currently has a proven physical-deployment advantage. The structural proxies are:

| Construction | Zero-voltage 6-cycles | Zero-voltage 8-cycles | second Gram eigenvalue |
|---|---:|---:|---:|
| new `{0,11,34}` (`d=16`) | 840 | 10,836 | **24.934131173** |
| released `{0,11,76}` (`d=16`) | 840 | 10,836 | 24.944271910 |
| published `{0,13,32}` (`d=16`) | 840 | 12,894 | 27.305727611 |
| `{0,10,44}` (`d=14`) | 1,050 | 13,062 | 25.858856367 |
| `{0,29,61}` (`d=14`) | 840 | 12,012 | 26.417432833 |

Lower second eigenvalue and fewer short zero-voltage cycles are potentially favorable for iterative decoding. Note that these proxies do not track exact distance: `{0,29,61}` has the same zero-voltage six-cycle count as the three maximizers yet is exactly `d=14`, and `{0,10,44}` is worse on both cycle proxies than `{0,29,61}` while sharing its distance. On these limited proxies, `{0,11,34}` is the strongest of the three certified maximizers: it matches the released code's short-cycle counts and is marginally better on the expansion proxy. This is a hypothesis, not deployment evidence. The released recipe also has an elementary recipe stabilizer of order two, while the other four have trivial stabilizers within the tested translation/automorphism/block-swap action; additional symmetry may be useful for implementation or logical gates.

A deployment claim requires further comparisons:

1. optimize the two-dimensional lattice basis and measure physical interaction lengths;
2. embed the Tanner graph into a target coupler graph and count routing/SWAP overhead;
3. synthesize check-measurement circuits and compare depth, parallelism, and ancilla demand;
4. analyze hook errors and correlated-fault propagation;
5. benchmark BP/OSD and other decoders under identical phenomenological and circuit-level noise;
6. determine automorphism-induced logical gates and scheduling symmetries;
7. compare only at certified equal distance; the exact catalogue now supports this for the three-member `[[210,10,16]]` cohort.

The cyclic support labels alone do not define Euclidean hardware locality, so routing advantages cannot be inferred from them without choosing and optimizing a physical embedding.

## 9. Extension to other parameter sets

The same approach extends naturally to other lengths and logical dimensions. For a target length `n=2N`, begin with the finite abelian translation group `G` of order `N` and its group algebra `GF(2)[G]`. For cyclic `G=C_N`, factor `z^N-1`; for a multivariate quotient, use Smith normal form and Gröbner bases. Select a common annihilator `h` whose factor degrees give the desired

```text
k = 2 deg(h)
```

in the cyclic semisimple case. Then enumerate sparse pairs `A=h*a`, `B=h*b`, quotient them by recipe symmetries, and separate the problem into:

- **algebraic sector selection:** choose `h` to determine `k` and topological content;
- **metric embedding selection:** choose the quotient multipliers and voltage lifts to improve locality, cycle structure, expansion, and logical branch profiles.

When `N=N_base*N_lift` with coprime factors, use

```text
C_N ~= C_N_base x C_N_lift
```

and regard every construction as a voltage lift of a smaller base complex. Enumerate short nontrivial base relations, calculate their lift voltages symbolically, and reject voltage assignments that leave undesirable relations at zero. Only the small surviving set should receive decoder simulations and exact-distance certification.

This produces a reusable search pipeline:

1. enumerate group/lattice types using Smith normal form;
2. factor the group algebra and choose annihilator sectors for target `k`;
3. enumerate sparse support generators modulo automorphisms;
4. parameterize coprime-factor coordinates as voltage lifts;
5. reject disconnected and short-relation lifts algebraically;
6. rank survivors by locality, voltage-cycle, spectral, and branch-profile measures;
7. classify recipe, Tanner, CSS, and local-Clifford equivalence;
8. certify distance only for canonical representatives.

Promising next targets are lengths where `N` has several coprime factors, because they give a small base algebra plus a nontrivial lift space. The existing `[[210,10,*]]` case demonstrates the pattern `N=21*5`; analogous searches can use `N=N_base*p` with a small prime lift `p`, while choosing different irreducible-factor subsets of `z^N-1` to target new values of `k`.

## 10. Generalization standard

The ingredients of this study overlap established group-algebra,
generalized-toric, and graph-lift methods. A general discovery law therefore
requires more than a new support pair or interpretation. The auditable gates in
[`CODE_DISCOVERY_LAW_TRACKER.md`](CODE_DISCOVERY_LAW_TRACKER.md) require exact
search coverage, independently checked enumeration, a theorem extending beyond
`N=105`, and a constructive all-parameter consequence or a sharp no-go result.

## Reproduction

```bash
python -m pytest -q -o addopts='' \
  tests/test_classify_c105.py \
  tests/test_verify_c105_classification.py \
  tests/test_verify_c105_exact_certificates.py
```

These focused checks replay the `56` recipe classes and stored exact-distance
evidence. Fresh lower-bound solver generation is a separate, optional
long-running step.
