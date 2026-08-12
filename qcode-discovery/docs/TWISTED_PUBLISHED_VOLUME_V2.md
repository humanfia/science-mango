# Published-volume generalized-toric experiment

This is a fresh, checkpoint-incompatible Stage-1 experiment selected after
the four-round `twisted-torus-v1` audit. It is not a claim that a new algebraic
code family has been invented. It is a distinct, narrower ansatz and a new
geometry domain inside the generalized-toric / bivariate-bicycle family:

\[
A=1+x+x^a y^b,\qquad B=1+y+x^c y^d.
\]

The mutable program proposes only `(a,b,c,d)`. The immutable wrapper owns the
HNF quotient, candidate quotas, normalization, known controls, and the
explicitly contracted geometry coverage.

## Why this experiment was selected

The source audit sealed 24 distinct formal candidates over four rounds. All
24 were terminal negative, with no exact result, no UNKNOWN, and no win. Of
the 20 candidates that entered through a replayed `d >= 5` lower-bound lane,
17 (85%) subsequently received a trusted `d <= 8` upper-bound witness. That
crossed the predeclared 80% low-weight-failure threshold. The machine decision
therefore selected broader, paper-backed geometry coverage instead of a
full-pool `w <= 6 -> 8 -> required-1` ladder. Reviewer text was advisory and
did not vote on this decision.

## Geometry contract

The immutable target volumes are:

```text
105, 124, 126, 127, 132, 147, 170
```

Every ordered non-degenerate factor shape is scanned at every canonical twist.
The prime-volume thin lane is deliberately bounded to the paper representative
`(ell,m,q)=(1,127,25)`. This experiment does **not** claim that omitted q
values are equivalent, nor that the thin prime-volume geometry is exhaustively
covered. Volume 144 was completely covered by the preceding run, so only
`(12,12,0)` remains as a continuity control.

The immutable preflight contains 44 shapes (41 target shapes plus three Pareto
controls), 822 contracted twist strata, and 3,627 deterministic seed
constructions. Each stratum has at least three matrix-valid construction rows;
the normal static filter may still reject rows with `k=0`.

The quick-fitness probes are:

```text
(12,12), (5,21), (2,62), (5,34)
```

The bounded deep-evaluation representatives are:

```text
(5,21), (2,62), (7,18), (1,127),
(2,66), (12,12), (7,21), (5,34)
```

Together with the three Pareto controls, Stage 2 has 11 deep lanes.

## Published controls and novelty

Eight exact codes reported by Liang, Liu, Song, and Chen are injected as
reachability controls:

```text
[[210,10,16]], [[248,10,18]], [[252,12,16]], [[254,14,16]],
[[264,8,20]],  [[288,12,18]], [[294,10,20]], [[340,16,18]]
```

Their definitions are reconstructed locally and indexed in the known-code
registry. Published distances are metadata with
`locally_exact_proven=false`; they receive no search proof credit and can
never be awarded as novel discoveries. A newly generated candidate must pass
the normal matrix-replay novelty gate and the full proof pipeline.

Source: Liang et al., *Generalized toric codes on twisted tori for quantum
error correction*, arXiv:2503.03827v3.

## Scientific target

The strict scalar target is evaluated with integer arithmetic:

\[
k d^2 > 12n.
\]

BP/OSD outputs are upper bounds and receive no positive proof credit. A win
requires independent exact/certificate replay and a negative match against
the pinned known-code registry.
