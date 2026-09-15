# A rigorous roadmap for discovering laws of sparse cyclic quantum codes

> Current update (2026-09-15): M5 is adopted at arithmetic-workflow strength. [M6 is complete at scoped symbolic exact-reduction strength](../quantum_m6/README.md), with final dual reviews and executable verification. M7 remains open. The historical frontier discussion below is retained for context.

> **Goal.** Replace raw exhaustive search in a declared family of cyclic
> two-block CSS codes with an exact mathematical workflow that canonicalizes
> every construction, predicts which parameter sectors can occur, constructs
> all admissible classes, and returns all certified optima.
>
> **Evidence boundary.** This repository contains the new structural-law
> effort. It does not duplicate the earlier broad candidate-search repository.
> Small derived `C105` tables are retained only as regression data. Proofs,
> exhaustive finite certificates, independent audits, empirical patterns, and
> conjectures are kept as separate evidence levels.

## 1. What is proved and what is open

| Level | Statement | Status |
|---|---|---|
| A | Every raw support pair has one reversible canonical representative under the declared recipe group. | Proved and independently audited. |
| A | Raw, staged, and final quotient sizes obey exact Burnside formulas. | Proved and independently audited. |
| A | Fixed support weight reduces representative enumeration from `Theta(N^(2w))` to `Theta(N^(2w-2))`. | Proved for the declared grammar. |
| A | Four complete weight-three quotient fibres contain `43,086` labelled recipe classes. | Exhaustively certified and audited. |
| A | The connected `N=105`, `k=10` fibre contains `56` recipe classes; all exact distances are known and five attain distance `16`. | Exhaustively certified in that fibre. |
| B | Factor incidence, birth, and lift data can generate every logical sector for arbitrary admissible parameters. | Partly proved; the uniform order-seven incidence envelope remains open. |
| B | Certified class invariants can be composed into an exact constrained selector. | Proved where every requested label is available. |
| C | A small invariant tuple predicts distance throughout all parameter fibres. | Open; simple candidates have failed held-out transfer. |
| C | The method classifies every CSS or stabilizer code. | False scope; it classifies only the declared recipe family. |

## 2. Exact object being classified

Fix `C_N = Z/NZ` and support weight `w`. A raw recipe is an ordered pair of
`w`-element subsets `(A,B)`. Define

```text
a(z) = sum_{i in A} z^i,
b(z) = sum_{j in B} z^j
```

in `GF(2)[z]/(z^N-1)`. Their circulant matrices give

```text
H_X = [A | B],       H_Z = [B^T | A^T].
```

Circulants commute, so over `GF(2)`, `H_X H_Z^T = AB+BA = 0`.

The declared recipe group is

```text
G_N = C_N^2 semidirect (U(N) x C_2),
```

using independent translations, a common unit multiplier, and block exchange.
Completeness is relative to this exact group.

## 3. Quotient lattice and the `N=105` example

The quotient

```text
Omega = Z^2 / <(0,5),(21,3)>
```

identifies grid points that differ by either generator. The fundamental cell
has area

```text
|det [[0,21],[5,3]]| = 105,
```

so `Omega` has `105` sites. Its Smith form is `diag(1,105)`, hence it is
abstractly `C_105`. Two code blocks give `2*105=210` physical qubits.

```text
       (0,5)+(21,3)
          /-------/
         /  105  /
    (0,5)-------/ (21,3)
         origin
```

This periodic coordinate system defines the code recipe, not a physical-device
layout.

## 4. Code parameters

For the CSS matrices,

```text
n = 2N,
k = n-rank(H_X)-rank(H_Z),
d = minimum weight of a nontrivial logical operator.
```

For odd `N` in this family,

```text
k = 2 deg gcd(a,b,z^N-1).
```

Thus the logical dimension is controlled by shared factor incidence. Distance
is separate: an upper witness constructs a logical operator, while a lower
certificate must exclude every smaller nontrivial logical operator.

## 5. Exact canonical quotient

For a support `S`, let `nu(S)` be its least cyclic translation. Normalize both
supports, sort the pair, apply every common unit, normalize again, and keep the
lexicographically least word `kappa(A,B)`.

The proved statement is

```text
kappa(x)=kappa(y)  iff  x and y are related by G_N.
```

The certificate stores the unit, translations, and swap, so the raw word can
be reconstructed. This proves a quotient theorem, not merely deduplication by
a heuristic fingerprint.

## 6. Exact search collapse

The raw domain contains

```text
R(N,w)=binom(N,w)^2
```

ordered words. If `T(N,w)` is the exact number of translation necklaces, only

```text
P(N,w)=T(N,w)(T(N,w)+1)/2
```

normalized unordered pairs reach the unit quotient. For fixed `w>=2`,

```text
R(N,w)=Theta(N^(2w)),
P(N,w)=Theta(N^(2w-2)),
R/P ~ 2N^2.
```

Burnside terms handle periodic supports and nontrivial stabilizers exactly.

## 7. Complete finite classification

Every weight-three recipe class has been enumerated for

```text
N in {35,45,63,105}.
```

The four catalogues contain `43,086` classes with exact `k`, connectivity,
factor signatures, orbit sizes, stabilizers, and reconstruction witnesses.
They show that realizable connected `k` values form gapped, nonmonotone spectra.
Therefore a simple threshold law in `k` is already falsified.

Finite completeness has three meanings that must not be confused:

1. the canonical quotient is uniform for every finite `N,w`;
2. the four named fibres have actually been enumerated;
3. a closed all-parameter law predicting every stratum is still missing.

## 8. The structural-law hypothesis

Chinese-remainder decomposition separates:

- **factor topology:** which irreducible sectors are shared;
- **birth:** the first connected cyclic order realizing a sector;
- **lift:** how that sector appears at later orders;
- **sparse realization:** which supports realize the incidence pattern;
- **quality:** distance and locality variation after `n,k` are fixed.

The desired theorem should generate every later sector from earlier connected
births plus explicitly characterized exceptions. It must work for an unbounded
parameter class, not merely summarize more finite catalogues.

## 9. Current order-seven theorem frontier

Accepted results include phase-to-binary descent, a covering theorem on the
accepted `A-BO` subfamily, translation-quotient descent of both orientations,
and a split between local label failure and global label coherence.

Two important no-go results sharpen the problem:

1. broad structural assumptions alone admit closure countermodels and cannot
   prove the missing implication;
2. the paired translation-invariant residue tower is isomorphic at every order
   to the one-orientation expansion, so it only rewrites existing information.

The remaining proof must use a genuinely septic property of the actual sparse
selector in one orientation, or an admissible symbolic infinite counterfamily
must falsify the intended birth/lift theorem.

The newest constructor theorem, `SELF`, goes further: it gives a closed form
for the complete local Lucas-selector expansion and argues that every local jet
layer is already determined by the accepted factor data. This would close the
entire local-coefficient route, but it remains pending independent audit. If
accepted, only a non-local relation coupling factors or orientations can supply
the missing septic premise.

## 10. Distance and quality law

The `N=105`, `k=10` fibre proves why `n,k` are insufficient: its `56` classes
have exact distances from `2` through `16`. Five attain `[[210,10,16]]`.

The research target is not to assume distance is a factor label. It is to find
either:

- a proved invariant law on a sharply defined class;
- a certified reduction that makes exact distance cheaper;
- or a no-go theorem showing why a proposed predictor cannot be universal.

Discovery and validation fibres must be frozen separately.

## 11. Certificate boundary

| Evidence | Allowed conclusion |
|---|---|
| Symbolic proof | Holds throughout written hypotheses. |
| Exhaustive finite certificate | Complete only on its frozen finite domain. |
| Logical upper witness | `d` is no larger than the witness weight. |
| Lower-bound certificate | No smaller logical exists within the checked formulation. |
| Constructor result awaiting audit | Candidate theorem, not accepted premise. |
| Correlation | Hypothesis generator, not law. |

Independent auditors should use different orbit generation or polynomial
arithmetic where practical and must include corruption controls.

## 12. Milestones

| Milestone | Acceptance criterion | Status |
|---|---|---|
| M1 canonical quotient | Soundness, completeness, reconstruction, independent audit | Complete |
| M2 search-size law | Exact Burnside count and raw-enumeration controls | Complete |
| M3 varied catalogues | Full partitions across multiple quotient orders | Complete for four weight-three fibres |
| M4 exact target distances | Matching upper/lower evidence for every class in scope | Complete for `109` frozen classes |
| M5 birth/lift law | Every admissible sector generated or proved exceptional | Complete at arithmetic-workflow strength |
| M6 distance law | Proved domain or frozen held-out predictive success | Complete at scoped symbolic exact-reduction strength; see current update |
| M7 universal selector | All certified optima for requested parameters without raw scan | Conditional on M5/M6 |

## 13. Reproducible workflow

```bash
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements-study.txt

python -m pytest -q -o addopts='' \
  tests/test_cyclic_recipe_reduction.py \
  tests/test_quantify_cyclic_search_collapse.py \
  tests/test_catalogue_cyclic_weight3_k_strata.py \
  tests/test_audit_order7_canonical_binomial_padic_translation_quotient.py
```

For a new theorem turn:

1. state the unbounded claim, scope, and falsifier;
2. derive a symbolic reduction before extending any finite catalogue;
3. generate deterministic evidence only when it distinguishes uniform routes;
4. add focused tests and negative controls;
5. obtain an independent audit;
6. update `docs/CODE_DISCOVERY_LAW_TRACKER.md` without weakening the open gate.

The immediate task is to audit `SELF`; do not build further claims on it until
that audit accepts its formal-branch and factorization arguments.

## 14. Failure modes

- Calling recipe classes inequivalent codes without a broader certificate.
- Calling four finite catalogues an all-parameter classification.
- Inferring exact distance from an upper witness.
- Repeating adjacent finite cases after the bottleneck is a uniform implication.
- Reusing the same implementation as constructor and auditor.
- Promoting an audit-pending theorem.
- Fitting and testing a quality law on the same fibre.
- Hiding unknown distance labels by assigning them a convenient value.

## 15. Current progress and relative-path handoff

Current state:

- exact canonical quotient: complete;
- exact fixed-weight search collapse: complete;
- four cross-parameter catalogues: complete;
- `C105`, `k=10` distance fibre: complete;
- uniform factor-incidence birth/lift law: open;
- cross-parameter distance law: open;
- next decisive step: independently audit the local-selector uniformization
  theorem; if accepted, seek a non-local septic relation or an in-scope
  infinite counterfamily.

Primary files:

- `README.md`
- `docs/CODE_DISCOVERY_LAW_TRACKER.md`
- `docs/CYCLIC_TWO_BLOCK_CANONICAL_QUOTIENT_THEOREM.md`
- `docs/CYCLIC_QUOTIENT_INDEPENDENT_AUDIT.md`
- `docs/CYCLIC_SEARCH_COLLAPSE_THEOREM.md`
- `docs/CYCLIC_SEARCH_COLLAPSE_INDEPENDENT_AUDIT.md`
- `docs/CYCLIC_WEIGHT3_K_STRATIFIED_CATALOGUES.md`
- `docs/CYCLIC_WEIGHT3_K_STRATA_INDEPENDENT_AUDIT.md`
- `docs/C105_COMPLETENESS_PROOF.md`
- `docs/C105_EXACT_DISTANCE_CATALOGUE.md`
- `docs/C105_STRUCTURE_STUDY.md`
- `docs/ORDER7_PHASE_BINARY_DESCENT_THEOREM.md`
- `docs/ORDER7_CANONICAL_BINOMIAL_TRANSLATION_QUOTIENT_INCIDENCE_ENVELOPE_INDEPENDENT_AUDIT.md`
- `docs/ORDER7_CANONICAL_BINOMIAL_PADIC_TRANSLATION_QUOTIENT_INDEPENDENT_AUDIT.md`
- `docs/ORDER7_CANONICAL_BINOMIAL_LOCAL_SELECTOR_UNIFORMIZATION_THEOREM.md`
- `scripts/certify_cyclic_recipe_reduction.py`
- `scripts/quantify_cyclic_search_collapse.py`
- `scripts/catalogue_cyclic_weight3_k_strata.py`
- `evidence/cyclic_recipe_reduction_certificate.json`
- `evidence/cyclic_search_collapse.json`
- `evidence/cyclic_weight3_k_stratified_catalogues.json`

All paths are relative to the repository root. The repository can therefore be
moved to another server without editing this handoff.
