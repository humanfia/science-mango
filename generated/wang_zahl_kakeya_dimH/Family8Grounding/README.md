# Family 8 grounding status

## Exact target

The Family 8 endpoint is the theorem-level implication

```lean
theorem mainLemmaOne (beta : Real) :
    KatzTaoProperty beta → FrostmanProperty beta
```

where both predicates are the actual quantified definitions in
`Family8KatzTaoFrostmanPropertiesV1.lean`.  This theorem is **not yet
closed**.  The aggregate deliberately exposes the proved components and the
remaining geometric seams; it does not replace the endpoint by a callback or
an axiom.

## Current restart checkpoint: V588

`Family8Grounding.lean` now imports
`Family8PaperFullCanonicalGroundingV588.lean`.  The committed source closure,
fresh-clone commands, verified boundary, remaining seams, and the two
remaining proof lanes are recorded in
[`../FAMILY8_RESTART.md`](../FAMILY8_RESTART.md).  That file is the
authoritative recovery guide for this branch.

V588 is an additive, exact-green integration checkpoint; it is **not** a proof
of `mainLemmaOne`.  In particular, the Family 7/small-`b` and labelled-slab/
large-`b` producer lanes described in the recovery guide remain open.

## Archived checkpoint narrative: V291

The remainder of this document records the older V291 dependency audit.  It is
kept as historical seam-level context only and must not be used as the current
restart plan.

The then-current additive aggregate was
`Family8PaperFullCanonicalGroundingV291.lean`.  Its exact build completed as
`10718/10718`; every theorem added on the V269--V291 edge reports only
`propext`, `Classical.choice`, and `Quot.sound`, and the placeholder scan of
that edge is empty.  Failed drafts are not imported.

The V291-era shortest dependency graph was:

```text
mainLemmaOne
  <- positive pointwise self-improvement on 0 < beta < gamma <= 1
     (property iteration, right-limit closure, beta=0 and all-Real boundary:
      closed)
  <- fixed ParameterLadder Section 8 endpoint
     (positive fixed decrement and outer-three/middle-ten exponent algebra:
      closed)
  <- actual normalized dividing-scale trichotomy
     |- source-to-tau normalized upper from actual all-scale Frostman: closed
     |- base Frostman -> interval all-scale Frostman from a parent commuting
     |  square and two-sided assigned-parent mass comparison: closed
     |- actual density constructor for that comparison and its adjacent-upper
     |  composition: closed
     |- concrete identity-radius cover base Frostman and parent square:
     |  closed
     |- parent commuting-square for the arbitrary coherent cover used by the
     |  full actual dividing-scale path: OPEN
     |- normalized long witness, canonical buffered cover and numerical
     |  bootstrap: closed after the explicit scalar-loss input
     `- first strict crossing + all earlier barriers -> full-refinement
        source-tau frozen comparable assembly: closed
        `- successor G' / second-long geometric recursion: OPEN
  <- same-object Equation (45) x Equation (46)
     |- upper activeFine=univ, Q-to-P induced average, max-witness count,
     |  exact-assembly product and actual-volume algebra: closed
     |- callback-free common-width fallback with the actual
     |  `(2 * activeCard)^2` cap: closed
     |- one actual MassPopular `(parent,label)` supplies the same selected
     |  `(a,b)` scales to Eq. (45) and adaptive Eq. (46): closed
     |- actual local `MassPopularCrossEq46Budget` from the displayed
     |  full-refinement residual scalar: closed
     |- honest `thickM^(beta/2)` retained explicitly, with canonical
     |  `Delta <= CF*card` and rpow envelope: closed
     |- the actual every-scale Katz--Tao input supplies the finite native
     |  tau-active constant, and card-weighting bounds the complete coefficient
     |  by one explicit negative power of delta: closed
     |- the literal five-parameter packing cap dominates `(b/a)^2`, cancelling
     |  the corresponding bad aspect power without a supplied cap: closed
     |- the actual adaptive inner factor dominates exactly
     |  `tau^(-epsilon/2) * (b/a) * (tau/a)^(2-3*beta)`: closed
     `- retain the lower mass/scale certificate for the selected mass-rich
        label (mere occupancy of every label cannot supply it), then finish
        Proposition 66 composition: OPEN
  <- retained-owner local geometry
     |- actual packing, ambient-volume and packing-card cancellation, common
     |  CubeWeight witness, K/fineMass cancellation and the pointwise actual
     |  local dense-ball density lower bound: closed
     |- exact normalization to
     |  `density*a*b*vol(B_rho) <= 54000*C^3*loss*localMass`: closed
     |- datum-local absorption to `rho^(-absorbExponent)*localMass`: closed
     |- canonical comparison/log-retention coefficient has a datum-uniform
     |  beta-dependent threshold and exact count-exponent reserve: closed
     |- positive retained mass removes the auxiliary left-hand count reserve,
     |  giving the direct `coefficient <= a^-absorb * N^(1-beta/2)` form:
     |  closed
     |- common-cell fine/coarse shaded-union equality and a canonical unit-slab
     |  incidence on the literal cell-restricted fine datum: closed
     |- arbitrary-theta canonical angle rows and exact finite occupancy bound
     |  for every certified slab member set: closed
     |- the nonempty active support, shared fine/coarse/dense-ball point and
     |  containment of every active owner's thickened body in the same
     |  controlled slab thickening: closed
     |- the active certified incidence and actual deduplicated selected-owner
     |  row `P_{theta,S}`, with its card bound and same-container theorem: closed
     |- actual coarse family/shading, active representative and dense-ball
     |  witness for each owner, plus the full angle-occupancy bound: closed
     |- the actual common flat-prism body has an explicit slab-thickening
     |  volume bound, and maximal concentration gives the cross-multiplied
     |  Family 6 cardinal/volume reserve: closed
     |- at the same slab/clustering scale this reserve is linear:
     |  `#P * C^(-3)ab <= 125 * maximalConcentration * theta`, with an
     |  explicit divided count bound and its min with angle occupancy: closed
     `- obtain the missing rowwise owner-fibre mass lower bound (the proved
        carrier-to-owner mass comparison has only the opposite direction): OPEN
  <- Family7/Sticky native-high aggregation
     |- callback-free local dyadic pair-mass upper for every actual high centre:
     |  closed
     |- finite sum over all high centres, charged to the exact source-mass
     |  partition through one explicit maximum coefficient: closed
     `- prove the displayed maximum coefficient is a paper-small scale loss
        and splice it into the Sticky union branch: OPEN
  <- generalized-Frostman
     |- B2 support/eighth-normalization/fresh selection/conflict, density/base
     |  budgets and canonical same-object frozen third-factor use: closed
     |- copied B2-to-normalized-B1 construction and genuine property-level
     |  quantifier transport to the improved source RHS: closed
     |- datum-uniform automatic repetition bound and a callback-free sharp
     |  power cap for `fixedJohnFrostmanTransportScalar`: closed
     |- a genuine max-threshold selector removes the degree-15 catalogue sum,
     |  lowering the greedy-loss exponent from 17 to 2: closed
     `- cancel the remaining `rho^(-2)` tube-volume loss through the retained
        copy/source mass product so it fits the arbitrary epsilon budget: OPEN
```

This live graph supersedes older checkpoint prose below when the two differ;
the older sections remain as proof-history records.

## Historical dependencies, Families 1–11

The numbers below record proof-history roles, not artificial Lean imports.

| Family | Relationship to Family 8 |
| --- | --- |
| 1–3 | Historical reductions preceding the current checked-in grounding. There is no direct `Family1`, `Family2`, or `Family3` import in the present Family 8 closure. |
| 4 | Supplies the actual extremal tube/shading model used by `ActualTubeDatum` through `Family4GlobalExtremalUpstream`. |
| 5 | Historical combinatorial input; no separately named direct import remains in the current Family 8 closure. |
| 6 | Supplies convex Frostman constants, affine/volume facts, finite fibre bounds, and the Sticky hierarchy geometry consumed here. |
| 7 | Supplies the fully actual cinematic/slab-plank sampled-lens endpoint. Its local output is proved, but the global row-scale/power-cap transport into the Sticky union argument is still open. |
| 8 | This directory: Katz–Tao/Frostman predicates, packing, generalized-scale, all-Frostman, and self-improvement layers. |
| 9–11 | Downstream/history families are not logical prerequisites of the current Family 8 import graph. No theorem from them is silently assumed here. |

Thus the actual external import boundary is transparent: `Submission`,
Family 4 upstream files, `Family6Grounding`, and
`FamilyStickyGrounding`.  Family numbering alone must not be read as an
import edge.

## Closed dependency graph

```text
actual tube/shading definitions
  ├─ sphere + common-point packing
  │    ├─ pointwise multiplicity cap
  │    ├─ actual-family-volume cap
  │    └─ K_F(1)
  ├─ generalized KKT quantified property wrapper
  │    ├─ automatic multiplicity and density budgets
  │    ├─ polynomial/John coefficient budgets on actual samples
  │    └─ `KatzTaoProperty.exists_generalizedKatzTao_parameters`
  │       merges the trivial/nontrivial scale branches
  ├─ generalized Frostman random-motion core
  │    ├─ exact finite conflict/John means and grid double counts
  │    └─ automatic mean-to-Frostman producer
  ├─ generalized relative-scale algebra
  │    ├─ nontrivial same-family threshold transport
  │    └─ crude small-scale branch from common-point packing
  ├─ all-Frostman algebra
  │    ├─ union lower ⇒ exact K_F(gamma/2)
  │    ├─ pointwise/card packing ⇒ volume upper
  │    ├─ automatic parent popularity and exact average-mass floor
  │    ├─ division-free parentMass²/sourceMass² union estimates
  │    ├─ automatic parent hull containment in B(0,4), volume ≤ 512
  │    └─ honest coarse source-card fallback with exact delta^-12 loss
  ├─ first long-interval numerical core
  │    ├─ sharp two-sided `X = b²|T_b|` power split
  │    ├─ actual `b ≤ d^(1-epsilon)` scale conversion
  │    └─ explicit ParameterLadder exponent absorption
  ├─ exponent boundary geometry
  │    ├─ explicit parallel-tube grids rule out `beta < 0`
  │    ├─ common-point packing closes `beta ≥ 1`
  │    └─ the all-Real statement reduces transparently to the genuine
  │       `0 ≤ beta ≤ 1` theorem
  └─ abstract exponent iteration + limit closure
```

In particular, `Family8AllFrostmanStickyUnionProducerV1.lean` proves from
the actual Frostman hypothesis

```lean
(delta : ENNReal) ^ eta ≤ D.actualFamilyVolume
(delta : ENNReal) ^ (2 * eta) ≤ D.shading.shadingMass
```

and no longer assumes `1 ≤ D.actualFamilyVolume`.
`Family8StickyParentPopularCanonicalUnionV1.lean` then removes the old
restricted-mass and fibre-cardinality callbacks: the literal source mass
gives parent-mass positivity, the exact average floor gives a
`parentMass²` estimate, and the source-card cube bounds every finite fibre.
Its final actual union theorem is conditional only on the explicit scalar
budget

```lean
stickyPopularCardCubeFactor S katzTaoError ≤ delta ^ (-zeta)
```

The parent-hull term is now automatic: `Family8StickyParentHullVolumeBoundV1.lean`
puts the full active-parent hull in `B(0,4)` and bounds its volume by `512`.
`Family8StickySourceCardFallbackV1.lean` also proves the completely explicit
fallback

```lean
stickyPopularCardCubeFactor S katzTaoError
  ≤ C0 * katzTaoError * delta ^ (-12)
```

with a proved finite constant `C0`.  The fixed exponent loss `12` is too
large for the intended small-loss bootstrap.  Replacing that global card
cube by a local multiscale/popular-mass loss is the precise remaining Sticky
seam; it is not an equivalent union-lower-bound callback.

## Open dependency graph

```text
KatzTaoProperty beta
  ├─ OPEN: complete generalized-Frostman B2-normalization → B1/property
  │        transport
  ├─ OPEN: connect the actual dividing-scales decomposition
  ├─ OPEN: connect the Family 6 flat-prism theorem
  ├─ OPEN: replace the Family7/Sticky global delta^-12 card-cube fallback
  │        by the required local multiscale/popular-mass small loss
  ├─ OPEN: connect the completed first long-interval numerical core to the
  │        actual dividing-scale/KKT/KF geometric bootstrap
  ├─ OPEN: second long-interval exponent bootstrap
  └─ OPEN: prove the substantive central theorem on `0 ≤ beta ≤ 1`
           (the boundary reduction outside this interval is closed)
           ↓
     FrostmanProperty beta
```

The parent-hull constant and the coarse global-card fallback are closed.
The remaining Sticky seam is to avoid paying the proved but unusable fixed
`delta^-12` loss: the local hierarchy/popular selection must retain enough
mass while charging only the paper-small scale loss (together with the
actual Katz--Tao error).  Passing that small-loss estimate, the final union
lower bound, or the final multiplicity estimate as a new structure field
does not count as completion.

The generalized-KKT line now contains genuine finite sampling, automatic
sampling multiplicity/density budgets, polynomial/John coefficient
budgets, and the branch-free quantified theorem
`KatzTaoProperty.exists_generalizedKatzTao_parameters`.  The generalized-Frostman line has exact
finite means and conflict grids; its next seam is the B2-to-B1 transport.

The all-Real boundary is now an honest mechanical reduction rather than an
open geometric seam.  `Family8KatzTaoNegativeExponentV1.KatzTaoProperty.nonneg`
rules out negative exponents using an explicit admissible parallel-tube grid,
and `frostmanProperty_of_one_le` handles exponents at least one.
`Family8AllRealBoundaryReductionV1.mainLemmaOne_of_unitInterval` therefore
derives the all-Real statement from an explicitly supplied theorem on
`0 ≤ beta ≤ 1`.  It does **not** prove or hide that central theorem, so
`mainLemmaOne` remains open.
It introduces no new structure field or theorem-level axiom.

## Completion gate

Family 8 is complete only when all of the following hold:

1. **Closed:** the generalized-KKT sampling/polynomial estimates and the
   trivial/nontrivial scale branches are merged by
   `KatzTaoProperty.exists_generalizedKatzTao_parameters`.
2. The generalized-Frostman (`genKF`) B2-normalization is transported to
   the B1/property statement with its actual random choices and scale losses.
3. The actual dividing-scales decomposition is connected, without replacing
   its conclusion by a callback.
4. The Family 6 flat-prism input is connected to the relevant Family 8
   multiscale branch.
5. A theorem replaces the proved coarse Sticky `delta^-12` card-cube bound
   by the required local multiscale/popular-mass small loss from existing
   Family 6–7 actual data, with no equivalent callback.
6. The first and second long-interval bootstrap rounds are both proved with
   their explicit parameter ladders.
7. The substantive theorem is proved throughout `0 ≤ beta ≤ 1`; the already
   closed transparent boundary reduction then upgrades it to the exact
   endpoint `mainLemmaOne (beta : Real)`.
8. `lake build Family8Grounding`, direct source compilation, placeholder
   scans, and `#print axioms` show no `sorryAx`, `admit`, custom
   `axiom`, or opaque replacement for an open seam.
