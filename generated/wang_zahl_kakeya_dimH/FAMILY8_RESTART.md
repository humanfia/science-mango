# Family 8 proof restart guide

Snapshot date: 2026-09-07 (UTC)

Repository: `https://github.com/humanfia/science-mango`

Checkpoint branch: `codex/family8-v581-restart`

Recovery document:
`https://github.com/humanfia/science-mango/blob/codex/family8-v581-restart/generated/wang_zahl_kakeya_dimH/FAMILY8_RESTART.md`

Checkpoint branch URL:
`https://github.com/humanfia/science-mango/tree/codex/family8-v581-restart`

This branch deliberately records an in-progress proof.  The aggregate target
`Family8Grounding` currently imports checkpoint V588, but V588 is not the
mathematical completion criterion.

## Clone and reproduce the checkpoint

```bash
git clone --branch codex/family8-v581-restart \
  https://github.com/humanfia/science-mango.git
cd science-mango/generated/wang_zahl_kakeya_dimH

# Install/select the pinned Lean toolchain through elan, then fetch packages.
lake update

# Recheck the last integrated checkpoint and its aggregate import root.
lake build Family8Grounding.Family8PaperFullCanonicalGroundingV588
lake build Family8Grounding
```

Record the exact snapshot you resumed from before editing:

```bash
git rev-parse HEAD
git status --short --branch
```

The checkout should be clean.  Do not resume from `master`; use the checkpoint
branch above.

## Final top-level theorem to create and close

The unambiguous Family 8 goal has the following intended signature:

```lean
theorem mainLemmaOne (beta : Real) :
  KatzTaoProperty beta → FrostmanProperty beta
```

There is no declaration named exactly `mainLemmaOne` in this checkpoint yet;
the final integration module must add it after both analytic lanes close.  Do
not treat the signature above as an already buildable declaration.

Its quantified definitions are in
`Family8Grounding/Family8KatzTaoFrostmanPropertiesV1.lean`.  The all-real
boundary reduction is
`Family8AllRealBoundaryReductionV1.mainLemmaOne_of_unitInterval`.  The current
interior-parameter route ultimately goes through
`Family8AllGammaSelectedTrueSplitEtaLongGeometryCommonV3.mainLemmaOne_of_selectedTrueSplitEtaCorrelatedHDatumDSOProvider`.

Both remaining analytic branches must ultimately construct
`SelectedTrueSplitEtaExactSameCoreAutomaticHighEq32PaymentAt`, defined in
`Family8EndpointIdentitySameCoreHighLossAwareEq32IntegrationV1.lean`.  A green
checkpoint import alone does not establish this theorem.

## Last integrated checkpoint: V588

`Family8Grounding.lean` imports
`Family8Grounding.Family8PaperFullCanonicalGroundingV588`.

Reproduce the checkpoint and aggregate from a fresh clone with:

```bash
lake build Family8Grounding.Family8PaperFullCanonicalGroundingV588
lake build Family8Grounding
```

The serial cold-chain validation on the restart machine completed V581 as
12146/12146 jobs, V588 as 12162/12162 jobs, and the aggregate import root as
12173/12173 jobs.

Cached `.olean` files are not committed and are not evidence on a new machine.
The V582--V588 edge was freshly checked on the restart machine with these exact
module builds:

```bash
lake build Family8Grounding.Family8FiniteRigidMotionScaleOnlyElongatedConflictProjectionV1
lake build Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyJointSelectorV1
lake build Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyFullCatalogueCWAV1
lake build Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyRefinementCWAV1
lake build Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyFrostmanCWAV1
lake build Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyTailNumericsV1
lake build Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyAutomaticCopyFrostmanCWAV1
lake build Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyAutomaticCopyBudgetReductionV1
lake build Family8Grounding.Family8CertifiedPlankLabelledSlabL2V1
```

They completed respectively as 9028/9028, 9060/9060, 9064/9064, 9067/9067,
9071/9071, 9061/9061, 9468/9468, 9469/9469, and 9125/9125.  Their terminal
declarations report only the standard dependencies `propext`,
`Classical.choice`, and `Quot.sound`.

V581 already integrated these relevant links:

- `Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyConflictMeanV1`:
  the elongated-conflict mean on the same raw scale-only
  rotation-by-translation outcome type as the John/CWA mean.
- `Family8CertifiedPlankIntersectingNearParallelRowV1`:
  the Appendix-B.2-style intersecting near-parallel row container with side
  vector `[8 * theta, 4, 4]`, exact volume `128 * theta`, and its Katz--Tao row
  mass bound.  This theorem is exact-green in isolation, but its current
  `F_k ⊆ B(0,1)` premise does **not** bind directly to the fixed-`W`
  normalized outer family: the available normalization only puts that family
  in a scalar-dilated unit ball, and the dilation factor need not be at most
  one.  Do not silently assume the missing unit-ball premise.
- `Family8WinnerSideJointBucketLargeBWeightedOverlapCrossConsumerV1`:
  the weakest whole-cross payment consumer.  It no longer requires the
  stronger common `innerResidual` factorization and directly produces the
  fixed-witness large-`b` conclusion.

V582 through V588 add the following verified links:

- `Family8FiniteRigidMotionScaleOnlyElongatedConflictProjectionV1` converts
  uniform internal elongated-body loads into the actual copied-anchor
  conflict-card bound without admissibility, `BoundAt`, or
  essential-distinctness premises.
- `Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyJointSelectorV1`
  exposes one common `omega` controlling every fixed-John catalogue tail and
  the actual conflict-cardinality cap.  The internal elongated catalogue is
  not leaked through the public endpoint.
- `Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyFullCatalogueCWAV1`
  turns that fixed-John tail into the cardinal-normalized Convex Wolff axioms
  for the full normalized indexed rigid-copy family.
- `Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyRefinementCWAV1`
  feeds the conflict cap to the fresh greedy selector and restricts the full
  CWA certificate to the same nonempty admissible refinement.  Its output also
  carries retained cardinality and shading mass, Katz--Tao control, and the
  source-to-selected average-multiplicity comparison.
- `Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyFrostmanCWAV1`
  composes that exact selected object with the honest B2 Frostman connector.
  Under explicit density and base budgets, it returns the final source
  Frostman multiplicity estimate while retaining the same CWA certificate.
- `Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyTailNumericsV1`
  supplies separate canonical logarithmic John/conflict thresholds and proves
  the exact asymmetric two-family tail-room inequality from factor-two
  reserves.  The tail-room premise is no longer a numerical callback.
- `Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyAutomaticCopyFrostmanCWAV1`
  fixes the repetition count to the ceiling of the eighth-normalized source
  canonical Frostman constant.  It proves positivity, the factor-two copy
  bound, and the corresponding selected-card upper bound while retaining the
  same selected Frostman/CWA object.
- `Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyAutomaticCopyBudgetReductionV1`
  uses that factor-two bound to remove the integer copy count from both
  product-mean budgets and cancels it exactly from the Frostman base budget.
  The remaining conditions are source-level scalar inequalities.
- `Family8CertifiedPlankLabelledSlabL2V1` closes the exact-level labelled-slab
  row calculation: its certified row mass estimate combines with the
  inverse-sine factor and cancels the B.2 thickness at one thresholded level.

The reduced source product-mean/base inequalities and the density budget are
still explicit inputs.  Paying them and the remaining greedy/card/small-power
factors into the fixed-geometry Family 7 endpoint is open.  Family 8 is
therefore **not closed** at V588.  In particular, the full Appendix B.3
dyadic aggregate and its whole-cross producer remain open.

## Verified Lane B boundary

`Family8CertifiedPlankLabelledSlabL2V1.lean` is exact-green and imported by
V588.  It proves the thresholded exact-level row estimate and the
inverse-sine/B.2-thickness cancellation.  It does **not** yet supply the
intersection-anchored local row binding, the full Appendix B.3 dyadic
aggregate, or the whole-cross producer required by the large-`b` endpoint.

## Shortest continuation plan

Run at most two semantic proof families in parallel: the Family 7/small-`b`
lane and the labelled-slab/large-`b` lane.  Multiple reviewers or compilers may
work inside a lane, but each source file must have one owner.

### Lane A: Family 7 / small-`b`

The conflict projection, common selector, full copied CWA, and fresh selected
refinement, Frostman, tail-numerics, and automatic-copy connectors are
exact-green in V588, together with the automatic-copy budget reduction.
Continue from
`scaleOnlyCanonicalCopy_refinement_CWA_frostman`; do not reconstruct those
eight steps through the older independent-choice interfaces.

1. Discharge the two reduced source-level John/conflict product-mean budgets,
   plus the reduced Frostman base and density budgets, using the V588 scalar
   adapters.
2. Pay the remaining greedy/card/small-power scalar factors needed for the
   fixed-geometry Family 7 `BoundAt` and selected outer Equation (45).  The
   V588 modules deliberately do not assert these numerical payments.
3. The endpoint still requires the exact chosen-outer geometry and Section 8
   power budgets in
   `Family8WinnerSideJointBucketEndpointPackedEq32LossAwarePaymentV1`.

### Lane B: labelled slab / large-`b`

The exact-level inverse-sine/B.2-thickness cancellation is green in V588.
Continue from that verified boundary:

1. Replace the unusable global-unit-ball binding by an intersection-anchored
   local row lemma.  For two certified `a x b x 1` boxes sharing a point, the
   intersection controls the long coordinate; a `[8 * theta, 8, 8]` test box
   (volume `512 * theta`) is the intended safe target and removes the false
   `hunit` premise.
2. Add the intersection-supported row weighted-overlap majorant and the full
   dyadic Appendix B.3 aggregate.  Do not fall back to a global hull,
   `carrierFloor`, or the trivial `Q = N` estimate.
3. Prove the final small-power scalar directly in the whole-cross form
   `WinnerSideLargeBWeightedOverlapWholeCrossPaymentAt`.  Do not split it
   through an auxiliary common `innerResidual`; reviewer audit showed that is
   strictly stronger than the downstream endpoint needs.
4. Apply
   `winnerSide_largeB_weightedOverlap_productAtFixedW_of_wholeCrossPayment`,
   followed by the existing loss-aware Equation-(32) consumer.

The small- and large-`b` lanes then join at the same high-payment/top-level
chain leading to `mainLemmaOne`.

## Verification and honesty gates

For every newly closed module, run both the direct file check and the exact
Lake target where useful:

```bash
lake env lean Family8Grounding/<File>.lean
lake build Family8Grounding.<Module>
```

Before declaring Family 8 complete:

1. Build the final canonical checkpoint and `Family8Grounding` from a clean
   checkout.
2. Complete a final integration module that declares `mainLemmaOne`, and build
   that module rather than only the aggregate import file.
3. Search all newly added or modified source files for placeholders:

   ```bash
   grep -nE '\bsorry\b|\badmit\b|^[[:space:]]*(axiom|opaque)\b' \
     Family8Grounding/*.lean
   ```

   Inspect hits; comments and documentation are not proof terms, but any
   `sorryAx` dependency is a failure.
4. Keep terminal `#print axioms` checks and require only
   `propext`, `Classical.choice`, and `Quot.sound`.
5. Run `git diff --check`, review the exact staged file list, commit, and push
   the final branch to the `science-mango` remote.

## Repository hygiene

The original working tree contained thousands of historical scratch files and
unrelated experiments.  This checkpoint is intended to include the local Lean
source import closure rooted at `Family8Grounding`, the project configuration,
and this guide.  Do not assume unrelated untracked files from the original
machine were part of the proof.  Continue to use selective staging and never
discard user-owned changes with `git reset --hard` or `git checkout --`.
