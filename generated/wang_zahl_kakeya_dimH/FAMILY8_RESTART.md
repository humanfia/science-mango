# Family 8 proof restart guide

Snapshot date: 2026-09-07 (UTC)

Repository: `https://github.com/humanfia/science-mango`

Checkpoint branch: `codex/family8-v581-restart`

This branch deliberately records an in-progress proof.  The aggregate target
`Family8Grounding` currently imports checkpoint V581, but V581 is not the
mathematical completion criterion.

## Clone and reproduce the checkpoint

```bash
git clone --branch codex/family8-v581-restart \
  https://github.com/humanfia/science-mango.git
cd science-mango/generated/wang_zahl_kakeya_dimH

# Install/select the pinned Lean toolchain through elan, then fetch packages.
lake update

# Recheck the last integrated checkpoint and its aggregate import root.
lake build Family8Grounding.Family8PaperFullCanonicalGroundingV581
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

## Last integrated checkpoint: V581

`Family8Grounding.lean` imports
`Family8Grounding.Family8PaperFullCanonicalGroundingV581`.

Before this snapshot, the following exact builds succeeded in the original
workspace:

```bash
lake build Family8Grounding.Family8PaperFullCanonicalGroundingV581
lake build Family8Grounding
```

The build contained 12,157 jobs.  The V581 terminal declarations printed only
the standard dependencies `propext`, `Classical.choice`, and `Quot.sound`.
Re-run the commands after cloning; cached `.olean` files are not committed and
are not evidence on the new machine.

V581 integrates these latest verified links:

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
- `Family8FiniteRigidMotionScaleOnlyElongatedConflictProjectionV1` was exact
  green after V581 was built, but is not yet imported by V581.  It converts
  uniform elongated-body loads into the actual copied-anchor conflict-card
  bound without admissibility, `BoundAt`, or essential-distinctness premises.

Family 8 is **not closed** at V581.

## Unintegrated drafts in this snapshot

These files are intentionally saved so work can resume without reconstructing
the abandoned compiler sessions.  Treat them as unverified until a fresh
compiler run succeeds:

- `Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyJointSelectorV1.lean`
  contains the internal two-family Chernoff selector.  Its public endpoint
  still needs to return the weakest useful pair: all John-catalogue tails and
  the actual copied-anchor conflict-card cap.  The full elongated catalogue
  may be used internally for the union bound but should not be exposed as the
  final result.
- `Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyFullCatalogueCWAV1.lean`
  is a source-only raw scale-only adapter from the full John tail to the CWA of
  the full normalized indexed rigid-copy family.  It had no successful exact
  build at snapshot time.
- `Family8CertifiedPlankLabelledSlabL2V1.lean` contains the exact-level
  intersecting row mass estimates and the proposed inverse-sine/thickness
  cancellation.  It does not yet contain the full Appendix B.3 dyadic
  aggregate or the whole-cross producer and had no successful exact build at
  snapshot time.

The last background compile of the joint selector was stopped before creating
the checkpoint because its output channel belonged to an interrupted agent.
Start a fresh compiler run; do not infer success or failure from that stopped
process.

## Shortest continuation plan

Run at most two semantic proof families in parallel: the Family 7/small-`b`
lane and the labelled-slab/large-`b` lane.  Multiple reviewers or compilers may
work inside a lane, but each source file must have one owner.

### Lane A: Family 7 / small-`b`

1. Reverify the conflict projection:

   ```bash
   lake build Family8Grounding.Family8FiniteRigidMotionScaleOnlyElongatedConflictProjectionV1
   ```

2. Compile and repair
   `Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyJointSelectorV1`.
   The same `omega` must control both load families.  Keep all John tests in
   the public result, but immediately project the internal all-elongated-test
   result to
   `forall a, (normalizedConflictIndices copied a).card <= threshold`.

3. Compile and repair
   `Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyFullCatalogueCWAV1`.
   Its output should only be the full copied-family
   `SatisfiesConvexWolffAxioms` with the exact copied-card normalization; do not
   reintroduce `IsAdmissible`, `BoundAt`, or essential distinctness.

4. Feed the conflict-card result to
   `Family8FiniteRandomRigidMotionPaperFixedJohnFreshSelectionV2.exists_normalized_refinement_admissible_isKatzTao_of_scale_B2`.
   Combine the selected refinement, CWA, automatic copy count, and Frostman
   connector.  Then discharge the remaining greedy/card/small-power scalar
   payments needed for the fixed-geometry Family 7 `BoundAt` and selected
   outer Equation (45).

5. The endpoint still requires the exact chosen-outer geometry and Section 8
   power budgets in
   `Family8WinnerSideJointBucketEndpointPackedEq32LossAwarePaymentV1`.

### Lane B: labelled slab / large-`b`

1. Fresh-compile `Family8CertifiedPlankLabelledSlabL2V1.lean` and repair the
   current inverse-sine times B.2-thickness cancellation.
2. Replace the unusable global-unit-ball binding by an intersection-anchored
   local row lemma.  For two certified `a x b x 1` boxes sharing a point, the
   intersection controls the long coordinate; a `[8 * theta, 8, 8]` test box
   (volume `512 * theta`) is the intended safe target and removes the false
   `hunit` premise.
3. Add the intersection-supported row weighted-overlap majorant and the full
   dyadic Appendix B.3 aggregate.  Do not fall back to a global hull,
   `carrierFloor`, or the trivial `Q = N` estimate.
4. Prove the final small-power scalar directly in the whole-cross form
   `WinnerSideLargeBWeightedOverlapWholeCrossPaymentAt`.  Do not split it
   through an auxiliary common `innerResidual`; reviewer audit showed that is
   strictly stronger than the downstream endpoint needs.
5. Apply
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
