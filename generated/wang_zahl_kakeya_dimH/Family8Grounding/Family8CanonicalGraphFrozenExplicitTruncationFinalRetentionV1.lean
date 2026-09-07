import Family8Grounding.Family8CanonicalGraphFrozenExplicitTruncationSelectorV1
import Family8Grounding.Family8CanonicalGraphFrozenExplicitTruncationHighFibreExactCardCeilingV1
import Mathlib.Tactic

/-!
# Final same-graph retention after explicit truncation

This file composes the explicit half-mass truncation, the exact-card
selector, and the pointwise fibre-mass cap.  All three statements use the
literal graph, shading, zero projection and explicit level stored in the
same `SameAssemblyFullCoefficientGraphIdentity`; in particular no dyadic
scale counter or reselected graph witness occurs.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalGraphFrozenExplicitTruncationFinalRetentionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenExplicitTruncationHalfRetentionV1
open Family8CanonicalGraphFrozenExplicitTruncationHighFibreExactCardV1
open Family8CanonicalGraphFrozenExplicitTruncationSelectorV1
open Family8CanonicalGraphFrozenExplicitTruncationHighFibreExactCardCeilingV1
open Family8CanonicalGraphFrozenLowFibreWeightedTailV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8ProjectedActiveShadingMassMeasureV1
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-- Final no-`ell` explicit-truncation ledger on the frozen canonical graph.

The selected high-fibre band keeps enough mass to pay the projected source,
and its weighted mass is bounded by `2 * p` times its planar volume.  The
last conjunct records the resulting direct source-to-volume estimate. -/
theorem exists_sameGraph_explicitLevel_exactCard_retention_and_ceiling
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htauHalf : tau ≤ (2 : NNReal)⁻¹) :
    let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
    let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
      VS R.label
    let Z := firstCrossingFamilyGraphBucketShading
      R.axis R.label F P R.A R.k
    let f0 : Real → Real := fun _ ↦ 0
    let Yw := shadingWindowRestriction Z f0 measurable_const
      Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
    let densityFloor :=
      ((Family8FrozenComparableActualAverageMassDensityV1.Assembly.sourceActiveFineShading
          P Y).shadingDensity /
        ((R.A.loss : ENNReal) * (P.index.coarse.card : ENNReal))) /
        R.graphLoss
    let level0 := densityFloor * (tau : ENNReal) / 96
    let highPhysical :=
      positiveLowerFibreProjectedPhysical Yw graph f0
        measurable_const level0
    let E := highPhysical.multiplicityBand
    ∃ p : Nat, 1 ≤ p ∧ p ≤ graph.card ∧
      projectedActiveShadingMassMeasure Yw graph f0 Set.univ ≤
        2 * (graph.card : ENNReal) *
          highFibreWeightedMass Yw graph f0 level0 (E p p) ∧
      highFibreWeightedMass Yw graph f0 level0 (E p p) ≤
        2 * (p : ENNReal) * volume (E p p) ∧
      projectedActiveShadingMassMeasure Yw graph f0 Set.univ ≤
        4 * (graph.card : ENNReal) * (p : ENNReal) * volume (E p p) := by
  dsimp only
  let VS := firstCrossingFamilyVerticalSource R.axis F P R.k
  let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
    VS R.label
  let Z := firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k
  let f0 : Real → Real := fun _ ↦ 0
  let Yw := shadingWindowRestriction Z f0 measurable_const
    Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
  let densityFloor :=
    ((Family8FrozenComparableActualAverageMassDensityV1.Assembly.sourceActiveFineShading
        P Y).shadingDensity /
      ((R.A.loss : ENNReal) * (P.index.coarse.card : ENNReal))) /
      R.graphLoss
  let level0 := densityFloor * (tau : ENNReal) / 96
  let highPhysical :=
    positiveLowerFibreProjectedPhysical Yw graph f0
      measurable_const level0
  let E := highPhysical.multiplicityBand
  obtain ⟨p, hpLower, hpUpper, hretention⟩ :=
    exists_sameGraph_explicitLevel_exactCard_highMass_payment
      R htauHalf
  have hretention' :
      projectedActiveShadingMassMeasure Yw graph f0 Set.univ ≤
        2 * (graph.card : ENNReal) *
          highFibreWeightedMass Yw graph f0 level0 (E p p) := by
    simpa only [VS, graph, Z, f0, Yw, densityFloor, level0,
      highPhysical, E] using hretention
  have hceiling :
      highFibreWeightedMass Yw graph f0 level0 (E p p) ≤
        2 * (p : ENNReal) * volume (E p p) := by
    simpa only [VS, graph, Z, f0, Yw, densityFloor, level0,
      highPhysical, E] using
      sameGraph_zeroWindow_highFibreWeightedMass_exactCard_le
        R htauHalf level0 p
  refine ⟨p, hpLower, hpUpper, hretention', hceiling, ?_⟩
  calc
    projectedActiveShadingMassMeasure Yw graph f0 Set.univ ≤
        2 * (graph.card : ENNReal) *
          highFibreWeightedMass Yw graph f0 level0 (E p p) :=
      hretention'
    _ ≤ 2 * (graph.card : ENNReal) *
          (2 * (p : ENNReal) * volume (E p p)) := by
      exact mul_le_mul' le_rfl hceiling
    _ = 4 * (graph.card : ENNReal) * (p : ENNReal) *
          volume (E p p) := by
      ring

#print axioms exists_sameGraph_explicitLevel_exactCard_retention_and_ceiling

end

end Family8CanonicalGraphFrozenExplicitTruncationFinalRetentionV1
