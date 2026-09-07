import Family8Grounding.Family8CanonicalGraphFrozenExplicitTruncationHalfRetentionV1
import Family8Grounding.Family8CanonicalGraphFrozenExplicitTruncationHighFibreExactCardV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalGraphFrozenExplicitTruncationSelectorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenExplicitTruncationHalfRetentionV1
open Family8CanonicalGraphFrozenExplicitTruncationHighFibreExactCardV1
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

/-- Explicit truncation followed by exact-card selection on the same high
active pattern.  There is no dyadic level count. -/
theorem exists_sameGraph_explicitLevel_exactCard_highMass_payment
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
    ∃ p : Nat, 1 ≤ p ∧ p ≤ graph.card ∧
      projectedActiveShadingMassMeasure Yw graph f0 Set.univ ≤
        2 * (graph.card : ENNReal) *
          highFibreWeightedMass Yw graph f0 level0
            (highPhysical.multiplicityBand p p) := by
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
  have hhalf :
      projectedActiveShadingMassMeasure Yw graph f0 Set.univ ≤
        2 * highFibreWeightedMass Yw graph f0 level0 Set.univ := by
    simpa only [VS, graph, Z, f0, Yw, densityFloor, level0] using
      sameGraph_zeroWindow_explicitLevel_highFibreWeightedMass_retains_half
        R htauHalf
  obtain ⟨p, hpLower, hpUpper, hpMass⟩ :=
    exists_sameGraph_zeroWindow_positiveLower_exactCard_highMass
      R level0
  refine ⟨p, hpLower, hpUpper, ?_⟩
  calc
    projectedActiveShadingMassMeasure Yw graph f0 Set.univ ≤
        2 * highFibreWeightedMass Yw graph f0 level0 Set.univ := hhalf
    _ ≤ 2 * ((graph.card : ENNReal) *
          highFibreWeightedMass Yw graph f0 level0
            (highPhysical.multiplicityBand p p)) := by
      exact mul_le_mul' le_rfl (by
        simpa only [VS, graph, Z, f0, Yw, highPhysical] using hpMass)
    _ = 2 * (graph.card : ENNReal) *
          highFibreWeightedMass Yw graph f0 level0
            (highPhysical.multiplicityBand p p) := by
      ac_rfl

end
end Family8CanonicalGraphFrozenExplicitTruncationSelectorV1
