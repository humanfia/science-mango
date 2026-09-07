import Family8Grounding.Family8CanonicalFrostmanWeightedFirstLongBaseBudgetV6
import Family8Grounding.Family8StickyParentHullB2SupportHalfV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CanonicalFrostmanWeightedFirstLongBaseBudgetV7

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8ParameterLadderV1
open Family8CanonicalLowerBufferedScaleV4
open Family8StickyParentHullVolumeBoundV1
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8DoubledParentConflictWeightedShadingMassBridgeV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover

noncomputable section

/-!
# Weighted first-long base budget from radius-two fine support

The raw identified `tau` parent datum is automatically supported in
`B(0,2)`.  At a buffered radius at most one half, its next parents still lie
in `B(0,4)`, so the same canonical Frostman and selected-volume estimates go
through without any admissibility or pairwise-distinctness certificate for
the widened parent datum.
-/

namespace StickyScaleCover

theorem activeCoarseFamily_isFrostmanIn_canonical_of_fine_B2
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (hfineB2 : forall i,
      (fine.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2)
    (S : StickyScaleCover fine rho)
    (hrho : 0 < rho) (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (hcoarse : S.activeCoarse.Nonempty) :
    IsFrostmanIn
      (canonicalFrostmanConstant S.activeCoarseFamily closedBallFourBody)
      S.activeCoarseFamily closedBallFourBody := by
  have hcontained : forall k,
      (S.activeCoarseFamily k : Set Space) ⊆
        (closedBallFourBody : Set Space) := by
    intro k
    simpa only [coe_closedBallFourBody] using
      (Family8StickyParentHullB2SupportHalfV2.activeCoarseFamily_body_subset_closedBall_four_of_fine_B2
        fine hfineB2 S hrhoHalf k)
  apply
    Family8ActiveCoarseCanonicalFrostmanXLowerV3.canonicalFrostmanConstant_isFrostmanIn
      S.activeCoarseFamily closedBallFourBody hcontained
  · rw [containedMass_eq_familyVolume_of_contained
      S.activeCoarseFamily closedBallFourBody hcontained]
    exact
      (Family8ActiveCoarseCanonicalFrostmanXLowerV3.StickyScaleCover.activeCoarseFamilyVolume_pos
        S hrho hcoarse).ne'
  · rw [containedMass_eq_familyVolume_of_contained
      S.activeCoarseFamily closedBallFourBody hcontained]
    exact familyVolume_ne_top S.activeCoarseFamily

theorem global_rpow_le_eight_mul_activeCoarseCardScaleMass_of_B2
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (hfineB2 : forall i,
      (fine.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2)
    (S : StickyScaleCover fine rho)
    {globalDelta : NNReal} {etaPrime : Real}
    (hglobal : 0 < globalDelta)
    (hrho : 0 < rho) (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (hcoarse : S.activeCoarse.Nonempty)
    (hC : canonicalFrostmanConstant
        S.activeCoarseFamily closedBallFourBody <=
      (globalDelta : ENNReal) ^ (-etaPrime)) :
    (globalDelta : ENNReal) ^ etaPrime <=
      8 * (activeCoarseCardScaleMass S : ENNReal) := by
  apply
    Family8ActiveCoarseFrostmanCardScaleMassLowerV3.StickyScaleCover.global_rpow_le_eight_mul_activeCoarseCardScaleMass_of_frostman
      S closedBallFourBody hglobal hrho hrhoHalf hcoarse
      Family8ActiveCoarseCanonicalFrostmanXLowerV3.StickyScaleCover.one_le_volume_closedBallFourBody
  · exact activeCoarseFamily_isFrostmanIn_canonical_of_fine_B2
      fine hfineB2 S hrho hrhoHalf hcoarse
  · exact hC

theorem parameterLadder_global_rpow_le_activeCoarseCardScaleMass_of_B2
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (hfineB2 : forall i,
      (fine.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2)
    (S : StickyScaleCover fine rho)
    {globalDelta : NNReal} {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    (hbeta : 0 < beta)
    (hglobal : 0 < globalDelta)
    (hrho : 0 < rho) (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (hcoarse : S.activeCoarse.Nonempty)
    (hC : canonicalFrostmanConstant
        S.activeCoarseFamily closedBallFourBody <=
      (globalDelta : ENNReal) ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P j))
    (hdelta : globalDelta <=
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P j) :
    globalDelta ^ (10 * P.eta j / (P.epsilon * beta)) <=
      activeCoarseCardScaleMass S := by
  have hrough : (globalDelta : ENNReal) ^
        Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P j <= 8 * (activeCoarseCardScaleMass S : ENNReal) :=
    global_rpow_le_eight_mul_activeCoarseCardScaleMass_of_B2
      fine hfineB2 S hglobal hrho hrhoHalf hcoarse hC
  have hcore : (globalDelta : ENNReal) ^
        (Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
            P j +
          Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanAbsorbExponent
            P j) <= (activeCoarseCardScaleMass S : ENNReal) :=
    Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.global_rpow_add_absorb_le_of_le_eight_mul
      hglobal
      (Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanAbsorbExponent_pos
        P j hbeta)
      hdelta hrough
  apply ENNReal.coe_le_coe.mp
  rw [ENNReal.coe_rpow_of_ne_zero hglobal.ne',
    <- Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanExponent_add_absorb
      P j]
  exact hcore

/-- The weighted selected-family base estimate for a radius-two supported
fine datum. -/
theorem weightedSelected_baseBudget_of_parameterLadder_canonicalFrostman_B2
    {globalDelta tau theta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum tau index)
    (hfineB2 : forall i,
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2)
    (htauHalf : tau <= (2 : NNReal)⁻¹)
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    (hbeta : 0 < beta)
    {S : StickyScaleCover D.family
      (canonicalLowerBufferedScale tau theta P.epsilon)}
    {B A : ENNReal} {loss : Real}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading) B)
    (hglobal : 0 < globalDelta) (hglobalTau : globalDelta <= tau)
    (hthetaOne : theta <= 1)
    (hrho : 0 < canonicalLowerBufferedScale tau theta P.epsilon)
    (hrhoHalf : canonicalLowerBufferedScale tau theta P.epsilon <=
      (2 : NNReal)⁻¹)
    (hcoarse : S.activeCoarse.Nonempty)
    (hB0 : B ≠ 0) (hBTop : B ≠ ∞)
    (hC : canonicalFrostmanConstant
        S.activeCoarseFamily closedBallFourBody <=
      (globalDelta : ENNReal) ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P j))
    (hdelta : globalDelta <=
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P j)
    (hscalarCap :
      B * (A * volume (unitBallBody : Set Space)) <=
        (tau : ENNReal) ^ (-loss) *
          ((globalDelta : ENNReal) ^
            (10 * P.eta j / (P.epsilon * beta) + 2 * P.epsilon) / 2)) :
    A * volume (unitBallBody : Set Space) <=
      (tau : ENNReal) ^ (-loss) *
        (restrictActualTubeDatum D
          (weightedSelectedFineIndices D.shading W)).actualFamilyVolume := by
  have hXLower :
      globalDelta ^ (10 * P.eta j / (P.epsilon * beta)) <=
        activeCoarseCardScaleMass S :=
    parameterLadder_global_rpow_le_activeCoarseCardScaleMass_of_B2
      D.family hfineB2 S P j hbeta hglobal hrho hrhoHalf hcoarse hC hdelta
  exact
    Family8LongIntervalActiveCoarseCardScaleMassBridgeV2.StickyScaleCover.weightedSelected_baseBudget_of_canonicalCardScaleMassLower
      D W hglobal hglobalTau hthetaOne P.epsilon_pos.le htauHalf
        hB0 hBTop hXLower hscalarCap

#print axioms activeCoarseFamily_isFrostmanIn_canonical_of_fine_B2
#print axioms global_rpow_le_eight_mul_activeCoarseCardScaleMass_of_B2
#print axioms parameterLadder_global_rpow_le_activeCoarseCardScaleMass_of_B2
#print axioms
  weightedSelected_baseBudget_of_parameterLadder_canonicalFrostman_B2

end StickyScaleCover
end
end Family8CanonicalFrostmanWeightedFirstLongBaseBudgetV7
