import Family8Grounding.Family8WinnerSideJointBucketLargeBWeightedOverlapJointScalarReductionV1
import Family8Grounding.Family8SelectedOccurrenceFrozenSameQPositiveCarrierEq46ComposerV1
import Mathlib.Tactic

/-!
# Fixed-witness cross-overlap consumer for the winner-side large-`b` branch

The honest output of a weighted Lemma 6.9 argument is naturally
cross-multiplied by the total mass of the one chosen normalized outer
shading.  This file consumes that form directly.  It constructs the auxiliary
outer overlap factor internally (by division only in the nonzero-mass case),
combines it with the already isolated same-`q` inner scale, and returns the
existing fixed-coordinate large-`b` conclusion.

No memberwise carrier floor and no linear `Rside.card` overlap factor occur in
the interface.  The zero-mass case is discharged structurally: then every
pairwise shaded overlap has zero volume.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 100000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8WinnerSideJointBucketLargeBWeightedOverlapCrossConsumerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceFrozenSameQPositiveCarrierEq46ComposerV1
open Family8SelectedOccurrenceFrozenSameQPositiveCarrierPaymentV1
open Family8SelectedOccurrenceNormalizedOuterDatumV1
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8WinnerSideJointBucketLargeBLemma69ConsumerV1
open Family8WinnerSideJointBucketLargeBWeightedOverlapConsumerV1
open Family8WinnerSideJointBucketLargeBWeightedOverlapJointScalarReductionV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- If the total shaded mass vanishes, so does the complete ordered-pair
overlap sum.  This is the only fact needed to make the quotient construction
total at zero mass. -/
theorem overlapSum_eq_zero_of_shadingMass_eq_zero
    {iota : Type*} [Fintype iota]
    {F : ConvexFamily iota} (Y : Shading F)
    (hmass : Y.shadingMass = 0) :
    (∑ i, ∑ j, volume (Y.carrier i ∩ Y.carrier j)) = 0 := by
  classical
  apply nonpos_iff_eq_zero.mp
  calc
    (∑ i, ∑ j, volume (Y.carrier i ∩ Y.carrier j)) ≤
        ∑ i, ∑ _j, volume (Y.carrier i) := by
      exact Finset.sum_le_sum fun i _hi =>
        Finset.sum_le_sum fun j _hj =>
          measure_mono inter_subset_left
    _ = ∑ i, (Fintype.card iota : ENNReal) *
          volume (Y.carrier i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Fintype.card iota : ENNReal) * Y.shadingMass := by
      simp only [Shading.shadingMass, Finset.mul_sum]
    _ = 0 := by rw [hmass, mul_zero]

/-- Pure `ENNReal` quotient lemma behind the cross-overlap consumer.  At
positive finite mass the factor is `overlap / mass`; at zero mass both the
overlap and the required payment vanish. -/
theorem exists_overlapFactor_of_crossWeightedPayment
    {memberCount overlap mass target : ENNReal}
    (hmassTop : mass ≠ ∞)
    (hoverlapZero : mass = 0 → overlap = 0)
    (hcross : memberCount * overlap ≤ target * mass) :
    ∃ outerBound : ENNReal,
      overlap ≤ outerBound * mass ∧
      memberCount * outerBound ≤ target := by
  by_cases hmass0 : mass = 0
  · refine ⟨0, ?_, ?_⟩
    · simp only [hoverlapZero hmass0, hmass0, mul_zero, le_refl]
    · simp
  · refine ⟨overlap / mass, ?_, ?_⟩
    · exact le_of_eq (ENNReal.div_mul_cancel hmass0 hmassTop).symm
    · apply (ENNReal.mul_le_mul_iff_right hmass0 hmassTop).mp
      calc
        mass * (memberCount * (overlap / mass)) =
            memberCount * ((overlap / mass) * mass) := by ac_rfl
        _ = memberCount * overlap := by
          rw [ENNReal.div_mul_cancel hmass0 hmassTop]
        _ ≤ target * mass := hcross
        _ = mass * target := by ac_rfl

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {sourceFine : UniformTubeFamily delta index}

/-- The weakest large-`b` analytic seam on the exact selected normalized
outer shading.  It is the cross-multiplied form of the two downstream facts
that there is one `outerBound` controlling both the weighted overlap and the
whole outer-times-inner John budget.  In particular, no auxiliary
residual factor and no separately stronger inner payment occur here. -/
def WinnerSideLargeBWeightedOverlapWholeCrossPaymentAt
    (S : StickyScaleCover sourceFine rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (Rside : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (source : Shading S.activeCoarseFamily)
    (Y : Shading S.activeCoarseFamily)
    (q : Fin (blocks S.activeCoarseFamily P).length)
    (labelOuter labelInner : Fin 3 -> Int)
    (outerKT geometryLoss densityLoss : ENNReal)
    (epsilon gamma : Real) : Prop :=
  let Youter := selectedOccurrenceNormalizedOuterShading
    (delta := rho) (iota := ActiveParentIndex S)
    (fine := S.coarse.restrictTo S.activeCoarse)
    (active := (Finset.univ : Finset (ActiveParentIndex S)))
    P Y labelOuter Rside
  let m : ENNReal :=
    ((blockAt S.activeCoarseFamily P q).fiber.card : ENNReal)
  let overlapSum : ENNReal :=
    ∑ i, ∑ j, volume (Youter.carrier i ∩ Youter.carrier j)
  let outerFactor : ENNReal := proposition66AOuterFactor rho
        (bucketShortA labelOuter) (bucketShortB labelOuter)
        Rside.card outerKT epsilon gamma
  let innerFactor : ENNReal := proposition66AInnerFactor rho
        (bucketShortA labelInner) (bucketShortB labelInner)
        (blockAt S.activeCoarseFamily P q).fiber.card epsilon gamma
  let target : ENNReal :=
    (source.shadingDensity * geometryLoss * densityLoss) *
      (outerFactor * innerFactor)
  (winnerSideLargeBWeightedOverlapJohnLoss * m) * overlapSum ≤
    target * Youter.shadingMass

/-- The whole-cross estimate is exactly sufficient to manufacture the one
auxiliary `outerBound` expected by the existing coordinate consumer. -/
theorem exists_weightedOverlapBudget_and_jointBudget_of_wholeCrossPayment
    (S : StickyScaleCover sourceFine rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (Rside : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (source : Shading S.activeCoarseFamily)
    (Y : Shading S.activeCoarseFamily)
    (q : Fin (blocks S.activeCoarseFamily P).length)
    (labelOuter labelInner : Fin 3 -> Int)
    (outerKT geometryLoss densityLoss : ENNReal)
    (epsilon gamma : Real)
    (hcross : WinnerSideLargeBWeightedOverlapWholeCrossPaymentAt
      S P Rside source Y q labelOuter labelInner outerKT geometryLoss
        densityLoss epsilon gamma) :
    ∃ outerBound : ENNReal,
      SelectedNormalizedOuterWeightedOverlapBudgetAt
        (rho := rho) (iota := ActiveParentIndex S)
        (fine := S.coarse.restrictTo S.activeCoarse)
        (active := (Finset.univ : Finset (ActiveParentIndex S)))
        P Y labelOuter Rside outerBound ∧
      WinnerSideLargeBWeightedOverlapJointBudgetAt
        S P Rside source q labelOuter labelInner outerBound outerKT
          geometryLoss densityLoss epsilon gamma := by
  classical
  let Youter := selectedOccurrenceNormalizedOuterShading
    (delta := rho) (iota := ActiveParentIndex S)
    (fine := S.coarse.restrictTo S.activeCoarse)
    (active := (Finset.univ : Finset (ActiveParentIndex S)))
    P Y labelOuter Rside
  let overlapSum : ENNReal :=
    ∑ i, ∑ j, volume (Youter.carrier i ∩ Youter.carrier j)
  let memberCount : ENNReal :=
    winnerSideLargeBWeightedOverlapJohnLoss *
      ((blockAt S.activeCoarseFamily P q).fiber.card : ENNReal)
  let outerFactor : ENNReal := proposition66AOuterFactor rho
    (bucketShortA labelOuter) (bucketShortB labelOuter)
    Rside.card outerKT epsilon gamma
  let innerFactor : ENNReal := proposition66AInnerFactor rho
    (bucketShortA labelInner) (bucketShortB labelInner)
    (blockAt S.activeCoarseFamily P q).fiber.card epsilon gamma
  let target : ENNReal :=
    (source.shadingDensity * geometryLoss * densityLoss) *
      (outerFactor * innerFactor)
  have hmassTop : Youter.shadingMass ≠ ∞ :=
    ne_of_lt Youter.shadingMass_lt_top
  have hoverlapZero : Youter.shadingMass = 0 → overlapSum = 0 := by
    intro hmass
    dsimp only [overlapSum]
    exact overlapSum_eq_zero_of_shadingMass_eq_zero Youter hmass
  have hcross' : memberCount * overlapSum ≤
      target * Youter.shadingMass := by
    exact hcross
  obtain ⟨outerBound, hoverlap, hpayment⟩ :=
    exists_overlapFactor_of_crossWeightedPayment
      hmassTop hoverlapZero hcross'
  refine ⟨outerBound, ?_, ?_⟩
  · change overlapSum ≤ outerBound * Youter.shadingMass
    exact hoverlap
  · change memberCount * outerBound ≤ target
    exact hpayment

/-- Direct fixed-coordinate conclusion from the weakest whole-cross seam. -/
theorem
    winnerSide_largeB_weightedOverlap_productAtCoordinates_of_wholeCrossPayment
    (S : StickyScaleCover sourceFine rho) (hrho : 0 < rho)
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (Rside : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (source : Shading S.activeCoarseFamily)
    (hsource : source.shadingMass ≠ 0)
    (rFrozen : Real)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (selectedOccurrenceFactorization P Rside) source rFrozen)
    (hAfrozen : A.frozenCoarse =
      (selectedOccurrenceFactorization P Rside).inducedShading
        A.refinement.shading)
    (q : Fin (blocks S.activeCoarseFamily P).length)
    (hproduct :
      (actualRefinementShading A).averageMultiplicity ≤
        4 * (A.frozenCoarse.averageMultiplicity *
          (finalFiberShading A (some q)).averageMultiplicity))
    (r : NNReal) (hr : 0 < r)
    (labelInner labelOuter : Fin 3 -> Int)
    (hinnerCross :
      selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
          S hrho P q source r hr labelInner *
        (finalFiberShading A (some q)).averageMultiplicity ≤
      selectedOccurrenceFrozenSameQPositiveCarrierExpandedEq46LHS
        S P r labelInner
          (blockDensity S.activeCoarseFamily
            (blockAt S.activeCoarseFamily P q)))
    (outerKT geometryLoss densityLoss : ENNReal)
    (epsilon gamma : Real) (hgamma : 0 ≤ gamma) (hgammaOne : gamma ≤ 1)
    (hcross : WinnerSideLargeBWeightedOverlapWholeCrossPaymentAt
      S P Rside source A.refinement.shading q labelOuter labelInner outerKT
        geometryLoss densityLoss epsilon gamma) :
    WinnerSideLargeBWeightedOverlapConclusionAt
      S P Rside source rFrozen A q labelOuter labelInner
        outerKT geometryLoss densityLoss epsilon gamma := by
  obtain ⟨outerBound, hoverlap, hjoint⟩ :=
    exists_weightedOverlapBudget_and_jointBudget_of_wholeCrossPayment
      S P Rside source A.refinement.shading q labelOuter labelInner outerKT
        geometryLoss densityLoss epsilon gamma hcross
  exact winnerSide_largeB_weightedOverlap_productAtCoordinates
    S hrho hrhoHalf P Rside source hsource rFrozen A hAfrozen q hproduct
      r hr labelInner labelOuter hinnerCross outerBound outerKT geometryLoss
      densityLoss epsilon gamma hgamma hgammaOne hoverlap hjoint

/-- Fixed-`W` endpoint form.  All coordinates are read from `Wfix`; its only
analytic input is the weakest whole-cross payment. -/
theorem winnerSide_largeB_weightedOverlap_productAtFixedW_of_wholeCrossPayment
    (S : StickyScaleCover sourceFine rho) (hrho : 0 < rho)
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (Rside : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (source : Shading S.activeCoarseFamily)
    (hsource : source.shadingMass ≠ 0)
    (rFrozen : Real) (r : NNReal) (hr : 0 < r)
    (Wfix : WinnerSideLargeBLemma69PaymentWitness
      S hrho P Rside source rFrozen r hr)
    (labelOuter : Fin 3 -> Int)
    (outerKT geometryLoss densityLoss : ENNReal)
    (epsilon gamma : Real) (hgamma : 0 ≤ gamma) (hgammaOne : gamma ≤ 1)
    (hcross : WinnerSideLargeBWeightedOverlapWholeCrossPaymentAt
      S P Rside source Wfix.assembly.refinement.shading Wfix.occurrence
        labelOuter Wfix.innerLabel outerKT geometryLoss densityLoss
        epsilon gamma) :
    WinnerSideLargeBWeightedOverlapConclusionAt
      S P Rside source rFrozen Wfix.assembly Wfix.occurrence
        labelOuter Wfix.innerLabel outerKT geometryLoss densityLoss
        epsilon gamma := by
  exact
    winnerSide_largeB_weightedOverlap_productAtCoordinates_of_wholeCrossPayment
      S hrho hrhoHalf P Rside source hsource rFrozen Wfix.assembly
        Wfix.frozen_eq Wfix.occurrence Wfix.actual_le_four_mul r hr
        Wfix.innerLabel labelOuter Wfix.inner_cross outerKT geometryLoss
        densityLoss epsilon gamma hgamma hgammaOne hcross

#print axioms overlapSum_eq_zero_of_shadingMass_eq_zero
#print axioms exists_overlapFactor_of_crossWeightedPayment
#print axioms WinnerSideLargeBWeightedOverlapWholeCrossPaymentAt
#print axioms
  exists_weightedOverlapBudget_and_jointBudget_of_wholeCrossPayment
#print axioms
  winnerSide_largeB_weightedOverlap_productAtCoordinates_of_wholeCrossPayment
#print axioms
  winnerSide_largeB_weightedOverlap_productAtFixedW_of_wholeCrossPayment

end
end Family8WinnerSideJointBucketLargeBWeightedOverlapCrossConsumerV1
