import Family8Grounding.Family8WinnerSideJointBucketLargeBLemma69ConsumerV1
import Family8Grounding.Family8CoreHighFiberDensitySameQExactJointOuterHullTwoScaleV1
import Family8Grounding.Family8SelectedParentBlockDensityHullReserveInnerJointV1
import Mathlib.Tactic

/-!
# Winner-side large-b consumer with a weighted outer-overlap input

The positive-carrier minimum used by the earlier direct Lemma 6.9 adapter is
positive and finite, but it has no quantitative lower bound.  This file does
not use that minimum.  Instead it receives the genuine aggregate overlap
estimate on the one normalized outer shading already fixed by the selected
payment witness:

`sum_i sum_j |Y_i intersect Y_j| <= outerBound * Y.shadingMass`.

Thus the full carrier mass remains as the row-sum weight.  The analytic
overlap estimate is still an input; this file does not assert or manufacture
it from positivity.  The first theorem converts it to the corresponding
frozen outer average bound.  The final theorem keeps `outerBound` intact until
the same chosen occurrence and inner label enter the existing joint
outer-hull payment.  In particular there is no isolated comparison
`outerBound <= OuterFactor`, no memberwise carrier floor, and no callback over
other possible witnesses.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8WinnerSideJointBucketLargeBWeightedOverlapConsumerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8CoreHighFiberDensitySameQExactJointOuterHullTwoScaleV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8Prop66InnerScaleMismatchAbsorptionV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceFrozenSameQPositiveCarrierEq46ComposerV1
open Family8SelectedOccurrenceFrozenSameQPositiveCarrierPaymentV1
open Family8SelectedOccurrenceNormalizedOuterDatumV1
open Family8SelectedParentBlockDensityHullReserveInnerJointV1
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8WinnerSideJointBucketLargeBLemma69ConsumerV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

variable {rho : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily rho iota}
  {active : Finset iota}

/-- The honest aggregate overlap estimate at one fixed normalized outer
shading.  Its right side retains the total carrier mass; there is no
memberwise lower-volume premise. -/
def SelectedNormalizedOuterWeightedOverlapBudgetAt
    (P : GreedyDensityPartition fine.bodyFamily
      (hullCandidates active) (hullContainer fine.bodyFamily) active)
    (Y : Shading fine.bodyFamily)
    (labelOuter : Fin 3 -> Int)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (outerBound : ENNReal) : Prop :=
  let Youter := selectedOccurrenceNormalizedOuterShading
    P Y labelOuter Rside
  (∑ i, ∑ j, volume (Youter.carrier i ∩ Youter.carrier j)) <=
    outerBound * Youter.shadingMass

/-- Aggregate overlap on the exact chosen outer shading bounds the frozen
outer average.  This is the complete replacement for the unquantified
positive-carrier minimum in the old outer helper. -/
theorem winnerSideLargeB_frozenOuter_le_of_weightedOverlap_atCoordinates
    (P : GreedyDensityPartition fine.bodyFamily
      (hullCandidates active) (hullContainer fine.bodyFamily) active)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (source : Shading fine.bodyFamily) (rFrozen : Real)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (selectedOccurrenceFactorization P Rside) source rFrozen)
    (hAfrozen : A.frozenCoarse =
      (selectedOccurrenceFactorization P Rside).inducedShading
        A.refinement.shading)
    (labelOuter : Fin 3 -> Int) (outerBound : ENNReal)
    (hoverlap : SelectedNormalizedOuterWeightedOverlapBudgetAt
      (rho := rho) (iota := iota) (fine := fine) (active := active)
      P A.refinement.shading labelOuter Rside outerBound) :
    A.frozenCoarse.averageMultiplicity <= outerBound := by
  let Youter := selectedOccurrenceNormalizedOuterShading
    P A.refinement.shading labelOuter Rside
  have hnormalized : Youter.averageMultiplicity <= outerBound := by
    apply averageMultiplicity_le_factor_of_overlapSum_le
      (Y := Youter) (Q := outerBound)
    simpa only [SelectedNormalizedOuterWeightedOverlapBudgetAt, Youter] using
      hoverlap
  rw [winnerSideLargeBLemma69_outerTransport_at
    P Rside source rFrozen A hAfrozen labelOuter]
  exact hnormalized

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {sourceFine : UniformTubeFamily delta index}

/-- The fixed numerical loss already present when the selected product and
the selected inner cross estimate are combined.  It contains the literal
factor four, the inner side-bucket loss, and the frozen positive-carrier loss;
it contains neither `outerBound` nor a Proposition 6.6 factor.  The named
positive-carrier term belongs to `W.inner_cross`, where its inner carrier
quantity has already been cancelled; this definition introduces no carrier
floor input. -/
noncomputable def winnerSideLargeBWeightedOverlapRawLoss
    (S : StickyScaleCover sourceFine rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (labelInner : Fin 3 -> Int) : ENNReal :=
  4 *
    ((selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
      (2 *
        (certifiedPlankThresholdedAngleBucketLoss
          (bucketShortA labelInner) (bucketShortB labelInner) : ENNReal))) *
    selectedOccurrenceFrozenSameQPositiveCarrierLoss S P

/-- The exact John/card constant in the already proved local density-to-hull
comparison. -/
noncomputable def winnerSideLargeBWeightedOverlapJohnLoss : ENNReal :=
  16 * certifiedPlankThresholdedAngleScaleCap 576 * (288 : ENNReal) ^ 3

/-- The sole new whole-product scalar gate at the already selected occurrence
and two already selected labels.  The raw overlap factor is paid only after it
has met the actual inner fibre count and source density. -/
def WinnerSideLargeBWeightedOverlapJointBudgetAt
    (S : StickyScaleCover sourceFine rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (Rside : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (source : Shading S.activeCoarseFamily)
    (q : Fin (blocks S.activeCoarseFamily P).length)
    (labelOuter labelInner : Fin 3 -> Int)
    (outerBound outerKT geometryLoss densityLoss : ENNReal)
    (epsilon beta : Real) : Prop :=
  winnerSideLargeBWeightedOverlapJohnLoss *
      ((blockAt S.activeCoarseFamily P q).fiber.card : ENNReal) * outerBound <=
    (source.shadingDensity * geometryLoss * densityLoss) *
      (proposition66AOuterFactor rho
          (bucketShortA labelOuter) (bucketShortB labelOuter)
          Rside.card outerKT epsilon beta *
        proposition66AInnerFactor rho
          (bucketShortA labelInner) (bucketShortB labelInner)
          (blockAt S.activeCoarseFamily P q).fiber.card epsilon beta)

/-- Exact fixed-witness result of the weighted-overlap route.  The count is
still the literal product `Rside.card * fibre.card`; its later comparison with
the endpoint index count remains outside this analytic consumer. -/
def WinnerSideLargeBWeightedOverlapConclusionAt
    (S : StickyScaleCover sourceFine rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (Rside : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (source : Shading S.activeCoarseFamily) (rFrozen : Real)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (selectedOccurrenceFactorization P Rside) source rFrozen)
    (q : Fin (blocks S.activeCoarseFamily P).length)
    (labelOuter labelInner : Fin 3 -> Int) (outerKT : ENNReal)
    (geometryLoss densityLoss : ENNReal) (epsilon beta : Real) : Prop :=
  (actualRefinementShading A).averageMultiplicity <=
    (winnerSideLargeBWeightedOverlapRawLoss S P labelInner *
        geometryLoss * densityLoss *
        prop66InnerScaleMismatchLoss
          (bucketShortA labelOuter) (bucketShortB labelOuter)
          (bucketShortA labelInner) (bucketShortB labelInner) beta) *
      proposition66AFrostmanFactor rho
        (bucketShortA labelOuter) (bucketShortB labelOuter)
        (Rside.card * (blockAt S.activeCoarseFamily P q).fiber.card)
        outerKT epsilon beta

/-- Pure multiplicative assembly of the selected product estimate with one
outer-average bound and one scaled inner estimate. -/
theorem source_mul_average_le_four_mul_outerBound_mul_innerNumerator
    (sourceFactor actual outerAverage innerAverage outerBound innerNumerator :
      ENNReal)
    (hproduct : actual <= 4 * (outerAverage * innerAverage))
    (houter : outerAverage <= outerBound)
    (hinner : sourceFactor * innerAverage <= innerNumerator) :
    sourceFactor * actual <= 4 * outerBound * innerNumerator := by
  calc
    sourceFactor * actual <=
        sourceFactor * (4 * (outerAverage * innerAverage)) :=
      mul_le_mul' le_rfl hproduct
    _ = 4 * outerAverage * (sourceFactor * innerAverage) := by
      ac_rfl
    _ <= 4 * outerBound * (sourceFactor * innerAverage) :=
      mul_le_mul' (mul_le_mul' le_rfl houter) le_rfl
    _ <= 4 * outerBound * innerNumerator :=
      mul_le_mul' le_rfl hinner

/-- Count-one specialization of the existing joint outer-hull whole-product
consumer.  It fixes the honest total count to the literal outer/inner product
and removes the resulting neutral count-loss power. -/
theorem average_le_wholeProp66AFrostmanFactor_of_jointOuterHullReserve_twoScale_countOne
    {delta outerA outerB innerA innerB : NNReal}
    {plankCount tubesPerPlank : Nat}
    {average d outerBound geometricScale jacobian sourceDensity area johnLoss
      rawLoss geometryLoss targetCF densityLoss : ENNReal}
    {epsilon beta : Real}
    (hdelta : 0 < delta)
    (houterA : 0 < outerA) (houterB : 0 < outerB)
    (hinnerA : 0 < innerA) (hinnerB : 0 < innerB)
    (hbeta0 : 0 <= beta) (hbetaOne : beta <= 1)
    (hsource0 : jacobian * (sourceDensity * area) ≠ 0)
    (hsourceTop : jacobian * (sourceDensity * area) ≠ ∞)
    (hscaled : (jacobian * (sourceDensity * area)) * average <=
      rawLoss * (outerBound * (d * geometricScale)))
    (hJohn : d * geometricScale <=
      jacobian * (johnLoss * ((tubesPerPlank : ENNReal) * area)))
    (hjoint : johnLoss * (tubesPerPlank : ENNReal) * outerBound <=
      (sourceDensity * geometryLoss * densityLoss) *
        (proposition66AOuterFactor delta outerA outerB plankCount
            targetCF epsilon beta *
          proposition66AInnerFactor delta innerA innerB tubesPerPlank
            epsilon beta)) :
    average <=
      (rawLoss * geometryLoss * densityLoss *
        prop66InnerScaleMismatchLoss
          outerA outerB innerA innerB beta) *
        proposition66AFrostmanFactor delta outerA outerB
          (plankCount * tubesPerPlank) targetCF epsilon beta := by
  have hcount : ((plankCount * tubesPerPlank : Nat) : ENNReal) <=
      (1 : ENNReal) * ((plankCount * tubesPerPlank : Nat) : ENNReal) := by
    simp
  have hwhole :
      average <=
        (rawLoss * geometryLoss * densityLoss *
          (prop66InnerScaleMismatchLoss outerA outerB innerA innerB beta *
            (1 : ENNReal) ^ (1 - beta / 2))) *
          proposition66AFrostmanFactor delta outerA outerB
            (plankCount * tubesPerPlank) targetCF epsilon beta :=
    average_le_wholeProp66AFrostmanFactor_of_jointOuterHullReserve_twoScale_actualCount
      (delta := delta) (outerA := outerA) (outerB := outerB)
      (innerA := innerA) (innerB := innerB)
      (plankCount := plankCount) (tubesPerPlank := tubesPerPlank)
      (totalCount := plankCount * tubesPerPlank)
      (average := average) (d := d) (outerBound := outerBound)
      (geometricScale := geometricScale) (jacobian := jacobian)
      (sourceDensity := sourceDensity) (area := area)
      (johnLoss := johnLoss) (rawLoss := rawLoss)
      (geometryLoss := geometryLoss) (targetCF := targetCF)
      (densityLoss := densityLoss) (countLoss := 1)
      (epsilon := epsilon) (beta := beta)
      hdelta houterA houterB hinnerA hinnerB hbeta0 hbetaOne
      hsource0 hsourceTop hcount hscaled hJohn hjoint
  simpa only [ENNReal.one_rpow, mul_one] using hwhole

/-- Fixed-coordinate chosen-witness large-`b` consumer with no carrier
minimum.  The endpoint destructs its one `WinnerSideLargeBLemma69PaymentWitness`
once and passes these exact assembly, occurrence, product, and inner-cross
coordinates.  The aggregate outer overlap estimate supplies `outerBound`; the
existing John/card lemma and the one chosen joint gate close the two-scale
Proposition 6.6 product. -/
theorem winnerSide_largeB_weightedOverlap_productAtCoordinates
    (S : StickyScaleCover sourceFine rho) (hrho : 0 < rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
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
      (actualRefinementShading A).averageMultiplicity <=
        4 * (A.frozenCoarse.averageMultiplicity *
          (finalFiberShading A (some q)).averageMultiplicity))
    (r : NNReal) (hr : 0 < r)
    (labelInner labelOuter : Fin 3 -> Int)
    (hinnerCross :
      selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
          S hrho P q source r hr labelInner *
        (finalFiberShading A (some q)).averageMultiplicity <=
      selectedOccurrenceFrozenSameQPositiveCarrierExpandedEq46LHS
        S P r labelInner
          (blockDensity S.activeCoarseFamily
            (blockAt S.activeCoarseFamily P q)))
    (outerBound outerKT geometryLoss densityLoss : ENNReal)
    (epsilon beta : Real) (hbeta : 0 <= beta) (hbetaOne : beta <= 1)
    (hoverlap : SelectedNormalizedOuterWeightedOverlapBudgetAt
      (rho := rho) (iota := ActiveParentIndex S)
      (fine := S.coarse.restrictTo S.activeCoarse)
      (active := (Finset.univ : Finset (ActiveParentIndex S)))
      P A.refinement.shading labelOuter Rside outerBound)
    (hjoint : WinnerSideLargeBWeightedOverlapJointBudgetAt
      S P Rside source q labelOuter labelInner
        outerBound outerKT geometryLoss densityLoss epsilon beta) :
    WinnerSideLargeBWeightedOverlapConclusionAt
      S P Rside source rFrozen A q labelOuter labelInner
        outerKT geometryLoss densityLoss
        epsilon beta := by
  classical
  let m : Nat := (blockAt S.activeCoarseFamily P q).fiber.card
  let d : ENNReal := blockDensity S.activeCoarseFamily
    (blockAt S.activeCoarseFamily P q)
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P q) r hr
  let J : ENNReal := affineJacobian (bucketNormalizedAffineEquiv e labelInner)
  let area : ENNReal := (rho : ENNReal) ^ 2 / 2
  let G : ENNReal := certifiedPlankThresholdedAngleScaleCap 576 *
    (((((sideShapeUpper labelInner 2)⁻¹ * r : NNReal) : ENNReal) ^ 3))
  let sourceFactor : ENNReal := J * (source.shadingDensity * area)
  let johnLoss : ENNReal := winnerSideLargeBWeightedOverlapJohnLoss
  let rawLoss : ENNReal :=
    winnerSideLargeBWeightedOverlapRawLoss S P labelInner
  have houter : A.frozenCoarse.averageMultiplicity <= outerBound :=
    winnerSideLargeB_frozenOuter_le_of_weightedOverlap_atCoordinates
      (rho := rho) (iota := ActiveParentIndex S)
      (fine := S.coarse.restrictTo S.activeCoarse)
      (active := (Finset.univ : Finset (ActiveParentIndex S)))
      P Rside source rFrozen A hAfrozen labelOuter outerBound hoverlap
  have hcrossScaled : sourceFactor *
        (finalFiberShading A (some q)).averageMultiplicity <=
      selectedOccurrenceFrozenSameQPositiveCarrierExpandedEq46LHS
        S P r labelInner d := by
    simpa only [sourceFactor, J, area, e, d,
      selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor] using
        hinnerCross
  have hscaled : sourceFactor *
        (actualRefinementShading A).averageMultiplicity <=
      rawLoss * (outerBound * (d * G)) := by
    apply (source_mul_average_le_four_mul_outerBound_mul_innerNumerator
      sourceFactor (actualRefinementShading A).averageMultiplicity
      A.frozenCoarse.averageMultiplicity
      (finalFiberShading A (some q)).averageMultiplicity outerBound
      (selectedOccurrenceFrozenSameQPositiveCarrierExpandedEq46LHS
        S P r labelInner d) hproduct houter hcrossScaled).trans_eq
    dsimp only [rawLoss, G]
    unfold winnerSideLargeBWeightedOverlapRawLoss
      selectedOccurrenceFrozenSameQPositiveCarrierExpandedEq46LHS
    ac_rfl
  have hsource0 : sourceFactor ≠ 0 := by
    dsimp only [sourceFactor, J, area, e]
    exact selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor_ne_zero
      S hrho P q source r hr labelInner hsource
  have hsourceTop : sourceFactor ≠ ∞ := by
    dsimp only [sourceFactor, J, area, e]
    exact selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor_ne_top
      S hrho P q source r hr labelInner hsource
  have hJohn : d * G <= J * (johnLoss * ((m : ENNReal) * area)) := by
    simpa only [d, G, J, johnLoss, m, area, e,
      winnerSideLargeBWeightedOverlapJohnLoss] using
        blockDensity_mul_thresholdedCordobaNumerator_le_jacobian_card_area
          S hrho hrhoHalf P q r hr labelInner
  have hjoint' : johnLoss * (m : ENNReal) * outerBound <=
      (source.shadingDensity * geometryLoss * densityLoss) *
        (proposition66AOuterFactor rho
            (bucketShortA labelOuter) (bucketShortB labelOuter)
            Rside.card outerKT epsilon beta *
          proposition66AInnerFactor rho
            (bucketShortA labelInner) (bucketShortB labelInner)
            m epsilon beta) := by
    simpa only [WinnerSideLargeBWeightedOverlapJointBudgetAt,
      johnLoss, m] using hjoint
  have hwhole :
      (actualRefinementShading A).averageMultiplicity <=
        (rawLoss * geometryLoss * densityLoss *
          prop66InnerScaleMismatchLoss
            (bucketShortA labelOuter) (bucketShortB labelOuter)
            (bucketShortA labelInner) (bucketShortB labelInner) beta) *
          proposition66AFrostmanFactor rho
            (bucketShortA labelOuter) (bucketShortB labelOuter)
            (Rside.card * m) outerKT epsilon beta :=
    average_le_wholeProp66AFrostmanFactor_of_jointOuterHullReserve_twoScale_countOne
      (delta := rho)
      (outerA := bucketShortA labelOuter)
      (outerB := bucketShortB labelOuter)
      (innerA := bucketShortA labelInner)
      (innerB := bucketShortB labelInner)
      (plankCount := Rside.card) (tubesPerPlank := m)
      (average := (actualRefinementShading A).averageMultiplicity)
      (d := d) (outerBound := outerBound) (geometricScale := G)
      (jacobian := J) (sourceDensity := source.shadingDensity)
      (area := area) (johnLoss := johnLoss) (rawLoss := rawLoss)
      (geometryLoss := geometryLoss) (targetCF := outerKT)
      (densityLoss := densityLoss)
      (epsilon := epsilon) (beta := beta)
      hrho
      (bucketShortA_pos labelOuter)
      ((bucketShortA_pos labelOuter).trans_le
        (bucketShortA_le_bucketShortB labelOuter))
      (bucketShortA_pos labelInner)
      ((bucketShortA_pos labelInner).trans_le
        (bucketShortA_le_bucketShortB labelInner))
      hbeta hbetaOne hsource0 hsourceTop
      (by simpa only [sourceFactor] using hscaled)
      hJohn hjoint'
  simpa only [WinnerSideLargeBWeightedOverlapConclusionAt,
    rawLoss, m] using hwhole

#print axioms SelectedNormalizedOuterWeightedOverlapBudgetAt
#print axioms winnerSideLargeB_frozenOuter_le_of_weightedOverlap_atCoordinates
#print axioms WinnerSideLargeBWeightedOverlapJointBudgetAt
#print axioms WinnerSideLargeBWeightedOverlapConclusionAt
#print axioms source_mul_average_le_four_mul_outerBound_mul_innerNumerator
#print axioms
  average_le_wholeProp66AFrostmanFactor_of_jointOuterHullReserve_twoScale_countOne
#print axioms winnerSide_largeB_weightedOverlap_productAtCoordinates

end
end Family8WinnerSideJointBucketLargeBWeightedOverlapConsumerV1
