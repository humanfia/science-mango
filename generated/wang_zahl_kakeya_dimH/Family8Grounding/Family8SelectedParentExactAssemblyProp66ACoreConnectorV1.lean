import Family8Grounding.Family8SelectedParentExactAssemblyProp66ACountLossConnectorV2
import Family8Grounding.Family8SelectedParentLogarithmicCordobaCoreV2

/-!
# Selected-parent Prop. 6.6(A) connector after automatic log absorption

This successor removes the full logarithmic Córdoba scalar from the honest
count-loss connector.  Its only inner analytic premise compares the actual
non-logarithmic Katz--Tao / normalized-volume / popular-mass core with
Equation (46).  Both dyadic logarithms and the fixed certified-plank angle
constant are discharged internally by explicit small-scale thresholds.

The remaining premise is the genuine density-and-scale estimate; it is not
an average-multiplicity conclusion.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentExactAssemblyProp66ACoreConnectorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentExactAssemblyProp66AConnectorV3
open Family8SelectedParentExactAssemblyProp66ACountLossConnectorV2
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankQuantitativeLossV10
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentLogarithmicCordobaCoreV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The actual count-loss endpoint, with all selected-parent logarithmic
losses absorbed before the only remaining Equation (46) comparison. -/
theorem exists_selectedParentScales_refinementAverage_le_countLoss_mul_actualFrostmanRHS_of_core
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (hsource :
      (IndexedShadingRefinement.restrictTo
        (parentAggregatedShading S D.shading)
        (greedyParentFactorization S P).index.fine).shading.shadingMass ≠ 0)
    (KT : ENNReal) (hKT : IsKatzTao KT S.activeCoarseFamily)
    {plankCount tubesPerPlank : Nat}
    {CF countLoss : ENNReal} {epsilon beta lossEta : Real}
    (hbeta : 0 ≤ beta) (hbetaOne : beta ≤ 1)
    (hlossEta : 0 < lossEta)
    (hsideThreshold :
      rho ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold
        1 (lossEta / 2))
    (hangleThreshold :
      rho / 2 ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold
        (4 * certifiedPlankThresholdedAngleScaleCap 576)
        (lossEta / 4))
    (hcount : ((plankCount * tubesPerPlank : Nat) : ENNReal) ≤
      countLoss * (Fintype.card (ActiveParentIndex S) : ENNReal))
    (houter : ∀ k label,
      label ∈ occupiedWeightBuckets
        (Finset.univ : Finset
          {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
        (fun p => sideShapeLabel
          (selectedParentLongRelabeledSide
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
            S (blockAt S.activeCoarseFamily P k).fiber hrho p)) ->
      ((greedyParentFactorization S P).inducedShading
        A.refinement.shading).averageMultiplicity ≤
        proposition66AOuterFactor rho
          (bucketShortA label) (bucketShortB label)
          plankCount CF epsilon beta)
    (hinnerCore : ∀ k label,
      label ∈ occupiedWeightBuckets
        (Finset.univ : Finset
          {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
        (fun p => sideShapeLabel
          (selectedParentLongRelabeledSide
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
            S (blockAt S.activeCoarseFamily P k).fiber hrho p)) ->
      (rho : ENNReal) ^ (-lossEta) *
          selectedParentFineLevelCordobaCore
            D S hrho P k r hr A label KT ≤
        proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label)
          tubesPerPlank epsilon beta) :
    ∃ a b : NNReal,
      0 < a ∧ a ≤ b ∧ b ≤ 1 ∧
      A.refinement.shading.averageMultiplicity ≤
        countLoss ^ (1 - beta / 2) *
          ((proposition66AFrostmanAspectGain a b CF beta *
              (2 : ENNReal) ^ (1 - beta / 2)) *
            frostmanMultiplicityRHS rho
              (activeParentActualTubeDatum S D.shading).actualFamilyVolume
              epsilon beta) := by
  apply
    exists_selectedParentScales_refinementAverage_le_countLoss_mul_actualFrostmanRHS
      D hD S hrho hrhoOne hrhoHalf P r hr A hsource KT hKT
      hbeta hbetaOne hcount houter
  intro k label hoccupied
  exact
    (selectedParentFineLevelLogarithmicCordobaRHS_le_rpow_mul_core
      D S hrho hrhoHalf P k r hr A label KT hlossEta
      hsideThreshold hangleThreshold).trans
        (hinnerCore k label hoccupied)

#print axioms
  exists_selectedParentScales_refinementAverage_le_countLoss_mul_actualFrostmanRHS_of_core

end

end Family8SelectedParentExactAssemblyProp66ACoreConnectorV1
