import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
import Family8Grounding.Family8SelectedParentExactAssemblyProp66ACountLossConnectorV2

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalProp66AConsumerV2

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
open Family8Prop66AActualFamilyVolumeTransportV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentExactAssemblyCordobaProductV2
open Family8SelectedParentExactAssemblyProp66AConnectorV3
open Family8SelectedParentExactAssemblyProp66ACountLossConnectorV2
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-!
# Direct global-cap adapter to the exact Prop. 6.6(A) count-loss consumer

The only count datum is the actual finite global cap.  Its callback-free
Eq. (46) inequality is filled internally.  The two remaining premises are
exactly the existing outer and inner analytic scalar estimates on the same
ExactAssembly; neither is a count callback.
-/

/-- The selected-parent scalar consumer with
`plankCount = card ActiveParentIndex`, `tubesPerPlank = globalCap`, and
`countLoss = globalCap`, so no independent Eq. (46) count premise remains. -/
theorem exists_selectedParentScales_refinementAverage_le_globalCap_mul_actualFrostmanRHS
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
    (C CF : ENNReal) {epsilon beta : Real}
    (hbeta : 0 ≤ beta) (hbetaOne : beta ≤ 1)
    (houter : ∀ k label,
      label ∈ occupiedWeightBuckets
        (Finset.univ : Finset
          {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
        (fun p ↦ sideShapeLabel
          (selectedParentLongRelabeledSide
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
            S (blockAt S.activeCoarseFamily P k).fiber hrho p)) →
      ((greedyParentFactorization S P).inducedShading
        A.refinement.shading).averageMultiplicity ≤
        proposition66AOuterFactor rho
          (bucketShortA label) (bucketShortB label)
          (Fintype.card (ActiveParentIndex S)) CF epsilon beta)
    (hinnerScalar : ∀ k label,
      label ∈ occupiedWeightBuckets
        (Finset.univ : Finset
          {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
        (fun p ↦ sideShapeLabel
          (selectedParentLongRelabeledSide
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
            S (blockAt S.activeCoarseFamily P k).fiber hrho p)) →
      selectedParentFineLevelLogarithmicCordobaRHS
          D S hrho P k r hr A label KT ≤
        proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label)
          (centeredAdaptiveGlobalFullFiberNatCap S hrho P r hr C)
          epsilon beta) :
    ∃ a b : NNReal,
      0 < a ∧ a ≤ b ∧ b ≤ 1 ∧
      A.refinement.shading.averageMultiplicity ≤
        (centeredAdaptiveGlobalFullFiberNatCap S hrho P r hr C : ENNReal) ^
            (1 - beta / 2) *
          ((proposition66AFrostmanAspectGain a b CF beta *
              (2 : ENNReal) ^ (1 - beta / 2)) *
            frostmanMultiplicityRHS rho
              (activeParentActualTubeDatum S D.shading).actualFamilyVolume
              epsilon beta) := by
  exact
    exists_selectedParentScales_refinementAverage_le_countLoss_mul_actualFrostmanRHS
      D hD S hrho hrhoOne hrhoHalf P r hr A hsource KT hKT
      (plankCount := Fintype.card (ActiveParentIndex S))
      (tubesPerPlank := centeredAdaptiveGlobalFullFiberNatCap
        S hrho P r hr C)
      (CF := CF)
      (countLoss := (centeredAdaptiveGlobalFullFiberNatCap
        S hrho P r hr C : ENNReal))
      hbeta hbetaOne
      (selectedParent_centeredAdaptive_globalEq46Count
        S hrho P r hr C)
      houter hinnerScalar

#print axioms
  exists_selectedParentScales_refinementAverage_le_globalCap_mul_actualFrostmanRHS

end
end Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalProp66AConsumerV2
