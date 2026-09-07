import Family8Grounding.Family8PaperEq45MaxWitnessAdaptiveEq46ThickLossEndpointV1
import Family8Grounding.Family8SelectedParentCardWeightedProp66AInnerV1
import Mathlib.Tactic

/-!
# Same-selected Equation (45)/(46) endpoint with the honest losses retained

The previous global product interface asks for a bare Proposition 6.6(A)
outer estimate for every occupied bucket.  Equation (45), however, selects
one actual bucket and supplies an outer estimate with its genuine
`fibreCardCap * conflictLoss * fibreCardCap` and `thickM^(beta/2)` losses.

This successor combines that selected Equation (45) bucket with the
card-weighted Equation (46) selector.  It neither assumes the over-strong
universal outer estimate nor hides the scale absorption in a callback.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessAdaptiveCardWeightedThickLossEndpointV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV13
open Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV17
open Family8PaperEq45MaxWitnessAdaptiveEq46ThickLossEndpointV1
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2.PaperEq45MaxWitnessCommonScaleInput
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8SelectedOccurrenceMaxWitnessCommonScaleV1
open Family8SelectedParentCardWeightedProp66AInnerV1
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankQuantitativeLossV10
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8UniqueOwnerLocalDeltaMaxThickControlV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 30000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho sigma : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  (D : ActualTubeDatum delta index)
  (S : StickyScaleCover D.family rho)
  (U : StickyScaleCover (S.coarse.restrictTo S.activeCoarse) sigma)
  (P : GreedyDensityPartition S.activeCoarseFamily
    (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
    (hullContainer S.activeCoarseFamily) Finset.univ)
  {assemblyLoss : Nat}
  (A : FactoringMultiplicityAssembly.ExactAssembly
    (greedyParentFactorization S P)
    (parentAggregatedShading S D.shading) assemblyLoss)
  {conflictLoss : ENNReal}
  (W : DoubledParentConflictWeightedSelection U
    (occurrenceMaxOwnerMass U
      (canonicalUpperPartition S U P)
      A.refinement.shading Finset.univ) conflictLoss)
  (I : PaperEq45MaxWitnessCommonScaleInput U
    A.refinement.shading Finset.univ conflictLoss W)

/-- Honest same-selected-label product of Equation (45) and the card-weighted
Equation (46) inner estimate.  The scale-dependent Equation (45) losses are
kept explicitly for the later canonical-`Delta` envelope. -/
theorem exists_family6Parameters_refinementAverage_le_thickLossEq45_mul_cardWeightedEq46
    (hD : D.IsAdmissible)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (r : NNReal) (hr : 0 < r)
    (hsource :
      (IndexedShadingRefinement.restrictTo
        (parentAggregatedShading S D.shading)
        (greedyParentFactorization S P).index.fine).shading.shadingMass ≠ 0)
    (KT : ENNReal) (hKT : IsKatzTao KT S.activeCoarseFamily)
    (tubesPerPlank : Nat)
    {beta lossEta : Real}
    (H : ConvexPlankFrostmanMultiplicityHypothesis
      {q // q ∈ selectedOccurrenceIndices
        (canonicalUpperPartition S U P) (selected U I)} beta)
    (lemmaEpsilon epsilon : Real) (hlemmaEpsilon : 0 < lemmaEpsilon)
    (hlossEta : 0 < lossEta)
    (hsideThreshold :
      rho ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold
        1 (lossEta / 2))
    (hangleThreshold :
      rho / 2 ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold
        (4 * certifiedPlankThresholdedAngleScaleCap 576)
        (lossEta / 4))
    (hEq46 : ∀ k label,
      ActualSelectedParentBucketOccupied S hrho P k r hr label →
      CardWeightedCrossEq46Budget D S hrho P k r hr A label KT
        lossEta tubesPerPlank epsilon beta) :
    ∃ eta : Real, ∃ b0 : NNReal,
      0 < eta ∧ 0 < b0 ∧
      ∀ (_hw : 0 < maxWitnessCommonWidth rho),
        maxWitnessCommonWidth rho ≤ b0 →
        (maxWitnessCommonWidth rho : ENNReal) ^ eta ≤
          (datum U I).shading.shadingDensity →
        ∃ a b : NNReal,
          0 < a ∧ a ≤ b ∧ b ≤ 1 ∧
          A.refinement.shading.averageMultiplicity ≤
            ((((I.fibreCardCap : ENNReal) * conflictLoss) *
                (I.fibreCardCap : ENNReal)) *
              ((thickM U I : ENNReal) ^ (beta / 2) *
                commonWitnessFamily6Remainder U I
                  lemmaEpsilon beta)) *
              proposition66AInnerFactor rho a b
                tubesPerPlank epsilon beta := by
  obtain ⟨k, _hvolume, hproduct, label, hoccupied, ha, hab, hb, hinner⟩ :=
    exists_cardWeightedGreedyBlock_sourceAverage_le_prop66AInner
      D hD S hrho hrhoOne hrhoHalf P r hr A hsource KT hKT
      hlossEta hsideThreshold hangleThreshold (by
        intro k label hoccupied
        exact hEq46 k label (by
          simpa only [ActualSelectedParentBucketOccupied] using hoccupied))
  obtain ⟨eta, b0, heta, hb0, hEq45⟩ :=
    exists_family6Parameters_refinedAverage_le U I H lemmaEpsilon
      hlemmaEpsilon
  refine ⟨eta, b0, heta, hb0, ?_⟩
  intro hw hwb0 hdensity
  let outerLoss : ENNReal :=
    ((I.fibreCardCap : ENNReal) * conflictLoss) *
      (I.fibreCardCap : ENNReal)
  have houterSelected :
      (selectedOccurrenceOuterShading
        (canonicalUpperPartition S U P)
        A.refinement.shading Finset.univ).averageMultiplicity ≤
        outerLoss * family6Factor U I lemmaEpsilon beta := by
    exact (sourceAverage_le_refined U I).trans
      (mul_le_mul' le_rfl (hEq45 hw hwb0 hdensity))
  have houterQ :
      ((convexFactorization S.activeCoarseFamily
        (canonicalUpperPartition S U P)).inducedShading
          A.refinement.shading).averageMultiplicity ≤
        outerLoss * family6Factor U I lemmaEpsilon beta := by
    rw [← selectedOccurrenceOuterShading_univ_averageMultiplicity_eq_induced
      (canonicalUpperPartition S U P) A.refinement.shading]
    exact houterSelected
  have houter :
      ((greedyParentFactorization S P).inducedShading
        A.refinement.shading).averageMultiplicity ≤
        outerLoss * family6Factor U I lemmaEpsilon beta := by
    calc
      ((greedyParentFactorization S P).inducedShading
        A.refinement.shading).averageMultiplicity =
          ((convexFactorization S.activeCoarseFamily
            (canonicalUpperPartition S U P)).inducedShading
              A.refinement.shading).averageMultiplicity :=
        (upperPartitionOfAll_induced_averageMultiplicity_eq
          S U (upperCover_activeFine_eq_univ S U) P
            A.refinement.shading).symm
      _ ≤ _ := houterQ
  refine ⟨bucketShortA label, bucketShortB label, ha, hab, hb, ?_⟩
  calc
    A.refinement.shading.averageMultiplicity ≤
        ((greedyParentFactorization S P).inducedShading
          A.refinement.shading).averageMultiplicity *
          (sourceFineLevelShading A (some k)).averageMultiplicity := hproduct
    _ ≤ (outerLoss * family6Factor U I lemmaEpsilon beta) *
        proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label)
          tubesPerPlank epsilon beta := mul_le_mul' houter hinner
    _ = (outerLoss *
          ((thickM U I : ENNReal) ^ (beta / 2) *
            commonWitnessFamily6Remainder U I lemmaEpsilon beta)) *
        proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label)
          tubesPerPlank epsilon beta := by
      unfold family6Factor commonWitnessFamily6Remainder
      unfold convexPlankFrostmanFactor plankCount
      ac_rfl

#print axioms
  exists_family6Parameters_refinementAverage_le_thickLossEq45_mul_cardWeightedEq46

end
end Family8PaperEq45MaxWitnessAdaptiveCardWeightedThickLossEndpointV1
