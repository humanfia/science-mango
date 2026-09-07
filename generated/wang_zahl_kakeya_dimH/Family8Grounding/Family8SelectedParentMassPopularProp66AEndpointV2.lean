import Family8Grounding.Family8SelectedParentMassPopularProp66AInnerV4
import Family8Grounding.Family8SelectedParentExactAssemblyProp66ACountLossConnectorV2

/-!
# Proposition 6.6(A) after mass-popular inner cancellation

The mass-popular selected fibre now supplies the actual inner Lemma 6.4
factor once the division-free Equation (46) scalar budget is known.  This
module composes that result with the genuine outer factor, uniform-count
loss, and actual-family-volume transport already proved in the canonical
Proposition 6.6(A) algebra.

The only remaining geometric producers are therefore visible inputs:
the outer Lemma 6.4 estimate and `MassPopularCrossEq46Budget`.  Neither is
repackaged as a multiplicity conclusion field.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentMassPopularProp66AEndpointV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop66AActualFamilyVolumeTransportV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8Prop66AUniformCountLossAlgebraV3
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentExactAssemblyProp66ACountLossConnectorV2
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankQuantitativeLossV10
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentMassPopularProp66AInnerV4
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The actual selected-parent endpoint with all inner bucket denominators
and logarithmic losses removed internally. -/
theorem exists_selectedParentScales_refinementAverage_le_countLoss_mul_actualFrostmanRHS_of_crossEq46
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
            S (blockAt S.activeCoarseFamily P k).fiber hrho p)) →
      ((greedyParentFactorization S P).inducedShading
        A.refinement.shading).averageMultiplicity ≤
        proposition66AOuterFactor rho
          (bucketShortA label) (bucketShortB label)
          plankCount CF epsilon beta)
    (hEq46 : ∀ k label,
      label ∈ occupiedWeightBuckets
        (Finset.univ : Finset
          {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
        (fun p => sideShapeLabel
          (selectedParentLongRelabeledSide
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
            S (blockAt S.activeCoarseFamily P k).fiber hrho p)) →
      MassPopularCrossEq46Budget D S hrho P k r hr A label KT
        lossEta tubesPerPlank epsilon beta) :
    ∃ a b : NNReal,
      0 < a ∧ a ≤ b ∧ b ≤ 1 ∧
      A.refinement.shading.averageMultiplicity ≤
        countLoss ^ (1 - beta / 2) *
          ((proposition66AFrostmanAspectGain a b CF beta *
              (2 : ENNReal) ^ (1 - beta / 2)) *
            frostmanMultiplicityRHS rho
              (activeParentActualTubeDatum S D.shading).actualFamilyVolume
              epsilon beta) := by
  obtain ⟨k, _hvolume, hproduct, label, hoccupied, ha, hab, hb,
      hinner⟩ :=
    exists_massPopularGreedyBlock_sourceAverage_le_prop66AInner
      D hD S hrho hrhoOne hrhoHalf P r hr A hsource KT hKT hlossEta
      hsideThreshold hangleThreshold hEq46
  have hfactor : A.refinement.shading.averageMultiplicity ≤
      countLoss ^ (1 - beta / 2) *
        proposition66AFrostmanFactor rho
          (bucketShortA label) (bucketShortB label)
          (Fintype.card (ActiveParentIndex S)) CF epsilon beta := by
    calc
      A.refinement.shading.averageMultiplicity ≤
          ((greedyParentFactorization S P).inducedShading
            A.refinement.shading).averageMultiplicity *
            (sourceFineLevelShading A (some k)).averageMultiplicity := hproduct
      _ ≤ proposition66AOuterFactor rho
            (bucketShortA label) (bucketShortB label)
            plankCount CF epsilon beta *
          proposition66AInnerFactor rho
            (bucketShortA label) (bucketShortB label)
            tubesPerPlank epsilon beta :=
        mul_le_mul' (houter k label hoccupied) hinner
      _ ≤ countLoss ^ (1 - beta / 2) *
          proposition66AFrostmanFactor rho
            (bucketShortA label) (bucketShortB label)
            (Fintype.card (ActiveParentIndex S)) CF epsilon beta :=
        proposition66AOuterFactor_mul_innerFactor_le_countLoss_mul_frostmanFactor
          hrho ha (ha.trans_le hab) hbeta hbetaOne hcount
  have hactual :=
    proposition66AFrostmanFactor_le_actualRHS_with_two_rpow
      (activeParentActualTubeDatum S D.shading)
      (a := bucketShortA label) (b := bucketShortB label)
      (CF := CF) (epsilon := epsilon) (beta := beta)
      hrhoHalf (hbetaOne.trans (by norm_num))
  refine ⟨bucketShortA label, bucketShortB label, ha, hab, hb, ?_⟩
  exact hfactor.trans (mul_le_mul' le_rfl hactual)

#print axioms
  exists_selectedParentScales_refinementAverage_le_countLoss_mul_actualFrostmanRHS_of_crossEq46

end

end Family8SelectedParentMassPopularProp66AEndpointV2
