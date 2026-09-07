import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
import Family8Grounding.Family8SelectedParentMassPopularProp66AEndpointV2

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalMassPopularEndpointV3

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
open Family8Prop66AActualFamilyVolumeTransportV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankQuantitativeLossV10
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentMassPopularProp66AEndpointV2
open Family8SelectedParentMassPopularProp66AInnerV4
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
open Family8SelectedParentPlankCenteredAdaptiveThinCountUniformEq46CountV2
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8SelectedParentPlankFreshFullFiberCountV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-!
# Local actual Eq. (46) budgets lifted to the global adaptive cap

An analytic producer naturally works at one actual `(k,label)` bucket.  Its
local natural cap is below the finite global cap, and the Prop. 6.6(A) inner
factor is monotone in this count.  Thus local scalar budgets can be lifted
without demanding that a producer anticipate the downstream global maximum.
-/

/-- Canonical actual full-fibre cap at one selected-parent bucket. -/
def centeredAdaptiveActualBucketFullFiberNatCap
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (C : ENNReal) : Nat :=
  centeredAdaptiveUniformFullFiberNatCap
    (selectedParentCenteredHalfPostAdaptiveProxyScale delta rho r label)
    (contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
    S (blockAt S.activeCoarseFamily P k).fiber hrho label
      (selectedParentLiteralPlankBucket_isPlank S hrho P k r hr label) C

theorem centeredAdaptiveActualBucketFullFiberNatCap_le_global
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (hoccupied : label ∈ occupiedWeightBuckets
      (Finset.univ : Finset
        {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
      (fun p ↦ sideShapeLabel
        (selectedParentLongRelabeledSide
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho p)))
    (C : ENNReal) :
    centeredAdaptiveActualBucketFullFiberNatCap
        S hrho P k r hr label C ≤
      centeredAdaptiveGlobalFullFiberNatCap S hrho P r hr C := by
  apply centeredAdaptiveUniformFullFiberNatCap_le_global
    S hrho P k r hr label
  simpa only [selectedParentOccupiedShapeLabels] using hoccupied

/-- A local mass-popular Eq. (46) budget remains valid after replacing its
bucket cap by the single global cap. -/
theorem massPopularCrossEq46Budget_localCap_to_global
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (label : Fin 3 → Int) (KT C : ENNReal)
    {lossEta epsilon beta : Real} (hbetaOne : beta ≤ 1)
    (hoccupied : label ∈ occupiedWeightBuckets
      (Finset.univ : Finset
        {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
      (fun p ↦ sideShapeLabel
        (selectedParentLongRelabeledSide
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho p)))
    (hlocal : MassPopularCrossEq46Budget
      D S hrho P k r hr A label KT lossEta
      (centeredAdaptiveActualBucketFullFiberNatCap
        S hrho P k r hr label C) epsilon beta) :
    MassPopularCrossEq46Budget
      D S hrho P k r hr A label KT lossEta
      (centeredAdaptiveGlobalFullFiberNatCap S hrho P r hr C)
      epsilon beta := by
  unfold MassPopularCrossEq46Budget at hlocal ⊢
  exact hlocal.trans (mul_le_mul' le_rfl
    (proposition66AInnerFactor_mono_tubesPerPlank
      (hbetaOne.trans (by norm_num))
      (centeredAdaptiveActualBucketFullFiberNatCap_le_global
        S hrho P k r hr label hoccupied C)))

/-- Full selected-parent endpoint from bucket-local analytic Eq. (46)
budgets.  The global count loss and its outer cardinality inequality are
constructed internally. -/
theorem exists_selectedParentScales_refinementAverage_le_globalCap_mul_actualFrostmanRHS_of_localCrossEq46
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
    (C CF : ENNReal) {epsilon beta lossEta : Real}
    (hbeta : 0 ≤ beta) (hbetaOne : beta ≤ 1)
    (hlossEta : 0 < lossEta)
    (hsideThreshold :
      rho ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold
        1 (lossEta / 2))
    (hangleThreshold :
      rho / 2 ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold
        (4 * certifiedPlankThresholdedAngleScaleCap 576)
        (lossEta / 4))
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
    (hEq46Local : ∀ k label,
      label ∈ occupiedWeightBuckets
        (Finset.univ : Finset
          {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
        (fun p ↦ sideShapeLabel
          (selectedParentLongRelabeledSide
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
            S (blockAt S.activeCoarseFamily P k).fiber hrho p)) →
      MassPopularCrossEq46Budget D S hrho P k r hr A label KT
        lossEta
        (centeredAdaptiveActualBucketFullFiberNatCap
          S hrho P k r hr label C) epsilon beta) :
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
  apply
    exists_selectedParentScales_refinementAverage_le_countLoss_mul_actualFrostmanRHS_of_crossEq46
      D hD S hrho hrhoOne hrhoHalf P r hr A hsource KT hKT
      (plankCount := Fintype.card (ActiveParentIndex S))
      (tubesPerPlank := centeredAdaptiveGlobalFullFiberNatCap
        S hrho P r hr C)
      (CF := CF)
      (countLoss := (centeredAdaptiveGlobalFullFiberNatCap
        S hrho P r hr C : ENNReal))
      hbeta hbetaOne hlossEta hsideThreshold hangleThreshold
      (selectedParent_centeredAdaptive_globalEq46Count S hrho P r hr C)
      houter
  intro k label hoccupied
  exact massPopularCrossEq46Budget_localCap_to_global
    D S hrho P k r hr A label KT C hbetaOne hoccupied
    (hEq46Local k label hoccupied)

#print axioms centeredAdaptiveActualBucketFullFiberNatCap_le_global
#print axioms massPopularCrossEq46Budget_localCap_to_global
#print axioms
  exists_selectedParentScales_refinementAverage_le_globalCap_mul_actualFrostmanRHS_of_localCrossEq46

end
end Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalMassPopularEndpointV3
