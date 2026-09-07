import Family8Grounding.Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV13
import Family8Grounding.Family8PaperEq45MaxWitnessSelectedBucketUpperV1
import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalMassPopularEndpointV3
import Mathlib.Tactic

/-!
# Same actual bucket in max-witness Equation (45) and adaptive Equation (46)

The mass-popular argument first selects one actual `(k,label)` bucket.  The
selected-bucket upper producer then targets Equation (45) at exactly
`bucketShortA label, bucketShortB label`, while the adaptive local-to-global
producer bounds Equation (46) at the same scales.  Thus the Proposition
6.6(A) scalar product is exact; the max-witness refinement loss and the
global adaptive fibre cap remain explicit.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV17

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
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2.PaperEq45MaxWitnessCommonScaleInput
open Family8PaperEq45MaxWitnessSelectedBucketUpperV1
open Family8Prop66AActualFamilyVolumeTransportV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8Prop66AUniformCountLossAlgebraV3
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8SelectedOccurrenceMaxWitnessCommonScaleV1
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankQuantitativeLossV10
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentMassPopularProp66AInnerV4
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalMassPopularEndpointV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 30000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The literal occupied-label predicate used by the adaptive selector. -/
def ActualSelectedParentBucketOccupied
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int) : Prop :=
  label ∈ occupiedWeightBuckets
    (Finset.univ : Finset
      {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
    (fun p ↦ sideShapeLabel
      (selectedParentLongRelabeledSide
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber hrho p))

section SameSelectedBucket

variable {delta1 rho1 sigma1 : NNReal} {index1 : Type}
  [Fintype index1] [DecidableEq index1]
  (D1 : ActualTubeDatum delta1 index1)
  (S1 : StickyScaleCover D1.family rho1)
  (U1 : StickyScaleCover (S1.coarse.restrictTo S1.activeCoarse) sigma1)
  (P1 : GreedyDensityPartition S1.activeCoarseFamily
    (hullCandidates (Finset.univ : Finset (ActiveParentIndex S1)))
    (hullContainer S1.activeCoarseFamily) Finset.univ)
  {assemblyLoss1 : Nat}
  (A1 : FactoringMultiplicityAssembly.ExactAssembly
    (greedyParentFactorization S1 P1)
    (parentAggregatedShading S1 D1.shading) assemblyLoss1)
  {conflictLoss1 : ENNReal}
  (W1 : DoubledParentConflictWeightedSelection U1
    (occurrenceMaxOwnerMass U1
      (canonicalUpperPartition S1 U1 P1)
      A1.refinement.shading Finset.univ) conflictLoss1)
  (I1 : PaperEq45MaxWitnessCommonScaleInput U1
    A1.refinement.shading Finset.univ conflictLoss1 W1)

theorem exists_family6Parameters_refinementAverage_le_selectedBucketEq45_mul_adaptiveEq46
    (hD1 : D1.IsAdmissible)
    (hrho1 : 0 < rho1) (hrhoOne1 : rho1 ≤ 1)
    (hrhoHalf1 : rho1 ≤ (2 : NNReal)⁻¹)
    (r : NNReal) (hr : 0 < r)
    (hsource :
      (IndexedShadingRefinement.restrictTo
        (parentAggregatedShading S1 D1.shading)
        (greedyParentFactorization S1 P1).index.fine).shading.shadingMass ≠ 0)
    (KT : ENNReal) (hKT : IsKatzTao KT S1.activeCoarseFamily)
    (adaptiveC : ENNReal)
    {beta lossEta : Real}
    (H : ConvexPlankFrostmanMultiplicityHypothesis
      {q // q ∈ selectedOccurrenceIndices
        (canonicalUpperPartition S1 U1 P1) (selected U1 I1)} beta)
    (lemmaEpsilon epsilon : Real) (hlemmaEpsilon : 0 < lemmaEpsilon)
    (hbeta : 0 ≤ beta) (hbetaOne : beta ≤ 1)
    (hlossEta : 0 < lossEta)
    (hsideThreshold :
      rho1 ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold
        1 (lossEta / 2))
    (hangleThreshold :
      rho1 / 2 ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold
        (4 * certifiedPlankThresholdedAngleScaleCap 576)
        (lossEta / 4))
    (habsorb : ∀ k label,
      ActualSelectedParentBucketOccupied S1 hrho1 P1 k r hr label →
      SelectedBucketScaleAbsorption U1 I1 rho1
        (bucketShortA label) (bucketShortB label)
        lemmaEpsilon epsilon beta)
    (hEq46Local : ∀ k label,
      ActualSelectedParentBucketOccupied S1 hrho1 P1 k r hr label →
      MassPopularCrossEq46Budget D1 S1 hrho1 P1 k r hr A1 label KT
        lossEta
        (centeredAdaptiveActualBucketFullFiberNatCap
          S1 hrho1 P1 k r hr label adaptiveC) epsilon beta) :
    ∃ eta : Real, ∃ b0 : NNReal,
      0 < eta ∧ 0 < b0 ∧
      ∀ (_hw : 0 < maxWitnessCommonWidth rho1),
        maxWitnessCommonWidth rho1 ≤ b0 →
        (maxWitnessCommonWidth rho1 : ENNReal) ^ eta ≤
          (datum U1 I1).shading.shadingDensity →
        ∃ a b : NNReal,
          0 < a ∧ a ≤ b ∧ b ≤ 1 ∧
          A1.refinement.shading.averageMultiplicity ≤
            (((((I1.fibreCardCap : ENNReal) * conflictLoss1) *
                (I1.fibreCardCap : ENNReal)) *
              (centeredAdaptiveGlobalFullFiberNatCap
                S1 hrho1 P1 r hr adaptiveC : ENNReal) ^
                  (1 - beta / 2)) *
              ((proposition66AFrostmanAspectGain a b
                  I1.frostmanConstant beta *
                    (2 : ENNReal) ^ (1 - beta / 2)) *
                frostmanMultiplicityRHS rho1
                  (activeParentActualTubeDatum S1 D1.shading).actualFamilyVolume
                  epsilon beta)) := by
  let globalCap := centeredAdaptiveGlobalFullFiberNatCap
    S1 hrho1 P1 r hr adaptiveC
  have hEq46Global : ∀ k label,
      ActualSelectedParentBucketOccupied S1 hrho1 P1 k r hr label →
      MassPopularCrossEq46Budget D1 S1 hrho1 P1 k r hr A1 label KT
        lossEta globalCap epsilon beta := by
    intro k label hoccupied
    exact massPopularCrossEq46Budget_localCap_to_global
      D1 S1 hrho1 P1 k r hr A1 label KT adaptiveC hbetaOne
      (by simpa only [ActualSelectedParentBucketOccupied] using hoccupied)
      (hEq46Local k label hoccupied)
  obtain ⟨k, _hvolume, hproduct, label, hoccupied, ha, hab, hb, hinner⟩ :=
    exists_massPopularGreedyBlock_sourceAverage_le_prop66AInner
      D1 hD1 S1 hrho1 hrhoOne1 hrhoHalf1 P1 r hr A1 hsource KT hKT
      hlossEta hsideThreshold hangleThreshold (by
        intro k label hoccupied
        exact hEq46Global k label (by
          simpa only [ActualSelectedParentBucketOccupied] using hoccupied))
  have hoccupied' : ActualSelectedParentBucketOccupied
      S1 hrho1 P1 k r hr label := by
    simpa only [ActualSelectedParentBucketOccupied] using hoccupied
  obtain ⟨eta, b0, heta, hb0, hEq45⟩ :=
    exists_family6Parameters_sourceAverage_le_eq45_at_selectedBucketScales
      U1 I1 H rho1 lemmaEpsilon epsilon hlemmaEpsilon
      (habsorb k label hoccupied')
  refine ⟨eta, b0, heta, hb0, ?_⟩
  intro hw hwb0 hdensity
  let outerLoss : ENNReal :=
    ((I1.fibreCardCap : ENNReal) * conflictLoss1) *
      (I1.fibreCardCap : ENNReal)
  have houterSelected := hEq45 hw hwb0 hdensity
  have houterQ :
      ((convexFactorization S1.activeCoarseFamily
        (canonicalUpperPartition S1 U1 P1)).inducedShading
          A1.refinement.shading).averageMultiplicity ≤
        outerLoss * proposition66AOuterFactor rho1
          (bucketShortA label) (bucketShortB label)
          (plankCount U1 I1) I1.frostmanConstant epsilon beta := by
    rw [← selectedOccurrenceOuterShading_univ_averageMultiplicity_eq_induced
      (canonicalUpperPartition S1 U1 P1) A1.refinement.shading]
    convert houterSelected using 1
    congr 1
  have houter :
      ((greedyParentFactorization S1 P1).inducedShading
        A1.refinement.shading).averageMultiplicity ≤
        outerLoss * proposition66AOuterFactor rho1
          (bucketShortA label) (bucketShortB label)
          (plankCount U1 I1) I1.frostmanConstant epsilon beta := by
    calc
      ((greedyParentFactorization S1 P1).inducedShading
        A1.refinement.shading).averageMultiplicity =
          ((convexFactorization S1.activeCoarseFamily
            (canonicalUpperPartition S1 U1 P1)).inducedShading
              A1.refinement.shading).averageMultiplicity :=
        (upperPartitionOfAll_induced_averageMultiplicity_eq
          S1 U1 (upperCover_activeFine_eq_univ S1 U1) P1
            A1.refinement.shading).symm
      _ ≤ _ := houterQ
  have hcount := maxWitnessCommonScale_uniformEq46Count S1 U1 I1 globalCap
  have hbpos : 0 < bucketShortB label := ha.trans_le hab
  have hscalar :=
    proposition66AOuterFactor_mul_innerFactor_le_countLoss_mul_frostmanFactor
      (CF := I1.frostmanConstant) (countLoss := (globalCap : ENNReal))
      (epsilon := epsilon) (beta := beta)
      I1.delta_pos ha hbpos hbeta hbetaOne hcount
  have hactual := proposition66AFrostmanFactor_le_actualRHS_with_two_rpow
    (activeParentActualTubeDatum S1 D1.shading)
    (a := bucketShortA label) (b := bucketShortB label)
    (CF := I1.frostmanConstant) (epsilon := epsilon) (beta := beta)
    hrhoHalf1 (hbetaOne.trans (by norm_num))
  refine ⟨bucketShortA label, bucketShortB label, ha, hab, hb, ?_⟩
  calc
    A1.refinement.shading.averageMultiplicity ≤
        ((greedyParentFactorization S1 P1).inducedShading
          A1.refinement.shading).averageMultiplicity *
          (sourceFineLevelShading A1 (some k)).averageMultiplicity := hproduct
    _ ≤ (outerLoss * proposition66AOuterFactor rho1
          (bucketShortA label) (bucketShortB label)
          (plankCount U1 I1) I1.frostmanConstant epsilon beta) *
        proposition66AInnerFactor rho1
          (bucketShortA label) (bucketShortB label)
          globalCap epsilon beta := mul_le_mul' houter hinner
    _ = outerLoss *
        (proposition66AOuterFactor rho1
          (bucketShortA label) (bucketShortB label)
          (plankCount U1 I1) I1.frostmanConstant epsilon beta *
        proposition66AInnerFactor rho1
          (bucketShortA label) (bucketShortB label)
          globalCap epsilon beta) := by ac_rfl
    _ ≤ outerLoss *
        ((globalCap : ENNReal) ^ (1 - beta / 2) *
          proposition66AFrostmanFactor rho1
            (bucketShortA label) (bucketShortB label)
            (Fintype.card (ActiveParentIndex S1)) I1.frostmanConstant
            epsilon beta) := mul_le_mul' le_rfl hscalar
    _ ≤ outerLoss *
        ((globalCap : ENNReal) ^ (1 - beta / 2) *
          ((proposition66AFrostmanAspectGain
              (bucketShortA label) (bucketShortB label)
              I1.frostmanConstant beta *
                (2 : ENNReal) ^ (1 - beta / 2)) *
            frostmanMultiplicityRHS rho1
              (activeParentActualTubeDatum S1 D1.shading).actualFamilyVolume
              epsilon beta)) := by
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hactual)
    _ = (outerLoss *
          (globalCap : ENNReal) ^ (1 - beta / 2)) *
          ((proposition66AFrostmanAspectGain
              (bucketShortA label) (bucketShortB label)
              I1.frostmanConstant beta *
                (2 : ENNReal) ^ (1 - beta / 2)) *
            frostmanMultiplicityRHS rho1
              (activeParentActualTubeDatum S1 D1.shading).actualFamilyVolume
              epsilon beta) := by ac_rfl

end SameSelectedBucket

#print axioms ActualSelectedParentBucketOccupied
#print axioms
  exists_family6Parameters_refinementAverage_le_selectedBucketEq45_mul_adaptiveEq46

end
end Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV17
