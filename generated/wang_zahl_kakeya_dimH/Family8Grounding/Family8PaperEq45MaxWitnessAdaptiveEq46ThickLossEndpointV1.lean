import Family8Grounding.Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV17
import Mathlib.Tactic

/-!
# Honest selected-bucket endpoint retaining the Family 6 thickening loss

The SAFE V17 endpoint asks for a scalar absorption which is not uniform in
the current max-witness input: `Delta` has no upper bound, while the Family 6
factor contains `thickM^(beta/2)`.  This successor removes that absorption
premise.  It applies Equation (45) to the literal common-witness datum,
Equation (46) to the actual mass-popular selected bucket, and retains their
honest product.

The exact factorization below makes the missing loss explicit rather than
hiding it in a callback.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessAdaptiveEq46ThickLossEndpointV1

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
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2.PaperEq45MaxWitnessCommonScaleInput
open Family8Prop66AOuterInnerProductAlgebraV1
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
open Family8UniqueOwnerLocalDeltaMaxThickControlV1
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
  (C : StickyScaleCover fine rho)
  {P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine}
  {Y : Shading fine.bodyFamily}
  {R0 : Finset (Fin (blocks fine.bodyFamily P).length)}
  {conflictLoss : ENNReal}
  {W : DoubledParentConflictWeightedSelection C
    (occurrenceMaxOwnerMass C P Y R0) conflictLoss}

/-- The common-witness Family 6 scalar with only its honest thickening power
removed. -/
def commonWitnessFamily6Remainder
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 conflictLoss W)
    (epsilon beta : Real) : ENNReal :=
  (maxWitnessCommonWidth delta : ENNReal) ^ (-epsilon) *
    I.frostmanConstant ^ (1 - beta / 2) *
    ((maxWitnessCommonWidth delta : ENNReal) /
      (maxWitnessCommonWidth delta : ENNReal)) *
    (maxWitnessCommonWidth delta : ENNReal) ^ (-2 * beta) *
    (((maxWitnessCommonWidth delta : ENNReal) ^ (2 : Nat)) *
      (plankCount C I : ENNReal)) ^ (1 - beta / 2)

/-- Exact audit identity: this is the entire dependence of Equation (45) on
the underconstrained `Delta` field. -/
theorem family6Factor_eq_thickM_rpow_mul_remainder
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 conflictLoss W)
    (epsilon beta : Real) :
    family6Factor C I epsilon beta =
      (thickM C I : ENNReal) ^ (beta / 2) *
        commonWitnessFamily6Remainder C I epsilon beta := by
  unfold family6Factor convexPlankFrostmanFactor
  unfold commonWitnessFamily6Remainder plankCount
  ac_rfl

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

/-- V17 with the unprovable uniform absorption removed.  The actual selected
`a,b`, adaptive global cap, and exact-assembly object are unchanged; the RHS
now displays the genuine common-witness thickening power. -/
theorem exists_family6Parameters_refinementAverage_le_thickLossEq45_mul_adaptiveEq46
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
    (hbetaOne : beta ≤ 1)
    (hlossEta : 0 < lossEta)
    (hsideThreshold :
      rho1 ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold
        1 (lossEta / 2))
    (hangleThreshold :
      rho1 / 2 ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold
        (4 * certifiedPlankThresholdedAngleScaleCap 576)
        (lossEta / 4))
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
            ((((I1.fibreCardCap : ENNReal) * conflictLoss1) *
                (I1.fibreCardCap : ENNReal)) *
              ((thickM U1 I1 : ENNReal) ^ (beta / 2) *
                commonWitnessFamily6Remainder U1 I1
                  lemmaEpsilon beta)) *
              proposition66AInnerFactor rho1 a b
                (centeredAdaptiveGlobalFullFiberNatCap
                  S1 hrho1 P1 r hr adaptiveC) epsilon beta := by
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
  obtain ⟨eta, b0, heta, hb0, hEq45⟩ :=
    exists_family6Parameters_refinedAverage_le U1 I1 H lemmaEpsilon
      hlemmaEpsilon
  refine ⟨eta, b0, heta, hb0, ?_⟩
  intro hw hwb0 hdensity
  let outerLoss : ENNReal :=
    ((I1.fibreCardCap : ENNReal) * conflictLoss1) *
      (I1.fibreCardCap : ENNReal)
  have houterSelected :
      (selectedOccurrenceOuterShading
        (canonicalUpperPartition S1 U1 P1)
        A1.refinement.shading Finset.univ).averageMultiplicity ≤
        outerLoss * family6Factor U1 I1 lemmaEpsilon beta := by
    exact (sourceAverage_le_refined U1 I1).trans
      (mul_le_mul' le_rfl (hEq45 hw hwb0 hdensity))
  have houterQ :
      ((convexFactorization S1.activeCoarseFamily
        (canonicalUpperPartition S1 U1 P1)).inducedShading
          A1.refinement.shading).averageMultiplicity ≤
        outerLoss * family6Factor U1 I1 lemmaEpsilon beta := by
    rw [← selectedOccurrenceOuterShading_univ_averageMultiplicity_eq_induced
      (canonicalUpperPartition S1 U1 P1) A1.refinement.shading]
    exact houterSelected
  have houter :
      ((greedyParentFactorization S1 P1).inducedShading
        A1.refinement.shading).averageMultiplicity ≤
        outerLoss * family6Factor U1 I1 lemmaEpsilon beta := by
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
  refine ⟨bucketShortA label, bucketShortB label, ha, hab, hb, ?_⟩
  calc
    A1.refinement.shading.averageMultiplicity ≤
        ((greedyParentFactorization S1 P1).inducedShading
          A1.refinement.shading).averageMultiplicity *
          (sourceFineLevelShading A1 (some k)).averageMultiplicity := hproduct
    _ ≤ (outerLoss * family6Factor U1 I1 lemmaEpsilon beta) *
        proposition66AInnerFactor rho1
          (bucketShortA label) (bucketShortB label)
          globalCap epsilon beta := mul_le_mul' houter hinner
    _ = (outerLoss *
          ((thickM U1 I1 : ENNReal) ^ (beta / 2) *
            commonWitnessFamily6Remainder U1 I1 lemmaEpsilon beta)) *
        proposition66AInnerFactor rho1
          (bucketShortA label) (bucketShortB label)
          globalCap epsilon beta := by
      unfold family6Factor commonWitnessFamily6Remainder
      unfold convexPlankFrostmanFactor plankCount
      ac_rfl

end SameSelectedBucket

#print axioms commonWitnessFamily6Remainder
#print axioms family6Factor_eq_thickM_rpow_mul_remainder
#print axioms
  exists_family6Parameters_refinementAverage_le_thickLossEq45_mul_adaptiveEq46

end
end Family8PaperEq45MaxWitnessAdaptiveEq46ThickLossEndpointV1
