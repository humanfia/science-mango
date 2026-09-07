import Family8Grounding.Family8CanonicalExactWeightedDef212FrostmanEndpointV2
import Family8Grounding.Family8FrostmanRHSScaleVolumeAlgebraV8
import Family8Grounding.Family8RestrictedActualDatumDensityRetentionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalExactWeightedDef212SelfImprovementRHSV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8DoubledParentConflictWeightedRestrictedCoverEndpointV2.ScaleCover
open Family8DoubledParentConflictWeightedDef212EndpointV1.ScaleCover
open Family8DoubledParentConflictWeightedShadingMassBridgeV2.ScaleCover
open Family8DoubledParentConflictKatzTaoWeightedDef212FrostmanV2
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV14
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV17
open Family8CanonicalLowerBufferedScaleV4
open Family8FrostmanWeightedSelectedDirectBaseBudgetV3
open Family8FrostmanRHSScaleVolumeAlgebraV4
open Family8FrostmanRHSScaleVolumeAlgebraV8
open Family8RestrictedActualDatumDensityRetentionV1
open Family8CanonicalExactWeightedDef212FrostmanEndpointV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Exact-degree weighted self-improvement RHS

The retained source shading mass supplies a genuine volume floor for the
literal weighted restriction.  Combining that floor with the exact
doubled-parent conflict-degree cap absorbs the selection scalar directly
into an improved Frostman exponent.  There is no fixed-John loss, copy
factor, `J`, or desired-RHS callback in this connector.
-/

namespace ScaleCover

/-- The exact weighted retention inequality and a power cap on its conflict
budget force a power lower bound for the literal selected family volume.
The exponent is exactly twice the source Frostman loss plus the conflict
degree loss. -/
theorem weightedSelected_actualFamilyVolume_powerFloor_of_frostman
    {delta rho : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    {sourceExponent lossExponent : Real}
    (hF : FrostmanHypotheses D sourceExponent)
    {S : StickyScaleCover D.family rho} {B : ENNReal}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading) B)
    (hactive : S.activeFine = Finset.univ)
    (hB : B <= (delta : ENNReal) ^ (-lossExponent)) :
    (delta : ENNReal) ^ (2 * sourceExponent + lossExponent) <=
      (restrictActualTubeDatum D
        (weightedSelectedFineIndices D.shading W)).actualFamilyVolume := by
  let selected := restrictActualTubeDatum D
    (weightedSelectedFineIndices D.shading W)
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hsourceMass : (delta : ENNReal) ^ (2 * sourceExponent) <=
      D.shading.shadingMass :=
    Family8AllFrostmanStickyUnionProducerV1.delta_rpow_two_eta_le_shadingMass_of_frostman
      D hD hF
  have hretained : D.shading.shadingMass <=
      B * selected.shading.shadingMass := by
    exact source_shadingMass_le_mul_weightedSelected_shadingMass
      D W hactive
  have hselectedMass : selected.shading.shadingMass <=
      selected.actualFamilyVolume :=
    selected.shading.shadingMass_le_familyVolume
  calc
    (delta : ENNReal) ^ (2 * sourceExponent + lossExponent) =
        (delta : ENNReal) ^ lossExponent *
          (delta : ENNReal) ^ (2 * sourceExponent) := by
      rw [show 2 * sourceExponent + lossExponent =
        lossExponent + 2 * sourceExponent by ring,
        ENNReal.rpow_add _ _ hd0 hdTop]
    _ <= (delta : ENNReal) ^ lossExponent *
        D.shading.shadingMass := mul_le_mul' le_rfl hsourceMass
    _ <= (delta : ENNReal) ^ lossExponent *
        (B * selected.shading.shadingMass) :=
      mul_le_mul' le_rfl hretained
    _ <= (delta : ENNReal) ^ lossExponent *
        (B * selected.actualFamilyVolume) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl hselectedMass)
    _ <= (delta : ENNReal) ^ lossExponent *
        ((delta : ENNReal) ^ (-lossExponent) *
          selected.actualFamilyVolume) :=
      mul_le_mul' le_rfl (mul_le_mul' hB le_rfl)
    _ = selected.actualFamilyVolume := by
      rw [show (delta : ENNReal) ^ lossExponent *
          ((delta : ENNReal) ^ (-lossExponent) *
            selected.actualFamilyVolume) =
        ((delta : ENNReal) ^ lossExponent *
          (delta : ENNReal) ^ (-lossExponent)) *
            selected.actualFamilyVolume by ac_rfl,
        ← ENNReal.rpow_add _ _ hd0 hdTop]
      simp

/-- Complete same-scale exact-incidence self-improvement endpoint.  The
selected RHS produced by the weighted Def. 2.12/Frostman theorem is first
improved using its automatically derived volume floor and then transported
back to the source volume by literal restriction monotonicity. -/
theorem exists_canonicalExactWeightedDef212_improvedFrostmanRHS
    {beta frostmanEpsilon frostmanEta sourceExponent targetEpsilon nu : Real}
    {delta0 delta theta : NNReal}
    {index : Type} [Fintype index] [DecidableEq index]
    (hF : FrostmanAtParameters beta frostmanEpsilon frostmanEta delta0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (hSource : FrostmanHypotheses D sourceExponent)
    {scaleEpsilon katzTaoExponent degreeAbsorbExponent
      volumeAbsorbExponent : Real}
    {A : ENNReal} {Cnn : NNReal}
    (S : StickyScaleCover D.family
      (canonicalLowerBufferedScale delta theta scaleEpsilon))
    (hactive : S.activeFine = Finset.univ)
    (huniform : IsCUniform S (Cnn : ENNReal))
    (hpaper : Set.Pairwise (Set.univ : Set index) fun i j =>
      PaperEssentiallyDistinct (D.family.tubes i) (D.family.tubes j))
    (R : UnitRescalingGeometry S)
    (hCWA : R.FibresSatisfyCWA (Cnn : ENNReal))
    (hdeltaTheta : delta <= theta) (hthetaOne : theta <= 1)
    (hscaleEpsilon : 0 <= scaleEpsilon)
    (hdegreeAbsorb : 0 < degreeAbsorbExponent)
    (hvolumeAbsorb : 0 < volumeAbsorbExponent)
    (hdegreeThreshold :
      delta <= activeOwnerExactDegreeSmallDeltaThreshold degreeAbsorbExponent)
    (hvolumeThreshold :
      delta <= directSelectedBaseVolumeSmallDeltaThreshold
        volumeAbsorbExponent)
    (hAone : 1 <= A)
    (hA : A <= (delta : ENNReal) ^ (-katzTaoExponent))
    (hKT : IsKatzTao A D.family.bodyFamily)
    (hrhoSmall :
      canonicalLowerBufferedScale delta theta scaleEpsilon <=
        (1 / 16 : NNReal))
    (hdelta0 : delta <= delta0)
    (hdensityExponent :
      sourceExponent <= frostmanEta -
        activeOwnerExactDegreePowerEnvelope scaleEpsilon
          katzTaoExponent degreeAbsorbExponent)
    (hbaseExponent :
      2 * sourceExponent +
          directSelectedBasePowerLoss scaleEpsilon katzTaoExponent
            degreeAbsorbExponent volumeAbsorbExponent <= frostmanEta)
    (hnu : 0 <= nu)
    (hgamma : beta - nu <= 2)
    (hRHSbudget :
      activeOwnerExactDegreePowerEnvelope scaleEpsilon
            katzTaoExponent degreeAbsorbExponent + 2 * nu +
          (2 * sourceExponent +
              activeOwnerExactDegreePowerEnvelope scaleEpsilon
                katzTaoExponent degreeAbsorbExponent) * nu / 2 <=
        targetEpsilon - frostmanEpsilon) :
    ∃ E : WeightedDef212ScaleEndpoint S
        (parentShadingWeight S D.shading)
        (katzTaoDoubledParentConflictBudget delta
          (canonicalLowerBufferedScale delta theta scaleEpsilon) A)
        (Cnn : ENNReal),
      (restrictActualTubeDatum D
        (weightedSelectedFineIndices D.shading E.base.selection)).IsAdmissible ∧
      D.shading.averageMultiplicity <=
        katzTaoDoubledParentConflictBudget delta
            (canonicalLowerBufferedScale delta theta scaleEpsilon) A *
          (restrictActualTubeDatum D
            (weightedSelectedFineIndices D.shading
              E.base.selection)).shading.averageMultiplicity ∧
      D.shading.averageMultiplicity <=
        frostmanMultiplicityRHS delta D.actualFamilyVolume
          targetEpsilon (beta - nu) := by
  let B : ENNReal := katzTaoDoubledParentConflictBudget delta
    (canonicalLowerBufferedScale delta theta scaleEpsilon) A
  let lossExponent : Real :=
    activeOwnerExactDegreePowerEnvelope scaleEpsilon
      katzTaoExponent degreeAbsorbExponent
  obtain ⟨E, hadmissible, havg, hfrostman⟩ :=
    exists_canonicalExactWeightedDef212_frostmanEndpoint
      hF D hD hSource S hactive huniform hpaper R hCWA
      hdeltaTheta hthetaOne hscaleEpsilon hdegreeAbsorb hvolumeAbsorb
      hdegreeThreshold hvolumeThreshold hAone hA hKT hrhoSmall hdelta0
      hdensityExponent hbaseExponent
  let selected := restrictActualTubeDatum D
    (weightedSelectedFineIndices D.shading E.base.selection)
  have hB : B <= (delta : ENNReal) ^ (-lossExponent) := by
    simpa only [B, lossExponent, katzTaoDoubledParentConflictBudget] using
      (canonicalLowerBufferedScale_exactConflictDegree_le_powerEnvelope_auto
        (globalDelta := delta) (tau := delta) (theta := theta) (A := A)
        (epsilon := scaleEpsilon) (eta := katzTaoExponent)
        (absorbEta := degreeAbsorbExponent)
        hD.delta_pos le_rfl hdeltaTheta hthetaOne hscaleEpsilon
        hdegreeAbsorb hdegreeThreshold hAone hA)
  have hvolume : (delta : ENNReal) ^
        (2 * sourceExponent + lossExponent) <= selected.actualFamilyVolume := by
    exact weightedSelected_actualFamilyVolume_powerFloor_of_frostman
      D hD hSource E.base.selection hactive hB
  have hvolumeTop : selected.actualFamilyVolume ≠ ∞ := by
    exact familyVolume_ne_top selected.family.bodyFamily
  have hnumeric :
      B * frostmanMultiplicityRHS delta selected.actualFamilyVolume
          frostmanEpsilon beta <=
        frostmanMultiplicityRHS delta selected.actualFamilyVolume
          targetEpsilon (beta - nu) := by
    apply scalar_mul_frostmanMultiplicityRHS_le_improved_of_power_budgets
      hD.delta_pos (hD.delta_le_half.trans (by norm_num)) hvolumeTop
      hB hvolume hnu
    simpa only [lossExponent] using hRHSbudget
  have himprovedSelected : D.shading.averageMultiplicity <=
      frostmanMultiplicityRHS delta selected.actualFamilyVolume
        targetEpsilon (beta - nu) := by
    have hfrostman' : D.shading.averageMultiplicity <=
        B * frostmanMultiplicityRHS delta selected.actualFamilyVolume
          frostmanEpsilon beta := by
      simpa only [B, selected] using hfrostman
    exact hfrostman'.trans hnumeric
  have hselectedVolume : selected.actualFamilyVolume <=
      (1 : ENNReal) * D.actualFamilyVolume := by
    simpa only [one_mul, selected] using
      (restrictActualTubeDatum_actualFamilyVolume_le D
        (weightedSelectedFineIndices D.shading E.base.selection))
  have htransport :=
    frostmanMultiplicityRHS_le_of_volume_le_factor_mul
      (delta := delta) (selectedVolume := selected.actualFamilyVolume)
      (sourceVolume := D.actualFamilyVolume) (factor := (1 : ENNReal))
      (epsilon := targetEpsilon) (gamma := beta - nu)
      hgamma hselectedVolume
  refine ⟨E, ?_, ?_, ?_⟩
  · exact hadmissible
  · simpa only [B] using havg
  · exact himprovedSelected.trans (by simpa using htransport)

#print axioms weightedSelected_actualFamilyVolume_powerFloor_of_frostman
#print axioms exists_canonicalExactWeightedDef212_improvedFrostmanRHS

end ScaleCover
end
end Family8CanonicalExactWeightedDef212SelfImprovementRHSV1
