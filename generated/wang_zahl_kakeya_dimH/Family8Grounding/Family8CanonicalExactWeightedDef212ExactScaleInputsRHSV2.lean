import Family8Grounding.Family8CanonicalExactWeightedDef212SelfImprovementRHSV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalExactWeightedDef212ExactScaleInputsRHSV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8DoubledParentConflictWeightedShadingMassBridgeV2.ScaleCover
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV14
open Family8CanonicalLowerBufferedScaleV4
open Family8FrostmanWeightedSelectedDirectBaseBudgetV3
open Family8CanonicalExactWeightedDef212SelfImprovementRHSV1.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

theorem canonicalLowerBufferedScale_self
    {delta : NNReal} (hdelta : 0 < delta) (epsilon : Real) :
    canonicalLowerBufferedScale delta delta epsilon = delta := by
  rw [canonicalLowerBufferedScale_eq_lowerEndpoint hdelta]
  simp [hdelta.ne']

/-- `ExactScaleDef212Inputs` supplies an actual scale cover and its full
Def. 2.12 geometry.  The selected endpoint is constructed internally; only
the source-level improved RHS needed by the quantified property is exposed. -/
theorem averageMultiplicity_le_improvedRHS_of_exactScaleInputs
    {beta frostmanEpsilon frostmanEta sourceExponent targetEpsilon nu : Real}
    {delta0 delta : NNReal}
    {index : Type} [Fintype index] [DecidableEq index]
    (hF : FrostmanAtParameters beta frostmanEpsilon frostmanEta delta0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (hSource : FrostmanHypotheses D sourceExponent)
    {scaleEpsilon katzTaoExponent degreeAbsorbExponent
      volumeAbsorbExponent : Real}
    {A : ENNReal} {Cnn : NNReal}
    (M : StickyMultiscaleCover D.family)
    (H : ExactScaleDef212Inputs M Cnn)
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
    (hdeltaSixteen : delta <= (1 / 16 : NNReal))
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
    D.shading.averageMultiplicity <=
      frostmanMultiplicityRHS delta D.actualFamilyVolume
        targetEpsilon (beta - nu) := by
  let hdeltaOne : delta <= 1 := hD.delta_le_half.trans (by norm_num)
  have hscaleEq := canonicalLowerBufferedScale_self hD.delta_pos scaleEpsilon
  let hdeltaScale : delta <=
      canonicalLowerBufferedScale delta delta scaleEpsilon := by
    rw [hscaleEq]
  let hscaleOne : canonicalLowerBufferedScale delta delta scaleEpsilon <= 1 := by
    rw [hscaleEq]
    exact hdeltaOne
  let S := M.cover
    (canonicalLowerBufferedScale delta delta scaleEpsilon)
    hdeltaScale hscaleOne
  let R : UnitRescalingGeometry S :=
    H.unitRescalingGeometry
      (canonicalLowerBufferedScale delta delta scaleEpsilon)
      hdeltaScale hscaleOne
  have hactive : S.activeFine = Finset.univ := by
    rw [S.activeFine_eq_refined, H.fine_refined_eq_univ]
  have huniform : IsCUniform S (Cnn : ENNReal) := by
    exact H.c_uniform
      (canonicalLowerBufferedScale delta delta scaleEpsilon)
      hdeltaScale hscaleOne
  have hCWA : R.FibresSatisfyCWA (Cnn : ENNReal) := by
    exact H.rescaled_fibres_cwa
      (canonicalLowerBufferedScale delta delta scaleEpsilon)
      hdeltaScale hscaleOne
  have hrhoSmall :
      canonicalLowerBufferedScale delta delta scaleEpsilon <=
        (1 / 16 : NNReal) := by
    rw [hscaleEq]
    exact hdeltaSixteen
  obtain ⟨E, _hadmissible, _havg, himproved⟩ :=
    exists_canonicalExactWeightedDef212_improvedFrostmanRHS
      (theta := delta) hF D hD hSource S hactive huniform
      H.fine_pairwise_paperEssentiallyDistinct R hCWA le_rfl hdeltaOne
      hscaleEpsilon hdegreeAbsorb hvolumeAbsorb hdegreeThreshold
      hvolumeThreshold hAone hA hKT hrhoSmall hdelta0
      hdensityExponent hbaseExponent hnu hgamma hRHSbudget
  exact himproved

#print axioms canonicalLowerBufferedScale_self
#print axioms averageMultiplicity_le_improvedRHS_of_exactScaleInputs

end
end Family8CanonicalExactWeightedDef212ExactScaleInputsRHSV2
