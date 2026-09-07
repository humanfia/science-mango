import Family8Grounding.Family8CanonicalExactWeightedDef212SelfImprovementRHSV1
import Family8Grounding.Family8CanonicalExactWeightedDef212ExactScaleInputsRHSV2
import Family8Grounding.Family8FiniteFibreAutomaticCWAV3
import Family8Grounding.Family8TubeJohnUnitRescalingGeometryLeOneV7
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalExactWeightedDef212IdentityScaleRHSV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
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
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

/-!
# Callback-free identity-scale Def. 2.12 endpoint

At `theta = delta`, the canonical buffered scale is exactly `delta`.  The
identity-radius cover then has singleton fibres, automatic uniformity, and an
honest finite common CWA constant.  Tube John geometry supplies the unit
rescaling.  Thus the former all-scale `ExactScaleDef212Inputs` package is not
needed for this same-scale endpoint; only full refinement and the genuine
paper essential-distinctness field remain explicit.
-/

theorem averageMultiplicity_le_improvedRHS_of_identityScale
    {beta frostmanEpsilon frostmanEta sourceExponent targetEpsilon nu : Real}
    {delta0 delta : NNReal}
    {index : Type} [Fintype index] [DecidableEq index]
    (hF : FrostmanAtParameters beta frostmanEpsilon frostmanEta delta0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (hSource : FrostmanHypotheses D sourceExponent)
    (hfull : D.family.refinement.refined = Finset.univ)
    (hpaper : Set.Pairwise (Set.univ : Set index) fun i j =>
      PaperEssentiallyDistinct (D.family.tubes i) (D.family.tubes j))
    {scaleEpsilon katzTaoExponent degreeAbsorbExponent
      volumeAbsorbExponent : Real}
    {A : ENNReal}
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
  have hdeltaOne : delta <= 1 := hD.delta_le_half.trans (by norm_num)
  have hscaleEq : canonicalLowerBufferedScale delta delta scaleEpsilon = delta :=
    Family8CanonicalExactWeightedDef212ExactScaleInputsRHSV2.canonicalLowerBufferedScale_self
      hD.delta_pos scaleEpsilon
  have hdeltaScale : delta <=
      canonicalLowerBufferedScale delta delta scaleEpsilon := by
    rw [hscaleEq]
  have hscaleOne : canonicalLowerBufferedScale delta delta scaleEpsilon <= 1 := by
    rw [hscaleEq]
    exact hdeltaOne
  let S := identityRadiusScaleCover D.family
    (canonicalLowerBufferedScale delta delta scaleEpsilon) hdeltaScale
  have hrho : 0 < canonicalLowerBufferedScale delta delta scaleEpsilon := by
    rw [hscaleEq]
    exact hD.delta_pos
  let R : UnitRescalingGeometry S :=
    Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnUnitRescalingGeometry_of_le_one
      S hrho hscaleOne
  obtain ⟨Cnn, _hCnn, huniform, hCWA⟩ :=
    Family8FiniteFibreAutomaticCWAV3.exists_nat_identityRadiusScaleCover_cUniform_fibresCWA
      D.family (canonicalLowerBufferedScale delta delta scaleEpsilon)
        hdeltaScale hD.delta_pos R
  have hactive : S.activeFine = Finset.univ := by
    rw [S.activeFine_eq_refined, hfull]
  have hrhoSmall :
      canonicalLowerBufferedScale delta delta scaleEpsilon <=
        (1 / 16 : NNReal) := by
    rw [hscaleEq]
    exact hdeltaSixteen
  obtain ⟨_E, _hadmissible, _havg, himproved⟩ :=
    exists_canonicalExactWeightedDef212_improvedFrostmanRHS
      (theta := delta) (Cnn := (Cnn : NNReal)) hF D hD hSource S
      hactive huniform hpaper R hCWA le_rfl hdeltaOne
      hscaleEpsilon hdegreeAbsorb hvolumeAbsorb hdegreeThreshold
      hvolumeThreshold hAone hA hKT hrhoSmall hdelta0
      hdensityExponent hbaseExponent hnu hgamma hRHSbudget
  exact himproved

#print axioms averageMultiplicity_le_improvedRHS_of_identityScale

end
end Family8CanonicalExactWeightedDef212IdentityScaleRHSV2
