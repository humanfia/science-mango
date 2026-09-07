import Family8Grounding.Family8PaperEssentialDistinctIdentityScaleAbsorptionV2
import Family8Grounding.Family8FixedLossFrostmanRHSSmallDeltaV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8PaperEssentialDistinctIdentityScaleAutomaticLowBranchV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV14
open Family8FrostmanWeightedSelectedDirectBaseBudgetV3
open Family8PaperEssentialDistinctIdentityScaleLowBranchV3
open Family8PaperEssentialDistinctIdentityScaleAbsorptionV2
open Family8FixedLossFrostmanRHSSmallDeltaV3
open Family8RestrictedActualDatumDensityRetentionV1

noncomputable section

/-!
# Fully absorbed constant-loss identity-scale low branch

The common terminal scale below simultaneously:
* enters the paper conflict-code extraction range;
* absorbs both fixed constants needed to upgrade the selected datum's
  Frostman exponent; and
* absorbs the remaining multiplicity loss into the outer epsilon budget.

The selected actual-family volume is transported to the source volume only
through the proved restriction monotonicity and the genuine range
`beta - nu <= 2`.
-/

def paperIdentityScaleAutomaticLowBranchThreshold
    (absorbExponent innerEpsilon outerEpsilon : Real) : NNReal :=
  min (1 / 100 : NNReal)
    (min
      (paperActualSubtypeAbsorptionThreshold absorbExponent)
      (fixedLossFrostmanRHSThreshold
        paperActualSubtypeLoss innerEpsilon outerEpsilon))

theorem paperIdentityScaleAutomaticLowBranchThreshold_pos
    (absorbExponent innerEpsilon outerEpsilon : Real) :
    0 < paperIdentityScaleAutomaticLowBranchThreshold
      absorbExponent innerEpsilon outerEpsilon := by
  exact lt_min (by norm_num)
    (lt_min
      (paperActualSubtypeAbsorptionThreshold_pos absorbExponent)
      (fixedLossFrostmanRHSThreshold_pos
        paperActualSubtypeLoss innerEpsilon outerEpsilon))

/-- Callback-free low-branch endpoint with both fixed losses automatically
absorbed. -/
theorem averageMultiplicity_le_improved_sourceRHS_of_paperExtraction
    {beta frostmanEpsilon frostmanEta sourceExponent absorbExponent
      innerEpsilon outerEpsilon nu : Real}
    {delta0 delta : NNReal}
    {index : Type} [Fintype index] [DecidableEq index]
    (hF : FrostmanAtParameters beta frostmanEpsilon frostmanEta delta0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (hSource : FrostmanHypotheses D sourceExponent)
    (habsorb : 0 < absorbExponent)
    (hEpsilonGap : innerEpsilon < outerEpsilon)
    (hsmall : delta <=
      paperIdentityScaleAutomaticLowBranchThreshold
        absorbExponent innerEpsilon outerEpsilon)
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
    (hdelta0 : delta <= delta0)
    (hdensityExponent :
      sourceExponent + absorbExponent <= frostmanEta -
        activeOwnerExactDegreePowerEnvelope scaleEpsilon
          katzTaoExponent degreeAbsorbExponent)
    (hbaseExponent :
      2 * (sourceExponent + absorbExponent) +
          directSelectedBasePowerLoss scaleEpsilon katzTaoExponent
            degreeAbsorbExponent volumeAbsorbExponent <= frostmanEta)
    (hnu : 0 <= nu)
    (hgamma : beta - nu <= 2)
    (hRHSbudget :
      activeOwnerExactDegreePowerEnvelope scaleEpsilon
            katzTaoExponent degreeAbsorbExponent + 2 * nu +
          (2 * (sourceExponent + absorbExponent) +
              activeOwnerExactDegreePowerEnvelope scaleEpsilon
                katzTaoExponent degreeAbsorbExponent) * nu / 2 <=
        innerEpsilon - frostmanEpsilon) :
    D.shading.averageMultiplicity <=
      frostmanMultiplicityRHS delta D.actualFamilyVolume
        outerEpsilon (beta - nu) := by
  have hdeltaSmall : delta <= (1 / 100 : NNReal) :=
    hsmall.trans (min_le_left _ _)
  have habsorbSmall : delta <=
      paperActualSubtypeAbsorptionThreshold absorbExponent :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRHSSmall : delta <=
      fixedLossFrostmanRHSThreshold
        paperActualSubtypeLoss innerEpsilon outerEpsilon :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdensityAbsorb :
      (delta : ENNReal) ^ (sourceExponent + absorbExponent) <=
        (delta : ENNReal) ^ sourceExponent / paperActualSubtypeLoss :=
    density_rpow_add_absorb_le_div_paperLoss
      hD.delta_pos habsorb habsorbSmall
  have hfrostmanAbsorb :
      paperActualSubtypeFrostmanLoss *
          (delta : ENNReal) ^ (-sourceExponent) <=
        (delta : ENNReal) ^ (-(sourceExponent + absorbExponent)) :=
    paperFrostmanLoss_mul_rpow_neg_le_rpow_neg_add
      hD.delta_pos habsorb habsorbSmall
  obtain ⟨selected, hselected⟩ :=
    exists_paperEssentiallyDistinct_identityScale_improvedRHS
      (sourceExponent := sourceExponent)
      (selectedExponent := sourceExponent + absorbExponent)
      (targetEpsilon := innerEpsilon)
      hF D hD hSource hdeltaSmall hdensityAbsorb hfrostmanAbsorb
        hscaleEpsilon hdegreeAbsorb hvolumeAbsorb hdegreeThreshold
        hvolumeThreshold hAone hA hKT hdelta0 hdensityExponent
        hbaseExponent hnu hgamma hRHSbudget
  dsimp only at hselected
  rcases hselected with
    ⟨_hnonempty, _hadmissible, _hfull, _hpaper, _hselectedSource,
      _hselectedKT, _haverageTransport, _hselectedImproved,
      hselectedRHS⟩
  have hvolume :
      (restrictActualTubeDatum D selected).actualFamilyVolume <=
        D.actualFamilyVolume :=
    restrictActualTubeDatum_actualFamilyVolume_le D selected
  exact
    source_averageMultiplicity_le_of_fixedLoss_selectedRHS
      hD.delta_pos paperActualSubtypeLoss_ne_top hEpsilonGap hgamma
        hvolume hRHSSmall hselectedRHS

#print axioms paperIdentityScaleAutomaticLowBranchThreshold_pos
#print axioms averageMultiplicity_le_improved_sourceRHS_of_paperExtraction

end
end Family8PaperEssentialDistinctIdentityScaleAutomaticLowBranchV1
