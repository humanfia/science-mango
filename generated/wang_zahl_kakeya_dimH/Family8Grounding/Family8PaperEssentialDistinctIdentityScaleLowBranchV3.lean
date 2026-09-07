import Family8Grounding.Family8PaperEssentialDistinctActualDatumConstantExtractionV3
import Family8Grounding.Family8CanonicalExactWeightedDef212IdentityScaleRHSV2
import Family8Grounding.Family8RestrictedActualDatumDensityRetentionV1
import Family8Grounding.Family8ActualFamilyVolumePackingV1
import Family8Grounding.Family8FiniteRandomRigidMotionFrostmanConnectorV1
import Family8Grounding.Family8SharpKatzTaoOrGreedyHighConcentrationV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8PaperEssentialDistinctIdentityScaleLowBranchV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8RestrictedActualDatumMassBridgeV1
open Family8RestrictedActualDatumDensityRetentionV1
open Family8ActualFamilyVolumePackingV1
open Family8FiniteRandomRigidMotionFrostmanConnectorV1
open Family8SharpKatzTaoOrGreedyHighConcentrationV1
open Family8PaperEssentialDistinctConstantExtractionV2
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV14
open Family8FrostmanWeightedSelectedDirectBaseBudgetV3
open Family8Def212ConvexWolffAtEveryScaleV2
open Family6CanonicalFrostmanConstantCoreV1

noncomputable section

/-!
# Constant-loss paper-distinct extraction into the identity-scale endpoint

An arbitrary Frostman family cannot be restricted with no loss: the
normalizing ambient mass decreases.  The constant-code extraction does,
however, retain cardinality, while the standard radius-`delta` tube volume
sandwich turns this into a fixed factor-`16` actual-family-volume loss.
Together with the separately retained shading mass, this gives the two honest
numerical absorption premises displayed by the final theorem below.

The conclusion deliberately keeps the Frostman RHS normalized by the actual
volume of the selected datum.  No monotonicity step replaces it by the source
actual volume.
-/

/-- The literal shading/average-multiplicity loss of the paper-distinct
constant-code extraction. -/
def paperActualSubtypeLoss : ENNReal :=
  (paperConflictConstantCodeLoss + 1 : Nat)

/-- The conservative actual-family-volume loss obtained from the universal
upper/lower volume sandwich for equal-radius tubes. -/
def paperActualSubtypeFrostmanLoss : ENNReal :=
  16 * paperActualSubtypeLoss

/-- Cardinality retention from the paper conflict code implies honest
actual-family-volume retention. -/
theorem source_actualFamilyVolume_le_paperFrostmanLoss_mul_restrict
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (selected : Finset index)
    (hcard : (Fintype.card index : ENNReal) <=
      paperActualSubtypeLoss *
        (Fintype.card {i // i ∈ selected} : ENNReal)) :
    D.actualFamilyVolume <=
      paperActualSubtypeFrostmanLoss *
        (restrictActualTubeDatum D selected).actualFamilyVolume := by
  have hupper :=
    actualFamilyVolume_le_card_mul_eight_sq D hD.delta_le_half
  have hlower :=
    card_mul_half_sq_le_actualFamilyVolume
      (restrictActualTubeDatum D selected) hD.delta_le_half
  have hlowerDiv :
      ((Fintype.card {i // i ∈ selected} : ENNReal) *
          (delta : ENNReal) ^ 2) / 2 <=
        (restrictActualTubeDatum D selected).actualFamilyVolume := by
    simpa only [div_eq_mul_inv, mul_assoc] using hlower
  have hlowerMul :
      (Fintype.card {i // i ∈ selected} : ENNReal) *
          (delta : ENNReal) ^ 2 <=
        (restrictActualTubeDatum D selected).actualFamilyVolume * 2 :=
    (ENNReal.div_le_iff (by norm_num) (by norm_num)).mp hlowerDiv
  calc
    D.actualFamilyVolume <=
        (Fintype.card index : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) := hupper
    _ <= (paperActualSubtypeLoss *
          (Fintype.card {i // i ∈ selected} : ENNReal)) *
        (8 * (delta : ENNReal) ^ 2) := by gcongr
    _ = (8 * paperActualSubtypeLoss) *
        ((Fintype.card {i // i ∈ selected} : ENNReal) *
          (delta : ENNReal) ^ 2) := by ac_rfl
    _ <= (8 * paperActualSubtypeLoss) *
        ((restrictActualTubeDatum D selected).actualFamilyVolume * 2) := by
      exact mul_le_mul' le_rfl hlowerMul
    _ = paperActualSubtypeFrostmanLoss *
        (restrictActualTubeDatum D selected).actualFamilyVolume := by
      unfold paperActualSubtypeFrostmanLoss
      ring

/-- A Frostman certificate restricts with loss `L` when the source ambient
family volume is at most `L` times the selected ambient family volume. -/
theorem isFrostmanIn_restrictActualTubeDatum_of_volume_retention
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (selected : Finset index)
    {C L : ENNReal}
    (hF : IsFrostmanIn C D.family.bodyFamily unitBallBody)
    (hvolume : D.actualFamilyVolume <=
      L * (restrictActualTubeDatum D selected).actualFamilyVolume) :
    IsFrostmanIn (L * C)
      (restrictActualTubeDatum D selected).family.bodyFamily unitBallBody := by
  let Dp := restrictActualTubeDatum D selected
  have hcontained : forall i,
      (Dp.family.bodyFamily i : Set Space) ⊆
        (unitBallBody : Set Space) := by
    intro i
    exact hF.1 i.1
  refine ⟨hcontained, ?_⟩
  intro K hK
  have hmassMono :
      containedMass Dp.family.bodyFamily K <=
        containedMass D.family.bodyFamily K := by
    rw [restrictActualTubeDatum_containedMass]
    calc
      containedMassOn D.family.bodyFamily selected K <=
          containedMassOn D.family.bodyFamily Finset.univ K :=
        containedMassOn_mono (Finset.subset_univ selected) K
      _ = containedMass D.family.bodyFamily K := by
        simp [containedMassOn, containedMass]
  have hsourceAmbient :
      containedMass D.family.bodyFamily unitBallBody =
        D.actualFamilyVolume := by
    simpa only [ActualTubeDatum.actualFamilyVolume] using
      (containedMass_eq_familyVolume_of_contained
        D.family.bodyFamily unitBallBody hF.1)
  have hselectedAmbient :
      containedMass Dp.family.bodyFamily unitBallBody =
        Dp.actualFamilyVolume := by
    simpa only [ActualTubeDatum.actualFamilyVolume] using
      (containedMass_eq_familyVolume_of_contained
        Dp.family.bodyFamily unitBallBody hcontained)
  calc
    containedMass Dp.family.bodyFamily K *
          volume (unitBallBody : Set Space) <=
        containedMass D.family.bodyFamily K *
          volume (unitBallBody : Set Space) :=
      mul_le_mul' hmassMono le_rfl
    _ <= C * containedMass D.family.bodyFamily unitBallBody *
          volume (K : Set Space) :=
      hF.2 K hK
    _ = C * D.actualFamilyVolume * volume (K : Set Space) := by
      rw [hsourceAmbient]
    _ <= C * (L * Dp.actualFamilyVolume) * volume (K : Set Space) := by
      gcongr
    _ = (L * C) * containedMass Dp.family.bodyFamily unitBallBody *
          volume (K : Set Space) := by
      rw [hselectedAmbient]
      ac_rfl

/-- Constant-loss low-branch connector into the callback-free identity-scale
Definition 2.12 endpoint.

The two absorption hypotheses are purely scalar:
* `hdensityAbsorb` absorbs the shading-mass loss;
* `hfrostmanAbsorb` absorbs the (conservative) fixed volume-normalization
  loss.

The final RHS uses the selected actual family volume, exactly as produced by
the identity-scale endpoint. -/
theorem exists_paperEssentiallyDistinct_identityScale_improvedRHS
    {beta frostmanEpsilon frostmanEta sourceExponent selectedExponent
      targetEpsilon nu : Real}
    {delta0 delta : NNReal}
    {index : Type} [Fintype index] [DecidableEq index]
    (hF : FrostmanAtParameters beta frostmanEpsilon frostmanEta delta0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (hSource : FrostmanHypotheses D sourceExponent)
    (hdeltaSmall : delta <= (1 / 100 : NNReal))
    (hdensityAbsorb :
      (delta : ENNReal) ^ selectedExponent <=
        (delta : ENNReal) ^ sourceExponent / paperActualSubtypeLoss)
    (hfrostmanAbsorb :
      paperActualSubtypeFrostmanLoss *
          (delta : ENNReal) ^ (-sourceExponent) <=
        (delta : ENNReal) ^ (-selectedExponent))
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
      selectedExponent <= frostmanEta -
        activeOwnerExactDegreePowerEnvelope scaleEpsilon
          katzTaoExponent degreeAbsorbExponent)
    (hbaseExponent :
      2 * selectedExponent +
          directSelectedBasePowerLoss scaleEpsilon katzTaoExponent
            degreeAbsorbExponent volumeAbsorbExponent <= frostmanEta)
    (hnu : 0 <= nu)
    (hgamma : beta - nu <= 2)
    (hRHSbudget :
      activeOwnerExactDegreePowerEnvelope scaleEpsilon
            katzTaoExponent degreeAbsorbExponent + 2 * nu +
          (2 * selectedExponent +
              activeOwnerExactDegreePowerEnvelope scaleEpsilon
                katzTaoExponent degreeAbsorbExponent) * nu / 2 <=
        targetEpsilon - frostmanEpsilon) :
    ∃ selected : Finset index,
      let Dp := restrictActualTubeDatum D selected
      (Nonempty index -> Nonempty {i // i ∈ selected}) ∧
      Dp.IsAdmissible ∧
      Dp.family.refinement.refined = Finset.univ ∧
      (Set.Pairwise (Set.univ : Set {i // i ∈ selected}) fun i j =>
        PaperEssentiallyDistinct (Dp.family.tubes i) (Dp.family.tubes j)) ∧
      FrostmanHypotheses Dp selectedExponent ∧
      IsKatzTao A Dp.family.bodyFamily ∧
      D.shading.averageMultiplicity <=
        paperActualSubtypeLoss * Dp.shading.averageMultiplicity ∧
      Dp.shading.averageMultiplicity <=
        frostmanMultiplicityRHS delta Dp.actualFamilyVolume
          targetEpsilon (beta - nu) ∧
      D.shading.averageMultiplicity <=
        paperActualSubtypeLoss *
          frostmanMultiplicityRHS delta Dp.actualFamilyVolume
            targetEpsilon (beta - nu) := by
  classical
  obtain ⟨selected, hnonempty, hadmissible, hfull, hpaper, hcard, hmass⟩ :=
    Family8PaperEssentialDistinctActualDatumConstantExtractionV3.exists_paperEssentiallyDistinct_actualSubtype
      D hD hdeltaSmall
  let Dp := restrictActualTubeDatum D selected
  have hcard' : (Fintype.card index : ENNReal) <=
      paperActualSubtypeLoss *
        (Fintype.card {i // i ∈ selected} : ENNReal) := by
    simpa only [paperActualSubtypeLoss] using hcard
  have hvolume :
      D.actualFamilyVolume <=
        paperActualSubtypeFrostmanLoss * Dp.actualFamilyVolume :=
    source_actualFamilyVolume_le_paperFrostmanLoss_mul_restrict
      D hD selected hcard'
  have hselectedFrostman0 :
      IsFrostmanIn
          (paperActualSubtypeFrostmanLoss *
            (delta : ENNReal) ^ (-sourceExponent))
        Dp.family.bodyFamily unitBallBody :=
    isFrostmanIn_restrictActualTubeDatum_of_volume_retention
      D selected hSource.2 hvolume
  have hselectedFrostman :
      IsFrostmanIn ((delta : ENNReal) ^ (-selectedExponent))
        Dp.family.bodyFamily unitBallBody :=
    hselectedFrostman0.mono hfrostmanAbsorb
  have hdensityTransport :
      D.shading.shadingDensity / paperActualSubtypeLoss <=
        Dp.shading.shadingDensity :=
    source_shadingDensity_div_loss_le_restrictActualTubeDatum
      D selected paperActualSubtypeLoss (by
        simpa only [paperActualSubtypeLoss] using hmass)
  have hselectedDensity :
      (delta : ENNReal) ^ selectedExponent <=
        Dp.shading.shadingDensity := by
    calc
      (delta : ENNReal) ^ selectedExponent <=
          (delta : ENNReal) ^ sourceExponent /
            paperActualSubtypeLoss := hdensityAbsorb
      _ <= D.shading.shadingDensity / paperActualSubtypeLoss :=
        ENNReal.div_le_div_right hSource.1 _
      _ <= Dp.shading.shadingDensity := hdensityTransport
  have hselectedSource : FrostmanHypotheses Dp selectedExponent :=
    ⟨hselectedDensity, hselectedFrostman⟩
  have hselectedKT : IsKatzTao A Dp.family.bodyFamily :=
    isKatzTao_restrictActualTubeDatum_of_isKatzTaoOn
      D selected A (hKT.on selected)
  have havgTransport :
      D.shading.averageMultiplicity <=
        paperActualSubtypeLoss * Dp.shading.averageMultiplicity :=
    source_averageMultiplicity_le_loss_mul_restrictActualTubeDatum
      D selected paperActualSubtypeLoss (by
        simpa only [paperActualSubtypeLoss] using hmass)
  have hdeltaSixteen : delta <= (1 / 16 : NNReal) :=
    hdeltaSmall.trans (by
      simpa only [one_div] using
        (inv_anti₀ (show (0 : NNReal) < 16 by norm_num)
          (show (16 : NNReal) <= 100 by norm_num)))
  have himproved :
      Dp.shading.averageMultiplicity <=
        frostmanMultiplicityRHS delta Dp.actualFamilyVolume
          targetEpsilon (beta - nu) :=
    Family8CanonicalExactWeightedDef212IdentityScaleRHSV2.averageMultiplicity_le_improvedRHS_of_identityScale
      hF Dp hadmissible hselectedSource hfull hpaper hscaleEpsilon
        hdegreeAbsorb hvolumeAbsorb hdegreeThreshold hvolumeThreshold
        hAone hA hselectedKT hdeltaSixteen hdelta0 hdensityExponent
        hbaseExponent hnu hgamma hRHSbudget
  refine ⟨selected, ?_⟩
  dsimp only
  exact ⟨hnonempty, hadmissible, hfull, hpaper, hselectedSource,
    hselectedKT, havgTransport, himproved,
    havgTransport.trans (mul_le_mul' le_rfl himproved)⟩

#print axioms source_actualFamilyVolume_le_paperFrostmanLoss_mul_restrict
#print axioms isFrostmanIn_restrictActualTubeDatum_of_volume_retention
#print axioms exists_paperEssentiallyDistinct_identityScale_improvedRHS

end
end Family8PaperEssentialDistinctIdentityScaleLowBranchV3
