import Family8Grounding.Family8FactorTwoLowKatzTaoFreshParameterEndpointV1
import Family8Grounding.Family8Prop66AActualFamilyVolumeTransportV1
import Family8Grounding.Family8UnitBallBodyVolumeUpperV1
import Mathlib.Tactic

/-!
# Retained factor-two low witness through fresh selection

The previous public low endpoint erased the mass retention, admissibility,
and Katz--Tao certificate of the literal `selectedLow`.  This successor keeps
those facts together with the fresh child selected from that same set.  It
does not rerun either selection.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8GreedyFactorTwoLowFreshRetainedV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family8FactorTwoLowKatzTaoFreshParameterEndpointV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyHighPrefixActualOccurrenceV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AActualFamilyVolumeTransportV1
open Family8ScaleContainedB2NativeFreshKatzTaoEndpointV1
open Family8UnitBallBodyVolumeUpperV1

noncomputable section

/-- The factor-two low restriction and its fresh child, with one literal
`selectedLow` shared by all conjuncts. -/
def RetainedFactorTwoFreshLow
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (A : ENNReal)
    (epsilon beta : Real) : Prop :=
  ∃ selectedLow : Finset index,
    D.shading.shadingMass ≤ 2 *
      (restrictActualTubeDatum D selectedLow).shading.shadingMass ∧
    (restrictActualTubeDatum D selectedLow).IsAdmissible ∧
    IsKatzTao A
      (restrictActualTubeDatum D selectedLow).family.bodyFamily ∧
    ∃ selectedFresh : Finset {i // i ∈ selectedLow},
      selectedFresh.Nonempty ∧
      selectedFresh.card ≤ selectedLow.card ∧
      D.shading.averageMultiplicity ≤
        (2 * (sourceKatzTaoFreshLoss A : ENNReal)) *
          katzTaoMultiplicityRHS
            (delta / 8) selectedFresh.card epsilon beta

/-- Package an already-produced factor-two low restriction and run the fresh
selection exactly once on that restriction. -/
theorem retainedFactorTwoFreshLow_of_lowRestriction
    {beta epsilon eta : Real} {delta0 delta : NNReal}
    {index : Type} [Fintype index] [DecidableEq index]
    (hKTP : KatzTaoAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta index)
    (selectedLow : Finset index)
    (hmass : D.shading.shadingMass ≤ 2 *
      (restrictActualTubeDatum D selectedLow).shading.shadingMass)
    (hDlow : (restrictActualTubeDatum D selectedLow).IsAdmissible)
    (A : ENNReal)
    (hKTlow : IsKatzTao A
      (restrictActualTubeDatum D selectedLow).family.bodyFamily)
    (hdelta0 : delta / 8 ≤ delta0)
    (hdensityBudget :
      (((delta / 8 : NNReal) : ENNReal) ^ eta) *
          (2 * (128 * (sourceKatzTaoFreshLoss A : ENNReal))) ≤
        D.shading.shadingDensity)
    (hcoefficient :
      128 * A ≤ ((delta / 8 : NNReal) : ENNReal) ^ (-eta)) :
    RetainedFactorTwoFreshLow D A epsilon beta := by
  obtain ⟨selectedFresh, hnonempty, hcard, hbound⟩ :=
    exists_fresh_katzTaoParameter_bound_of_factorTwo_lowRestriction
      hKTP D selectedLow hmass hDlow hKTlow hdelta0
        hdensityBudget hcoefficient
  exact ⟨selectedLow, hmass, hDlow, hKTlow,
    selectedFresh, hnonempty, hcard, hbound⟩

/-- Successor of the public greedy split.  The high branch is literal; the
low branch retains the certificates that its predecessor erased. -/
theorem retainedFactorTwoFreshLow_or_actualHighOccurrencePrefix
    {beta epsilon eta : Real} {delta0 delta : NNReal}
    {index : Type} [Fintype index] [DecidableEq index]
    (hKTP : KatzTaoAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (A : ENNReal)
    (hdelta0 : delta / 8 ≤ delta0)
    (hdensityBudget :
      (((delta / 8 : NNReal) : ENNReal) ^ eta) *
          (2 * (128 * (sourceKatzTaoFreshLoss A : ENNReal))) ≤
        D.shading.shadingDensity)
    (hcoefficient :
      128 * A ≤ ((delta / 8 : NNReal) : ENNReal) ^ (-eta)) :
    RetainedFactorTwoFreshLow D A epsilon beta ∨
      ∃ P : GreedyDensityPartition D.family.bodyFamily
          (hullCandidates (Finset.univ : Finset index))
          (hullContainer D.family.bodyFamily) Finset.univ,
        ∃ selected : Finset index,
          D.shading.shadingMass ≤ 2 *
            (restrictActualTubeDatum D selected).shading.shadingMass ∧
          D.shading.averageMultiplicity ≤ 2 *
            (restrictActualTubeDatum D selected).shading.averageMultiplicity ∧
          (restrictActualTubeDatum D selected).IsAdmissible ∧
          ∀ i ∈ selected,
            ∃ q : Fin (blocks D.family.bodyFamily P).length,
              i ∈ (blockAt D.family.bodyFamily P q).fiber ∧
              ActualHighConcentrationOccurrence D P A q := by
  rcases
      exists_factorTwo_lowKatzTaoRestriction_or_actualHighOccurrencePrefix
        D hD A with hlow | hhigh
  · left
    obtain ⟨selectedLow, hmass, _haverage, hDlow, hKTlow⟩ := hlow
    exact retainedFactorTwoFreshLow_of_lowRestriction
      hKTP D selectedLow hmass hDlow A hKTlow hdelta0
        hdensityBudget hcoefficient
  · exact Or.inr hhigh

/-- The retained low Katz--Tao certificate bounds the fresh card-scale
volume by `16*A`.  Both comparisons use the same `selectedLow`. -/
theorem fresh_cardScale_le_sixteen_mul_of_retained_low
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (A : ENNReal)
    (selectedLow : Finset index)
    (hDlow : (restrictActualTubeDatum D selectedLow).IsAdmissible)
    (hKTlow : IsKatzTao A
      (restrictActualTubeDatum D selectedLow).family.bodyFamily)
    (selectedFresh : Finset {i // i ∈ selectedLow})
    (hcard : selectedFresh.card ≤ selectedLow.card) :
    proposition66ACardScaleVolume delta selectedFresh.card ≤ 16 * A := by
  let Dlow := restrictActualTubeDatum D selectedLow
  have hfreshLow :
      proposition66ACardScaleVolume delta selectedFresh.card ≤
        proposition66ACardScaleVolume delta selectedLow.card := by
    unfold proposition66ACardScaleVolume
    gcongr
  have hcardVolume :
      proposition66ACardScaleVolume delta selectedLow.card ≤
        2 * Dlow.actualFamilyVolume := by
    simpa only [Dlow, Fintype.card_coe] using
      proposition66ACardScaleVolume_le_two_mul_actualFamilyVolume
        Dlow hDlow.delta_le_half
  have hcontained : ∀ i,
      (Dlow.family.bodyFamily i : Set Space) ⊆
        (unitBallBody : Set Space) := by
    intro i
    simpa only [Dlow, UniformTubeFamily.bodyFamily, Tube.coe_body,
      coe_unitBallBody] using hDlow.contained_in_unit_ball i
  have hcontainedMass :
      containedMass Dlow.family.bodyFamily unitBallBody =
        Dlow.actualFamilyVolume := by
    simpa only [ActualTubeDatum.actualFamilyVolume] using
      Family6CanonicalFrostmanConstantCoreV1.containedMass_eq_familyVolume_of_contained
        Dlow.family.bodyFamily unitBallBody hcontained
  have hvolumeA : Dlow.actualFamilyVolume ≤
      A * volume (unitBallBody : Set Space) := by
    have hKT := hKTlow unitBallBody
    unfold IsKatzTaoAt at hKT
    rw [hcontainedMass] at hKT
    exact hKT
  calc
    proposition66ACardScaleVolume delta selectedFresh.card ≤
        proposition66ACardScaleVolume delta selectedLow.card := hfreshLow
    _ ≤ 2 * Dlow.actualFamilyVolume := hcardVolume
    _ ≤ 2 * (A * volume (unitBallBody : Set Space)) :=
      mul_le_mul' le_rfl hvolumeA
    _ ≤ 2 * (A * 8) := by
      gcongr
      exact volume_unitBallBody_le_eight
    _ = 16 * A := by ring

/-- Cross-multiplied sharp form of the endpoint card-scale budget. -/
theorem eight_mul_fresh_cardScale_le_divEight_negativePower_of_retained_low
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (A : ENNReal)
    (selectedLow : Finset index)
    (hDlow : (restrictActualTubeDatum D selectedLow).IsAdmissible)
    (hKTlow : IsKatzTao A
      (restrictActualTubeDatum D selectedLow).family.bodyFamily)
    (selectedFresh : Finset {i // i ∈ selectedLow})
    (hcard : selectedFresh.card ≤ selectedLow.card)
    {eta : Real}
    (hcoefficient :
      128 * A ≤ ((delta / 8 : NNReal) : ENNReal) ^ (-eta)) :
    8 * proposition66ACardScaleVolume delta selectedFresh.card ≤
      ((delta / 8 : NNReal) : ENNReal) ^ (-eta) := by
  calc
    8 * proposition66ACardScaleVolume delta selectedFresh.card ≤
        8 * (16 * A) := mul_le_mul' le_rfl
          (fresh_cardScale_le_sixteen_mul_of_retained_low
            D A selectedLow hDlow hKTlow selectedFresh hcard)
    _ = 128 * A := by ring
    _ ≤ ((delta / 8 : NNReal) : ENNReal) ^ (-eta) := hcoefficient

/-- Minimal consumer form, obtained from the sharper cross-multiplied
estimate without adding any premise. -/
theorem fresh_cardScale_le_divEight_negativePower_of_retained_low
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (A : ENNReal)
    (selectedLow : Finset index)
    (hDlow : (restrictActualTubeDatum D selectedLow).IsAdmissible)
    (hKTlow : IsKatzTao A
      (restrictActualTubeDatum D selectedLow).family.bodyFamily)
    (selectedFresh : Finset {i // i ∈ selectedLow})
    (hcard : selectedFresh.card ≤ selectedLow.card)
    {eta : Real}
    (hcoefficient :
      128 * A ≤ ((delta / 8 : NNReal) : ENNReal) ^ (-eta)) :
    proposition66ACardScaleVolume delta selectedFresh.card ≤
      ((delta / 8 : NNReal) : ENNReal) ^ (-eta) := by
  have hsharp :=
    eight_mul_fresh_cardScale_le_divEight_negativePower_of_retained_low
      D A selectedLow hDlow hKTlow selectedFresh hcard hcoefficient
  calc
    proposition66ACardScaleVolume delta selectedFresh.card =
        1 * proposition66ACardScaleVolume delta selectedFresh.card := by
      rw [one_mul]
    _ ≤ 8 * proposition66ACardScaleVolume delta selectedFresh.card := by
      simpa only [mul_comm] using (mul_le_mul_right (by norm_num : (1 : ENNReal) ≤ 8) (proposition66ACardScaleVolume delta selectedFresh.card))
    _ ≤ ((delta / 8 : NNReal) : ENNReal) ^ (-eta) := hsharp

#print axioms RetainedFactorTwoFreshLow
#print axioms retainedFactorTwoFreshLow_of_lowRestriction
#print axioms retainedFactorTwoFreshLow_or_actualHighOccurrencePrefix
#print axioms fresh_cardScale_le_sixteen_mul_of_retained_low
#print axioms
  eight_mul_fresh_cardScale_le_divEight_negativePower_of_retained_low
#print axioms
  fresh_cardScale_le_divEight_negativePower_of_retained_low

end
end Family8GreedyFactorTwoLowFreshRetainedV2
