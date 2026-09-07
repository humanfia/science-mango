import Family8Grounding.Family8CommonPointTubePackingV1
import Family8Grounding.Family8FrostmanExponentMonotonicitySmallScaleV1

open scoped ENNReal NNReal

namespace Family8ExponentRangeConsequencesV1

open MeasureTheory
open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Honest exponent-range consequences

This module first proves the lossless upward monotonicity of the Katz--Tao
property.  The empty indexed family is handled separately, so no hidden
positivity assumption on its cardinality enters the rpow comparison.
-/

/-- Katz--Tao at fixed parameters is monotone upward in the counting
exponent. -/
theorem katzTaoAtParameters_mono_exponent
    {lower upper epsilon eta : Real} {delta0 : NNReal}
    (hlowerUpper : lower ≤ upper)
    (hlower : KatzTaoAtParameters lower epsilon eta delta0) :
    KatzTaoAtParameters upper epsilon eta delta0 := by
  intro delta index _ _ D hD hdelta hKT
  have hsource := hlower delta index D hD hdelta hKT
  by_cases hcard : Fintype.card index = 0
  · have huniv : (Finset.univ : Finset index) = ∅ :=
      Finset.card_eq_zero.mp (by simpa only [Finset.card_univ] using hcard)
    have hmass : D.shading.shadingMass = 0 := by
      unfold Shading.shadingMass
      rw [huniv]
      simp only [Finset.sum_empty]
    have havg : D.shading.averageMultiplicity = 0 := by
      unfold Shading.averageMultiplicity
      rw [hmass]
      exact ENNReal.zero_div
    rw [havg]
    exact bot_le
  · have hbase : (1 : ENNReal) ≤ (Fintype.card index : ENNReal) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hcard)
    have hpow :
        (Fintype.card index : ENNReal) ^ lower ≤
          (Fintype.card index : ENNReal) ^ upper :=
      ENNReal.rpow_le_rpow_of_exponent_le hbase hlowerUpper
    exact hsource.trans (by
      unfold katzTaoMultiplicityRHS
      exact mul_le_mul' (le_refl _) hpow)

/-- The full Katz--Tao property is monotone upward in its exponent, with the
same loss exponent and terminal scale for each requested epsilon. -/
theorem katzTaoProperty_mono
    {lower upper : Real} (hlowerUpper : lower ≤ upper)
    (hlower : KatzTaoProperty lower) :
    KatzTaoProperty upper := by
  intro epsilon hepsilon
  obtain ⟨eta, delta0, heta, hdelta0, hdelta0Half, hsource⟩ :=
    hlower epsilon hepsilon
  exact ⟨eta, delta0, heta, hdelta0, hdelta0Half,
    katzTaoAtParameters_mono_exponent hlowerUpper hsource⟩

/-- Named implication form for branches which already know a lower
Katz--Tao exponent. -/
theorem katzTaoProperty_of_le
    {lower upper : Real} (hlowerUpper : lower ≤ upper) :
    KatzTaoProperty lower → KatzTaoProperty upper :=
  katzTaoProperty_mono hlowerUpper

/-- Actual common-point packing removes the callback from Frostman exponent
monotonicity.  Its geometric validity scale is recorded honestly as
`1/100`. -/
theorem frostmanProperty_mono
    {lower upper : Real} (hlowerUpper : lower ≤ upper)
    (hlower : FrostmanProperty lower) :
    FrostmanProperty upper := by
  exact
    Family8FrostmanExponentMonotonicitySmallScaleV1.frostmanProperty_mono_of_familyVolumePackingAtSmallScales
      Family8CommonPointTubePackingV1.commonPointFamilyVolumeConstant
      Family8CommonPointTubePackingV1.commonPointFamilyVolumeConstant_ne_top
      (1 / 100 : NNReal) (by positivity)
      (fun D hD hdelta =>
        Family8CommonPointTubePackingV1.actualFamilyVolume_le_commonPointPacking
          D hD hdelta)
      hlowerUpper hlower

/-- Every exponent at least one has the Frostman property. -/
theorem frostmanProperty_of_one_le
    {beta : Real} (hbeta : 1 ≤ beta) :
    FrostmanProperty beta :=
  frostmanProperty_mono hbeta
    Family8CommonPointTubePackingV1.frostmanProperty_one

#print axioms katzTaoAtParameters_mono_exponent
#print axioms katzTaoProperty_mono
#print axioms katzTaoProperty_of_le
#print axioms frostmanProperty_mono
#print axioms frostmanProperty_of_one_le

end

end Family8ExponentRangeConsequencesV1
