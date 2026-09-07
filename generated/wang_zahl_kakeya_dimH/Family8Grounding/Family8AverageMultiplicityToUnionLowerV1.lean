import Submission.Kakeya.ConvexGeometry.Shading
import Mathlib.Tactic

/-!
# Average multiplicity to a shaded-union lower bound

This file records the division-free converse to the definition of average
multiplicity.  For arbitrary `ENNReal`s there are exactly two exceptional
denominator/cap pairs, `(0, ∞)` and `(∞, 0)`.  The generic lemma below
states only the compatibility needed in those two cases.

For a shading of a finite convex family, both compatibilities are automatic:
the shaded union has finite volume, and zero shaded-union volume forces every
shaded carrier, hence the total shading mass, to have zero volume.  Thus an
average-multiplicity upper bound yields its division-free mass bound without
any positivity or finiteness assumption on the cap.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8AverageMultiplicityToUnionLowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-- Clear an `ENNReal` denominator under precisely the compatibility
conditions needed in the two exceptional cases `(denominator, cap) = (0, ∞)`
and `(denominator, cap) = (∞, 0)`.

Outside those two cases this is `ENNReal.div_le_iff_le_mul`.  In either
exceptional case the desired product bound itself is equivalent to the
numerator being zero, so the two premises are also sharp. -/
theorem numerator_le_cap_mul_denominator_of_div_le
    {numerator denominator cap : ENNReal}
    (hzeroTop : denominator = 0 ∧ cap = ∞ → numerator = 0)
    (htopZero : denominator = ∞ ∧ cap = 0 → numerator = 0)
    (hdiv : numerator / denominator ≤ cap) :
    numerator ≤ cap * denominator := by
  by_cases hzeroSide : denominator ≠ 0 ∨ cap ≠ ∞
  · by_cases htopSide : denominator ≠ ∞ ∨ cap ≠ 0
    · exact (ENNReal.div_le_iff_le_mul hzeroSide htopSide).mp hdiv
    · simp only [not_or, not_not] at htopSide
      rw [htopZero htopSide]
      exact bot_le
  · simp only [not_or, not_not] at hzeroSide
    rw [hzeroTop hzeroSide]
    exact bot_le

/-- A finite convex-family shading has finite shaded-union volume. -/
theorem volume_shadedUnion_ne_top
    {iota : Type*} [Fintype iota]
    {F : ConvexFamily iota} (Y : Shading F) :
    volume Y.shadedUnion ≠ ∞ := by
  exact ((measure_mono Y.shadedUnion_subset_familyUnion).trans_lt
    (familyUnion_isCompact F).measure_lt_top).ne

/-- If the shaded union has zero volume, then the total mass of all shaded
pieces is zero, even though that mass counts overlaps. -/
theorem shadingMass_eq_zero_of_volume_shadedUnion_eq_zero
    {iota : Type*} [Fintype iota]
    {F : ConvexFamily iota} (Y : Shading F)
    (hvolume : volume Y.shadedUnion = 0) :
    Y.shadingMass = 0 := by
  unfold Shading.shadingMass
  apply Finset.sum_eq_zero
  intro i _hi
  apply le_antisymm
  · have hcarrier : volume (Y.carrier i) ≤ volume Y.shadedUnion :=
      measure_mono (Set.subset_iUnion (fun j ↦ Y.carrier j) i)
    simpa only [hvolume] using hcarrier
  · exact bot_le

/-- Division-free form of an average-multiplicity upper bound.  No condition
on `cap` is required for an actual shading of a finite convex family. -/
theorem shadingMass_le_cap_mul_volume_shadedUnion_of_averageMultiplicity_le
    {iota : Type*} [Fintype iota]
    {F : ConvexFamily iota} (Y : Shading F) (cap : ENNReal)
    (haverage : Y.averageMultiplicity ≤ cap) :
    Y.shadingMass ≤ cap * volume Y.shadedUnion := by
  apply numerator_le_cap_mul_denominator_of_div_le
  · rintro ⟨hvolume, _hcap⟩
    exact shadingMass_eq_zero_of_volume_shadedUnion_eq_zero Y hvolume
  · rintro ⟨hvolume, _hcap⟩
    exact (volume_shadedUnion_ne_top Y hvolume).elim
  · simpa only [Shading.averageMultiplicity] using haverage

/-- A mass floor and an average-multiplicity cap give the corresponding
division-free lower bound for the actual shaded union. -/
theorem massFloor_le_cap_mul_volume_shadedUnion_of_averageMultiplicity_le
    {iota : Type*} [Fintype iota]
    {F : ConvexFamily iota} (Y : Shading F)
    (massFloor cap : ENNReal)
    (hmass : massFloor ≤ Y.shadingMass)
    (haverage : Y.averageMultiplicity ≤ cap) :
    massFloor ≤ cap * volume Y.shadedUnion :=
  hmass.trans
    (shadingMass_le_cap_mul_volume_shadedUnion_of_averageMultiplicity_le
      Y cap haverage)

/-- Quotient form of
`massFloor_le_cap_mul_volume_shadedUnion_of_averageMultiplicity_le`.
It remains valid for `cap = 0` and `cap = ∞`; the division-free theorem has
already handled the exceptional products. -/
theorem massFloor_div_cap_le_volume_shadedUnion_of_averageMultiplicity_le
    {iota : Type*} [Fintype iota]
    {F : ConvexFamily iota} (Y : Shading F)
    (massFloor cap : ENNReal)
    (hmass : massFloor ≤ Y.shadingMass)
    (haverage : Y.averageMultiplicity ≤ cap) :
    massFloor / cap ≤ volume Y.shadedUnion := by
  apply ENNReal.div_le_of_le_mul
  simpa only [mul_comm] using
    (massFloor_le_cap_mul_volume_shadedUnion_of_averageMultiplicity_le
      Y massFloor cap hmass haverage)

#print axioms numerator_le_cap_mul_denominator_of_div_le
#print axioms volume_shadedUnion_ne_top
#print axioms shadingMass_eq_zero_of_volume_shadedUnion_eq_zero
#print axioms
  shadingMass_le_cap_mul_volume_shadedUnion_of_averageMultiplicity_le
#print axioms
  massFloor_le_cap_mul_volume_shadedUnion_of_averageMultiplicity_le
#print axioms
  massFloor_div_cap_le_volume_shadedUnion_of_averageMultiplicity_le

end
end Family8AverageMultiplicityToUnionLowerV1
