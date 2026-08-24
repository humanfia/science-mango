import FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32PyzLowMultiplicityDegreeCapCleanV1

open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1

noncomputable section

/-!
# The honest low-multiplicity alternative in PYZ Section 5

The high branch requires `24 * logCount ≤ degreeLower`.  On its strict
complement the actual dyadic E₂ window has upper endpoint strictly below
`48 * logCount`, since its two endpoints differ by at most a factor two.
Consequently every literal active Y₁ family on E₂ obeys the same cap.

This is only the finite numerical entrance to the weak/trivial branch.  It
does not assert PYZ (5.24), a measure bound, or an `L^(3/2)` conclusion.
-/

theorem pyzE2DegreeUpper_lt_fortyEight_mul_logCount
    (label : Int) (logCount : Nat)
    (hlow : pyzE2DegreeLower label < 24 * logCount) :
    pyzE2DegreeUpper label < 48 * logCount := by
  have hwindow := pyzE2DegreeUpper_le_two_mul_lower label
  omega

theorem pyzE2DegreeUpper_le_fortyEight_mul_logCount
    (label : Int) (logCount : Nat)
    (hlow : pyzE2DegreeLower label < 24 * logCount) :
    pyzE2DegreeUpper label ≤ 48 * logCount :=
  (pyzE2DegreeUpper_lt_fortyEight_mul_logCount label logCount hlow).le

theorem active_card_lt_fortyEight_mul_logCount_of_mem_pyzE2
    {point index : Type*} [MeasurableSpace point]
    (Z : FiniteProjectedShading point index) (label : Int)
    (logCount : Nat) (x : point)
    (hx : x ∈ projectedPositiveMultiplicityDyadicCell Z label)
    (hactive : (Z.activeAtPoint x).Nonempty)
    (hlow : pyzE2DegreeLower label < 24 * logCount) :
    (Z.activeAtPoint x).card < 48 * logCount := by
  exact (active_card_le_pyzE2DegreeUpper_of_mem_cell Z label x hx hactive).trans_lt
    (pyzE2DegreeUpper_lt_fortyEight_mul_logCount label logCount hlow)

theorem active_card_le_fortyEight_mul_logCount_of_mem_pyzE2
    {point index : Type*} [MeasurableSpace point]
    (Z : FiniteProjectedShading point index) (label : Int)
    (logCount : Nat) (x : point)
    (hx : x ∈ projectedPositiveMultiplicityDyadicCell Z label)
    (hactive : (Z.activeAtPoint x).Nonempty)
    (hlow : pyzE2DegreeLower label < 24 * logCount) :
    (Z.activeAtPoint x).card ≤ 48 * logCount :=
  (active_card_lt_fortyEight_mul_logCount_of_mem_pyzE2
    Z label logCount x hx hactive hlow).le

#print axioms pyzE2DegreeUpper_lt_fortyEight_mul_logCount
#print axioms pyzE2DegreeUpper_le_fortyEight_mul_logCount
#print axioms active_card_lt_fortyEight_mul_logCount_of_mem_pyzE2
#print axioms active_card_le_fortyEight_mul_logCount_of_mem_pyzE2

end
end FamilyStickyCinematicL32PyzLowMultiplicityDegreeCapCleanV1
