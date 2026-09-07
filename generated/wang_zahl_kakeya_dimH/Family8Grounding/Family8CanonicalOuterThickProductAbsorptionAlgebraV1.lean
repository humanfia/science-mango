import Mathlib.Tactic

/-!
# Scalar absorption of the canonical outer/thick factor

The same-selected Equation (45)/(46) endpoint leaves the product in the
association `outer * (thick * remainder) * inner`.  This lemma reassociates
the exact canonical outer/thick power estimate, without losing either the
Family 6 remainder or the selected Equation (46) inner factor.
-/

open scoped ENNReal

namespace Family8CanonicalOuterThickProductAbsorptionAlgebraV1

set_option autoImplicit false
set_option warningAsError true

theorem outer_mul_thick_mul_remainder_mul_inner_le_power_mul
    {outer thick remainder inner power : ENNReal}
    (houterThick : outer * thick ≤ power) :
    (outer * (thick * remainder)) * inner ≤
      power * (remainder * inner) := by
  calc
    (outer * (thick * remainder)) * inner =
        (outer * thick) * (remainder * inner) := by ac_rfl
    _ ≤ power * (remainder * inner) :=
      mul_le_mul' houterThick le_rfl

#print axioms outer_mul_thick_mul_remainder_mul_inner_le_power_mul

end Family8CanonicalOuterThickProductAbsorptionAlgebraV1
