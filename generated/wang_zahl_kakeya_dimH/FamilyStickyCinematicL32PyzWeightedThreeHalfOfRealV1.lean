import FamilyStickyCinematicL32PyzWeightedThreeHalfAbsorptionV1

set_option autoImplicit false

open scoped ENNReal

namespace FamilyStickyCinematicL32PyzWeightedThreeHalfOfRealV1

/-! Real-to-ENNReal bridge for denominator-free three-halves absorption. -/

open FamilyStickyCinematicL32PyzWeightedThreeHalfAbsorptionV1

theorem weighted_threeHalf_absorption_ofReal
    {a b d : Real} {E M : ENNReal}
    (hb : 0 ≤ b)
    (hab : a ≤ b * d)
    (hmoment : (ENNReal.ofReal d) ^ (3 / 2 : Real) * E ≤ M) :
    (ENNReal.ofReal a) ^ (3 / 2 : Real) * E ≤
      (ENNReal.ofReal b) ^ (3 / 2 : Real) * M := by
  apply weighted_threeHalf_absorption
  · have h := ENNReal.ofReal_le_ofReal hab
    simpa only [ENNReal.ofReal_mul hb] using h
  · exact hmoment

end FamilyStickyCinematicL32PyzWeightedThreeHalfOfRealV1
