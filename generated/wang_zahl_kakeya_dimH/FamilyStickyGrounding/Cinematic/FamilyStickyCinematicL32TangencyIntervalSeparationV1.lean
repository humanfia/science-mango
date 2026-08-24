import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32TangencyIntervalSeparationV1

/-!
# Separating the rectangle base from an exterior critical point

Provenance: the interval-nesting geometry in Pramanik--Yang--Zahl,
arXiv:2207.02259v3, Lemmas 3.8--3.9: the tangency parameter is minimized
on `J/2`, while a tangent rectangle has base in `J/4`.
-/

/-- If a base interval lies an explicit distance `s` inside a minimization
interval, then every point of the base is `s`-separated from any point
outside the minimization interval. -/
theorem critical_mem_minimizerInterval_or_base_separated
    {minA minB baseA baseB theta0 s : Real}
    (hleftNesting : minA + s <= baseA)
    (hrightNesting : baseB + s <= minB) :
    theta0 ∈ Icc minA minB ∨
      forall theta, theta ∈ Icc baseA baseB ->
        s <= |theta - theta0| := by
  by_cases hinside : theta0 ∈ Icc minA minB
  · exact Or.inl hinside
  · right
    have houtside : theta0 < minA ∨ minB < theta0 := by
      rw [mem_Icc, not_and_or] at hinside
      rcases hinside with hleft | hright
      · exact Or.inl (lt_of_not_ge hleft)
      · exact Or.inr (lt_of_not_ge hright)
    intro theta htheta
    rcases houtside with hleft | hright
    · have hdistance : s <= theta - theta0 := by
        linarith [htheta.1]
      exact hdistance.trans (le_abs_self (theta - theta0))
    · have hdistance : s <= -(theta - theta0) := by
        linarith [htheta.2]
      exact hdistance.trans (neg_le_abs (theta - theta0))

#print axioms critical_mem_minimizerInterval_or_base_separated

end FamilyStickyCinematicL32TangencyIntervalSeparationV1
