import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CenteredFractionIntervalsV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32CenteredFractionHalfMarginV1

open FamilyStickyCinematicL32CenteredFractionIntervalsV1

/-!
# Margins of the concentric half interval

Provenance: PYZ Definition 3.7 and Lemma 3.8(1a): the tangency minimizer is
chosen in `J/2`, hence has one quarter of the length of `J` available on
both sides inside `J`.
-/

/-- Every point of the concentric half interval has a quarter-length margin
to both endpoints of the ambient interval. -/
theorem mem_half_has_whole_margin
    {A B x : Real}
    (hx : x ∈ centeredFractionIcc A B (1 / 2 : Real)) :
    (B - A) / 4 <= x - A ∧
      (B - A) / 4 <= B - x := by
  rcases hx with ⟨hxLeft, hxRight⟩
  constructor <;>
    simp only [centeredFractionLeft,
      centeredFractionRight] at * <;>
    linarith

/-- If the normalized interval has length at least one half, points of its
concentric half have an absolute one-eighth margin to both endpoints. -/
theorem mem_half_has_eighth_whole_margin
    {A B x : Real} (hwidth : (1 / 2 : Real) <= B - A)
    (hx : x ∈ centeredFractionIcc A B (1 / 2 : Real)) :
    (1 / 8 : Real) <= x - A ∧ (1 / 8 : Real) <= B - x := by
  have hmargins := mem_half_has_whole_margin hx
  constructor <;> linarith

#print axioms mem_half_has_whole_margin
#print axioms mem_half_has_eighth_whole_margin

end FamilyStickyCinematicL32CenteredFractionHalfMarginV1
