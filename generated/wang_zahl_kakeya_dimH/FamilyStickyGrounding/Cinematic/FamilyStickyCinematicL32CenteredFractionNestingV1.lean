import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CenteredFractionIntervalsV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32CenteredFractionNestingV1

open FamilyStickyCinematicL32CenteredFractionIntervalsV1

/-!
# Nesting of the canonical PYZ centered intervals

These are the literal `J/4 ⊆ J/2 ⊆ J` inclusions used to transfer the
universal lower bound from Definition 3.7 to rectangle-base sublevels.
-/

/-- The concentric quarter interval is contained in the concentric half
interval. -/
theorem quarter_subset_half {A B : Real} (hAB : A <= B) :
    centeredFractionIcc A B (1 / 4 : Real) ⊆
      centeredFractionIcc A B (1 / 2 : Real) := by
  intro z hz
  rcases hz with ⟨hzLeft, hzRight⟩
  constructor <;>
    simp only [centeredFractionLeft, centeredFractionRight] at * <;>
    linarith

/-- The concentric half interval is contained in its ambient interval. -/
theorem half_subset_whole {A B : Real} (hAB : A <= B) :
    centeredFractionIcc A B (1 / 2 : Real) ⊆ Icc A B := by
  intro z hz
  rcases hz with ⟨hzLeft, hzRight⟩
  constructor <;>
    simp only [centeredFractionLeft, centeredFractionRight] at * <;>
    linarith

/-- The concentric quarter interval is contained in its ambient interval. -/
theorem quarter_subset_whole {A B : Real} (hAB : A <= B) :
    centeredFractionIcc A B (1 / 4 : Real) ⊆ Icc A B :=
  (quarter_subset_half hAB).trans (half_subset_whole hAB)

/-- Both canonical centered intervals are nonempty when the ambient interval
is ordered. -/
theorem centered_half_and_quarter_endpoints_ordered {A B : Real}
    (hAB : A <= B) :
    centeredFractionLeft A B (1 / 2 : Real) <=
        centeredFractionRight A B (1 / 2 : Real) ∧
      centeredFractionLeft A B (1 / 4 : Real) <=
        centeredFractionRight A B (1 / 4 : Real) := by
  constructor <;>
    simp only [centeredFractionLeft, centeredFractionRight] <;>
    linarith

#print axioms quarter_subset_half
#print axioms half_subset_whole
#print axioms quarter_subset_whole
#print axioms centered_half_and_quarter_endpoints_ordered

end FamilyStickyCinematicL32CenteredFractionNestingV1
