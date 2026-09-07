import Mathlib.Tactic

/-!
# Insert a positive middle average into a three-factor bound, V2

This scalar lemma records the exact regrouping used by the long-core branch.
It never identifies two geometrically different averages: a separately
constructed middle average may be inserted only after proving it is at least
one.  V1 used an unavailable order helper and is not imported.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal

namespace Family8InsertPositiveMiddleAverageRegroupingV2

/-- Selector, branching, and assembly losses can be grouped with the first
factor while a genuine positive middle average is inserted explicitly. -/
theorem le_regrouped_threeFactors_of_one_le_middle
    {source first selector assembly middle third : ENNReal}
    (hsource : source <= first * (selector * (assembly * third)))
    (hmiddle : 1 <= middle) :
    source <= (first * (selector * assembly)) * (middle * third) := by
  have hthird : third <= middle * third := by
    simpa only [one_mul] using
      (mul_le_mul' hmiddle (le_refl third))
  calc
    source <= first * (selector * (assembly * third)) := hsource
    _ <= first * (selector * (assembly * (middle * third))) :=
      mul_le_mul' le_rfl
        (mul_le_mul' le_rfl (mul_le_mul' le_rfl hthird))
    _ = (first * (selector * assembly)) * (middle * third) := by
      ac_rfl

#print axioms le_regrouped_threeFactors_of_one_le_middle

end Family8InsertPositiveMiddleAverageRegroupingV2
