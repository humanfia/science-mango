import Family8Grounding.Family8DoubledParentConflictKatzTaoWeightedDef212FrostmanV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8KatzTaoDoubledParentConflictBudgetSideConditionsV1

open Family8DoubledParentConflictKatzTaoWeightedDef212FrostmanV2

noncomputable section

/-!
# Automatic side conditions for the exact Katz--Tao conflict budget

The loss is the `ENNReal` coercion of the natural number `1 + N*M`.
Consequently it is at least one, nonzero, and finite without any geometric
hypothesis.
-/

theorem one_le_katzTaoDoubledParentConflictBudget
    (delta rho : NNReal) (A : ENNReal) :
    (1 : ENNReal) ≤ katzTaoDoubledParentConflictBudget delta rho A := by
  unfold katzTaoDoubledParentConflictBudget
  norm_cast
  omega

theorem katzTaoDoubledParentConflictBudget_ne_zero
    (delta rho : NNReal) (A : ENNReal) :
    katzTaoDoubledParentConflictBudget delta rho A ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1)
    (one_le_katzTaoDoubledParentConflictBudget delta rho A))

theorem katzTaoDoubledParentConflictBudget_ne_top
    (delta rho : NNReal) (A : ENNReal) :
    katzTaoDoubledParentConflictBudget delta rho A ≠ ∞ := by
  unfold katzTaoDoubledParentConflictBudget
  exact ENNReal.coe_ne_top

#print axioms one_le_katzTaoDoubledParentConflictBudget
#print axioms katzTaoDoubledParentConflictBudget_ne_zero
#print axioms katzTaoDoubledParentConflictBudget_ne_top

end
end Family8KatzTaoDoubledParentConflictBudgetSideConditionsV1
