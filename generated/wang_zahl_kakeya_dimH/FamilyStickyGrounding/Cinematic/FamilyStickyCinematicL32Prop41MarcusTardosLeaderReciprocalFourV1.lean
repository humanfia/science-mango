import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosLeaderReciprocalFourV1

/-! # Four leaders per level imply the reciprocal-weight factor four -/

theorem sum_leader_reciprocal_le_four_mul_sum
    {level leader : Type*} [Fintype level]
    [DecidableEq level] [DecidableEq leader]
    (leaders : Finset leader) (levelOf : leader → level)
    (weight : level → Real)
    (hweight : ∀ l, 0 < weight l)
    (hfour : ∀ l,
      (leaders.filter fun x => levelOf x = l).card ≤ 4) :
    (∑ x ∈ leaders, (weight (levelOf x))⁻¹) ≤
      4 * ∑ l, (weight l)⁻¹ := by
  classical
  calc
    (∑ x ∈ leaders, (weight (levelOf x))⁻¹) =
        ∑ x ∈ leaders, ∑ l, if levelOf x = l then (weight l)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      simp
    _ = ∑ l, ∑ x ∈ leaders,
        if levelOf x = l then (weight l)⁻¹ else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ l, ((leaders.filter fun x => levelOf x = l).card : Real) *
        (weight l)⁻¹ := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [← Finset.sum_filter]
      simp
    _ ≤ ∑ l, 4 * (weight l)⁻¹ := by
      apply Finset.sum_le_sum
      intro l hl
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfour l)
        (inv_nonneg.mpr (hweight l).le)
    _ = 4 * ∑ l, (weight l)⁻¹ := by rw [Finset.mul_sum]

#print axioms sum_leader_reciprocal_le_four_mul_sum

end FamilyStickyCinematicL32Prop41MarcusTardosLeaderReciprocalFourV1
