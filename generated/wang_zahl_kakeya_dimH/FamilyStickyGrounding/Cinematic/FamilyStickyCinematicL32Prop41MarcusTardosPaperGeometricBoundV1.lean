import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosPaperGeometricBoundV1

/-! The explicit geometric tail used by the source paper's weights. -/

theorem four_thirds_le_sqrt_two :
    (4 / 3 : Real) ≤ Real.sqrt 2 := by
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith

theorem inv_sqrt_two_le_three_quarters :
    (Real.sqrt 2)⁻¹ ≤ (3 / 4 : Real) := by
  have h := one_div_le_one_div_of_le
    (by norm_num : (0 : Real) < 4 / 3) four_thirds_le_sqrt_two
  norm_num [one_div] at h ⊢
  exact h

theorem shifted_three_quarters_sum_le_three (depth : Nat) :
    (∑ level : Fin depth, (3 / 4 : Real) ^ (level.1 + 1)) ≤ 3 := by
  rw [Fin.sum_univ_eq_sum_range
    (fun i : Nat ↦ (3 / 4 : Real) ^ (i + 1)) depth]
  have hsumm : Summable (fun i : Nat ↦ (3 / 4 : Real) ^ i) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hunshifted :
      (∑ i ∈ Finset.range depth, (3 / 4 : Real) ^ i) ≤ 4 := by
    calc
      (∑ i ∈ Finset.range depth, (3 / 4 : Real) ^ i) ≤
          ∑' i : Nat, (3 / 4 : Real) ^ i :=
        hsumm.sum_le_tsum (Finset.range depth) (fun i hi ↦ by positivity)
      _ = (1 - (3 / 4 : Real))⁻¹ :=
        tsum_geometric_of_lt_one (by norm_num) (by norm_num)
      _ = 4 := by norm_num
  calc
    (∑ i ∈ Finset.range depth, (3 / 4 : Real) ^ (i + 1)) =
        (∑ i ∈ Finset.range depth, (3 / 4 : Real) ^ i) * (3 / 4) := by
      simp_rw [pow_succ]
      rw [Finset.sum_mul]
    _ ≤ 4 * (3 / 4 : Real) :=
      mul_le_mul_of_nonneg_right hunshifted (by norm_num)
    _ = 3 := by norm_num

theorem shifted_inv_sqrt_two_sum_le_three (depth : Nat) :
    (∑ level : Fin depth,
      (Real.sqrt 2)⁻¹ ^ (level.1 + 1)) ≤ 3 := by
  calc
    (∑ level : Fin depth,
        (Real.sqrt 2)⁻¹ ^ (level.1 + 1)) ≤
        ∑ level : Fin depth, (3 / 4 : Real) ^ (level.1 + 1) := by
      exact Finset.sum_le_sum fun level hlevel ↦
        pow_le_pow_left₀ (by positivity) inv_sqrt_two_le_three_quarters _
    _ ≤ 3 := shifted_three_quarters_sum_le_three depth

#print axioms four_thirds_le_sqrt_two
#print axioms inv_sqrt_two_le_three_quarters
#print axioms shifted_three_quarters_sum_le_three
#print axioms shifted_inv_sqrt_two_sum_le_three

end FamilyStickyCinematicL32Prop41MarcusTardosPaperGeometricBoundV1
