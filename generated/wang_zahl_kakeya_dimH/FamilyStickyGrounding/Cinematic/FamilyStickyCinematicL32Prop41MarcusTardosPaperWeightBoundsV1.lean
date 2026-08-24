import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosPaperGeometricBoundV1
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosPaperWeightBoundsV1

open FamilyStickyCinematicL32Prop41MarcusTardosPaperGeometricBoundV1

/-!
# Explicit Marcus--Tardos paper weights

At source level `l = 1,...,k`, put
`w_l = 1 / (1 + k / 2^(l/2))`.  The realization below uses
`2^(l/2) = (sqrt 2)^l` and proves all three quoted finite estimates.
-/

noncomputable def paperWeight (depth : Nat) (level : Fin depth) : Real :=
  (1 + (depth : Real) /
    (Real.sqrt 2) ^ (level.1 + 1))⁻¹

theorem paperWeight_pos (depth : Nat) (level : Fin depth) :
    0 < paperWeight depth level := by
  unfold paperWeight
  positivity

theorem paperWeight_le_one (depth : Nat) (level : Fin depth) :
    paperWeight depth level ≤ 1 := by
  unfold paperWeight
  apply (inv_le_one₀ (by positivity)).2
  have hratio : 0 ≤ (depth : Real) /
      (Real.sqrt 2) ^ (level.1 + 1) := by positivity
  linarith

theorem paperWeight_inv (depth : Nat) (level : Fin depth) :
    (paperWeight depth level)⁻¹ =
      1 + (depth : Real) /
        (Real.sqrt 2) ^ (level.1 + 1) := by
  unfold paperWeight
  rw [inv_inv]

theorem paperWeight_sum_le_depth (depth : Nat) :
    (∑ level : Fin depth, paperWeight depth level) ≤ depth := by
  calc
    (∑ level : Fin depth, paperWeight depth level) ≤
        ∑ _level : Fin depth, (1 : Real) :=
      Finset.sum_le_sum fun level hlevel ↦ paperWeight_le_one depth level
    _ = depth := by simp

theorem paperWeight_reciprocal_sum_le_four_depth (depth : Nat) :
    (∑ level : Fin depth, (paperWeight depth level)⁻¹) ≤
      4 * depth := by
  have hgeom := shifted_inv_sqrt_two_sum_le_three depth
  calc
    (∑ level : Fin depth, (paperWeight depth level)⁻¹) =
        (depth : Real) + (depth : Real) *
          ∑ level : Fin depth,
            (Real.sqrt 2)⁻¹ ^ (level.1 + 1) := by
      simp_rw [paperWeight_inv, div_eq_mul_inv, inv_pow]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    _ ≤ (depth : Real) + (depth : Real) * 3 := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left hgeom (Nat.cast_nonneg depth)) _
    _ = 4 * depth := by ring

theorem sqrt_two_pow_sq (l : Nat) :
    ((Real.sqrt 2) ^ l) ^ 2 = (2 : Real) ^ l := by
  rw [pow_two, ← mul_pow, Real.mul_self_sqrt (by norm_num)]

theorem paperWeight_div_two_pow_le
    (depth : Nat) (hdepth : 1 ≤ depth) (level : Fin depth) :
    paperWeight depth level / (2 : Real) ^ (level.1 + 1) ≤
      (Real.sqrt 2)⁻¹ ^ (level.1 + 1) / (depth : Real) := by
  let a : Real := (Real.sqrt 2) ^ (level.1 + 1)
  let k : Real := depth
  have ha : 0 < a := by dsimp [a]; positivity
  have hk : 0 < k := by
    dsimp [k]
    exact_mod_cast hdepth
  have hweightA : paperWeight depth level ≤ a / k := by
    calc
      paperWeight depth level =
          1 / (1 + k / a) := by
        simp [paperWeight, a, k, one_div]
      _ ≤ 1 / (k / a) := by
        exact one_div_le_one_div_of_le (div_pos hk ha)
          (by linarith [div_pos hk ha])
      _ = a / k := by field_simp
  have haSq : a ^ 2 = (2 : Real) ^ (level.1 + 1) := by
    simpa [a] using sqrt_two_pow_sq (level.1 + 1)
  calc
    paperWeight depth level / (2 : Real) ^ (level.1 + 1) ≤
        (a / k) / (2 : Real) ^ (level.1 + 1) := by
      exact div_le_div_of_nonneg_right hweightA (by positivity)
    _ = a⁻¹ / k := by
      rw [← haSq]
      field_simp [ne_of_gt ha, ne_of_gt hk]
    _ = (Real.sqrt 2)⁻¹ ^ (level.1 + 1) / (depth : Real) := by
      simp [a, k, inv_pow]

theorem paperWeight_weighted_depth_sum_le_three_div
    (depth : Nat) (hdepth : 1 ≤ depth) :
    (∑ level : Fin depth,
      paperWeight depth level / (2 : Real) ^ (level.1 + 1)) ≤
        3 / (depth : Real) := by
  calc
    (∑ level : Fin depth,
      paperWeight depth level / (2 : Real) ^ (level.1 + 1)) ≤
        ∑ level : Fin depth,
          (Real.sqrt 2)⁻¹ ^ (level.1 + 1) / (depth : Real) := by
      exact Finset.sum_le_sum fun level hlevel ↦
        paperWeight_div_two_pow_le depth hdepth level
    _ = (∑ level : Fin depth,
          (Real.sqrt 2)⁻¹ ^ (level.1 + 1)) / (depth : Real) := by
      rw [Finset.sum_div]
    _ ≤ 3 / (depth : Real) := by
      exact div_le_div_of_nonneg_right
        (shifted_inv_sqrt_two_sum_le_three depth) (Nat.cast_nonneg depth)

#print axioms paperWeight_pos
#print axioms paperWeight_sum_le_depth
#print axioms paperWeight_reciprocal_sum_le_four_depth
#print axioms paperWeight_weighted_depth_sum_le_three_div

end FamilyStickyCinematicL32Prop41MarcusTardosPaperWeightBoundsV1
