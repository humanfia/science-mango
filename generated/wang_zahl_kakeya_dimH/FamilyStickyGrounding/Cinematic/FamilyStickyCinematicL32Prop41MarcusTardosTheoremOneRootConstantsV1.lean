import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosTheoremOneConstantClosureV1
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosTheoremOneRootConstantsV1

/-!
# Square-root constants in Marcus--Tardos Theorem 1

This module turns the exact denominator-free constants `64` and `384` into
the paper's displayed coefficients `8` and `21`.
-/

/-- Square-root form of the denominator-free conclusion.  The second
coefficient is rounded from `√384` to the paper's integer constant `21`. -/
theorem constant_bounds_imply_eight_or_twentyone
    {n m d k : Real}
    (hn : 0 ≤ n) (hm : 0 < m) (hd : 0 ≤ d) (hk : 0 ≤ k)
    (hbounds : d ^ 2 ≤ 64 * n * k ^ 2 ∨
      d ^ 2 * m ≤ 384 * n ^ 2) :
    d ≤ 8 * k * Real.sqrt n ∨
      d ≤ 21 * n / Real.sqrt m := by
  rcases hbounds with hfirst | hsecond
  · left
    have hrhs : 0 ≤ 8 * k * Real.sqrt n := by positivity
    apply (sq_le_sq₀ hd hrhs).mp
    calc
      d ^ 2 ≤ 64 * n * k ^ 2 := hfirst
      _ = (8 * k * Real.sqrt n) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hn]
        ring
  · right
    have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
    apply (le_div_iff₀ hsqrt).2
    have hleft : 0 ≤ d * Real.sqrt m := by positivity
    have hright : 0 ≤ 21 * n := by positivity
    apply (sq_le_sq₀ hleft hright).mp
    calc
      (d * Real.sqrt m) ^ 2 = d ^ 2 * m := by
        rw [mul_pow, Real.sq_sqrt hm.le]
      _ ≤ 384 * n ^ 2 := hsecond
      _ ≤ (21 * n) ^ 2 := by nlinarith [sq_nonneg n]

/-- The complementary small-incidence case `d*m ≤ 2n` is already inside
the paper's `21 n / √m` branch when the list count is at least one. -/
theorem small_total_incidence_le_twentyone
    {n m d : Real}
    (hn : 0 ≤ n) (hm : 1 ≤ m) (hd : 0 ≤ d)
    (hsmall : d * m ≤ 2 * n) :
    d ≤ 21 * n / Real.sqrt m := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hsqrtPos : 0 < Real.sqrt m := Real.sqrt_pos.2 hmpos
  apply (le_div_iff₀ hsqrtPos).2
  have hsqrtLe : Real.sqrt m ≤ m := by
    have hone : Real.sqrt m ≤ 1 ∨ 1 ≤ Real.sqrt m := le_total _ _
    rcases hone with hone | hone
    · exact hone.trans hm
    · have hsquare := mul_le_mul_of_nonneg_left hone (Real.sqrt_nonneg m)
      simpa [Real.mul_self_sqrt hmpos.le] using hsquare
  calc
    d * Real.sqrt m ≤ d * m := mul_le_mul_of_nonneg_left hsqrtLe hd
    _ ≤ 2 * n := hsmall
    _ ≤ 21 * n := by nlinarith

#print axioms constant_bounds_imply_eight_or_twentyone
#print axioms small_total_incidence_le_twentyone

end FamilyStickyCinematicL32Prop41MarcusTardosTheoremOneRootConstantsV1
