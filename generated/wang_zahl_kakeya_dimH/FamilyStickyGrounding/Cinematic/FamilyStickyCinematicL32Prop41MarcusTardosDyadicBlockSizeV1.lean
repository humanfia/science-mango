import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlocksV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlockSizeV1

open FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlocksV1

/-!
# Exact almost-equal size bound for recursive dyadic blocks
-/

/-- Each half has at most half the parent length, rounded upward.  The
subtraction-free form is convenient for iterating the estimate. -/
theorem two_mul_length_le_length_add_one_of_mem_bisect
    {α : Type*} {parent child : List α}
    (hchild : child ∈ bisect parent) :
    2 * child.length ≤ parent.length + 1 := by
  simp [bisect] at hchild
  rcases hchild with rfl | rfl
  · rw [List.length_take]
    have hdiv := Nat.mul_div_le (parent.length + 1) 2
    omega
  · rw [List.length_drop]
    omega

/-- Exact iterated almost-equal bound.  This is stronger than the paper's
real inequality `|A_s| < d / 2^l + 1`. -/
theorem pow_mul_length_le_length_add_pred
    {α : Type*} {depth : Nat} {l child : List α}
    (hchild : child ∈ dyadicBlocks depth l) :
    2 ^ depth * child.length ≤ l.length + (2 ^ depth - 1) := by
  induction depth generalizing child with
  | zero =>
      simp only [dyadicBlocks, List.mem_singleton] at hchild
      subst child
      simp
  | succ depth ih =>
      obtain ⟨parent, hparent, hchildParent⟩ :=
        mem_dyadicBlocks_succ_iff.mp hchild
      have hparentBound := ih hparent
      have hhalf :=
        two_mul_length_le_length_add_one_of_mem_bisect hchildParent
      rw [pow_succ]
      have hpow : 1 ≤ 2 ^ depth := one_le_pow₀ (by omega)
      calc
        2 ^ depth * 2 * child.length =
            2 ^ depth * (2 * child.length) := by ring
        _ ≤ 2 ^ depth * (parent.length + 1) :=
          Nat.mul_le_mul_left _ hhalf
        _ = 2 ^ depth * parent.length + 2 ^ depth := by ring
        _ ≤ (l.length + (2 ^ depth - 1)) + 2 ^ depth :=
          Nat.add_le_add_right hparentBound _
        _ = l.length + (2 ^ depth * 2 - 1) := by omega

#print axioms two_mul_length_le_length_add_one_of_mem_bisect
#print axioms pow_mul_length_le_length_add_pred

end FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlockSizeV1
