import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlockSizeV1
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlockRealSizeV1

open FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlocksV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlockSizeV1

/-! # Real form of the exact dyadic block-size estimate -/

/-- The exact real inequality used in the diagonal estimate of Lemma 4. -/
theorem length_sub_one_le_div_pow
    {α : Type*} {depth : Nat} {l child : List α}
    (hchild : child ∈ dyadicBlocks depth l) :
    (child.length : Real) - 1 ≤
      (l.length : Real) / (2 ^ depth : Nat) := by
  have hdenNat : 1 ≤ 2 ^ depth := one_le_pow₀ (by omega)
  have hdenReal : 0 < ((2 ^ depth : Nat) : Real) := by positivity
  by_cases hzero : child.length = 0
  · rw [hzero]
    have hnonneg : 0 ≤ (l.length : Real) / (2 : Real) ^ depth := by
      positivity
    norm_num at ⊢
    linarith
  · have hchildPos : 1 ≤ child.length := Nat.one_le_iff_ne_zero.mpr hzero
    have hbound := pow_mul_length_le_length_add_pred hchild
    have hchildDecomp : child.length = child.length - 1 + 1 := by omega
    rw [hchildDecomp, Nat.mul_add] at hbound
    have hnat : 2 ^ depth * (child.length - 1) ≤ l.length := by omega
    have hcast :
        (((2 ^ depth : Nat) : Real) * ((child.length - 1 : Nat) : Real)) ≤
          (l.length : Real) := by
      exact_mod_cast hnat
    have hcastSub : ((child.length - 1 : Nat) : Real) =
        (child.length : Real) - 1 := by
      rw [Nat.cast_sub hchildPos]
      norm_num
    apply (le_div_iff₀ hdenReal).2
    calc
      ((child.length : Real) - 1) * ((2 ^ depth : Nat) : Real) =
          ((2 ^ depth : Nat) : Real) *
            ((child.length - 1 : Nat) : Real) := by rw [hcastSub]; ring
      _ ≤ (l.length : Real) := hcast

#print axioms length_sub_one_le_div_pow

end FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlockRealSizeV1
