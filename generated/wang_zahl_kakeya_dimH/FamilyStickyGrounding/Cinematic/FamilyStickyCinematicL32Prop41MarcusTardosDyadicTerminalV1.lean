import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlockSizeV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosDyadicTerminalV1

open FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlocksV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlockSizeV1

/-! # Singleton terminal blocks at the paper's logarithmic depth -/

theorem length_le_one_of_length_le_pow
    {α : Type*} {depth : Nat} {l child : List α}
    (hlength : l.length ≤ 2 ^ depth)
    (hchild : child ∈ dyadicBlocks depth l) :
    child.length ≤ 1 := by
  have hbound := pow_mul_length_le_length_add_pred hchild
  by_contra hnot
  have htwo : 2 ≤ child.length := by omega
  have hpow : 1 ≤ 2 ^ depth := one_le_pow₀ (by omega)
  have hmul := Nat.mul_le_mul_left (2 ^ depth) htwo
  omega

#print axioms length_le_one_of_length_le_pow

end FamilyStickyCinematicL32Prop41MarcusTardosDyadicTerminalV1
