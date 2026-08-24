import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosSplitScoreNumericsV1

/-!
# Exact arithmetic in Marcus--Tardos Lemma 2

If the common symbols have first order `u ++ v` and second order
`u.reverse ++ v.reverse`, ordered cross-part pairs contribute `+1` and
ordered within-part pairs contribute `-1`.  `splitScore` is exactly the
resulting paper expression.  The separate sign-enumeration connector is not
assumed here.
-/

def splitScore (u v : Nat) : Real :=
  2 * (u : Real) * v -
    ((u : Real) * ((u : Real) - 1) +
      (v : Real) * ((v : Real) - 1))

theorem splitScore_eq_length_sub_square (u v : Nat) :
    splitScore u v =
      ((u + v : Nat) : Real) - ((u : Real) - v) ^ 2 := by
  simp only [splitScore, Nat.cast_add]
  ring

theorem splitScore_le_length (u v : Nat) :
    splitScore u v ≤ (u + v : Nat) := by
  rw [splitScore_eq_length_sub_square]
  exact sub_le_self _ (sq_nonneg _)

theorem reverseScore_eq_length_sub_square (r : Nat) :
    splitScore r 0 = (r : Real) - (r : Real) ^ 2 := by
  simp [splitScore]
  ring

theorem reverseScore_le_length (r : Nat) :
    splitScore r 0 ≤ r :=
  splitScore_le_length r 0

#print axioms splitScore
#print axioms splitScore_eq_length_sub_square
#print axioms splitScore_le_length
#print axioms reverseScore_eq_length_sub_square
#print axioms reverseScore_le_length

end FamilyStickyCinematicL32Prop41MarcusTardosSplitScoreNumericsV1
