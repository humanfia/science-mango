import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosSplitScoreNumericsV1
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosCanonicalSplitQSumV1

open FamilyStickyCinematicL32Prop41MarcusTardosSplitScoreNumericsV1

/-!
# Finite four-class sign sum for a rotated reverse split

For `u ++ v` versus `u.reverse ++ v.reverse`, the two ordered cross classes
have sign product `+1`; the two ordered within-part off-diagonal classes have
sign product `-1`.  This module sums those literal finite classes and obtains
the exact `Q` formula from Marcus--Tardos Lemma 2.
-/

def canonicalSplitQ (u v : Nat) : Real :=
  (∑ _ij ∈ (Finset.univ : Finset (Fin u)).offDiag, (-1 : Real)) +
  (∑ _ij ∈ (Finset.univ : Finset (Fin v)).offDiag, (-1 : Real)) +
  (∑ _ij ∈
      (Finset.univ : Finset (Fin u)) ×ˢ
        (Finset.univ : Finset (Fin v)), (1 : Real)) +
  (∑ _ij ∈
      (Finset.univ : Finset (Fin v)) ×ˢ
        (Finset.univ : Finset (Fin u)), (1 : Real))

theorem canonicalSplitQ_eq_splitScore (u v : Nat) :
    canonicalSplitQ u v = splitScore u v := by
  rcases u with _ | u <;> rcases v with _ | v <;>
    simp [canonicalSplitQ, Finset.offDiag_card, splitScore] <;> ring

theorem canonicalSplitQ_eq_length_sub_square (u v : Nat) :
    canonicalSplitQ u v =
      ((u + v : Nat) : Real) - ((u : Real) - v) ^ 2 := by
  rw [canonicalSplitQ_eq_splitScore,
    splitScore_eq_length_sub_square]

theorem canonicalSplitQ_le_length (u v : Nat) :
    canonicalSplitQ u v ≤ (u + v : Nat) := by
  rw [canonicalSplitQ_eq_splitScore]
  exact splitScore_le_length u v

theorem canonicalReverseQ_eq (r : Nat) :
    canonicalSplitQ r 0 = (r : Real) - (r : Real) ^ 2 := by
  rw [canonicalSplitQ_eq_splitScore,
    reverseScore_eq_length_sub_square]

#print axioms canonicalSplitQ
#print axioms canonicalSplitQ_eq_splitScore
#print axioms canonicalSplitQ_eq_length_sub_square
#print axioms canonicalSplitQ_le_length
#print axioms canonicalReverseQ_eq

end FamilyStickyCinematicL32Prop41MarcusTardosCanonicalSplitQSumV1
