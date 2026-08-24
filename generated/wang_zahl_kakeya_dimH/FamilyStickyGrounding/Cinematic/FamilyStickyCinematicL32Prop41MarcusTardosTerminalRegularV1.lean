import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosTerminalRegularV1

open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1
open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1.DistinctLinearSequence

/-!
# Singleton blocks are automatically intersection reverse

At the terminal level of the Marcus--Tardos dyadic decomposition every block
has at most one symbol.  The order on a common set of at most one symbol is
therefore equal to its reverse.  This is the terminal regularity input for the
unique-leader construction; it is not a Marcus--Tardos estimate premise.
-/

theorem list_eq_of_perm_of_length_le_one
    {α : Type*} {l₁ l₂ : List α}
    (hperm : l₁.Perm l₂) (hlen : l₁.length ≤ 1) :
    l₁ = l₂ := by
  induction hperm with
  | nil => rfl
  | cons a h ih =>
      simp only [List.length_cons] at hlen
      exact congrArg (List.cons a) (ih (by omega))
  | swap a b l =>
      simp only [List.length_cons] at hlen
      omega
  | trans h₁ h₂ ih₁ ih₂ =>
      exact ih₁ hlen |>.trans (ih₂ (h₁.length_eq ▸ hlen))

namespace DistinctLinearSequence

variable {symbol : Type*} [DecidableEq symbol]

theorem commonOrder_perm (A B : DistinctLinearSequence symbol) :
    (A.commonOrder B).Perm (B.commonOrder A) := by
  apply (List.perm_ext_iff_of_nodup
    (A.nodup_order.filter _) (B.nodup_order.filter _)).2
  intro a
  simp [support, and_comm]

theorem intersectionReverse_of_left_length_le_one
    (A B : DistinctLinearSequence symbol)
    (hlen : A.order.length ≤ 1) :
    A.IntersectionReverse B := by
  rw [IntersectionReverse]
  have hcommon : (A.commonOrder B).length ≤ 1 :=
    (List.length_filter_le _ _).trans hlen
  have hself : (A.commonOrder B).reverse = A.commonOrder B := by
    apply list_eq_of_perm_of_length_le_one (List.reverse_perm _)
    simpa using hcommon
  exact hself.trans
    (list_eq_of_perm_of_length_le_one (commonOrder_perm A B) hcommon)

theorem intersectionReverse_of_right_length_le_one
    (A B : DistinctLinearSequence symbol)
    (hlen : B.order.length ≤ 1) :
    A.IntersectionReverse B := by
  rw [IntersectionReverse]
  have hcommon : (B.commonOrder A).length ≤ 1 :=
    (List.length_filter_le _ _).trans hlen
  have hperm := (commonOrder_perm A B)
  have hleft : A.commonOrder B = B.commonOrder A :=
    list_eq_of_perm_of_length_le_one hperm
      (hperm.length_eq ▸ hcommon)
  rw [hleft]
  exact list_eq_of_perm_of_length_le_one (List.reverse_perm _) (by simpa using hcommon)

#print axioms commonOrder_perm
#print axioms intersectionReverse_of_left_length_le_one
#print axioms intersectionReverse_of_right_length_le_one

end DistinctLinearSequence

end FamilyStickyCinematicL32Prop41MarcusTardosTerminalRegularV1
