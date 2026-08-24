import Mathlib.Data.List.Cycle

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosRotationSplitNormalFormV1

/-!
# Split normal form for a rotated reverse list

This is the literal first sentence of the proof of Marcus--Tardos Lemma 2:
if the common orders are cyclically reversed, then after choosing the two
linear cuts the second common order is `u.reverse ++ v.reverse` while the
first is `u ++ v`.
-/

theorem exists_append_reverse_append_reverse_of_reverse_isRotated
    {α : Type*} {l r : List α}
    (hrot : l.reverse ~r r) :
    ∃ u v : List α,
      l = u ++ v ∧ r = u.reverse ++ v.reverse := by
  rcases hrot with ⟨n, rfl⟩
  let k := n % l.reverse.length
  have hrotate : l.reverse.rotate n =
      l.reverse.drop k ++ l.reverse.take k := by
    simpa [k] using
      (List.rotate_eq_drop_append_take_mod (l := l.reverse) (n := n))
  refine ⟨(l.reverse.drop k).reverse,
    (l.reverse.take k).reverse, ?_, ?_⟩
  · rw [← List.reverse_append, List.take_append_drop, List.reverse_reverse]
  · simpa only [List.reverse_reverse] using hrotate

#print axioms exists_append_reverse_append_reverse_of_reverse_isRotated

end FamilyStickyCinematicL32Prop41MarcusTardosRotationSplitNormalFormV1
