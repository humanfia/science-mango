import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosSplitTagCoreV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosReverseListIndexV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosSplitTagReverseRankCleanV1

open FamilyStickyCinematicL32Prop41MarcusTardosSplitTagCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosReverseListIndexV1
open FamilyStickyCinematicL32Prop41MarcusTardosTaggedSplitOrderSignV1

/-! # The same split tags in the split-reversed list -/

def splitReverseTag {symbol : Type*} (left right : List symbol) :
    Sum (Fin left.length) (Fin right.length) →
      Sum (Fin left.reverse.length) (Fin right.reverse.length)
  | Sum.inl i => Sum.inl (reverseIndex left i)
  | Sum.inr j => Sum.inr (reverseIndex right j)

@[simp]
theorem firstRank_splitReverseTag
    {symbol : Type*} (left right : List symbol)
    (z : Sum (Fin left.length) (Fin right.length)) :
    firstRank (splitReverseTag left right z) = splitReverseRank z := by
  rcases z with i | j <;>
    simp [splitReverseTag, firstRank, splitReverseRank, reverseIndex_val]

@[simp]
theorem splitTagSymbol_splitReverseTag
    {symbol : Type*} (left right : List symbol)
    (z : Sum (Fin left.length) (Fin right.length)) :
    splitTagSymbol left.reverse right.reverse
        (splitReverseTag left right z) =
      splitTagSymbol left right z := by
  rcases z with i | j
  · simpa only [splitReverseTag, splitTagSymbol_inl] using
      reverse_get_reverseIndex left i
  · simpa only [splitReverseTag, splitTagSymbol_inr] using
      reverse_get_reverseIndex right j

theorem idxOf_splitReverse_splitTagSymbol_eq_splitReverseRank
    {symbol : Type*} [DecidableEq symbol]
    {left right : List symbol} (hnodup : (left ++ right).Nodup)
    (z : Sum (Fin left.length) (Fin right.length)) :
    (left.reverse ++ right.reverse).idxOf
        (splitTagSymbol left right z) = splitReverseRank z := by
  have hswap : (right.reverse ++ left.reverse).Nodup := by
    rw [← List.reverse_append]
    exact List.nodup_reverse.mpr hnodup
  have hrevNodup : (left.reverse ++ right.reverse).Nodup :=
    List.nodup_append_comm.mp hswap
  rw [← splitTagSymbol_splitReverseTag left right z]
  rw [idxOf_splitTagSymbol_eq_firstRank hrevNodup]
  exact firstRank_splitReverseTag left right z

#print axioms splitReverseTag
#print axioms firstRank_splitReverseTag
#print axioms splitTagSymbol_splitReverseTag
#print axioms idxOf_splitReverse_splitTagSymbol_eq_splitReverseRank

end FamilyStickyCinematicL32Prop41MarcusTardosSplitTagReverseRankCleanV1
