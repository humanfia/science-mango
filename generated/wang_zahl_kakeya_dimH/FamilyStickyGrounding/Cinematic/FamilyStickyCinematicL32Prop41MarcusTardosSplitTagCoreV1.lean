import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosTaggedSplitOrderSignV1
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosSplitTagCoreV1

open FamilyStickyCinematicL32Prop41MarcusTardosTaggedSplitOrderSignV1

/-! # Position tags for a literal left/right list split -/

def splitTagIndex {symbol : Type*} (left right : List symbol) :
    Sum (Fin left.length) (Fin right.length) → Fin (left ++ right).length :=
  fun z ↦ Fin.cast (by simp) (finSumFinEquiv z)

def splitTagSymbol {symbol : Type*} (left right : List symbol)
    (z : Sum (Fin left.length) (Fin right.length)) : symbol :=
  (left ++ right).get (splitTagIndex left right z)

@[simp]
theorem splitTagIndex_inl_val
    {symbol : Type*} (left right : List symbol) (i : Fin left.length) :
    (splitTagIndex left right (Sum.inl i)).1 = i.1 := by
  simp [splitTagIndex]

@[simp]
theorem splitTagIndex_inr_val
    {symbol : Type*} (left right : List symbol) (j : Fin right.length) :
    (splitTagIndex left right (Sum.inr j)).1 = left.length + j.1 := by
  simp [splitTagIndex]

@[simp]
theorem splitTagSymbol_inl
    {symbol : Type*} (left right : List symbol) (i : Fin left.length) :
    splitTagSymbol left right (Sum.inl i) = left.get i := by
  simp [splitTagSymbol, splitTagIndex]

@[simp]
theorem splitTagSymbol_inr
    {symbol : Type*} (left right : List symbol) (j : Fin right.length) :
    splitTagSymbol left right (Sum.inr j) = right.get j := by
  simp [splitTagSymbol, splitTagIndex]

theorem splitTagSymbol_mem
    {symbol : Type*} (left right : List symbol)
    (z : Sum (Fin left.length) (Fin right.length)) :
    splitTagSymbol left right z ∈ left ++ right := by
  unfold splitTagSymbol
  exact List.get_mem (l := left ++ right) _

theorem splitTagSymbol_injective
    {symbol : Type*} {left right : List symbol}
    (hnodup : (left ++ right).Nodup) :
    Function.Injective (splitTagSymbol left right) := by
  intro z w hzw
  have hget : splitTagIndex left right z = splitTagIndex left right w :=
    (hnodup.get_inj_iff).mp hzw
  apply finSumFinEquiv.injective
  apply Fin.ext
  have hval := congrArg Fin.val hget
  simpa [splitTagIndex] using hval

theorem exists_splitTagSymbol_eq_of_mem
    {symbol : Type*} {left right : List symbol} {x : symbol}
    (hx : x ∈ left ++ right) :
    ∃ z : Sum (Fin left.length) (Fin right.length),
      splitTagSymbol left right z = x := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
  let k : Fin (left.length + right.length) := Fin.cast (by simp) i
  refine ⟨finSumFinEquiv.symm k, ?_⟩
  unfold splitTagSymbol splitTagIndex
  simp only [Equiv.apply_symm_apply, k]
  congr

theorem idxOf_splitTagSymbol
    {symbol : Type*} [DecidableEq symbol]
    {left right : List symbol} (hnodup : (left ++ right).Nodup)
    (z : Sum (Fin left.length) (Fin right.length)) :
    (left ++ right).idxOf (splitTagSymbol left right z) =
      (splitTagIndex left right z).1 := by
  simpa [splitTagSymbol] using
    (List.get_idxOf hnodup (splitTagIndex left right z))

theorem idxOf_splitTagSymbol_eq_firstRank
    {symbol : Type*} [DecidableEq symbol]
    {left right : List symbol} (hnodup : (left ++ right).Nodup)
    (z : Sum (Fin left.length) (Fin right.length)) :
    (left ++ right).idxOf (splitTagSymbol left right z) = firstRank z := by
  rw [idxOf_splitTagSymbol hnodup]
  rcases z with i | j <;> simp [firstRank]

#print axioms splitTagIndex
#print axioms splitTagSymbol
#print axioms splitTagSymbol_injective
#print axioms exists_splitTagSymbol_eq_of_mem
#print axioms idxOf_splitTagSymbol_eq_firstRank

end FamilyStickyCinematicL32Prop41MarcusTardosSplitTagCoreV1
