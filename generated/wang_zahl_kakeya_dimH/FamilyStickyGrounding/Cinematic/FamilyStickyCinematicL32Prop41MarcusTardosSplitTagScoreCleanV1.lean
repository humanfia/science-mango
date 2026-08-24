import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosSplitTagReverseRankCleanV1
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosSplitTagScoreCleanV1

open FamilyStickyCinematicL32Prop41MarcusTardosSplitTagCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosSplitTagReverseRankCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosTaggedSplitOrderSignV1

/-! # Relabeling an actual split-symbol score by finite position tags -/

noncomputable def splitTagEquiv
    {symbol : Type*} [DecidableEq symbol]
    (left right : List symbol) (hnodup : (left ++ right).Nodup) :
    Sum (Fin left.length) (Fin right.length) ≃
      {x : symbol // x ∈ left ++ right} :=
  Equiv.ofBijective
    (fun z ↦ ⟨splitTagSymbol left right z,
      splitTagSymbol_mem left right z⟩)
    ⟨by
      intro z w hzw
      apply splitTagSymbol_injective hnodup
      exact congrArg Subtype.val hzw,
    by
      intro x
      obtain ⟨z, hz⟩ := exists_splitTagSymbol_eq_of_mem x.2
      exact ⟨z, Subtype.ext hz⟩⟩

@[simp]
theorem splitTagEquiv_apply_val
    {symbol : Type*} [DecidableEq symbol]
    (left right : List symbol) (hnodup : (left ++ right).Nodup)
    (z : Sum (Fin left.length) (Fin right.length)) :
    ((splitTagEquiv left right hnodup z :
      {x : symbol // x ∈ left ++ right}) : symbol) =
        splitTagSymbol left right z := rfl

theorem rankSign_splitTag_first
    {symbol : Type*} [DecidableEq symbol]
    {left right : List symbol} (hnodup : (left ++ right).Nodup)
    (a b : Sum (Fin left.length) (Fin right.length)) :
    rankSign (fun x ↦ (left ++ right).idxOf x)
        (splitTagSymbol left right a) (splitTagSymbol left right b) =
      rankSign firstRank a b := by
  have hinj := splitTagSymbol_injective hnodup
  have ha := idxOf_splitTagSymbol_eq_firstRank hnodup a
  have hb := idxOf_splitTagSymbol_eq_firstRank hnodup b
  by_cases hab : a = b
  · subst b
    simp [rankSign]
  · have hsym : splitTagSymbol left right a ≠
        splitTagSymbol left right b := fun h ↦ hab (hinj h)
    simp only [rankSign, hab, hsym, if_false]
    have hiff :
        (left ++ right).idxOf (splitTagSymbol left right a) <
            (left ++ right).idxOf (splitTagSymbol left right b) ↔
          firstRank a < firstRank b := by
      simp [ha, hb]
    by_cases hlt :
        (left ++ right).idxOf (splitTagSymbol left right a) <
          (left ++ right).idxOf (splitTagSymbol left right b)
    · have hlt' := hiff.mp hlt
      simp [hlt, hlt']
    · have hlt' : ¬ firstRank a < firstRank b := fun h ↦
        hlt (hiff.mpr h)
      simp [hlt, hlt']

theorem rankSign_splitTag_reverse
    {symbol : Type*} [DecidableEq symbol]
    {left right : List symbol} (hnodup : (left ++ right).Nodup)
    (a b : Sum (Fin left.length) (Fin right.length)) :
    rankSign (fun x ↦ (left.reverse ++ right.reverse).idxOf x)
        (splitTagSymbol left right a) (splitTagSymbol left right b) =
      rankSign splitReverseRank a b := by
  have hinj := splitTagSymbol_injective hnodup
  have ha := idxOf_splitReverse_splitTagSymbol_eq_splitReverseRank hnodup a
  have hb := idxOf_splitReverse_splitTagSymbol_eq_splitReverseRank hnodup b
  by_cases hab : a = b
  · subst b
    simp [rankSign]
  · have hsym : splitTagSymbol left right a ≠
        splitTagSymbol left right b := fun h ↦ hab (hinj h)
    simp only [rankSign, hab, hsym, if_false]
    have hiff :
        (left.reverse ++ right.reverse).idxOf
            (splitTagSymbol left right a) <
          (left.reverse ++ right.reverse).idxOf
            (splitTagSymbol left right b) ↔
          splitReverseRank a < splitReverseRank b := by
      simp [ha, hb]
    by_cases hlt :
        (left.reverse ++ right.reverse).idxOf
            (splitTagSymbol left right a) <
          (left.reverse ++ right.reverse).idxOf
            (splitTagSymbol left right b)
    · have hlt' := hiff.mp hlt
      simp [hlt, hlt']
    · have hlt' : ¬ splitReverseRank a < splitReverseRank b := fun h ↦
        hlt (hiff.mpr h)
      simp [hlt, hlt']

/-- Exact finite relabeling of the actual split-symbol double rank score by
the paper's tagged `Q`; no inequality is used. -/
theorem sum_actual_split_rank_product_eq_taggedSplitQ
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (left right : List symbol) (hnodup : (left ++ right).Nodup) :
    (∑ a : {x : symbol // x ∈ left ++ right},
      ∑ b : {x : symbol // x ∈ left ++ right},
        rankSign (fun x ↦ (left ++ right).idxOf x) a.1 b.1 *
          rankSign (fun x ↦
            (left.reverse ++ right.reverse).idxOf x) a.1 b.1) =
      taggedSplitQ left.length right.length := by
  let e := splitTagEquiv left right hnodup
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro b _
  change
    rankSign (fun x ↦ (left ++ right).idxOf x)
        (splitTagSymbol left right a) (splitTagSymbol left right b) *
      rankSign (fun x ↦ (left.reverse ++ right.reverse).idxOf x)
        (splitTagSymbol left right a) (splitTagSymbol left right b) = _
  rw [rankSign_splitTag_first hnodup,
    rankSign_splitTag_reverse hnodup]

#print axioms splitTagEquiv
#print axioms rankSign_splitTag_first
#print axioms rankSign_splitTag_reverse
#print axioms sum_actual_split_rank_product_eq_taggedSplitQ

end FamilyStickyCinematicL32Prop41MarcusTardosSplitTagScoreCleanV1
