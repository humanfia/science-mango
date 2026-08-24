import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceBlockV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceNestedV1

open List
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlocksV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicDiagonalV1
open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceBlockV1

/-!
# Nested occurrence blocks

The unique block containing a fixed symbol at level `depth + 1` is one of the
two literal halves of its unique level-`depth` parent.  We also record the
exact restriction identity needed to invoke hereditary intersection reversal.
-/

theorem mem_parent_of_mem_child_of_mem_bisect
    {α : Type*} {x : α} {parent child : List α}
    (hx : x ∈ child) (hchild : child ∈ bisect parent) :
    x ∈ parent := by
  simp [bisect] at hchild
  rcases hchild with rfl | rfl
  · exact List.mem_of_mem_take hx
  · exact List.mem_of_mem_drop hx

theorem sublist_of_mem_bisect
    {α : Type*} {parent child : List α}
    (hchild : child ∈ bisect parent) :
    child <+ parent := by
  simp [bisect] at hchild
  rcases hchild with rfl | rfl
  · exact List.take_sublist _ _
  · exact List.drop_sublist _ _

theorem filter_toFinset_eq_of_sublist_of_nodup
    {α : Type*} [DecidableEq α] {child parent : List α}
    (hsub : child <+ parent) (hparent : parent.Nodup) :
    parent.filter (fun a => a ∈ child.toFinset) = child := by
  induction hsub with
  | slnil => simp
  | cons a hsub ih =>
      rw [List.nodup_cons] at hparent
      have ha : a ∉ _ := fun ha => hparent.1 (hsub.subset ha)
      rw [List.filter_cons_of_neg (by simpa using ha)]
      simpa only [List.mem_toFinset] using ih hparent.2
  | cons_cons a hsub ih =>
      rw [List.nodup_cons] at hparent
      rw [List.filter_cons_of_pos (by simp)]
      congr 1
      have hih := ih hparent.2
      simp only [List.mem_toFinset] at hih
      rw [← hih]
      apply List.filter_congr
      intro b hb
      have hba : b ≠ a := fun hba => hparent.1 (hba ▸ hb)
      simp [hba]
      intro hb1
      exact hsub.subset hb1

theorem distinctLinearSequence_ext_order
    {α : Type*} {A B : DistinctLinearSequence α}
    (horder : A.order = B.order) : A = B := by
  cases A with
  | mk Aorder Anodup =>
      cases B with
      | mk Border Bnodup =>
          simp only at horder
          subst Border
          rfl

theorem occurrenceBlock_succ_mem_bisect
    {α : Type*} {depth : Nat} {l : List α} (hl : l.Nodup)
    (x : α) (hx : x ∈ l) :
    occurrenceBlock (depth + 1) l hl x hx ∈
      bisect (occurrenceBlock depth l hl x hx) := by
  have hchildLevel : occurrenceBlock (depth + 1) l hl x hx ∈
      dyadicBlocks (depth + 1) l := blockAt_mem _ _ _
  obtain ⟨parent, hparentLevel, hchildParent⟩ :=
    mem_dyadicBlocks_succ_iff.mp hchildLevel
  have hxparent : x ∈ parent :=
    mem_parent_of_mem_child_of_mem_bisect
      (mem_occurrenceBlock (depth + 1) l hl x hx) hchildParent
  obtain ⟨n, hn, hget⟩ := List.getElem_of_mem hparentLevel
  let i : BlockIndex depth l := ⟨n, hn⟩
  have hi : x ∈ blockAt depth l i := by
    simpa [blockAt, i, hget] using hxparent
  have hidx : blockIndexOf hl hx = i :=
    blockIndexOf_eq_of_mem hl hx i hi
  have hparentEq : occurrenceBlock depth l hl x hx = parent := by
    simp only [occurrenceBlock]
    rw [hidx]
    simpa [blockAt, i] using hget
  simpa [hparentEq] using hchildParent

theorem occurrenceBlock_succ_sublist
    {α : Type*} {depth : Nat} {l : List α} (hl : l.Nodup)
    (x : α) (hx : x ∈ l) :
    occurrenceBlock (depth + 1) l hl x hx <+
      occurrenceBlock depth l hl x hx :=
  sublist_of_mem_bisect (occurrenceBlock_succ_mem_bisect hl x hx)

theorem occurrenceLinearBlock_succ_eq_restrict
    {α : Type*} [DecidableEq α] {depth : Nat} {l : List α}
    (hl : l.Nodup) (x : α) (hx : x ∈ l) :
    occurrenceLinearBlock (depth + 1) l hl x hx =
      (occurrenceLinearBlock depth l hl x hx).restrict
        (occurrenceBlock (depth + 1) l hl x hx).toFinset := by
  have horder : occurrenceBlock (depth + 1) l hl x hx =
      (occurrenceBlock depth l hl x hx).filter
        (fun a => a ∈ (occurrenceBlock (depth + 1) l hl x hx).toFinset) :=
    (filter_toFinset_eq_of_sublist_of_nodup
      (occurrenceBlock_succ_sublist hl x hx)
      (occurrenceBlock_nodup depth l hl x hx)).symm
  apply distinctLinearSequence_ext_order
  exact horder

#print axioms mem_parent_of_mem_child_of_mem_bisect
#print axioms sublist_of_mem_bisect
#print axioms filter_toFinset_eq_of_sublist_of_nodup
#print axioms distinctLinearSequence_ext_order
#print axioms occurrenceBlock_succ_mem_bisect
#print axioms occurrenceBlock_succ_sublist
#print axioms occurrenceLinearBlock_succ_eq_restrict

end FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceNestedV1
