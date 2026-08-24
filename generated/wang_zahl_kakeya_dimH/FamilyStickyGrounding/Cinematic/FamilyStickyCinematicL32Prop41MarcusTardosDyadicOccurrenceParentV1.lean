import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosFlatMapBisectChildrenV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceNestedV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosOccurrenceCommonPairCoreV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceParentV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlocksV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicDiagonalV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceBlockV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceNestedV1
open FamilyStickyCinematicL32Prop41MarcusTardosFlatMapBisectChildrenV1
open FamilyStickyCinematicL32Prop41MarcusTardosOccurrenceCommonPairCoreV1

/-! # Exact parent index on an actual occurrence path -/

def leftDyadicChildIndex
    {α : Type*} (depth : Nat) (l : List α)
    (i : BlockIndex depth l) : BlockIndex (depth + 1) l := by
  change Fin ((dyadicBlocks depth l).flatMap bisect).length
  exact leftChildIndex (dyadicBlocks depth l) i

def rightDyadicChildIndex
    {α : Type*} (depth : Nat) (l : List α)
    (i : BlockIndex depth l) : BlockIndex (depth + 1) l := by
  change Fin ((dyadicBlocks depth l).flatMap bisect).length
  exact rightChildIndex (dyadicBlocks depth l) i

@[simp]
theorem leftDyadicChildIndex_val
    {α : Type*} (depth : Nat) (l : List α)
    (i : BlockIndex depth l) :
    (leftDyadicChildIndex depth l i).1 = 2 * i.1 := rfl

@[simp]
theorem rightDyadicChildIndex_val
    {α : Type*} (depth : Nat) (l : List α)
    (i : BlockIndex depth l) :
    (rightDyadicChildIndex depth l i).1 = 2 * i.1 + 1 := rfl

@[simp]
theorem blockAt_leftDyadicChildIndex
    {α : Type*} (depth : Nat) (l : List α)
    (i : BlockIndex depth l) :
    blockAt (depth + 1) l (leftDyadicChildIndex depth l i) =
      (blockAt depth l i).take (((blockAt depth l i).length + 1) / 2) := by
  exact flatMap_bisect_get_left (dyadicBlocks depth l) i

@[simp]
theorem blockAt_rightDyadicChildIndex
    {α : Type*} (depth : Nat) (l : List α)
    (i : BlockIndex depth l) :
    blockAt (depth + 1) l (rightDyadicChildIndex depth l i) =
      (blockAt depth l i).drop (((blockAt depth l i).length + 1) / 2) := by
  exact flatMap_bisect_get_right (dyadicBlocks depth l) i

theorem blockIndexOf_succ_eq_left_or_right
    {α : Type*} {depth : Nat} {l : List α} (hl : l.Nodup)
    (x : α) (hx : x ∈ l) :
    blockIndexOf (depth := depth + 1) hl hx =
        leftDyadicChildIndex depth l (blockIndexOf (depth := depth) hl hx) ∨
      blockIndexOf (depth := depth + 1) hl hx =
        rightDyadicChildIndex depth l (blockIndexOf (depth := depth) hl hx) := by
  have hchild := occurrenceBlock_succ_mem_bisect hl x hx (depth := depth)
  simp [bisect] at hchild
  rcases hchild with hleft | hright
  · left
    apply blockIndexOf_eq_of_mem hl hx
    rw [blockAt_leftDyadicChildIndex]
    change x ∈ (occurrenceBlock depth l hl x hx).take
      (((occurrenceBlock depth l hl x hx).length + 1) / 2)
    rw [← hleft]
    exact mem_occurrenceBlock (depth + 1) l hl x hx
  · right
    apply blockIndexOf_eq_of_mem hl hx
    rw [blockAt_rightDyadicChildIndex]
    change x ∈ (occurrenceBlock depth l hl x hx).drop
      (((occurrenceBlock depth l hl x hx).length + 1) / 2)
    rw [← hright]
    exact mem_occurrenceBlock (depth + 1) l hl x hx

theorem blockIndexOf_succ_div_two
    {α : Type*} {depth : Nat} {l : List α} (hl : l.Nodup)
    (x : α) (hx : x ∈ l) :
    (blockIndexOf (depth := depth + 1) hl hx).1 / 2 =
      (blockIndexOf (depth := depth) hl hx).1 := by
  rcases blockIndexOf_succ_eq_left_or_right hl x hx with h | h
  · have hv := congrArg Fin.val h
    simp only [leftDyadicChildIndex_val] at hv
    omega
  · have hv := congrArg Fin.val h
    simp only [rightDyadicChildIndex_val] at hv
    omega

theorem occurrenceCommonIndex_succ_div_two
    {symbol : Type*} [DecidableEq symbol]
    {depth : Nat} (A B : DistinctCyclicSequence symbol)
    (x : symbol) (hxA : x ∈ A.support) :
    (occurrenceCommonIndex (depth + 1) A B x hxA).1 / 2 =
      (occurrenceCommonIndex depth A B x hxA).1 := by
  exact blockIndexOf_succ_div_two A.nodup_order x
    ((A.mem_support_iff x).mp hxA)

#print axioms leftDyadicChildIndex
#print axioms rightDyadicChildIndex
#print axioms blockAt_leftDyadicChildIndex
#print axioms blockAt_rightDyadicChildIndex
#print axioms blockIndexOf_succ_eq_left_or_right
#print axioms blockIndexOf_succ_div_two
#print axioms occurrenceCommonIndex_succ_div_two

end FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceParentV1
