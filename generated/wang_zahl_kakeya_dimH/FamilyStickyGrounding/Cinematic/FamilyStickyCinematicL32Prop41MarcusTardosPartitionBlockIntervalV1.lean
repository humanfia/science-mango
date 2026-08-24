import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosPartitionCutUniqueV1
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosPartitionBlockIntervalV1

open List
open FamilyStickyCinematicL32Prop41MarcusTardosPartitionCutUniqueV1

/-! # Literal interval occupied by a position-indexed block -/

def partitionBlock {α : Type*} (blocks : List (List α))
    (i : Fin blocks.length) : List α :=
  blocks.get i

theorem flatten_eq_prefix_append_block_append_suffix
    {α : Type*} (blocks : List (List α)) (i : Fin blocks.length) :
    blocks.flatten =
      (blocks.take i.1).flatten ++ partitionBlock blocks i ++
        (blocks.drop (i.1 + 1)).flatten := by
  conv_lhs => rw [← List.take_append_drop i.1 blocks]
  rw [List.flatten_append]
  rw [List.drop_eq_getElem_cons i.2, List.flatten_cons]
  simp [partitionBlock, List.append_assoc]

theorem prefixLength_succ
    {α : Type*} (blocks : List (List α)) (i : Fin blocks.length) :
    prefixLength blocks (i.1 + 1) =
      prefixLength blocks i.1 + (partitionBlock blocks i).length := by
  unfold prefixLength partitionBlock
  rw [← List.take_concat_get' blocks i.1 i.2]
  simp

theorem prefix_append_block_eq_take
    {α : Type*} (blocks : List (List α)) (i : Fin blocks.length) :
    (blocks.take i.1).flatten ++ partitionBlock blocks i =
      blocks.flatten.take (prefixLength blocks (i.1 + 1)) := by
  have hprefix :
      (blocks.take i.1).flatten ++ partitionBlock blocks i <+:
        blocks.flatten := by
    refine ⟨(blocks.drop (i.1 + 1)).flatten, ?_⟩
    exact (flatten_eq_prefix_append_block_append_suffix blocks i).symm
  rw [List.prefix_iff_eq_take] at hprefix
  calc
    (blocks.take i.1).flatten ++ partitionBlock blocks i =
        blocks.flatten.take
          (((blocks.take i.1).flatten ++ partitionBlock blocks i).length) :=
      hprefix
    _ = blocks.flatten.take (prefixLength blocks (i.1 + 1)) := by
      congr 1
      rw [prefixLength_succ]
      simp [prefixLength]

theorem partitionBlock_sublist_take_of_end_le
    {α : Type*} (blocks : List (List α)) (cut : Nat)
    (i : Fin blocks.length)
    (hend : prefixLength blocks (i.1 + 1) ≤ cut) :
    partitionBlock blocks i <+ blocks.flatten.take cut := by
  have hblock : partitionBlock blocks i <+
      (blocks.take i.1).flatten ++ partitionBlock blocks i :=
    List.sublist_append_right _ _
  rw [prefix_append_block_eq_take] at hblock
  exact hblock.trans <|
    ((List.take_isPrefix_take (l := blocks.flatten)).2
      (Or.inl hend)).sublist

theorem block_append_suffix_eq_drop
    {α : Type*} (blocks : List (List α)) (i : Fin blocks.length) :
    partitionBlock blocks i ++ (blocks.drop (i.1 + 1)).flatten =
      blocks.flatten.drop (prefixLength blocks i.1) := by
  rw [flatten_eq_prefix_append_block_append_suffix blocks i]
  simp [prefixLength, List.append_assoc]

theorem partitionBlock_sublist_drop_of_cut_le_start
    {α : Type*} (blocks : List (List α)) (cut : Nat)
    (i : Fin blocks.length)
    (hstart : cut ≤ prefixLength blocks i.1) :
    partitionBlock blocks i <+ blocks.flatten.drop cut := by
  have hblock : partitionBlock blocks i <+
      partitionBlock blocks i ++ (blocks.drop (i.1 + 1)).flatten :=
    List.sublist_append_left _ _
  rw [block_append_suffix_eq_drop] at hblock
  have hdrop : blocks.flatten.drop (prefixLength blocks i.1) =
      (blocks.flatten.drop cut).drop
        (prefixLength blocks i.1 - cut) := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [hdrop] at hblock
  exact hblock.trans (List.drop_sublist _ _)

theorem not_crossesCut_side
    {α : Type*} (blocks : List (List α)) (cut : Nat)
    (i : Fin blocks.length)
    (hnot : ¬CrossesCut blocks cut i) :
    prefixLength blocks (i.1 + 1) ≤ cut ∨
      cut ≤ prefixLength blocks i.1 := by
  simp only [CrossesCut] at hnot
  rw [prefixLength_succ] at hnot ⊢
  omega

theorem partitionBlock_sublist_left_or_right_of_not_crossesSplit
    {α : Type*} (blocks : List (List α)) (u v : List α)
    (hflat : blocks.flatten = u ++ v) (i : Fin blocks.length)
    (hnot : ¬CrossesCut blocks u.length i) :
    partitionBlock blocks i <+ u ∨ partitionBlock blocks i <+ v := by
  rcases not_crossesCut_side blocks u.length i hnot with hend | hstart
  · left
    have hsub := partitionBlock_sublist_take_of_end_le
      blocks u.length i hend
    rw [hflat] at hsub
    simpa using hsub
  · right
    have hsub := partitionBlock_sublist_drop_of_cut_le_start
      blocks u.length i hstart
    rw [hflat] at hsub
    simpa using hsub


#print axioms partitionBlock
#print axioms flatten_eq_prefix_append_block_append_suffix
#print axioms prefixLength_succ
#print axioms prefix_append_block_eq_take
#print axioms partitionBlock_sublist_take_of_end_le
#print axioms block_append_suffix_eq_drop
#print axioms partitionBlock_sublist_drop_of_cut_le_start
#print axioms partitionBlock_sublist_left_or_right_of_not_crossesSplit
#print axioms not_crossesCut_side

end FamilyStickyCinematicL32Prop41MarcusTardosPartitionBlockIntervalV1
