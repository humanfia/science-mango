import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosOneSideRegularV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosPartitionBlockIntervalV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosDoubleCrossCoreCleanV1

open List
open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1
open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1.DistinctLinearSequence
open FamilyStickyCinematicL32Prop41MarcusTardosLinearSublistReverseV1
open FamilyStickyCinematicL32Prop41MarcusTardosOneSideRegularV1
open FamilyStickyCinematicL32Prop41MarcusTardosPartitionCutUniqueV1
open FamilyStickyCinematicL32Prop41MarcusTardosPartitionBlockIntervalV1

/-!
# Singular block pairs cross both linear cuts

This is the mechanical part of Marcus--Tardos Lemma 2.  The two common
cyclic orders have the cut normal form `u ++ v` and
`u.reverse ++ v.reverse`.  A block pair which is not linearly intersection
reverse must cross the unique cut in both block partitions.
-/

theorem partitionBlock_sublist_flatten
    {α : Type*} (blocks : List (List α)) (i : Fin blocks.length) :
    partitionBlock blocks i <+ blocks.flatten := by
  rw [flatten_eq_prefix_append_block_append_suffix]
  exact (List.sublist_append_right _ _).trans
    (List.sublist_append_left _ _)

theorem intersectionReverse_comm
    {α : Type*} [DecidableEq α]
    {A B : DistinctLinearSequence α}
    (h : A.IntersectionReverse B) :
    B.IntersectionReverse A := by
  rw [IntersectionReverse] at h ⊢
  simpa using (congrArg List.reverse h).symm

def SingularPair
    {α : Type*} [DecidableEq α]
    (blocksA blocksB : List (List α))
    (hA : blocksA.flatten.Nodup) (hB : blocksB.flatten.Nodup)
    (ij : Fin blocksA.length × Fin blocksB.length) : Prop :=
  ¬(linearOfList (partitionBlock blocksA ij.1)
      (hA.sublist (partitionBlock_sublist_flatten blocksA ij.1))).IntersectionReverse
    (linearOfList (partitionBlock blocksB ij.2)
      (hB.sublist (partitionBlock_sublist_flatten blocksB ij.2)))

theorem singularPair_crosses_left
    {α : Type*} [DecidableEq α]
    {blocksA blocksB : List (List α)} {u v : List α}
    (hflatA : blocksA.flatten = u ++ v)
    (hflatB : blocksB.flatten = u.reverse ++ v.reverse)
    (hA : blocksA.flatten.Nodup) (hB : blocksB.flatten.Nodup)
    (ij : Fin blocksA.length × Fin blocksB.length)
    (hsingular : SingularPair blocksA blocksB hA hB ij) :
    CrossesCut blocksA u.length ij.1 := by
  by_contra hnot
  have huv : (u ++ v).Nodup := by simpa [← hflatA] using hA
  have hCnodup := hA.sublist
    (partitionBlock_sublist_flatten blocksA ij.1)
  have hDnodup := hB.sublist
    (partitionBlock_sublist_flatten blocksB ij.2)
  have hD : partitionBlock blocksB ij.2 <+
      u.reverse ++ v.reverse := by
    rw [← hflatB]
    exact partitionBlock_sublist_flatten blocksB ij.2
  rcases partitionBlock_sublist_left_or_right_of_not_crossesSplit
      blocksA u v hflatA ij.1 hnot with hC | hC
  · exact hsingular <|
      intersectionReverse_of_left_sublist_left_split
        huv hCnodup hDnodup hC hD
  · exact hsingular <|
      intersectionReverse_of_left_sublist_right_split
        huv hCnodup hDnodup hC hD

theorem singularPair_crosses_right
    {α : Type*} [DecidableEq α]
    {blocksA blocksB : List (List α)} {u v : List α}
    (hflatA : blocksA.flatten = u ++ v)
    (hflatB : blocksB.flatten = u.reverse ++ v.reverse)
    (hA : blocksA.flatten.Nodup) (hB : blocksB.flatten.Nodup)
    (ij : Fin blocksA.length × Fin blocksB.length)
    (hsingular : SingularPair blocksA blocksB hA hB ij) :
    CrossesCut blocksB u.length ij.2 := by
  by_contra hnot
  have hnot' : ¬CrossesCut blocksB u.reverse.length ij.2 := by
    simpa using hnot
  have hrev : (u.reverse ++ v.reverse).Nodup := by
    simpa [← hflatB] using hB
  have hCnodup := hB.sublist
    (partitionBlock_sublist_flatten blocksB ij.2)
  have hDnodup := hA.sublist
    (partitionBlock_sublist_flatten blocksA ij.1)
  have hD : partitionBlock blocksA ij.1 <+
      u.reverse.reverse ++ v.reverse.reverse := by
    simpa using (show partitionBlock blocksA ij.1 <+ u ++ v by
      rw [← hflatA]
      exact partitionBlock_sublist_flatten blocksA ij.1)
  rcases partitionBlock_sublist_left_or_right_of_not_crossesSplit
      blocksB u.reverse v.reverse hflatB ij.2 hnot' with hC | hC
  · exact hsingular <| intersectionReverse_comm <|
      intersectionReverse_of_left_sublist_left_split
        hrev hCnodup hDnodup hC hD
  · exact hsingular <| intersectionReverse_comm <|
      intersectionReverse_of_left_sublist_right_split
        hrev hCnodup hDnodup hC hD

#print axioms partitionBlock_sublist_flatten
#print axioms intersectionReverse_comm
#print axioms SingularPair
#print axioms singularPair_crosses_left
#print axioms singularPair_crosses_right

end FamilyStickyCinematicL32Prop41MarcusTardosDoubleCrossCoreCleanV1
