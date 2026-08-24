import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosPartitionOccurrenceUniqueV1
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosPartitionPairIncidenceV1

open FamilyStickyCinematicL32Prop41MarcusTardosPartitionBlockIntervalV1
open FamilyStickyCinematicL32Prop41MarcusTardosDoubleCrossCoreCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosPartitionOccurrenceUniqueV1

/-! # Double count of intersections of two literal block partitions -/

abbrev PairOccurrence
    (α : Type*) [Fintype α] [DecidableEq α]
    (blocksA blocksB : List (List α)) :=
  Σ i : Fin blocksA.length, Σ j : Fin blocksB.length,
    {a : α // a ∈ partitionBlock blocksA i ∧
      a ∈ partitionBlock blocksB j}

noncomputable def pairOccurrenceEquivFlatSupport
    {α : Type*} [Fintype α] [DecidableEq α]
    (blocksA blocksB : List (List α))
    (hA : blocksA.flatten.Nodup) (hB : blocksB.flatten.Nodup)
    (hsupport : blocksA.flatten.toFinset = blocksB.flatten.toFinset) :
    PairOccurrence α blocksA blocksB ≃
      {a : α // a ∈ blocksA.flatten.toFinset} where
  toFun x := ⟨x.2.2.1, by
    simpa using (partitionBlock_sublist_flatten blocksA x.1).subset x.2.2.2.1⟩
  invFun a := by
    have haA : a.1 ∈ blocksA.flatten := List.mem_toFinset.mp a.2
    have haBfin : a.1 ∈ blocksB.flatten.toFinset := by
      rw [← hsupport]
      exact a.2
    have haB : a.1 ∈ blocksB.flatten := List.mem_toFinset.mp haBfin
    exact ⟨partitionIndexOf hA haA, partitionIndexOf hB haB,
      ⟨a.1, mem_partitionBlock_partitionIndexOf hA haA,
        mem_partitionBlock_partitionIndexOf hB haB⟩⟩
  left_inv x := by
    rcases x with ⟨i, j, ⟨a, haAi, haBj⟩⟩
    dsimp
    have haA : a ∈ blocksA.flatten :=
      (partitionBlock_sublist_flatten blocksA i).subset haAi
    have haB : a ∈ blocksB.flatten :=
      (partitionBlock_sublist_flatten blocksB j).subset haBj
    have hi := partitionIndexOf_eq_of_mem hA haA i haAi
    have hj := partitionIndexOf_eq_of_mem hB haB j haBj
    subst i
    subst j
    rfl
  right_inv a := by
    apply Subtype.ext
    rfl

theorem card_pairOccurrence
    {α : Type*} [Fintype α] [DecidableEq α]
    (blocksA blocksB : List (List α)) :
    Fintype.card (PairOccurrence α blocksA blocksB) =
      ∑ i : Fin blocksA.length, ∑ j : Fin blocksB.length,
        ((partitionBlock blocksA i).toFinset ∩
          (partitionBlock blocksB j).toFinset).card := by
  classical
  simp only [PairOccurrence, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [Fintype.card_subtype]
  congr 1
  ext a
  simp

theorem sum_pair_intersection_card_eq_flatten_length
    {α : Type*} [Fintype α] [DecidableEq α]
    (blocksA blocksB : List (List α))
    (hA : blocksA.flatten.Nodup) (hB : blocksB.flatten.Nodup)
    (hsupport : blocksA.flatten.toFinset = blocksB.flatten.toFinset) :
    (∑ i : Fin blocksA.length, ∑ j : Fin blocksB.length,
      ((partitionBlock blocksA i).toFinset ∩
        (partitionBlock blocksB j).toFinset).card) =
      blocksA.flatten.length := by
  rw [← card_pairOccurrence]
  rw [Fintype.card_congr
    (pairOccurrenceEquivFlatSupport blocksA blocksB hA hB hsupport)]
  change Fintype.card ↥blocksA.flatten.toFinset = blocksA.flatten.length
  rw [Fintype.card_coe, List.toFinset_card_of_nodup hA]

#print axioms PairOccurrence
#print axioms pairOccurrenceEquivFlatSupport
#print axioms card_pairOccurrence
#print axioms sum_pair_intersection_card_eq_flatten_length

end FamilyStickyCinematicL32Prop41MarcusTardosPartitionPairIncidenceV1
