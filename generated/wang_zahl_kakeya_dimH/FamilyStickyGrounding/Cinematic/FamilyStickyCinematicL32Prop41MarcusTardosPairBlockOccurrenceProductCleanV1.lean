import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosPartitionOccurrenceUniqueV1
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosPairBlockOccurrenceProductCleanV1

open FamilyStickyCinematicL32Prop41MarcusTardosPartitionBlockIntervalV1
open FamilyStickyCinematicL32Prop41MarcusTardosDoubleCrossCoreCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosPartitionOccurrenceUniqueV1

/-!
# Product-indexed occurrence type for two literal list partitions

The outer index is the actual block pair, exactly as required by the
Marcus--Tardos `Q_st` sum.
-/

def PairBlockFibre
    {α : Type*} [DecidableEq α]
    (blocksA blocksB : List (List α))
    (ij : Fin blocksA.length × Fin blocksB.length) (a : α) : Prop :=
  a ∈ partitionBlock blocksA ij.1 ∧
    a ∈ partitionBlock blocksB ij.2

abbrev PairBlockOccurrence
    (α : Type*) [Fintype α] [DecidableEq α]
    (blocksA blocksB : List (List α)) :=
  Σ ij : Fin blocksA.length × Fin blocksB.length,
    {a : α // PairBlockFibre blocksA blocksB ij a}

noncomputable def pairBlockOccurrenceEquivFlatSupport
    {α : Type*} [Fintype α] [DecidableEq α]
    (blocksA blocksB : List (List α))
    (hA : blocksA.flatten.Nodup) (hB : blocksB.flatten.Nodup)
    (hsupport : blocksA.flatten.toFinset = blocksB.flatten.toFinset) :
    PairBlockOccurrence α blocksA blocksB ≃
      {a : α // a ∈ blocksA.flatten.toFinset} where
  toFun x := ⟨x.2.1, by
    exact List.mem_toFinset.mpr
      ((partitionBlock_sublist_flatten blocksA x.1.1).subset x.2.2.1)⟩
  invFun a := by
    have haA : a.1 ∈ blocksA.flatten := List.mem_toFinset.mp a.2
    have haBfin : a.1 ∈ blocksB.flatten.toFinset := by
      rw [← hsupport]
      exact a.2
    have haB : a.1 ∈ blocksB.flatten := List.mem_toFinset.mp haBfin
    exact ⟨(partitionIndexOf hA haA, partitionIndexOf hB haB),
      ⟨a.1, mem_partitionBlock_partitionIndexOf hA haA,
        mem_partitionBlock_partitionIndexOf hB haB⟩⟩
  left_inv x := by
    rcases x with ⟨⟨i, j⟩, ⟨a, haAi, haBj⟩⟩
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

@[simp]
theorem pairBlockOccurrenceEquivFlatSupport_apply_val
    {α : Type*} [Fintype α] [DecidableEq α]
    (blocksA blocksB : List (List α))
    (hA : blocksA.flatten.Nodup) (hB : blocksB.flatten.Nodup)
    (hsupport : blocksA.flatten.toFinset = blocksB.flatten.toFinset)
    (x : PairBlockOccurrence α blocksA blocksB) :
    (pairBlockOccurrenceEquivFlatSupport blocksA blocksB hA hB hsupport x).1 =
      x.2.1 := rfl

#print axioms PairBlockFibre
#print axioms PairBlockOccurrence
#print axioms pairBlockOccurrenceEquivFlatSupport

end FamilyStickyCinematicL32Prop41MarcusTardosPairBlockOccurrenceProductCleanV1
