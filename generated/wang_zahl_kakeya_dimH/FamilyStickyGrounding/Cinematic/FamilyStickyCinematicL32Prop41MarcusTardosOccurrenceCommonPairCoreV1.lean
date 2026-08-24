import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicLemmaTwoDataV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceBlockV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosOccurrenceCommonPairCoreV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlocksV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicDiagonalV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceBlockV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicCommonOrderPartitionV1
open FamilyStickyCinematicL32Prop41MarcusTardosPartitionBlockIntervalV1

/-!
# Occurrence indices in the filtered common-block partitions

Filtering literal dyadic blocks to the other cyclic support preserves their
position.  This records that reindexing explicitly, including empty blocks,
and connects a common symbol to its two actual filtered blocks.
-/

def commonIndexOfBlockIndex
    {symbol : Type*} [DecidableEq symbol]
    {depth : Nat} (A B : DistinctCyclicSequence symbol)
    (i : BlockIndex depth A.order) :
    Fin (commonBlocks depth A B).length :=
  ⟨i.1, by simpa [commonBlocks] using i.2⟩

@[simp]
theorem commonIndexOfBlockIndex_val
    {symbol : Type*} [DecidableEq symbol]
    {depth : Nat} (A B : DistinctCyclicSequence symbol)
    (i : BlockIndex depth A.order) :
    (commonIndexOfBlockIndex A B i).1 = i.1 := rfl

@[simp]
theorem partitionBlock_commonIndexOfBlockIndex
    {symbol : Type*} [DecidableEq symbol]
    {depth : Nat} (A B : DistinctCyclicSequence symbol)
    (i : BlockIndex depth A.order) :
    partitionBlock (commonBlocks depth A B)
        (commonIndexOfBlockIndex A B i) =
      (blockAt depth A.order i).filter (fun a => a ∈ B.support) := by
  simp [commonBlocks, partitionBlock, commonIndexOfBlockIndex, blockAt]

noncomputable def occurrenceCommonIndex
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (x : symbol) (hxA : x ∈ A.support) :
    Fin (commonBlocks depth A B).length :=
  commonIndexOfBlockIndex A B
    (blockIndexOf A.nodup_order ((A.mem_support_iff x).mp hxA))

@[simp]
theorem partitionBlock_occurrenceCommonIndex
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (x : symbol) (hxA : x ∈ A.support) :
    partitionBlock (commonBlocks depth A B)
        (occurrenceCommonIndex depth A B x hxA) =
      (occurrenceBlock depth A.order A.nodup_order x
        ((A.mem_support_iff x).mp hxA)).filter
          (fun a => a ∈ B.support) := by
  simp [occurrenceCommonIndex, occurrenceBlock]

theorem mem_partitionBlock_occurrenceCommonIndex
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (x : symbol) (hxA : x ∈ A.support) (hxB : x ∈ B.support) :
    x ∈ partitionBlock (commonBlocks depth A B)
      (occurrenceCommonIndex depth A B x hxA) := by
  rw [partitionBlock_occurrenceCommonIndex]
  have hxBorder : x ∈ B.order := (B.mem_support_iff x).mp hxB
  simp [mem_occurrenceBlock, hxBorder]

noncomputable def occurrenceCommonPairIndex
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (x : symbol) (hx : x ∈ A.support ∩ B.support) :
    Fin (commonBlocks depth A B).length ×
      Fin (commonBlocks depth B A).length :=
  (occurrenceCommonIndex depth A B x (Finset.mem_inter.mp hx).1,
    occurrenceCommonIndex depth B A x (Finset.mem_inter.mp hx).2)

theorem occurrenceCommonPairIndex_mem_both
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (x : symbol) (hx : x ∈ A.support ∩ B.support) :
    x ∈ partitionBlock (commonBlocks depth A B)
        (occurrenceCommonPairIndex depth A B x hx).1 ∧
      x ∈ partitionBlock (commonBlocks depth B A)
        (occurrenceCommonPairIndex depth A B x hx).2 := by
  have hxi := Finset.mem_inter.mp hx
  exact ⟨mem_partitionBlock_occurrenceCommonIndex depth A B x hxi.1 hxi.2,
    mem_partitionBlock_occurrenceCommonIndex depth B A x hxi.2 hxi.1⟩

#print axioms commonIndexOfBlockIndex
#print axioms partitionBlock_commonIndexOfBlockIndex
#print axioms occurrenceCommonIndex
#print axioms partitionBlock_occurrenceCommonIndex
#print axioms mem_partitionBlock_occurrenceCommonIndex
#print axioms occurrenceCommonPairIndex
#print axioms occurrenceCommonPairIndex_mem_both

end FamilyStickyCinematicL32Prop41MarcusTardosOccurrenceCommonPairCoreV1
