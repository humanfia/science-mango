import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosPairBlockOccurrenceProductCleanV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosOccurrenceCommonPairCoreV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosCommonPairIndexTransportV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceBlockV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicCommonOrderPartitionV1
open FamilyStickyCinematicL32Prop41MarcusTardosOccurrenceCommonPairCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosPartitionOccurrenceUniqueV1
open FamilyStickyCinematicL32Prop41MarcusTardosPairBlockOccurrenceProductCleanV1

/-! # Product-partition occurrence indices and actual dyadic block indices -/

theorem commonBlocks_flat_support_eq
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol) :
    (commonBlocks depth A B).flatten.toFinset =
      (commonBlocks depth B A).flatten.toFinset := by
  rw [flatten_commonBlocks, flatten_commonBlocks,
    commonOrder_toFinset, commonOrder_toFinset]
  exact Finset.inter_comm _ _

noncomputable def flatSupportPairIndex
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (x : {a : symbol //
      a ∈ (commonBlocks depth A B).flatten.toFinset}) :
    Fin (commonBlocks depth A B).length ×
      Fin (commonBlocks depth B A).length :=
  (partitionIndexOf (flatten_commonBlocks_nodup depth A B)
      (List.mem_toFinset.mp x.2),
    partitionIndexOf (flatten_commonBlocks_nodup depth B A)
      (List.mem_toFinset.mp (by
        rw [← commonBlocks_flat_support_eq depth A B]
        exact x.2)))

theorem pairBlockInverse_index_eq_flatSupportPairIndex
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (x : {a : symbol //
      a ∈ (commonBlocks depth A B).flatten.toFinset}) :
    let e := pairBlockOccurrenceEquivFlatSupport
      (commonBlocks depth A B) (commonBlocks depth B A)
      (flatten_commonBlocks_nodup depth A B)
      (flatten_commonBlocks_nodup depth B A)
      (commonBlocks_flat_support_eq depth A B)
    (e.symm x).1 = flatSupportPairIndex depth A B x := by
  rfl

theorem flatSupportPairIndex_fst_eq_occurrenceCommonIndex
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (x : {a : symbol //
      a ∈ (commonBlocks depth A B).flatten.toFinset}) :
    let hxCommon : x.1 ∈ A.commonOrder B := by
      simpa [flatten_commonBlocks] using (List.mem_toFinset.mp x.2)
    (flatSupportPairIndex depth A B x).1 =
      occurrenceCommonIndex depth A B x.1
        ((A.mem_commonOrder_iff B x.1).mp hxCommon).1 := by
  classical
  dsimp only
  let hxCommon : x.1 ∈ A.commonOrder B := by
    simpa [flatten_commonBlocks] using (List.mem_toFinset.mp x.2)
  let hx := (A.mem_commonOrder_iff B x.1).mp hxCommon
  have hidx := partitionIndexOf_eq_of_mem
    (flatten_commonBlocks_nodup depth A B)
    (List.mem_toFinset.mp x.2)
    (occurrenceCommonIndex depth A B x.1 hx.1)
    (mem_partitionBlock_occurrenceCommonIndex depth A B x.1 hx.1 hx.2)
  exact hidx

theorem flatSupportPairIndex_snd_eq_occurrenceCommonIndex
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (x : {a : symbol //
      a ∈ (commonBlocks depth A B).flatten.toFinset}) :
    let hxCommon : x.1 ∈ A.commonOrder B := by
      simpa [flatten_commonBlocks] using (List.mem_toFinset.mp x.2)
    (flatSupportPairIndex depth A B x).2 =
      occurrenceCommonIndex depth B A x.1
        ((A.mem_commonOrder_iff B x.1).mp hxCommon).2 := by
  classical
  dsimp only
  let hxCommon : x.1 ∈ A.commonOrder B := by
    simpa [flatten_commonBlocks] using (List.mem_toFinset.mp x.2)
  let hx := (A.mem_commonOrder_iff B x.1).mp hxCommon
  let hxBflat : x.1 ∈ (commonBlocks depth B A).flatten := by
    rw [flatten_commonBlocks]
    exact (B.mem_commonOrder_iff A x.1).mpr ⟨hx.2, hx.1⟩
  have hidx := partitionIndexOf_eq_of_mem
    (flatten_commonBlocks_nodup depth B A) hxBflat
    (occurrenceCommonIndex depth B A x.1 hx.2)
    (mem_partitionBlock_occurrenceCommonIndex depth B A x.1 hx.2 hx.1)
  exact hidx

theorem occurrenceCommonIndex_eq_iff_blockIndexOf_eq
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    {x y : symbol} (hx : x ∈ A.support) (hy : y ∈ A.support) :
    occurrenceCommonIndex depth A B x hx =
        occurrenceCommonIndex depth A B y hy ↔
      blockIndexOf (depth := depth) A.nodup_order
          ((A.mem_support_iff x).mp hx) =
        blockIndexOf (depth := depth) A.nodup_order
          ((A.mem_support_iff y).mp hy) := by
  unfold occurrenceCommonIndex commonIndexOfBlockIndex
  constructor
  · intro h
    apply Fin.ext
    exact congrArg
      (fun z : Fin (commonBlocks depth A B).length => z.1) h
  · intro h
    exact congrArg (commonIndexOfBlockIndex A B) h

#print axioms commonBlocks_flat_support_eq
#print axioms flatSupportPairIndex
#print axioms pairBlockInverse_index_eq_flatSupportPairIndex
#print axioms flatSupportPairIndex_fst_eq_occurrenceCommonIndex
#print axioms flatSupportPairIndex_snd_eq_occurrenceCommonIndex
#print axioms occurrenceCommonIndex_eq_iff_blockIndexOf_eq

end FamilyStickyCinematicL32Prop41MarcusTardosCommonPairIndexTransportV1
