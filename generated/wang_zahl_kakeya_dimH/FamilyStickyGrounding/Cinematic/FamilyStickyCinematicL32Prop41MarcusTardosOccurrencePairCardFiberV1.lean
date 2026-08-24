import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualFirstRegularLeaderV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicPairLengthTotalV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosOccurrencePairCardFiberV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosActualFirstRegularLeaderV1
open FamilyStickyCinematicL32Prop41MarcusTardosCommonPairParentV1
open FamilyStickyCinematicL32Prop41MarcusTardosOccurrenceCommonPairCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicCommonOrderPartitionV1
open FamilyStickyCinematicL32Prop41MarcusTardosPartitionBlockIntervalV1
open FamilyStickyCinematicL32Prop41MarcusTardosPartitionOccurrenceUniqueV1
open FamilyStickyCinematicL32Prop41MarcusTardosDoubleCrossCoreCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicLemmaTwoDataV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicPairLengthTotalV1

/-! # Common-symbol fibres of an actual dyadic block pair -/

def pairSymbolFinset
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (ij : CommonPairIndex depth A B) : Finset symbol :=
  (partitionBlock (commonBlocks depth A B) ij.1).toFinset ∩
    (partitionBlock (commonBlocks depth B A) ij.2).toFinset

theorem occurrenceCommonPairIndex_eq_of_mem_both
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (x : symbol) (hx : x ∈ A.support ∩ B.support)
    (ij : CommonPairIndex depth A B)
    (hxA : x ∈ partitionBlock (commonBlocks depth A B) ij.1)
    (hxB : x ∈ partitionBlock (commonBlocks depth B A) ij.2) :
    occurrenceCommonPairIndex depth A B x hx = ij := by
  have hxAflat : x ∈ (commonBlocks depth A B).flatten := by
    exact (partitionBlock_sublist_flatten _ _).subset hxA
  have hxBflat : x ∈ (commonBlocks depth B A).flatten := by
    exact (partitionBlock_sublist_flatten _ _).subset hxB
  have hmem := occurrenceCommonPairIndex_mem_both depth A B x hx
  apply Prod.ext
  · have hocc := partitionIndexOf_eq_of_mem
      (flatten_commonBlocks_nodup depth A B) hxAflat
      (occurrenceCommonPairIndex depth A B x hx).1 hmem.1
    have hij := partitionIndexOf_eq_of_mem
      (flatten_commonBlocks_nodup depth A B) hxAflat ij.1 hxA
    exact hocc.symm.trans hij
  · have hocc := partitionIndexOf_eq_of_mem
      (flatten_commonBlocks_nodup depth B A) hxBflat
      (occurrenceCommonPairIndex depth A B x hx).2 hmem.2
    have hij := partitionIndexOf_eq_of_mem
      (flatten_commonBlocks_nodup depth B A) hxBflat ij.2 hxB
    exact hocc.symm.trans hij

noncomputable def occurrencePairFiber
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (ij : CommonPairIndex depth A B) : Finset (CommonSymbol A B) := by
  classical
  exact Finset.univ.filter fun x =>
    occurrenceCommonPairIndex depth A B x.1 x.2 = ij

theorem occurrencePairFiber_image_val
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (ij : CommonPairIndex depth A B) :
    (occurrencePairFiber depth A B ij).image (fun x => x.1) =
      pairSymbolFinset depth A B ij := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hindex := (Finset.mem_filter.mp hy).2
    have hmem := occurrenceCommonPairIndex_mem_both depth A B y.1 y.2
    rw [hindex] at hmem
    simpa [pairSymbolFinset] using hmem
  · intro hx
    have hparts :
        x ∈ partitionBlock (commonBlocks depth A B) ij.1 ∧
          x ∈ partitionBlock (commonBlocks depth B A) ij.2 := by
      simpa [pairSymbolFinset] using hx
    have hxAflat : x ∈ (commonBlocks depth A B).flatten :=
      (partitionBlock_sublist_flatten _ _).subset hparts.1
    have hxCommonOrder : x ∈ A.commonOrder B := by
      simpa [flatten_commonBlocks] using hxAflat
    have hxcommon : x ∈ A.support ∩ B.support :=
      Finset.mem_inter.mpr ((A.mem_commonOrder_iff B x).mp hxCommonOrder)
    let y : CommonSymbol A B := ⟨x, hxcommon⟩
    apply Finset.mem_image.mpr
    refine ⟨y, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact occurrenceCommonPairIndex_eq_of_mem_both
      depth A B x hxcommon ij hparts.1 hparts.2

theorem occurrencePairFiber_card_eq_dyadicPairLength
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (ij : CommonPairIndex depth A B) :
    (occurrencePairFiber depth A B ij).card =
      dyadicPairLength depth A B ij := by
  rw [dyadicPairLength_eq_intersection_card]
  change (occurrencePairFiber depth A B ij).card =
    (pairSymbolFinset depth A B ij).card
  calc
    (occurrencePairFiber depth A B ij).card =
        ((occurrencePairFiber depth A B ij).image (fun x => x.1)).card := by
      symm
      exact Finset.card_image_of_injective _ Subtype.val_injective
    _ = (pairSymbolFinset depth A B ij).card := by
      rw [occurrencePairFiber_image_val]

#print axioms pairSymbolFinset
#print axioms occurrenceCommonPairIndex_eq_of_mem_both
#print axioms occurrencePairFiber
#print axioms occurrencePairFiber_image_val
#print axioms occurrencePairFiber_card_eq_dyadicPairLength

end FamilyStickyCinematicL32Prop41MarcusTardosOccurrencePairCardFiberV1
