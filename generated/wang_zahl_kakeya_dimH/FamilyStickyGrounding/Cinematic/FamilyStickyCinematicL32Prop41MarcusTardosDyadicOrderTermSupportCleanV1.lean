import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicActualPairTermV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosDyadicOrderTermSupportCleanV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceBlockV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicWithinBlockPairCountV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicActualPairTermV1
open FamilyStickyCinematicL32Prop41MarcusTardosTaggedSplitOrderSignV1

/-! # Support and unique-block characterization of the actual dyadic term -/

theorem sameDyadicOrderedPair_iff_blockIndexOf_eq
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A : DistinctCyclicSequence symbol)
    {a b : symbol} (ha : a ∈ A.support) (hb : b ∈ A.support) :
    SameDyadicOrderedPair depth A.order (a, b) ↔
      a ≠ b ∧
        blockIndexOf (depth := depth) A.nodup_order
            ((A.mem_support_iff a).mp ha) =
          blockIndexOf (depth := depth) A.nodup_order
            ((A.mem_support_iff b).mp hb) := by
  constructor
  · rintro ⟨hab, i, hai, hbi⟩
    have hia := blockIndexOf_eq_of_mem A.nodup_order
      ((A.mem_support_iff a).mp ha) i hai
    have hib := blockIndexOf_eq_of_mem A.nodup_order
      ((A.mem_support_iff b).mp hb) i hbi
    exact ⟨hab, hia.trans hib.symm⟩
  · rintro ⟨hab, hidx⟩
    refine ⟨hab,
      blockIndexOf (depth := depth) A.nodup_order
        ((A.mem_support_iff a).mp ha),
      mem_blockAt_blockIndexOf A.nodup_order
        ((A.mem_support_iff a).mp ha), ?_⟩
    rw [hidx]
    exact mem_blockAt_blockIndexOf A.nodup_order
      ((A.mem_support_iff b).mp hb)

theorem dyadicOrderTerm_eq_if_blockIndexOf_eq
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (A : DistinctCyclicSequence symbol)
    {a b : symbol} (ha : a ∈ A.support) (hb : b ∈ A.support) :
    dyadicOrderTerm depth A (a, b) =
      if a ≠ b ∧
          blockIndexOf (depth := depth) A.nodup_order
              ((A.mem_support_iff a).mp ha) =
            blockIndexOf (depth := depth) A.nodup_order
              ((A.mem_support_iff b).mp hb)
      then rankSign (fun x ↦ A.order.idxOf x) a b else 0 := by
  classical
  unfold dyadicOrderTerm
  have hmem : ((a, b) ∈ sameDyadicOrderedPairs depth A.order) ↔
      a ≠ b ∧
        blockIndexOf (depth := depth) A.nodup_order
            ((A.mem_support_iff a).mp ha) =
          blockIndexOf (depth := depth) A.nodup_order
            ((A.mem_support_iff b).mp hb) := by
    simpa [sameDyadicOrderedPairs] using
      (sameDyadicOrderedPair_iff_blockIndexOf_eq depth A ha hb)
  by_cases h : a ≠ b ∧
      blockIndexOf (depth := depth) A.nodup_order
          ((A.mem_support_iff a).mp ha) =
        blockIndexOf (depth := depth) A.nodup_order
          ((A.mem_support_iff b).mp hb)
  · simp [h, hmem.mpr h]
  · have hnmem : (a, b) ∉ sameDyadicOrderedPairs depth A.order :=
      fun hm => h (hmem.mp hm)
    simp [h, hnmem]

theorem dyadicOrderTerm_eq_zero_of_first_not_mem
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (A : DistinctCyclicSequence symbol)
    (a b : symbol) (ha : a ∉ A.support) :
    dyadicOrderTerm depth A (a, b) = 0 := by
  classical
  unfold dyadicOrderTerm
  by_cases hp : (a, b) ∈ sameDyadicOrderedPairs depth A.order
  · have hsame : SameDyadicOrderedPair depth A.order (a, b) := by
      simpa [sameDyadicOrderedPairs] using hp
    have haOrder := mem_order_of_mem_blockAt hsame.2.choose_spec.1
    exact (ha ((A.mem_support_iff a).mpr haOrder)).elim
  · simp [hp]

theorem dyadicOrderTerm_eq_zero_of_second_not_mem
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (A : DistinctCyclicSequence symbol)
    (a b : symbol) (hb : b ∉ A.support) :
    dyadicOrderTerm depth A (a, b) = 0 := by
  classical
  unfold dyadicOrderTerm
  by_cases hp : (a, b) ∈ sameDyadicOrderedPairs depth A.order
  · have hsame : SameDyadicOrderedPair depth A.order (a, b) := by
      simpa [sameDyadicOrderedPairs] using hp
    have hbOrder := mem_order_of_mem_blockAt hsame.2.choose_spec.2
    exact (hb ((A.mem_support_iff b).mpr hbOrder)).elim
  · simp [hp]

theorem dyadicTerm_product_zero_of_first_not_common
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (a : symbol) (ha : a ∉ A.support ∩ B.support) (b : symbol) :
    dyadicOrderTerm depth A (a, b) * dyadicOrderTerm depth B (a, b) = 0 := by
  by_cases haA : a ∈ A.support
  · have haB : a ∉ B.support := by
      intro h
      exact ha (Finset.mem_inter.mpr ⟨haA, h⟩)
    rw [dyadicOrderTerm_eq_zero_of_first_not_mem depth B a b haB]
    ring
  · rw [dyadicOrderTerm_eq_zero_of_first_not_mem depth A a b haA]
    ring

theorem dyadicTerm_product_zero_of_second_not_common
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (a b : symbol) (hb : b ∉ A.support ∩ B.support) :
    dyadicOrderTerm depth A (a, b) * dyadicOrderTerm depth B (a, b) = 0 := by
  by_cases hbA : b ∈ A.support
  · have hbB : b ∉ B.support := by
      intro h
      exact hb (Finset.mem_inter.mpr ⟨hbA, h⟩)
    rw [dyadicOrderTerm_eq_zero_of_second_not_mem depth B a b hbB]
    ring
  · rw [dyadicOrderTerm_eq_zero_of_second_not_mem depth A a b hbA]
    ring

#print axioms sameDyadicOrderedPair_iff_blockIndexOf_eq
#print axioms dyadicOrderTerm_eq_if_blockIndexOf_eq
#print axioms dyadicOrderTerm_eq_zero_of_first_not_mem
#print axioms dyadicOrderTerm_eq_zero_of_second_not_mem
#print axioms dyadicTerm_product_zero_of_first_not_common
#print axioms dyadicTerm_product_zero_of_second_not_common

end FamilyStickyCinematicL32Prop41MarcusTardosDyadicOrderTermSupportCleanV1
