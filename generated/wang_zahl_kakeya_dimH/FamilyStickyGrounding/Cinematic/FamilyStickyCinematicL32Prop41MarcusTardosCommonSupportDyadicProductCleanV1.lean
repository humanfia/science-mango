import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosCommonPairIndexTransportV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicOrderTermSupportCleanV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosCommonSupportDyadicProductCleanV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceBlockV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicCommonOrderPartitionV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicActualPairTermV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicOrderTermSupportCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosOccurrenceCommonPairCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosPairBlockOccurrenceProductCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosCommonPairIndexTransportV1
open FamilyStickyCinematicL32Prop41MarcusTardosTaggedSplitOrderSignV1

/-! # Product of two actual dyadic terms on the common support -/

theorem dyadicTerm_product_eq_samePairIndex_rankProduct
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (a b : {x : symbol //
      x ∈ (commonBlocks depth A B).flatten.toFinset}) :
    let e := pairBlockOccurrenceEquivFlatSupport
      (commonBlocks depth A B) (commonBlocks depth B A)
      (flatten_commonBlocks_nodup depth A B)
      (flatten_commonBlocks_nodup depth B A)
      (commonBlocks_flat_support_eq depth A B)
    dyadicOrderTerm depth A (a.1, b.1) *
        dyadicOrderTerm depth B (a.1, b.1) =
      if (e.symm a).1 = (e.symm b).1 then
        rankSign (fun x ↦ A.order.idxOf x) a.1 b.1 *
          rankSign (fun x ↦ B.order.idxOf x) a.1 b.1
      else 0 := by
  classical
  dsimp only
  let haCommon : a.1 ∈ A.commonOrder B := by
    simpa [flatten_commonBlocks] using (List.mem_toFinset.mp a.2)
  let hbCommon : b.1 ∈ A.commonOrder B := by
    simpa [flatten_commonBlocks] using (List.mem_toFinset.mp b.2)
  let ha := (A.mem_commonOrder_iff B a.1).mp haCommon
  let hb := (A.mem_commonOrder_iff B b.1).mp hbCommon
  let e := pairBlockOccurrenceEquivFlatSupport
    (commonBlocks depth A B) (commonBlocks depth B A)
    (flatten_commonBlocks_nodup depth A B)
    (flatten_commonBlocks_nodup depth B A)
    (commonBlocks_flat_support_eq depth A B)
  change dyadicOrderTerm depth A (a.1, b.1) *
      dyadicOrderTerm depth B (a.1, b.1) =
    if (e.symm a).1 = (e.symm b).1 then
      rankSign (fun x ↦ A.order.idxOf x) a.1 b.1 *
        rankSign (fun x ↦ B.order.idxOf x) a.1 b.1
    else 0
  have hpair : (e.symm a).1 = (e.symm b).1 ↔
      (blockIndexOf (depth := depth) A.nodup_order
            ((A.mem_support_iff a.1).mp ha.1) =
          blockIndexOf (depth := depth) A.nodup_order
            ((A.mem_support_iff b.1).mp hb.1)) ∧
        (blockIndexOf (depth := depth) B.nodup_order
            ((B.mem_support_iff a.1).mp ha.2) =
          blockIndexOf (depth := depth) B.nodup_order
            ((B.mem_support_iff b.1).mp hb.2)) := by
    rw [pairBlockInverse_index_eq_flatSupportPairIndex depth A B a,
      pairBlockInverse_index_eq_flatSupportPairIndex depth A B b]
    constructor
    · intro h
      have hfst := congrArg Prod.fst h
      have hsnd := congrArg Prod.snd h
      rw [flatSupportPairIndex_fst_eq_occurrenceCommonIndex depth A B a,
        flatSupportPairIndex_fst_eq_occurrenceCommonIndex depth A B b] at hfst
      rw [flatSupportPairIndex_snd_eq_occurrenceCommonIndex depth A B a,
        flatSupportPairIndex_snd_eq_occurrenceCommonIndex depth A B b] at hsnd
      exact ⟨
        (occurrenceCommonIndex_eq_iff_blockIndexOf_eq
          depth A B ha.1 hb.1).mp hfst,
        (occurrenceCommonIndex_eq_iff_blockIndexOf_eq
          depth B A ha.2 hb.2).mp hsnd⟩
    · rintro ⟨hfst, hsnd⟩
      apply Prod.ext
      · rw [flatSupportPairIndex_fst_eq_occurrenceCommonIndex depth A B a,
          flatSupportPairIndex_fst_eq_occurrenceCommonIndex depth A B b]
        exact (occurrenceCommonIndex_eq_iff_blockIndexOf_eq
          depth A B ha.1 hb.1).mpr hfst
      · rw [flatSupportPairIndex_snd_eq_occurrenceCommonIndex depth A B a,
          flatSupportPairIndex_snd_eq_occurrenceCommonIndex depth A B b]
        exact (occurrenceCommonIndex_eq_iff_blockIndexOf_eq
          depth B A ha.2 hb.2).mpr hsnd
  rw [dyadicOrderTerm_eq_if_blockIndexOf_eq depth A ha.1 hb.1,
    dyadicOrderTerm_eq_if_blockIndexOf_eq depth B ha.2 hb.2]
  by_cases hab : a.1 = b.1
  · simp [hab, rankSign]
  · by_cases hAidx :
        blockIndexOf (depth := depth) A.nodup_order
              ((A.mem_support_iff a.1).mp ha.1) =
            blockIndexOf (depth := depth) A.nodup_order
              ((A.mem_support_iff b.1).mp hb.1)
    · by_cases hBidx :
          blockIndexOf (depth := depth) B.nodup_order
                ((B.mem_support_iff a.1).mp ha.2) =
              blockIndexOf (depth := depth) B.nodup_order
                ((B.mem_support_iff b.1).mp hb.2)
      · have hp : (e.symm a).1 = (e.symm b).1 :=
          hpair.mpr ⟨hAidx, hBidx⟩
        simp [hab, hAidx, hBidx, hp]
      · have hp : ¬(e.symm a).1 = (e.symm b).1 :=
          fun h => hBidx (hpair.mp h).2
        simp [hab, hAidx, hBidx, hp]
    · have hp : ¬(e.symm a).1 = (e.symm b).1 :=
        fun h => hAidx (hpair.mp h).1
      simp [hab, hAidx, hp]

#print axioms dyadicTerm_product_eq_samePairIndex_rankProduct

end FamilyStickyCinematicL32Prop41MarcusTardosCommonSupportDyadicProductCleanV1
