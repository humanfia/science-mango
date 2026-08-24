import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosFinitePairSupportSumCleanV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosCommonSupportDyadicProductCleanV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosPartitionPairQScoreCleanV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicLemmaTwoCertificateV1
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosActualDyadicLevelScoreCleanV1

open List
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicCommonOrderPartitionV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicActualPairTermV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicOrderTermSupportCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosFinitePairSupportSumCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosCommonSupportDyadicProductCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosCommonPairIndexTransportV1
open FamilyStickyCinematicL32Prop41MarcusTardosPairBlockOccurrenceProductCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosPartitionPairQScoreCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicLemmaTwoDataV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicLemmaTwoCertificateV1

/-! # Exact one-level identity between the Gram feature score and `sum Q_st` -/

theorem sum_dyadicOrderTerm_product_eq_sum_dyadicPairQ
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (C : DyadicLemmaTwoCertificate depth A B) :
    (∑ p : symbol × symbol,
      dyadicOrderTerm depth A p * dyadicOrderTerm depth B p) =
      ∑ ij : Fin (commonBlocks depth A B).length ×
          Fin (commonBlocks depth B A).length,
        dyadicPairQ depth A B C.left C.right ij := by
  classical
  rw [Fintype.sum_prod_type]
  let s := (commonBlocks depth A B).flatten.toFinset
  have hs : s = A.support ∩ B.support := by
    simp [s, flatten_commonBlocks, commonOrder_toFinset]
  calc
    (∑ a : symbol, ∑ b : symbol,
      dyadicOrderTerm depth A (a, b) *
        dyadicOrderTerm depth B (a, b)) =
        ∑ a : ↥s, ∑ b : ↥s,
          dyadicOrderTerm depth A (a.1, b.1) *
            dyadicOrderTerm depth B (a.1, b.1) := by
      apply sum_pair_eq_sum_support_subtype
      · intro a ha b
        apply dyadicTerm_product_zero_of_first_not_common depth A B a
        simpa [hs] using ha
      · intro a b hb
        apply dyadicTerm_product_zero_of_second_not_common depth A B a b
        simpa [hs] using hb
    _ = ∑ a : ↥s, ∑ b : ↥s,
        if ((pairBlockOccurrenceEquivFlatSupport
              (commonBlocks depth A B) (commonBlocks depth B A)
              (flatten_commonBlocks_nodup depth A B)
              (flatten_commonBlocks_nodup depth B A)
              (commonBlocks_flat_support_eq depth A B)).symm a).1 =
            ((pairBlockOccurrenceEquivFlatSupport
              (commonBlocks depth A B) (commonBlocks depth B A)
              (flatten_commonBlocks_nodup depth A B)
              (flatten_commonBlocks_nodup depth B A)
              (commonBlocks_flat_support_eq depth A B)).symm b).1 then
          FamilyStickyCinematicL32Prop41MarcusTardosTaggedSplitOrderSignV1.rankSign
              (fun x ↦ A.order.idxOf x) a.1 b.1 *
            FamilyStickyCinematicL32Prop41MarcusTardosTaggedSplitOrderSignV1.rankSign
              (fun x ↦ B.order.idxOf x) a.1 b.1
        else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      simpa [s] using
        (dyadicTerm_product_eq_samePairIndex_rankProduct depth A B a b)
    _ = ∑ ij : Fin (commonBlocks depth A B).length ×
          Fin (commonBlocks depth B A).length,
        dyadicPairQ depth A B C.left C.right ij := by
      have hCommonA : C.left ++ C.right <+ A.order := by
        rw [← C.firstSplit, flatten_commonBlocks]
        exact List.filter_sublist
      have hCommonB : C.left.reverse ++ C.right.reverse <+ B.order := by
        rw [← C.secondSplit, flatten_commonBlocks]
        exact List.filter_sublist
      simpa [s, dyadicPairQ] using
        (flatSupport_samePairIndex_score_eq_sum_blockPairQ
          (commonBlocks depth A B) (commonBlocks depth B A)
          (flatten_commonBlocks_nodup depth A B)
          (flatten_commonBlocks_nodup depth B A)
          (commonBlocks_flat_support_eq depth A B)
          A.nodup_order B.nodup_order C.firstSplit C.secondSplit
          hCommonA hCommonB)

#print axioms sum_dyadicOrderTerm_product_eq_sum_dyadicPairQ

end FamilyStickyCinematicL32Prop41MarcusTardosActualDyadicLevelScoreCleanV1
