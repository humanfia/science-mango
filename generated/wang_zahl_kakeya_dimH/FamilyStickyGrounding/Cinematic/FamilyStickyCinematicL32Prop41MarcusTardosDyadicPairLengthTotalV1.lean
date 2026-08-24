import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicLemmaTwoDataV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosPartitionPairIncidenceV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosLinearCommonCardV1
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosDyadicPairLengthTotalV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicCommonOrderPartitionV1
open FamilyStickyCinematicL32Prop41MarcusTardosPartitionBlockIntervalV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicLemmaTwoDataV1
open FamilyStickyCinematicL32Prop41MarcusTardosPartitionPairIncidenceV1
open FamilyStickyCinematicL32Prop41MarcusTardosLinearCommonCardV1

/-! # Total dyadic block-pair common length -/

theorem dyadicPairLength_eq_intersection_card
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (ij : Fin (commonBlocks depth A B).length ×
      Fin (commonBlocks depth B A).length) :
    dyadicPairLength depth A B ij =
      ((partitionBlock (commonBlocks depth A B) ij.1).toFinset ∩
        (partitionBlock (commonBlocks depth B A) ij.2).toFinset).card := by
  unfold dyadicPairLength
  exact linearOfList_commonOrder_length _ _ _ _

theorem sum_dyadicPairLength_eq_commonOrder_length
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol) :
    (∑ ij : Fin (commonBlocks depth A B).length ×
      Fin (commonBlocks depth B A).length,
        dyadicPairLength depth A B ij) =
      (A.commonOrder B).length := by
  rw [Fintype.sum_prod_type]
  simp_rw [dyadicPairLength_eq_intersection_card]
  have hsupport :
      (commonBlocks depth A B).flatten.toFinset =
        (commonBlocks depth B A).flatten.toFinset := by
    rw [flatten_commonBlocks, flatten_commonBlocks,
      commonOrder_toFinset, commonOrder_toFinset,
      Finset.inter_comm]
  have hcount := sum_pair_intersection_card_eq_flatten_length
    (commonBlocks depth A B) (commonBlocks depth B A)
    (flatten_commonBlocks_nodup depth A B)
    (flatten_commonBlocks_nodup depth B A) hsupport
  simpa using hcount

theorem sum_dyadicPairLength_real_eq_commonOrder_length
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol) :
    (∑ ij : Fin (commonBlocks depth A B).length ×
      Fin (commonBlocks depth B A).length,
        (dyadicPairLength depth A B ij : Real)) =
      ((A.commonOrder B).length : Real) := by
  norm_cast
  exact sum_dyadicPairLength_eq_commonOrder_length depth A B

#print axioms dyadicPairLength_eq_intersection_card
#print axioms sum_dyadicPairLength_eq_commonOrder_length
#print axioms sum_dyadicPairLength_real_eq_commonOrder_length

end FamilyStickyCinematicL32Prop41MarcusTardosDyadicPairLengthTotalV1
