import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicSingularPairV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosBlockPairQCoreV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosDyadicLemmaTwoDataV1

open List
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicCommonOrderPartitionV1
open FamilyStickyCinematicL32Prop41MarcusTardosPartitionBlockIntervalV1
open FamilyStickyCinematicL32Prop41MarcusTardosDoubleCrossCoreCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosBlockPairQCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosLinearSublistReverseV1
open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1.DistinctLinearSequence

/-! # Pointwise dyadic data in Marcus--Tardos Lemma 2 -/

def dyadicPairQ
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (u v : List symbol)
    (ij : Fin (commonBlocks depth A B).length ×
      Fin (commonBlocks depth B A).length) : Real :=
  blockPairQ u v
    (partitionBlock (commonBlocks depth A B) ij.1)
    (partitionBlock (commonBlocks depth B A) ij.2)

def dyadicPairLength
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (ij : Fin (commonBlocks depth A B).length ×
      Fin (commonBlocks depth B A).length) : Nat :=
  ((linearOfList (partitionBlock (commonBlocks depth A B) ij.1)
      ((flatten_commonBlocks_nodup depth A B).sublist
        (partitionBlock_sublist_flatten (commonBlocks depth A B) ij.1))).commonOrder
    (linearOfList (partitionBlock (commonBlocks depth B A) ij.2)
      ((flatten_commonBlocks_nodup depth B A).sublist
        (partitionBlock_sublist_flatten (commonBlocks depth B A) ij.2)))).length

theorem dyadicPairQ_le_length
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    {u v : List symbol}
    (hflatA : (commonBlocks depth A B).flatten = u ++ v)
    (ij : Fin (commonBlocks depth A B).length ×
      Fin (commonBlocks depth B A).length) :
    dyadicPairQ depth A B u v ij ≤ dyadicPairLength depth A B ij := by
  have huv : (u ++ v).Nodup := by
    simpa [← hflatA] using flatten_commonBlocks_nodup depth A B
  have hC : partitionBlock (commonBlocks depth A B) ij.1 <+ u ++ v := by
    rw [← hflatA]
    exact partitionBlock_sublist_flatten _ _
  unfold dyadicPairQ dyadicPairLength
  exact blockPairQ_le_common_length huv hC _ _

theorem dyadicPairQ_eq_regular_score
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    {u v : List symbol}
    (hflatA : (commonBlocks depth A B).flatten = u ++ v)
    (hflatB : (commonBlocks depth B A).flatten =
      u.reverse ++ v.reverse)
    (ij : Fin (commonBlocks depth A B).length ×
      Fin (commonBlocks depth B A).length)
    (hregular : ¬SingularPair
      (commonBlocks depth A B) (commonBlocks depth B A)
      (flatten_commonBlocks_nodup depth A B)
      (flatten_commonBlocks_nodup depth B A) ij) :
    dyadicPairQ depth A B u v ij =
      (dyadicPairLength depth A B ij : Real) -
        (dyadicPairLength depth A B ij : Real) ^ 2 := by
  have huv : (u ++ v).Nodup := by
    simpa [← hflatA] using flatten_commonBlocks_nodup depth A B
  have hC : partitionBlock (commonBlocks depth A B) ij.1 <+ u ++ v := by
    rw [← hflatA]
    exact partitionBlock_sublist_flatten _ _
  have hD : partitionBlock (commonBlocks depth B A) ij.2 <+
      u.reverse ++ v.reverse := by
    rw [← hflatB]
    exact partitionBlock_sublist_flatten _ _
  have hIR :
      (linearOfList (partitionBlock (commonBlocks depth A B) ij.1)
        ((flatten_commonBlocks_nodup depth A B).sublist
          (partitionBlock_sublist_flatten _ _))).IntersectionReverse
      (linearOfList (partitionBlock (commonBlocks depth B A) ij.2)
        ((flatten_commonBlocks_nodup depth B A).sublist
          (partitionBlock_sublist_flatten _ _))) := by
    exact Classical.not_not.mp hregular
  unfold dyadicPairQ dyadicPairLength
  exact blockPairQ_eq_regular_score huv hC hD _ _ hIR

#print axioms dyadicPairQ
#print axioms dyadicPairLength
#print axioms dyadicPairQ_le_length
#print axioms dyadicPairQ_eq_regular_score

end FamilyStickyCinematicL32Prop41MarcusTardosDyadicLemmaTwoDataV1
