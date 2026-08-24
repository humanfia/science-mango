import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosPairBlockFibreFintypeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosBlockPairActualScoreV1
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosBlockPairIndexedFibreScoreV1

open List
open FamilyStickyCinematicL32Prop41MarcusTardosDoubleCrossCoreCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosPartitionBlockIntervalV1
open FamilyStickyCinematicL32Prop41MarcusTardosPairBlockOccurrenceProductCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosPairBlockFibreFintypeV1
open FamilyStickyCinematicL32Prop41MarcusTardosBlockPairSplitCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosBlockPairQCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosBlockPairActualScoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1
open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1.DistinctLinearSequence
open FamilyStickyCinematicL32Prop41MarcusTardosLinearSublistReverseV1
open FamilyStickyCinematicL32Prop41MarcusTardosTaggedSplitOrderSignV1

/-! # Actual score on one product-indexed partition fibre -/

noncomputable def indexedFibreEquivSplit
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (blocksA blocksB : List (List symbol))
    (ij : Fin blocksA.length × Fin blocksB.length)
    {u v : List symbol}
    (huv : (u ++ v).Nodup)
    (hC : partitionBlock blocksA ij.1 <+ u ++ v)
    (hCnodup : (partitionBlock blocksA ij.1).Nodup)
    (hDnodup : (partitionBlock blocksB ij.2).Nodup) :
    {x : symbol // PairBlockFibre blocksA blocksB ij x} ≃
      {x : symbol // x ∈ leftCommon u (partitionBlock blocksA ij.1)
          (partitionBlock blocksB ij.2) ++
        rightCommon v (partitionBlock blocksA ij.1)
          (partitionBlock blocksB ij.2)} where
  toFun x := ⟨x.1, by
    have hxCommon : x.1 ∈
        (linearOfList (partitionBlock blocksA ij.1) hCnodup).commonOrder
          (linearOfList (partitionBlock blocksB ij.2) hDnodup) := by
      simpa [PairBlockFibre, DistinctLinearSequence.commonOrder,
        linearOfList, DistinctLinearSequence.support] using x.2
    simpa only [first_commonOrder_eq_split huv hC hCnodup hDnodup]
      using hxCommon⟩
  invFun x := ⟨x.1, by
    have hxCommon : x.1 ∈
        (linearOfList (partitionBlock blocksA ij.1) hCnodup).commonOrder
          (linearOfList (partitionBlock blocksB ij.2) hDnodup) := by
      simpa only [first_commonOrder_eq_split huv hC hCnodup hDnodup]
        using x.2
    simpa [PairBlockFibre, DistinctLinearSequence.commonOrder,
      linearOfList, DistinctLinearSequence.support] using hxCommon⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

theorem indexedFibreScore_eq_blockPairQ
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (blocksA blocksB : List (List symbol))
    (ij : Fin blocksA.length × Fin blocksB.length)
    {ambientA ambientB u v : List symbol}
    (hAmbientA : ambientA.Nodup) (hAmbientB : ambientB.Nodup)
    (huv : (u ++ v).Nodup)
    (hCommonA : u ++ v <+ ambientA)
    (hCommonB : u.reverse ++ v.reverse <+ ambientB)
    (hC : partitionBlock blocksA ij.1 <+ u ++ v)
    (hD : partitionBlock blocksB ij.2 <+ u.reverse ++ v.reverse)
    (hCnodup : (partitionBlock blocksA ij.1).Nodup)
    (hDnodup : (partitionBlock blocksB ij.2).Nodup) :
    (∑ a : {x : symbol // PairBlockFibre blocksA blocksB ij x},
      ∑ b : {x : symbol // PairBlockFibre blocksA blocksB ij x},
        rankSign (fun x ↦ ambientA.idxOf x) a.1 b.1 *
          rankSign (fun x ↦ ambientB.idxOf x) a.1 b.1) =
      blockPairQ u v (partitionBlock blocksA ij.1)
        (partitionBlock blocksB ij.2) := by
  classical
  let e := indexedFibreEquivSplit blocksA blocksB ij huv hC hCnodup hDnodup
  calc
    (∑ a : {x : symbol // PairBlockFibre blocksA blocksB ij x},
      ∑ b : {x : symbol // PairBlockFibre blocksA blocksB ij x},
        rankSign (fun x ↦ ambientA.idxOf x) a.1 b.1 *
          rankSign (fun x ↦ ambientB.idxOf x) a.1 b.1) =
        ∑ a : {x : symbol //
            x ∈ leftCommon u (partitionBlock blocksA ij.1)
                (partitionBlock blocksB ij.2) ++
              rightCommon v (partitionBlock blocksA ij.1)
                (partitionBlock blocksB ij.2)},
          ∑ b : {x : symbol //
              x ∈ leftCommon u (partitionBlock blocksA ij.1)
                  (partitionBlock blocksB ij.2) ++
                rightCommon v (partitionBlock blocksA ij.1)
                  (partitionBlock blocksB ij.2)},
            rankSign (fun x ↦ ambientA.idxOf x) a.1 b.1 *
              rankSign (fun x ↦ ambientB.idxOf x) a.1 b.1 := by
      exact Fintype.sum_equiv e _ _ fun a => by
        exact Fintype.sum_equiv e _ _ fun b => by rfl
    _ = blockPairQ u v (partitionBlock blocksA ij.1)
          (partitionBlock blocksB ij.2) :=
      blockPairActualScore_eq_blockPairQ hAmbientA hAmbientB huv
        hCommonA hCommonB hC hD hCnodup hDnodup

#print axioms indexedFibreEquivSplit
#print axioms indexedFibreScore_eq_blockPairQ

end FamilyStickyCinematicL32Prop41MarcusTardosBlockPairIndexedFibreScoreV1
