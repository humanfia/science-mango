import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosPartitionPairDiagonalScoreCleanV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosBlockPairIndexedFibreScoreV1
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosPartitionPairQScoreCleanV1

open List
open FamilyStickyCinematicL32Prop41MarcusTardosDoubleCrossCoreCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosPartitionBlockIntervalV1
open FamilyStickyCinematicL32Prop41MarcusTardosPairBlockOccurrenceProductCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosPartitionPairDiagonalScoreCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosBlockPairIndexedFibreScoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosBlockPairQCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosTaggedSplitOrderSignV1

/-! # A full partition-pair actual score is the sum of all `Q_st` -/

theorem flatSupport_samePairIndex_score_eq_sum_blockPairQ
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (blocksA blocksB : List (List symbol))
    (hA : blocksA.flatten.Nodup) (hB : blocksB.flatten.Nodup)
    (hsupport : blocksA.flatten.toFinset = blocksB.flatten.toFinset)
    {ambientA ambientB u v : List symbol}
    (hAmbientA : ambientA.Nodup) (hAmbientB : ambientB.Nodup)
    (hflatA : blocksA.flatten = u ++ v)
    (hflatB : blocksB.flatten = u.reverse ++ v.reverse)
    (hCommonA : u ++ v <+ ambientA)
    (hCommonB : u.reverse ++ v.reverse <+ ambientB) :
    let e := pairBlockOccurrenceEquivFlatSupport
      blocksA blocksB hA hB hsupport
    (∑ a : {x : symbol // x ∈ blocksA.flatten.toFinset},
      ∑ b : {x : symbol // x ∈ blocksA.flatten.toFinset},
        if (e.symm a).1 = (e.symm b).1 then
          rankSign (fun x ↦ ambientA.idxOf x) a.1 b.1 *
            rankSign (fun x ↦ ambientB.idxOf x) a.1 b.1
        else 0) =
      ∑ ij : Fin blocksA.length × Fin blocksB.length,
        blockPairQ u v (partitionBlock blocksA ij.1)
          (partitionBlock blocksB ij.2) := by
  classical
  dsimp only
  rw [flatSupport_samePairIndex_sum_eq_fibre_sum blocksA blocksB hA hB
    hsupport (fun a b =>
      rankSign (fun x ↦ ambientA.idxOf x) a b *
        rankSign (fun x ↦ ambientB.idxOf x) a b)]
  apply Finset.sum_congr rfl
  intro ij hij
  have huv : (u ++ v).Nodup := by simpa [← hflatA] using hA
  have hC : partitionBlock blocksA ij.1 <+ u ++ v := by
    rw [← hflatA]
    exact partitionBlock_sublist_flatten blocksA ij.1
  have hD : partitionBlock blocksB ij.2 <+ u.reverse ++ v.reverse := by
    rw [← hflatB]
    exact partitionBlock_sublist_flatten blocksB ij.2
  have hCnodup : (partitionBlock blocksA ij.1).Nodup :=
    hA.sublist (partitionBlock_sublist_flatten blocksA ij.1)
  have hDnodup : (partitionBlock blocksB ij.2).Nodup :=
    hB.sublist (partitionBlock_sublist_flatten blocksB ij.2)
  exact indexedFibreScore_eq_blockPairQ blocksA blocksB ij
    hAmbientA hAmbientB huv hCommonA hCommonB hC hD hCnodup hDnodup

#print axioms flatSupport_samePairIndex_score_eq_sum_blockPairQ

end FamilyStickyCinematicL32Prop41MarcusTardosPartitionPairQScoreCleanV1
