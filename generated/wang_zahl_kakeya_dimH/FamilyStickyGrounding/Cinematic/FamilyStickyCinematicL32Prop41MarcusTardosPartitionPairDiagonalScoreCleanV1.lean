import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosPairBlockFibreFintypeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosSigmaDiagonalSumCleanV1
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosPartitionPairDiagonalScoreCleanV1

open FamilyStickyCinematicL32Prop41MarcusTardosPairBlockOccurrenceProductCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosPairBlockFibreFintypeV1
open FamilyStickyCinematicL32Prop41MarcusTardosSigmaDiagonalSumCleanV1

/-! # Exact block-pair fibre decomposition of a supported score -/

theorem flatSupport_samePairIndex_sum_eq_fibre_sum
    {α : Type*} [Fintype α] [DecidableEq α]
    (blocksA blocksB : List (List α))
    (hA : blocksA.flatten.Nodup) (hB : blocksB.flatten.Nodup)
    (hsupport : blocksA.flatten.toFinset = blocksB.flatten.toFinset)
    (g : α → α → Real) :
    let e := pairBlockOccurrenceEquivFlatSupport
      blocksA blocksB hA hB hsupport
    (∑ a : {x : α // x ∈ blocksA.flatten.toFinset},
      ∑ b : {x : α // x ∈ blocksA.flatten.toFinset},
        if (e.symm a).1 = (e.symm b).1 then g a.1 b.1 else 0) =
      ∑ ij : Fin blocksA.length × Fin blocksB.length,
        ∑ a : {x : α // PairBlockFibre blocksA blocksB ij x},
          ∑ b : {x : α // PairBlockFibre blocksA blocksB ij x},
            g a.1 b.1 := by
  classical
  dsimp only
  let e := pairBlockOccurrenceEquivFlatSupport
    blocksA blocksB hA hB hsupport
  calc
    (∑ a : {x : α // x ∈ blocksA.flatten.toFinset},
      ∑ b : {x : α // x ∈ blocksA.flatten.toFinset},
        if (e.symm a).1 = (e.symm b).1 then g a.1 b.1 else 0) =
        ∑ x : PairBlockOccurrence α blocksA blocksB,
          ∑ y : PairBlockOccurrence α blocksA blocksB,
            if x.1 = y.1 then g x.2.1 y.2.1 else 0 := by
      symm
      exact Fintype.sum_equiv e _ _ fun x => by
        exact Fintype.sum_equiv e _ _ fun y => by simp [e]
    _ = ∑ ij : Fin blocksA.length × Fin blocksB.length,
        ∑ a : {x : α // PairBlockFibre blocksA blocksB ij x},
          ∑ b : {x : α // PairBlockFibre blocksA blocksB ij x},
            g a.1 b.1 :=
      sum_sigma_same_fibre (PairBlockFibre blocksA blocksB) g

#print axioms flatSupport_samePairIndex_sum_eq_fibre_sum

end FamilyStickyCinematicL32Prop41MarcusTardosPartitionPairDiagonalScoreCleanV1
