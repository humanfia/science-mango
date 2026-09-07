import FamilyStickyGrounding.FamilyStickyScaleCoverAdjacentStepBridgeV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyBoundedFiberPartitionCoreV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleCoverAdjacentStepBridgeV2

noncomputable section

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The same Sticky parent map, with its genuine uniform upper fibre cap used
as the partition branching loss.  Positivity follows from occupation. -/
def boundedFiberCoarseTubePartition
    (S : StickyScaleCover fine rho)
    (hscale : delta <= rho)
    (hcoarse : S.activeCoarse.Nonempty)
    (M : Nat)
    (hM : forall k, k ∈ S.activeCoarse -> (S.fiber k).card <= M) :
    CoarseTubePartition fine S.coarse where
  scale_le := hscale
  index := coverIndexFactorization S
  fine_eq_refined := S.activeFine_eq_refined
  coarse_eq_refined := S.activeCoarse_eq_refined
  coarse_nonempty := hcoarse
  carrier_subset := S.carrier_subset
  parent_surjective := S.parent_surjective
  branching := 1
  branching_pos := Nat.zero_lt_one
  branchingLoss := M
  branchingLoss_pos := by
    obtain ⟨k, hk⟩ := hcoarse
    obtain ⟨i, hi, hparent⟩ := S.parent_surjective k hk
    have hiFiber : i ∈ S.fiber k :=
      (S.mem_fiber i k).2 ⟨hi, hparent⟩
    exact (Finset.card_pos.mpr ⟨i, hiFiber⟩).trans_le (hM k hk)
  branching_le_loss_mul_fiber := by
    intro k hk
    obtain ⟨i, hi, hparent⟩ := S.parent_surjective k hk
    have hfiber : (S.fiber k).Nonempty :=
      ⟨i, (S.mem_fiber i k).2 ⟨hi, hparent⟩⟩
    have hMpos : 0 < M :=
      (Finset.card_pos.mpr hfiber).trans_le (hM k hk)
    have hcardPos : 0 < (S.fiber k).card := Finset.card_pos.mpr hfiber
    change 1 <= M * (S.fiber k).card
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero hMpos.ne' hcardPos.ne')
  fiber_card_le_loss_mul_branching := by
    intro k hk
    change
      (S.activeFine.filter (fun i => S.parent i = k)).card <= M * 1
    simpa only [Nat.mul_one, StickyScaleCover.fiber] using hM k hk

@[simp]
theorem boundedFiberCoarseTubePartition_branchingLoss
    (S : StickyScaleCover fine rho)
    (hscale : delta <= rho)
    (hcoarse : S.activeCoarse.Nonempty)
    (M : Nat)
    (hM : forall k, k ∈ S.activeCoarse -> (S.fiber k).card <= M) :
    (boundedFiberCoarseTubePartition S hscale hcoarse M hM).branchingLoss = M :=
  rfl

@[simp]
theorem boundedFiberCoarseTubePartition_branching
    (S : StickyScaleCover fine rho)
    (hscale : delta <= rho)
    (hcoarse : S.activeCoarse.Nonempty)
    (M : Nat)
    (hM : forall k, k ∈ S.activeCoarse -> (S.fiber k).card <= M) :
    (boundedFiberCoarseTubePartition S hscale hcoarse M hM).branching = 1 :=
  rfl

#print axioms boundedFiberCoarseTubePartition
#print axioms boundedFiberCoarseTubePartition_branchingLoss
#print axioms boundedFiberCoarseTubePartition_branching

end
end Family8StickyBoundedFiberPartitionCoreV1
