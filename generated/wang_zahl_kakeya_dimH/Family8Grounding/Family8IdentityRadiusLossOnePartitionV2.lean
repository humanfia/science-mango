import Family8Grounding.Family8CoarseTubePartitionExactUniformStickyFiberV4
import FamilyStickyGrounding.FamilyStickyScaleCoverAdjacentStepBridgeV2
import FamilyStickyGrounding.FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

/-!
# The identity-radius cover has exact branching loss one

The generic Sticky-cover-to-partition adapter pays the total active fine
cardinality because an arbitrary parent map can have large fibres.  The
canonical identity-radius cover is different: its parent map is the finite
enumeration equivalence, hence injective, while active-parent surjectivity
makes every active fibre nonempty.  Every active fibre therefore has exactly
one child, and the associated coarse partition has both branching and
branching loss equal to one.

V1 was a dependent `Fin` simplification draft and is not imported.
-/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal

namespace Family8IdentityRadiusLossOnePartitionV2

open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CoarseTubePartitionExactUniformStickyFiberV4
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyScaleCoverAdjacentStepBridgeV2

noncomputable section

theorem identityRadiusScaleCover_fiber_card_le_one
    {delta rho : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (fine : UniformTubeFamily delta index)
    (hscale : delta <= rho) (k : Fin (Fintype.card index)) :
    ((identityRadiusScaleCover fine rho hscale).fiber k).card <= 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hiparent :=
    ((identityRadiusScaleCover fine rho hscale).mem_fiber i k).mp hi |>.2
  have hjparent :=
    ((identityRadiusScaleCover fine rho hscale).mem_fiber j k).mp hj |>.2
  change Fintype.equivFin index i = k at hiparent
  change Fintype.equivFin index j = k at hjparent
  exact (Fintype.equivFin index).injective
    (hiparent.trans hjparent.symm)

/-- The exact loss-one coarse partition carried by the identity-radius
Sticky cover. -/
def identityRadiusLossOnePartition
    {delta rho : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (fine : UniformTubeFamily delta index)
    (hscale : delta <= rho)
    (hcoarse : (identityRadiusScaleCover fine rho hscale).activeCoarse.Nonempty) :
    CoarseTubePartition fine
      (identityRadiusScaleCover fine rho hscale).coarse := by
  let S := identityRadiusScaleCover fine rho hscale
  exact {
    scale_le := hscale
    index := coverIndexFactorization S
    fine_eq_refined := S.activeFine_eq_refined
    coarse_eq_refined := S.activeCoarse_eq_refined
    coarse_nonempty := hcoarse
    carrier_subset := S.carrier_subset
    parent_surjective := S.parent_surjective
    branching := 1
    branching_pos := Nat.zero_lt_one
    branchingLoss := 1
    branchingLoss_pos := Nat.zero_lt_one
    branching_le_loss_mul_fiber := by
      intro k hk
      obtain ⟨i, hi, hparent⟩ := S.parent_surjective k hk
      have hfiber : (S.fiber k).Nonempty :=
        ⟨i, (S.mem_fiber i k).2 ⟨hi, hparent⟩⟩
      change 1 <= 1 * (S.fiber k).card
      simpa only [one_mul] using Finset.one_le_card.mpr hfiber
    fiber_card_le_loss_mul_branching := by
      intro k _hk
      change (S.fiber k).card <= 1 * 1
      simpa only [one_mul] using
        identityRadiusScaleCover_fiber_card_le_one fine hscale k }

@[simp] theorem identityRadiusLossOnePartition_branching
    {delta rho : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (fine : UniformTubeFamily delta index)
    (hscale : delta <= rho)
    (hcoarse : (identityRadiusScaleCover fine rho hscale).activeCoarse.Nonempty) :
    (identityRadiusLossOnePartition fine hscale hcoarse).branching = 1 := by
  rfl

@[simp] theorem identityRadiusLossOnePartition_branchingLoss
    {delta rho : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (fine : UniformTubeFamily delta index)
    (hscale : delta <= rho)
    (hcoarse : (identityRadiusScaleCover fine rho hscale).activeCoarse.Nonempty) :
    (identityRadiusLossOnePartition fine hscale hcoarse).branchingLoss = 1 := by
  rfl

/-- Forgetting the two loss-one cardinality fields recovers the literal
identity-radius Sticky cover definitionally. -/
theorem exactPartitionStickyCover_identityRadiusLossOnePartition
    {delta rho : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (fine : UniformTubeFamily delta index)
    (hscale : delta <= rho)
    (hcoarse : (identityRadiusScaleCover fine rho hscale).activeCoarse.Nonempty) :
    exactPartitionStickyCover
        (identityRadiusLossOnePartition fine hscale hcoarse) =
      identityRadiusScaleCover fine rho hscale := by
  rfl

#print axioms identityRadiusScaleCover_fiber_card_le_one
#print axioms identityRadiusLossOnePartition
#print axioms identityRadiusLossOnePartition_branching
#print axioms identityRadiusLossOnePartition_branchingLoss
#print axioms exactPartitionStickyCover_identityRadiusLossOnePartition

end
end Family8IdentityRadiusLossOnePartitionV2
