import Submission.Kakeya.ConvexFactoring.CoarseTubePartition
import Mathlib.Tactic

/-!
# The lower cardinality comparison for a coarse tube partition

Every active fibre contains at least `branching / branchingLoss` fine
indices.  Summing this literal lower bound gives the count comparison used
by the three-scale decomposition.  No exact-uniformity hypothesis is needed.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open scoped ENNReal NNReal BigOperators

namespace Family8CoarseTubePartitionLowerCountLossV1

open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity

variable {delta rho : NNReal} {iota kappa : Type*}
  [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho kappa}

/-- The target branching times the number of active parents is controlled by
the actual selected fine count with exactly one `branchingLoss` factor. -/
theorem CoarseTubePartition.coarse_card_mul_branching_le_loss_mul_fine_card
    (P : CoarseTubePartition fine coarse) :
    P.coarseIndices.card * P.branching <=
      P.branchingLoss * P.fineIndices.card := by
  rw [P.card_fine_eq_sum_card_fiber]
  calc
    P.coarseIndices.card * P.branching =
        ∑ _k ∈ P.coarseIndices, P.branching := by simp
    _ <= ∑ k ∈ P.coarseIndices,
        P.branchingLoss * (P.fiber k).card := by
      exact Finset.sum_le_sum fun k hk =>
        P.branching_le_loss_mul_fiber k hk
    _ = P.branchingLoss *
        ∑ k ∈ P.coarseIndices, (P.fiber k).card := by
      rw [Finset.mul_sum]

#print axioms
  CoarseTubePartition.coarse_card_mul_branching_le_loss_mul_fine_card

end Family8CoarseTubePartitionLowerCountLossV1
