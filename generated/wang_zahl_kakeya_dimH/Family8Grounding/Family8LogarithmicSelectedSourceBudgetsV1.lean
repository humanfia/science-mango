import Family8Grounding.Family8EfficientSelectedBranchingSourceBudgetV2
import Family8Grounding.Family8WithinFactorFineCardSourceBudgetV3

/-!
# Both source budgets for the logarithmic selected partition

This is the thin consumer of the honest logarithmic joint-factoring output.
It uses the retained body mass for the fine-card budget and membership in the
selected efficient bucket for the branching budget.  Only the two scalar
absorptions remain as inputs.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8LogarithmicSelectedSourceBudgetsV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8EfficientSelectedBranchingSourceBudgetV2
open Family8WithinFactorFineCardSourceBudgetV3

noncomputable section

variable {delta rho : NNReal} {iota kappa : Type}
  [Fintype iota] [DecidableEq iota]
  [Fintype kappa] [DecidableEq kappa]

/-- The exact output fields of logarithmic joint factoring turn the two
paper-facing scalar absorptions into both source budgets required by the
general-branching Family 8 endpoint. -/
theorem logarithmicSelected_sourceBudgets
    (fine : UniformTubeFamily delta iota)
    (coarse : UniformTubeFamily rho kappa)
    (active : Finset iota) (parent : iota -> kappa)
    (sourceA coverLoss fineTarget longTarget : NNReal)
    (b : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (selected : Finset kappa)
    (fine' : UniformTubeFamily delta iota)
    (coarse' : UniformTubeFamily rho kappa)
    (P : CoarseTubePartition fine' coarse')
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (hselected : selected = efficientLogCardBucket fine coarse active parent
      (sourceA : ENNReal) (coverLoss : ENNReal) b)
    (hindex : P.index = selectedIndexFactorization active parent selected)
    (hbranching : P.branching = logBucketBranching b)
    (hbranchingLoss : P.branchingLoss = 2)
    (hretain : WithinFactor
      (2 * (Nat.log 2 (Fintype.card iota) + 1))
      (bodyMassOn fine.bodyFamily active)
      (bodyMassOn fine'.bodyFamily P.fineIndices))
    (hFineAbsorb :
      (131072 : ENNReal) *
          (2 * (Nat.log 2 (Fintype.card iota) + 1) : Nat) *
          (2 : ENNReal) ^ 2 * (sourceA : ENNReal) <=
        (fineTarget : ENNReal) * bodyMassOn fine.bodyFamily active)
    (hBranchAbsorb : 524288 * coverLoss * (2 : NNReal) ^ 2 <= longTarget) :
    (8192 * (P.branchingLoss : NNReal) ^ 2 * sourceA <=
        fineTarget * (P.fineIndices.card : NNReal) * (delta ^ 2 / 2)) ∧
      (8192 * (P.branchingLoss : NNReal) * sourceA * rho ^ 2 <=
        longTarget * (P.branching : NNReal) * (delta ^ 2 / 2)) := by
  have hretainLoss :
      0 < 2 * (Nat.log 2 (Fintype.card iota) + 1) := by omega
  have hFineTwo := fineCard_source_budget_of_withinFactor
    fine' P.fineIndices hdeltaHalf
      (bodyMassOn fine.bodyFamily active)
      (2 * (Nat.log 2 (Fintype.card iota) + 1)) 2
      sourceA fineTarget hretainLoss hretain hFineAbsorb
  have hFine :
      8192 * (P.branchingLoss : NNReal) ^ 2 * sourceA <=
        fineTarget * (P.fineIndices.card : NNReal) * (delta ^ 2 / 2) := by
    rw [hbranchingLoss]
    exact hFineTwo
  obtain ⟨k, hkP⟩ := P.coarseIndices_nonempty
  have hkSelected : k ∈ selected := by
    change k ∈ P.index.coarse at hkP
    rw [hindex] at hkP
    exact hkP
  have hkBucket : k ∈ efficientLogCardBucket fine coarse active parent
      (sourceA : ENNReal) (coverLoss : ENNReal) b := by
    rw [← hselected]
    exact hkSelected
  have hkEfficient : k ∈ efficientParents fine coarse active parent
      (sourceA : ENNReal) (coverLoss : ENNReal) :=
    (mem_dyadicFiber
      (efficientParents fine coarse active parent
        (sourceA : ENNReal) (coverLoss : ENNReal))
      (fiberLogCardLabel active parent) b k).1 hkBucket |>.1
  have hrawCard :
      ((rawIndexFactorization active parent).fiber k).card <=
        2 * logBucketBranching b :=
    Nat.le_of_lt (efficientLogCardBucket_fiber_card_bounds
      fine coarse active parent (sourceA : ENNReal) (coverLoss : ENNReal)
        b hkBucket).2
  have hBranchTwo := branching_source_budget_of_efficientParent
    fine coarse active parent sourceA coverLoss longTarget
      hdeltaHalf hrhoHalf 2 (logBucketBranching b) k
      hkEfficient hrawCard hBranchAbsorb
  have hBranch :
      8192 * (P.branchingLoss : NNReal) * sourceA * rho ^ 2 <=
        longTarget * (P.branching : NNReal) * (delta ^ 2 / 2) := by
    rw [hbranchingLoss, hbranching]
    exact hBranchTwo
  exact ⟨hFine, hBranch⟩

end

end Family8LogarithmicSelectedSourceBudgetsV1
