import Family8Grounding.Family8StickyDensityAwareLogBranchingCoverLossV4
import Mathlib.Tactic

/-!
# Honest logarithmic branching for a literal Sticky scale cover

The actual Sticky parent map and the density-aware global cover loss satisfy
every hypothesis of the repository's genuine logarithmic
`JointTubeFactoring` construction.  Thus balanced branching, retained source
mass, coarse Katz--Tao control, and fiberwise Frostman control are all
conclusions rather than supplied certificates.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyDensityAwareLogBranchingProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.ConvexFactoring.AlmostCoverTubeFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open Family8StickyDensityAwareLogBranchingCoverLossV4

noncomputable section

set_option autoImplicit false
set_option warningAsError true

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- A literal Sticky parent hierarchy produces the honest logarithmically
balanced partition with density-aware non-concentration constant. -/
theorem exists_stickyDensityAware_logBranching
    (S : StickyScaleCover fine rho)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hscale : delta ≤ rho)
    (hactive : S.activeFine.Nonempty)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hfineKT : IsKatzTaoOn A fine.bodyFamily S.activeFine) :
    ∃ (b : Fin (Nat.log 2 (Fintype.card iota) + 1))
        (selected : Finset (Fin S.coarseCard))
        (selectedFine : Finset iota)
        (fine' : UniformTubeFamily delta iota)
        (coarse' : UniformTubeFamily rho (Fin S.coarseCard)),
      ∃ P : CoarseTubePartition fine' coarse',
        selected = efficientLogCardBucket fine S.coarse S.activeFine S.parent
          A (stickyDensityAwareCoverLoss S A) b ∧
        selectedFine = selectedFineIndices S.activeFine S.parent selected ∧
        (∀ i, fine'.tubes i = fine.tubes i) ∧
        (∀ k, coarse'.tubes k = S.coarse.tubes k) ∧
        fine'.refinement.profile = fine.refinement.profile ∧
        coarse'.refinement.profile = S.coarse.refinement.profile ∧
        P.index = selectedIndexFactorization S.activeFine S.parent selected ∧
        P.branching = logBucketBranching b ∧
        P.branchingLoss = 2 ∧
        WithinFactor (2 * (Nat.log 2 (Fintype.card iota) + 1))
          (bodyMassOn fine.bodyFamily S.activeFine)
          (bodyMassOn fine'.bodyFamily P.fineIndices) ∧
        selectedFine.Nonempty ∧ selected.Nonempty ∧
        selectedFine ⊆ S.activeFine ∧ selected ⊆ S.activeCoarse ∧
        (∀ k ∈ P.coarseIndices,
          logBucketBranching b ≤ (P.fiber k).card ∧
          (P.fiber k).card < 2 * logBucketBranching b) ∧
        IsKatzTaoOn (2 * stickyDensityAwareCoverLoss S A)
          coarse'.bodyFamily P.coarseIndices ∧
        ∀ k ∈ P.coarseIndices,
          IsFrostmanOn (2 * stickyDensityAwareCoverLoss S A)
            fine'.bodyFamily (P.fiber k) (coarse'.bodyFamily k) := by
  have hactiveRefined : S.activeFine ⊆ fine.refinement.refined := by
    rw [S.activeFine_eq_refined]
  have hcoarseRefined : S.activeCoarse ⊆ S.coarse.refinement.refined := by
    rw [S.activeCoarse_eq_refined]
  exact exists_jointTubeFactoring_logBranching
    fine S.coarse S.activeFine S.activeCoarse S.parent A
      (stickyDensityAwareCoverLoss S A)
      hdelta hscale hactive hactiveRefined hcoarseRefined
      S.parent_mem S.carrier_subset hA0 hAtop
      (stickyDensityAwareCoverLoss_ne_zero S hA0 hrho hactive)
      (stickyDensityAwareCoverLoss_ne_top S hAtop hdelta hactive)
      hfineKT (stickyDensityAwareCoverCost S A hdelta hactive)

#print axioms exists_stickyDensityAware_logBranching

end
end Family8StickyDensityAwareLogBranchingProducerV1
