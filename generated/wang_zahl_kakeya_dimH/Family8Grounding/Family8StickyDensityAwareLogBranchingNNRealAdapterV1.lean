import Family8Grounding.Family8StickyDensityAwareLogBranchingProducerV1
import Mathlib.Tactic

/-!
# Finite loss adapter for the density-aware logarithmic producer

The honest cover loss is finite, so it has a literal `NNReal` representative.
This is the form consumed by the source-budget and numerical endpoint
modules; the coercion theorem below keeps the selected efficient bucket
definitionally on the same loss.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyDensityAwareLogBranchingNNRealAdapterV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open Family8StickyDensityAwareLogBranchingCoverLossV4
open Family8StickyDensityAwareLogBranchingProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The finite representative of the honest density-aware cover loss. -/
def stickyDensityAwareCoverLossNNReal
    (S : StickyScaleCover fine rho) (A : NNReal) : NNReal :=
  (stickyDensityAwareCoverLoss S (A : ENNReal)).toNNReal

theorem coe_stickyDensityAwareCoverLossNNReal
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hdelta : 0 < delta) (hactive : S.activeFine.Nonempty) :
    (stickyDensityAwareCoverLossNNReal S A : ENNReal) =
      stickyDensityAwareCoverLoss S (A : ENNReal) := by
  unfold stickyDensityAwareCoverLossNNReal
  rw [ENNReal.coe_toNNReal]
  exact stickyDensityAwareCoverLoss_ne_top S ENNReal.coe_ne_top
    hdelta hactive

theorem stickyDensityAwareCoverLossNNReal_pos
    (S : StickyScaleCover fine rho) {A : NNReal}
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hactive : S.activeFine.Nonempty) :
    0 < stickyDensityAwareCoverLossNNReal S A := by
  apply ENNReal.coe_pos.mp
  rw [coe_stickyDensityAwareCoverLossNNReal S A hdelta hactive]
  exact (stickyDensityAwareCoverLoss_ne_zero S
    (ENNReal.coe_ne_zero.mpr hA.ne') hrho hactive).bot_lt

/-- The full logarithmic producer with its loss rewritten to the finite
representative required by the source-budget consumer. -/
theorem exists_stickyDensityAware_logBranching_nnreal
    (S : StickyScaleCover fine rho)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hscale : delta ≤ rho)
    (hactive : S.activeFine.Nonempty)
    (A : NNReal) (hA : 0 < A)
    (hfineKT : IsKatzTaoOn (A : ENNReal) fine.bodyFamily S.activeFine) :
    ∃ (b : Fin (Nat.log 2 (Fintype.card iota) + 1))
        (selected : Finset (Fin S.coarseCard))
        (selectedFine : Finset iota)
        (fine' : UniformTubeFamily delta iota)
        (coarse' : UniformTubeFamily rho (Fin S.coarseCard)),
      ∃ P : CoarseTubePartition fine' coarse',
        selected = efficientLogCardBucket fine S.coarse S.activeFine S.parent
          (A : ENNReal)
          (stickyDensityAwareCoverLossNNReal S A : ENNReal) b ∧
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
        IsKatzTaoOn
          (2 * (stickyDensityAwareCoverLossNNReal S A : ENNReal))
          coarse'.bodyFamily P.coarseIndices ∧
        ∀ k ∈ P.coarseIndices,
          IsFrostmanOn
            (2 * (stickyDensityAwareCoverLossNNReal S A : ENNReal))
            fine'.bodyFamily (P.fiber k) (coarse'.bodyFamily k) := by
  obtain ⟨b, selected, selectedFine, fine', coarse', P, hP⟩ :=
    exists_stickyDensityAware_logBranching S hdelta hrho hscale hactive
      (A : ENNReal) (ENNReal.coe_ne_zero.mpr hA.ne')
      ENNReal.coe_ne_top hfineKT
  refine ⟨b, selected, selectedFine, fine', coarse', P, ?_⟩
  simpa only [coe_stickyDensityAwareCoverLossNNReal S A hdelta hactive]
    using hP

#print axioms stickyDensityAwareCoverLossNNReal
#print axioms coe_stickyDensityAwareCoverLossNNReal
#print axioms stickyDensityAwareCoverLossNNReal_pos
#print axioms exists_stickyDensityAware_logBranching_nnreal

end
end Family8StickyDensityAwareLogBranchingNNRealAdapterV1
