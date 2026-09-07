import Family8Grounding.Family8StickyDensityAwareCanonicalLogPartitionV2
import Family8Grounding.Family8WithinFactorFineCardSourceBudgetV3
import Mathlib.Tactic

/-!
# Fine-card source budget for the canonical logarithmic partition

This universe-zero successor matches the existing scalar budget theorem.
Only the explicit scalar absorption remains an input.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyDensityAwareCanonicalLogFineSourceBudgetV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open Family8WithinFactorFineCardSourceBudgetV3
open Family8StickyDensityAwareCanonicalLogPartitionV2
open Family8StickyDensityAwareCanonicalLogRestrictedFamiliesV2

noncomputable section

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- Retained selected mass supplies the endpoint fine-card source budget for
the literal canonical partition. -/
theorem densityAwareLogPartition_fine_sourceBudget
    (S : StickyScaleCover fine rho) (A fineTarget : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hscale : delta ≤ rho) (hactive : S.activeFine.Nonempty)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hFineAbsorb :
      (131072 : ENNReal) *
          (2 * (Nat.log 2 (Fintype.card iota) + 1) : Nat) *
          (2 : ENNReal) ^ 2 * (A : ENNReal) ≤
        (fineTarget : ENNReal) *
          bodyMassOn fine.bodyFamily S.activeFine) :
    8192 * ((densityAwareLogPartition
        S A hA hdelta hrho hscale hactive).branchingLoss : NNReal) ^ 2 * A ≤
      fineTarget *
        ((densityAwareLogPartition
          S A hA hdelta hrho hscale hactive).fineIndices.card : NNReal) *
        (delta ^ 2 / 2) := by
  have hretainLoss :
      0 < 2 * (Nat.log 2 (Fintype.card iota) + 1) := by omega
  have hTwo := fineCard_source_budget_of_withinFactor
    (densityAwareSelectedFineFamily S A hA hdelta hrho hactive)
    (densityAwareLogPartition
      S A hA hdelta hrho hscale hactive).fineIndices
    hdeltaHalf (bodyMassOn fine.bodyFamily S.activeFine)
    (2 * (Nat.log 2 (Fintype.card iota) + 1)) 2
    A fineTarget hretainLoss
    (densityAwareLogPartition_bodyMass_withinFactor
      S A hA hdelta hrho hscale hactive)
    hFineAbsorb
  simpa only [densityAwareLogPartition_branchingLoss] using hTwo

#print axioms densityAwareLogPartition_fine_sourceBudget

end
end Family8StickyDensityAwareCanonicalLogFineSourceBudgetV2
