import Family8Grounding.Family8StickyDensityAwareCanonicalLogBranchSourceBudgetV1
import Family8Grounding.Family8LogarithmicSelectedScalarPowerBudgetsV1

/-!
# Power-envelope branch budget for the canonical logarithmic partition

The fixed dyadic branching constant is absorbed at a global small scale, then
the independent efficient-parent branch-budget projection is applied.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyDensityAwareCanonicalLogBranchPowerBudgetV1

open Submission.Kakeya.Uniformity
open Family8LogarithmicSelectedScalarPowerBudgetsV1
open Family8StickyDensityAwareLogBranchingNNRealAdapterV1
open Family8StickyDensityAwareCanonicalLogBranchSourceBudgetV1
open Family8StickyDensityAwareCanonicalLogPartitionV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho d : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- A power envelope for the honest density-aware cover loss implies the
exact canonical branching source budget. -/
theorem densityAwareLogPartition_branch_sourceBudget_of_powerEnvelope
    (S : StickyScaleCover fine rho) (sourceA : NNReal)
    (hsourceA : 0 < sourceA)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hscale : delta ≤ rho) (hactive : S.activeFine.Nonempty)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    {coverExponent absorbExponent longExponent : Real}
    (hd : 0 < d) (hdOne : d ≤ 1)
    (habsorbExponent : 0 < absorbExponent)
    (hdSmall : d ≤ branchingScalarThreshold absorbExponent)
    (hcover :
      (stickyDensityAwareCoverLossNNReal S sourceA : ENNReal) ≤
        (d : ENNReal) ^ (-coverExponent))
    (hexponent : coverExponent + absorbExponent ≤ longExponent) :
    8192 * ((densityAwareLogPartition
        S sourceA hsourceA hdelta hrho hscale hactive).branchingLoss : NNReal) *
        sourceA * rho ^ 2 ≤
      d ^ (-longExponent) *
        ((densityAwareLogPartition
          S sourceA hsourceA hdelta hrho hscale hactive).branching : NNReal) *
        (delta ^ 2 / 2) := by
  have hAbsorbENN := branching_scalarAbsorption_of_powerEnvelope
    hd hdOne habsorbExponent hdSmall hcover hexponent
  have hAbsorbNN :
      524288 * stickyDensityAwareCoverLossNNReal S sourceA *
          (2 : NNReal) ^ 2 ≤
        d ^ (-longExponent) := by
    apply ENNReal.coe_le_coe.mp
    simpa only [ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_pow,
      ENNReal.coe_rpow_of_ne_zero hd.ne'] using hAbsorbENN
  exact densityAwareLogPartition_branch_sourceBudget
    S sourceA (d ^ (-longExponent)) hsourceA hdelta hrho hscale hactive
    hdeltaHalf hrhoHalf hAbsorbNN

#print axioms
  densityAwareLogPartition_branch_sourceBudget_of_powerEnvelope

end
end Family8StickyDensityAwareCanonicalLogBranchPowerBudgetV1
