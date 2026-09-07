import Family8Grounding.Family8StickyDensityAwareCanonicalLogFineSourceBudgetV2
import Family8Grounding.Family8LogarithmicSelectedScalarPowerBudgetsV1

/-!
# Power-envelope fine budget for the canonical logarithmic partition

This successor makes the `NNReal`/`ENNReal` rpow cast explicit.  The fixed
logarithmic retention constant is absorbed before applying the independent
fine-card source-budget projection.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyDensityAwareCanonicalLogFinePowerBudgetV2

open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8LogarithmicSelectedScalarPowerBudgetsV1
open Family8StickyDensityAwareCanonicalLogFineSourceBudgetV2
open Family8StickyDensityAwareCanonicalLogPartitionV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho d : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Paper-sized coefficient and retained-mass power envelopes imply the exact
canonical fine-card source budget. -/
theorem densityAwareLogPartition_fine_sourceBudget_of_powerEnvelopes
    (S : StickyScaleCover fine rho) (sourceA : NNReal)
    (hsourceA : 0 < sourceA)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hscale : delta ≤ rho) (hactive : S.activeFine.Nonempty)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    {sourceExponent coefficientExponent absorbExponent baseExponent : Real}
    (hd : 0 < d) (hdOne : d ≤ 1)
    (habsorbExponent : 0 < absorbExponent)
    (hdSmall : d ≤ fineSourceScalarThreshold absorbExponent)
    (hcoefficient :
      ((2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) : ENNReal) *
          (sourceA : ENNReal) ≤
        (d : ENNReal) ^ (-coefficientExponent))
    (hsourceMass : (d : ENNReal) ^ sourceExponent ≤
      bodyMassOn fine.bodyFamily S.activeFine)
    (hexponent :
      sourceExponent + coefficientExponent + absorbExponent ≤
        baseExponent) :
    8192 * ((densityAwareLogPartition
        S sourceA hsourceA hdelta hrho hscale hactive).branchingLoss : NNReal) ^ 2 *
        sourceA ≤
      d ^ (-baseExponent) *
        ((densityAwareLogPartition
          S sourceA hsourceA hdelta hrho hscale hactive).fineIndices.card : NNReal) *
        (delta ^ 2 / 2) := by
  have hAbsorb := fineSource_scalarAbsorption_of_powerEnvelopes
    hd hdOne habsorbExponent hdSmall hcoefficient hsourceMass hexponent
  have hAbsorbNN :
      (131072 : ENNReal) *
          (2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) *
          (2 : ENNReal) ^ 2 * (sourceA : ENNReal) ≤
        ((d ^ (-baseExponent) : NNReal) : ENNReal) *
          bodyMassOn fine.bodyFamily S.activeFine := by
    simpa only [ENNReal.coe_rpow_of_ne_zero hd.ne'] using hAbsorb
  exact densityAwareLogPartition_fine_sourceBudget
    S sourceA (d ^ (-baseExponent)) hsourceA hdelta hrho hscale hactive
    hdeltaHalf hAbsorbNN

#print axioms
  densityAwareLogPartition_fine_sourceBudget_of_powerEnvelopes

end
end Family8StickyDensityAwareCanonicalLogFinePowerBudgetV2
