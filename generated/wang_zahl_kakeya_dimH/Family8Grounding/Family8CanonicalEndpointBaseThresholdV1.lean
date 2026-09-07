import Family8Grounding.Family8EndpointLongCoreHalfRadiusThresholdV2
import Family8Grounding.Family8ShadingAwareSelectionBranchLossPowerV1
import Family8Grounding.Family8ThreeScaleActualFrostmanFactorAbsorptionV2

/-!
# A common positive base threshold for the canonical Family 8 endpoint

This threshold combines the three small-scale conditions already shared by
the final branches: the actual-volume three-scale absorption, the endpoint
long-core half-radius bound, and the logarithmic selection/partition loss
power bound.  Later branch-specific thresholds can be intersected with this
one without reopening these proofs.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8CanonicalEndpointBaseThresholdV1

open Family8EndpointLongCoreHalfRadiusThresholdV2
open Family8ParameterLadderV1
open Family8ShadingAwareSelectionBranchLossPowerV1
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2

noncomputable section

variable {epsilon0 beta gamma : Real}

/-- The common positive base threshold for the literal endpoint branches. -/
def canonicalEndpointBaseThreshold
    (P : ParameterLadder epsilon0 beta gamma)
    (targetEpsilon lossEta : Real) : NNReal :=
  min (sectionEightThreeScaleActualThreshold gamma (targetEpsilon / 4))
    (min (endpointLongCoreHalfRadiusThreshold P)
      (shadingAwareSelectionBranchLossPowerThreshold lossEta))

theorem canonicalEndpointBaseThreshold_pos
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma ≤ 1)
    (targetEpsilon lossEta : Real) :
    0 < canonicalEndpointBaseThreshold P targetEpsilon lossEta := by
  unfold canonicalEndpointBaseThreshold
  exact lt_min (sectionEightThreeScaleActualThreshold_pos _ _)
    (lt_min (endpointLongCoreHalfRadiusThreshold_pos P hbeta hgamma)
      (shadingAwareSelectionBranchLossPowerThreshold_pos lossEta))

theorem canonicalEndpointBaseThreshold_le_threeScale
    (P : ParameterLadder epsilon0 beta gamma)
    (targetEpsilon lossEta : Real) :
    canonicalEndpointBaseThreshold P targetEpsilon lossEta ≤
      sectionEightThreeScaleActualThreshold gamma (targetEpsilon / 4) :=
  min_le_left _ _

theorem canonicalEndpointBaseThreshold_le_halfRadius
    (P : ParameterLadder epsilon0 beta gamma)
    (targetEpsilon lossEta : Real) :
    canonicalEndpointBaseThreshold P targetEpsilon lossEta ≤
      endpointLongCoreHalfRadiusThreshold P :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem canonicalEndpointBaseThreshold_le_selectionBranchLoss
    (P : ParameterLadder epsilon0 beta gamma)
    (targetEpsilon lossEta : Real) :
    canonicalEndpointBaseThreshold P targetEpsilon lossEta ≤
      shadingAwareSelectionBranchLossPowerThreshold lossEta :=
  (min_le_right _ _).trans (min_le_right _ _)

#print axioms canonicalEndpointBaseThreshold_pos
#print axioms canonicalEndpointBaseThreshold_le_threeScale
#print axioms canonicalEndpointBaseThreshold_le_halfRadius
#print axioms canonicalEndpointBaseThreshold_le_selectionBranchLoss

end
end Family8CanonicalEndpointBaseThresholdV1
