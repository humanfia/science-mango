import Family8Grounding.Family8CanonicalEndpointBaseThresholdV1
import Family8Grounding.Family8LongIntervalOrdinaryFiberCapNumericsV1

/-!
# Canonical endpoint threshold including the actual source-cap fibre power

This successor intersects the common endpoint base threshold with the
ordinary-fibre natural-cap threshold used by the full shading-aware source-cap
power estimate.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8CanonicalEndpointSourceCapThresholdV1

open Family8CanonicalEndpointBaseThresholdV1
open Family8EndpointLongCoreHalfRadiusThresholdV2
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8ParameterLadderV1
open Family8ShadingAwareSelectionBranchLossPowerV1
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2

noncomputable section

variable {epsilon0 beta gamma : Real}

/-- The common endpoint threshold extended by the actual branching-cap power
absorption. -/
def canonicalEndpointSourceCapThreshold
    (P : ParameterLadder epsilon0 beta gamma)
    (targetEpsilon selectionEta fiberAbsorbExponent : Real) : NNReal :=
  min (canonicalEndpointBaseThreshold P targetEpsilon selectionEta)
    (ordinaryFiberNatCapSmallDeltaThreshold fiberAbsorbExponent)

theorem canonicalEndpointSourceCapThreshold_pos
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma ≤ 1)
    (targetEpsilon selectionEta fiberAbsorbExponent : Real) :
    0 < canonicalEndpointSourceCapThreshold P targetEpsilon selectionEta
      fiberAbsorbExponent := by
  unfold canonicalEndpointSourceCapThreshold
  exact lt_min
    (canonicalEndpointBaseThreshold_pos P hbeta hgamma _ _)
    (ordinaryFiberNatCapSmallDeltaThreshold_pos _)

theorem canonicalEndpointSourceCapThreshold_le_base
    (P : ParameterLadder epsilon0 beta gamma)
    (targetEpsilon selectionEta fiberAbsorbExponent : Real) :
    canonicalEndpointSourceCapThreshold P targetEpsilon selectionEta
      fiberAbsorbExponent ≤
        canonicalEndpointBaseThreshold P targetEpsilon selectionEta :=
  min_le_left _ _

theorem canonicalEndpointSourceCapThreshold_le_fiber
    (P : ParameterLadder epsilon0 beta gamma)
    (targetEpsilon selectionEta fiberAbsorbExponent : Real) :
    canonicalEndpointSourceCapThreshold P targetEpsilon selectionEta
      fiberAbsorbExponent ≤
        ordinaryFiberNatCapSmallDeltaThreshold fiberAbsorbExponent :=
  min_le_right _ _

theorem canonicalEndpointSourceCapThreshold_le_threeScale
    (P : ParameterLadder epsilon0 beta gamma)
    (targetEpsilon selectionEta fiberAbsorbExponent : Real) :
    canonicalEndpointSourceCapThreshold P targetEpsilon selectionEta
      fiberAbsorbExponent ≤
        sectionEightThreeScaleActualThreshold gamma (targetEpsilon / 4) :=
  (canonicalEndpointSourceCapThreshold_le_base P targetEpsilon selectionEta
    fiberAbsorbExponent).trans
      (canonicalEndpointBaseThreshold_le_threeScale P targetEpsilon
        selectionEta)

theorem canonicalEndpointSourceCapThreshold_le_halfRadius
    (P : ParameterLadder epsilon0 beta gamma)
    (targetEpsilon selectionEta fiberAbsorbExponent : Real) :
    canonicalEndpointSourceCapThreshold P targetEpsilon selectionEta
      fiberAbsorbExponent ≤ endpointLongCoreHalfRadiusThreshold P :=
  (canonicalEndpointSourceCapThreshold_le_base P targetEpsilon selectionEta
    fiberAbsorbExponent).trans
      (canonicalEndpointBaseThreshold_le_halfRadius P targetEpsilon
        selectionEta)

theorem canonicalEndpointSourceCapThreshold_le_selectionBranchLoss
    (P : ParameterLadder epsilon0 beta gamma)
    (targetEpsilon selectionEta fiberAbsorbExponent : Real) :
    canonicalEndpointSourceCapThreshold P targetEpsilon selectionEta
      fiberAbsorbExponent ≤
        shadingAwareSelectionBranchLossPowerThreshold selectionEta :=
  (canonicalEndpointSourceCapThreshold_le_base P targetEpsilon selectionEta
    fiberAbsorbExponent).trans
      (canonicalEndpointBaseThreshold_le_selectionBranchLoss P targetEpsilon
        selectionEta)

#print axioms canonicalEndpointSourceCapThreshold_pos
#print axioms canonicalEndpointSourceCapThreshold_le_base
#print axioms canonicalEndpointSourceCapThreshold_le_fiber
#print axioms canonicalEndpointSourceCapThreshold_le_threeScale
#print axioms canonicalEndpointSourceCapThreshold_le_halfRadius
#print axioms canonicalEndpointSourceCapThreshold_le_selectionBranchLoss

end
end Family8CanonicalEndpointSourceCapThresholdV1
