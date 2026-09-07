import Family8Grounding.Family8ParameterLadderV1
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

/-!
# Small-scale base bridge for the low fresh long interval

The long-interval numerical consumer is used with lower scale
`d = delta / 8` and upper scale `b = delta`.  Its remaining scale premise is

`delta <= (delta / 8) ^ (1 - epsilon)`.

For the paper ladder, the positive exponent `epsilon` absorbs the fixed
factor eight below the existing finite-constant threshold.  The sole
numerical input is the built-in positivity `P.epsilon_pos`.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8LowFreshLongIntervalBaseScaleBridgeV1

open Family8ParameterLadderV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-- Explicit positive terminal scale at which `P.epsilon` absorbs the fixed
factor eight introduced by the normalized lower scale `delta / 8`. -/
def lowFreshLongIntervalBaseScaleThreshold
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) : NNReal :=
  finiteConstantSmallDeltaThreshold 8 P.epsilon

theorem lowFreshLongIntervalBaseScaleThreshold_pos
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) :
    0 < lowFreshLongIntervalBaseScaleThreshold P := by
  exact finiteConstantSmallDeltaThreshold_pos 8 P.epsilon

/-- Below the explicit threshold, the concrete low-branch scales
`b = delta` and `d = delta / 8` satisfy the upper-scale premise of the
long-interval consumer. -/
theorem delta_le_eighth_rpow_one_sub_of_le_threshold
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    {delta : NNReal}
    (hdelta : 0 < delta)
    (hsmall : delta <= lowFreshLongIntervalBaseScaleThreshold P) :
    delta <= (delta / 8) ^ (1 - P.epsilon) := by
  have hEightENN :
      (8 : ENNReal) <= (delta : ENNReal) ^ (-P.epsilon) := by
    exact finiteConstant_le_delta_negativePower
      (K := (8 : ENNReal)) (by norm_num) P.epsilon_pos hdelta
        (by
          simpa only [lowFreshLongIntervalBaseScaleThreshold] using hsmall)
  have hEight :
      (8 : NNReal) <= delta ^ (-P.epsilon) := by
    apply ENNReal.coe_le_coe.mp
    simpa only [ENNReal.coe_ofNat,
      ENNReal.coe_rpow_of_ne_zero hdelta.ne'] using hEightENN
  have hEightPower :
      (8 : NNReal) ^ (1 - P.epsilon) <= 8 := by
    simpa only [NNReal.rpow_one] using
      (NNReal.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : NNReal) <= 8)
        (by linarith [P.epsilon_pos] : 1 - P.epsilon <= (1 : Real)))
  have hEightPowerToDelta :
      (8 : NNReal) ^ (1 - P.epsilon) <=
        delta ^ (-P.epsilon) :=
    hEightPower.trans hEight
  have hdeltaPower :
      delta ^ P.epsilon <=
        (8 : NNReal) ^ (-(1 - P.epsilon)) := by
    have hinv :
        (delta ^ (-P.epsilon))⁻¹ <=
          ((8 : NNReal) ^ (1 - P.epsilon))⁻¹ := by
      exact (inv_le_inv₀
        (NNReal.rpow_pos hdelta)
        (NNReal.rpow_pos (by norm_num : (0 : NNReal) < 8))).2
          hEightPowerToDelta
    simpa only [NNReal.rpow_neg, inv_inv] using hinv
  calc
    delta = delta ^ ((1 - P.epsilon) + P.epsilon) := by
      rw [show (1 - P.epsilon) + P.epsilon = (1 : Real) by ring,
        NNReal.rpow_one]
    _ = delta ^ (1 - P.epsilon) * delta ^ P.epsilon :=
      NNReal.rpow_add hdelta.ne' _ _
    _ <= delta ^ (1 - P.epsilon) *
        (8 : NNReal) ^ (-(1 - P.epsilon)) :=
      mul_le_mul' le_rfl hdeltaPower
    _ = delta ^ (1 - P.epsilon) /
        (8 : NNReal) ^ (1 - P.epsilon) := by
      rw [NNReal.rpow_neg, div_eq_mul_inv]
    _ = (delta / 8) ^ (1 - P.epsilon) := by
      rw [NNReal.div_rpow]

#print axioms lowFreshLongIntervalBaseScaleThreshold_pos
#print axioms delta_le_eighth_rpow_one_sub_of_le_threshold

end

end Family8LowFreshLongIntervalBaseScaleBridgeV1
