import Family8Grounding.Family8LongIntervalFourSeparationV1
import Family8Grounding.Family8ParameterLadderV1
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

/-!
# A uniform ParameterLadder threshold for four-separated long intervals

The stopping exponent is fixed by `ParameterLadder`.  We adjoin one explicit
positive finite-constant threshold to any pre-existing terminal scale by a
minimum.  Below the resulting scale, every `IsLong P.epsilon` interval obeys
`4 * tau <= theta`.  Shrinking the terminal scale preserves the existing
fixed-parameter Katz--Tao and Frostman conclusions.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open scoped ENNReal NNReal

namespace Family8ParameterLadderFourSeparationThresholdV1

open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalFourSeparationV1
open Family8ParameterLadderV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-- Explicit positive threshold which absorbs the finite factor four into the
negative `epsilon` power of the terminal scale. -/
def fourSeparationDeltaThreshold (epsilon : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold 4 epsilon

theorem fourSeparationDeltaThreshold_pos (epsilon : Real) :
    0 < fourSeparationDeltaThreshold epsilon :=
  finiteConstantSmallDeltaThreshold_pos 4 epsilon

theorem fourSeparationDeltaThreshold_le_one
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    fourSeparationDeltaThreshold epsilon <= 1 :=
  finiteConstantSmallDeltaThreshold_le_one 4 hepsilon

/-- Below the threshold, the exact ENNReal factor required by the geometric
producer is at most one. -/
theorem four_mul_delta_rpow_le_one_of_le_threshold
    {delta : NNReal} {epsilon : Real}
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hsmall : delta <= fourSeparationDeltaThreshold epsilon) :
    4 * (delta : ENNReal) ^ epsilon <= 1 := by
  have hfour : (4 : ENNReal) <= (delta : ENNReal) ^ (-epsilon) := by
    exact finiteConstant_le_delta_negativePower
      (K := (4 : ENNReal)) (by norm_num) hepsilon hdelta
        (by simpa only [fourSeparationDeltaThreshold] using hsmall)
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  calc
    4 * (delta : ENNReal) ^ epsilon <=
        (delta : ENNReal) ^ (-epsilon) *
          (delta : ENNReal) ^ epsilon :=
      mul_le_mul' hfour le_rfl
    _ = (delta : ENNReal) ^ (-epsilon + epsilon) := by
      rw [ENNReal.rpow_add _ _ hd0 hdTop]
    _ = 1 := by simp

/-- Add the four-separation condition to any pre-existing terminal scale. -/
def parameterLadderFourSeparatedDelta0
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (delta0 : NNReal) : NNReal :=
  min delta0 (fourSeparationDeltaThreshold P.epsilon)

theorem parameterLadderFourSeparatedDelta0_pos
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) {delta0 : NNReal}
    (hdelta0 : 0 < delta0) :
    0 < parameterLadderFourSeparatedDelta0 P delta0 := by
  rw [parameterLadderFourSeparatedDelta0, lt_min_iff]
  exact ⟨hdelta0, fourSeparationDeltaThreshold_pos P.epsilon⟩

theorem parameterLadderFourSeparatedDelta0_le_base
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (delta0 : NNReal) :
    parameterLadderFourSeparatedDelta0 P delta0 <= delta0 :=
  min_le_left _ _

theorem parameterLadderFourSeparatedDelta0_le_half
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) {delta0 : NNReal}
    (hdelta0 : delta0 <= (2 : NNReal)⁻¹) :
    parameterLadderFourSeparatedDelta0 P delta0 <= (2 : NNReal)⁻¹ :=
  (parameterLadderFourSeparatedDelta0_le_base P delta0).trans hdelta0

theorem parameterLadder_four_mul_delta_rpow_le_one
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    {delta0 delta : NNReal} (hdelta : 0 < delta)
    (hsmall : delta <= parameterLadderFourSeparatedDelta0 P delta0) :
    4 * (delta : ENNReal) ^ P.epsilon <= 1 := by
  apply four_mul_delta_rpow_le_one_of_le_threshold
    hdelta P.epsilon_pos
  exact hsmall.trans (min_le_right _ _)

/-- Every long interval selected below the unified threshold supplies the
geometric `4tau <= theta` premise. -/
theorem parameterLadder_four_mul_tau_le_theta_of_isLong
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    {delta0 delta : NNReal} {depth : Nat}
    (S : FiniteScaleSequence delta depth) (m : Fin depth)
    (hdelta : 0 < delta)
    (hsmall : delta <= parameterLadderFourSeparatedDelta0 P delta0)
    (hlong : S.IsLong P.epsilon m) :
    4 * S.tau m <= S.theta m := by
  exact four_mul_tau_le_theta_of_isLong S P.epsilon m hlong
    (parameterLadder_four_mul_delta_rpow_le_one P hdelta hsmall)

/-- Fixed-parameter Katz--Tao control is preserved by the unified minimum. -/
theorem KatzTaoAtParameters.at_parameterLadderFourSeparatedDelta0
    {epsilon0 beta gamma targetEpsilon eta : Real}
    (P : ParameterLadder epsilon0 beta gamma) {delta0 : NNReal}
    (hKT : KatzTaoAtParameters beta targetEpsilon eta delta0) :
    KatzTaoAtParameters beta targetEpsilon eta
      (parameterLadderFourSeparatedDelta0 P delta0) :=
  hKT.mono_delta0 (parameterLadderFourSeparatedDelta0_le_base P delta0)

/-- Fixed-parameter Frostman control is preserved by the unified minimum. -/
theorem FrostmanAtParameters.at_parameterLadderFourSeparatedDelta0
    {epsilon0 beta gamma targetEpsilon eta : Real}
    (P : ParameterLadder epsilon0 beta gamma) {delta0 : NNReal}
    (hF : FrostmanAtParameters beta targetEpsilon eta delta0) :
    FrostmanAtParameters beta targetEpsilon eta
      (parameterLadderFourSeparatedDelta0 P delta0) :=
  hF.mono_delta0 (parameterLadderFourSeparatedDelta0_le_base P delta0)

#print axioms four_mul_delta_rpow_le_one_of_le_threshold
#print axioms parameterLadder_four_mul_tau_le_theta_of_isLong
#print axioms KatzTaoAtParameters.at_parameterLadderFourSeparatedDelta0
#print axioms FrostmanAtParameters.at_parameterLadderFourSeparatedDelta0

end
end Family8ParameterLadderFourSeparationThresholdV1
