import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

/-!
# Power-envelope discharge of the logarithmic selected scalar budgets

The two structural budget bridges leave fixed numerical constants.  This
file absorbs those constants at a uniform small scale and reduces the inputs
to the paper-sized power envelopes for retained source mass and cover loss.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open scoped ENNReal NNReal

namespace Family8LogarithmicSelectedScalarPowerBudgetsV1

open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-- Uniform threshold for the fixed `131072 * 2^2` fine-card constant. -/
def fineSourceScalarThreshold (absorbExponent : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold (131072 * 4) absorbExponent

theorem fineSourceScalarThreshold_pos (absorbExponent : Real) :
    0 < fineSourceScalarThreshold absorbExponent :=
  finiteConstantSmallDeltaThreshold_pos _ _

/-- A power bound for `retainLoss * sourceA`, together with a retained source
mass floor, implies the exact first scalar absorption for logarithmic
branching (`q = 2`). -/
theorem fineSource_scalarAbsorption_of_powerEnvelopes
    {d : NNReal} {retainLoss : Nat} {sourceA sourceMass : ENNReal}
    {sourceExponent coefficientExponent absorbExponent baseExponent : Real}
    (hd : 0 < d) (hdOne : d <= 1)
    (habsorbExponent : 0 < absorbExponent)
    (hdSmall : d <= fineSourceScalarThreshold absorbExponent)
    (hcoefficient :
      (retainLoss : ENNReal) * sourceA <=
        (d : ENNReal) ^ (-coefficientExponent))
    (hsourceMass : (d : ENNReal) ^ sourceExponent <= sourceMass)
    (hexponent :
      sourceExponent + coefficientExponent + absorbExponent <= baseExponent) :
    (131072 : ENNReal) * (retainLoss : ENNReal) * (2 : ENNReal) ^ 2 *
        sourceA <=
      (d : ENNReal) ^ (-baseExponent) * sourceMass := by
  have hd0 : (d : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hd.ne'
  have hdTop : (d : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hdOneENN : (d : ENNReal) <= 1 := by exact_mod_cast hdOne
  have hfixed : (131072 * 4 : ENNReal) <=
      (d : ENNReal) ^ (-absorbExponent) :=
    finiteConstant_le_delta_negativePower (by norm_num)
      habsorbExponent hd hdSmall
  calc
    (131072 : ENNReal) * (retainLoss : ENNReal) * (2 : ENNReal) ^ 2 *
        sourceA =
      (131072 * 4 : ENNReal) * ((retainLoss : ENNReal) * sourceA) := by
        norm_num
        ring
    _ <= (d : ENNReal) ^ (-absorbExponent) *
        (d : ENNReal) ^ (-coefficientExponent) :=
      mul_le_mul' hfixed hcoefficient
    _ = (d : ENNReal) ^ (-(absorbExponent + coefficientExponent)) := by
      rw [show -(absorbExponent + coefficientExponent) =
        -absorbExponent + -coefficientExponent by ring,
        ENNReal.rpow_add _ _ hd0 hdTop]
    _ <= (d : ENNReal) ^ (sourceExponent - baseExponent) := by
      apply ENNReal.rpow_le_rpow_of_exponent_ge hdOneENN
      linarith
    _ = (d : ENNReal) ^ (-baseExponent) *
        (d : ENNReal) ^ sourceExponent := by
      rw [show sourceExponent - baseExponent =
        -baseExponent + sourceExponent by ring,
        ENNReal.rpow_add _ _ hd0 hdTop]
    _ <= (d : ENNReal) ^ (-baseExponent) * sourceMass :=
      mul_le_mul' le_rfl hsourceMass

/-- Uniform threshold for the fixed `524288 * 2^2` branching constant. -/
def branchingScalarThreshold (absorbExponent : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold (524288 * 4) absorbExponent

theorem branchingScalarThreshold_pos (absorbExponent : Real) :
    0 < branchingScalarThreshold absorbExponent :=
  finiteConstantSmallDeltaThreshold_pos _ _

/-- A power envelope for the honest AlmostCover loss implies the exact
second scalar absorption for logarithmic branching (`q = 2`). -/
theorem branching_scalarAbsorption_of_powerEnvelope
    {d : NNReal} {coverLoss : ENNReal}
    {coverExponent absorbExponent longExponent : Real}
    (hd : 0 < d) (hdOne : d <= 1)
    (habsorbExponent : 0 < absorbExponent)
    (hdSmall : d <= branchingScalarThreshold absorbExponent)
    (hcover : coverLoss <= (d : ENNReal) ^ (-coverExponent))
    (hexponent : coverExponent + absorbExponent <= longExponent) :
    (524288 : ENNReal) * coverLoss * (2 : ENNReal) ^ 2 <=
      (d : ENNReal) ^ (-longExponent) := by
  have hd0 : (d : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hd.ne'
  have hdTop : (d : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hdOneENN : (d : ENNReal) <= 1 := by exact_mod_cast hdOne
  have hfixed : (524288 * 4 : ENNReal) <=
      (d : ENNReal) ^ (-absorbExponent) :=
    finiteConstant_le_delta_negativePower (by norm_num)
      habsorbExponent hd hdSmall
  calc
    (524288 : ENNReal) * coverLoss * (2 : ENNReal) ^ 2 =
        (524288 * 4 : ENNReal) * coverLoss := by
      norm_num
      ring
    _ <= (d : ENNReal) ^ (-absorbExponent) *
        (d : ENNReal) ^ (-coverExponent) := mul_le_mul' hfixed hcover
    _ = (d : ENNReal) ^ (-(absorbExponent + coverExponent)) := by
      rw [show -(absorbExponent + coverExponent) =
        -absorbExponent + -coverExponent by ring,
        ENNReal.rpow_add _ _ hd0 hdTop]
    _ <= (d : ENNReal) ^ (-longExponent) := by
      apply ENNReal.rpow_le_rpow_of_exponent_ge hdOneENN
      linarith

end

end Family8LogarithmicSelectedScalarPowerBudgetsV1
