import Family8Grounding.Family8FrostmanRHSScaleVolumeAlgebraV8
import Family8Grounding.Family8ParameterLadderV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8Section8FixedPositiveSelfImprovementBudgetV3

open Family8KatzTaoFrostmanPropertiesV1
open Family8FrostmanRHSScaleVolumeAlgebraV8
open Family8ParameterLadderV1

noncomputable section

/-!
# The fixed-positive numerical gate in Section 8

In the official Main Lemma 1 bootstrap, the two outside Frostman estimates
cost three copies of the current ladder exponent, while the middle interval
estimate gains ten copies.  The exponent decrement must be selected before
the datum and dividing stage are known.

This file formalizes that numerical step.  Its final theorem assumes only the
honest scalar output `outerLoss <= delta^(-3 eta_stage)`, the literal middle
gain, and a genuine source-volume floor.  It neither assumes the desired RHS
nor derives nonzero mass from admissibility of a possibly empty datum.

V1 and V2 are failed notation/API drafts and are not imported.
-/

/-- A decrement chosen once, at the smallest zero-indexed ladder level. -/
def sectionEightFixedNu
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) : Real :=
  P.eta 0

/-- Transitive form of the adjacent monotonicity stored by the ladder. -/
theorem eta_zero_le_eta_of_stage_le
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    (hj : j <= P.N) :
    P.eta 0 <= P.eta j := by
  revert hj
  induction j with
  | zero =>
      intro _hj
      exact le_rfl
  | succ j ih =>
      intro hj
      exact (ih (by omega)).trans (P.eta_mono j (by omega))

theorem sectionEightFixedNu_pos
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) :
    0 < sectionEightFixedNu P := by
  exact P.eta_pos 0

/-- In the paper range `0 <= beta < gamma <= 1`, the smallest volume-floor
exponent is at most two. -/
theorem eta_zero_le_two
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 <= beta) (hgamma : gamma <= 1) :
    P.eta 0 <= 2 := by
  have hgapUpper : gamma - beta <= 1 := by linarith
  have hepsilonUpper : P.epsilon < 1 / 16 := by
    nlinarith [P.epsilon_gap]
  have heta := P.eta_le_epsilon_div_five 0
  linarith

/-- The fixed exponent-shift cost is at most three copies of every possible
stage exponent. -/
theorem fixedNu_shift_cost_le_three_eta_stage
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    (hj : j <= P.N) (hbeta : 0 <= beta) (hgamma : gamma <= 1) :
    2 * sectionEightFixedNu P +
        P.eta 0 * sectionEightFixedNu P / 2 <=
      3 * P.eta j := by
  have hnu0 : 0 <= P.eta 0 := (P.eta_pos 0).le
  have hnuStage : P.eta 0 <= P.eta j :=
    eta_zero_le_eta_of_stage_le P j hj
  have hnuTwo : P.eta 0 <= 2 := eta_zero_le_two P hbeta hgamma
  have hsquare : P.eta 0 * P.eta 0 / 2 <= P.eta 0 := by
    nlinarith
  dsimp only [sectionEightFixedNu]
  nlinarith

/-- The official `3 eta_stage` outside loss plus the fixed exponent-shift
cost is absorbed by the `10 eta_stage` middle gain. -/
theorem three_loss_add_fixedNu_cost_le_ten_gain
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    (hj : j <= P.N) (hbeta : 0 <= beta) (hgamma : gamma <= 1) :
    3 * P.eta j +
        (2 * sectionEightFixedNu P +
          P.eta 0 * sectionEightFixedNu P / 2) <=
      10 * P.eta j := by
  have hcost := fixedNu_shift_cost_le_three_eta_stage
    P j hj hbeta hgamma
  have heta : 0 <= P.eta j := (P.eta_pos j).le
  linarith

/-! ## Gain-aware Frostman RHS transport -/

/-- A genuinely positive small-scale power pays for a fixed exponent
decrement.  Thus `2 * nu` need not fit inside an arbitrarily small epsilon
gap, unlike the direct loss-only route. -/
theorem scalar_mul_frostmanMultiplicityRHS_le_improved_of_positive_power_gain
    {delta : NNReal} {actualVolume scalar : ENNReal}
    {sourceEpsilon targetEpsilon gamma nu gain lambda : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (hvolumeTop : Ne actualVolume (⊤ : ENNReal))
    (hscalar : scalar <= (delta : ENNReal) ^ gain)
    (hvolume : (delta : ENNReal) ^ lambda <= actualVolume)
    (hnu : 0 <= nu)
    (hsourceTarget : sourceEpsilon <= targetEpsilon)
    (hcost : 2 * nu + lambda * nu / 2 <= gain) :
    scalar *
        frostmanMultiplicityRHS delta actualVolume sourceEpsilon gamma <=
      frostmanMultiplicityRHS delta actualVolume targetEpsilon
        (gamma - nu) := by
  have hscalar' :
      scalar <= (delta : ENNReal) ^ (-(-gain)) := by
    simpa only [neg_neg] using hscalar
  apply scalar_mul_frostmanMultiplicityRHS_le_improved_of_power_budgets
    hdelta hdeltaOne hvolumeTop
    (kappa := -gain) hscalar' hvolume hnu
  linarith

/-- Three copies of outside loss times ten copies of middle gain leave the
positive power `delta^(7 eta_stage)`. -/
theorem three_eta_loss_mul_ten_eta_gain_le_seven_eta_gain
    {delta : NNReal} {outerLoss : ENNReal} {etaStage : Real}
    (hdelta : 0 < delta)
    (houter : outerLoss <=
      (delta : ENNReal) ^ (-3 * etaStage)) :
    outerLoss * (delta : ENNReal) ^ (10 * etaStage) <=
      (delta : ENNReal) ^ (7 * etaStage) := by
  have hd0 : Ne (delta : ENNReal) 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : Ne (delta : ENNReal) (⊤ : ENNReal) := ENNReal.coe_ne_top
  calc
    outerLoss * (delta : ENNReal) ^ (10 * etaStage) <=
        (delta : ENNReal) ^ (-3 * etaStage) *
          (delta : ENNReal) ^ (10 * etaStage) :=
      mul_le_mul' houter le_rfl
    _ = (delta : ENNReal) ^
        ((-3 * etaStage) + (10 * etaStage)) :=
      (ENNReal.rpow_add (-3 * etaStage)
        (10 * etaStage) hd0 hdTop).symm
    _ = (delta : ENNReal) ^ (7 * etaStage) := by
      congr 1
      ring

/-- The final official Section 8 scalar gate.  The decrement is positive and
independent of the stage, scale, and datum.  The remaining premises are the
honest outside-loss estimate and source-volume floor. -/
theorem sectionEight_outerThree_middleTen_fixedPositive_improvement
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    (hj : j <= P.N) (hbeta : 0 <= beta) (hgamma : gamma <= 1)
    {delta : NNReal} {actualVolume outerLoss : ENNReal}
    {sourceEpsilon targetEpsilon : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (hvolumeTop : Ne actualVolume (⊤ : ENNReal))
    (hvolume : (delta : ENNReal) ^ (P.eta 0) <= actualVolume)
    (houter : outerLoss <=
      (delta : ENNReal) ^ (-3 * P.eta j))
    (hsourceTarget : sourceEpsilon <= targetEpsilon) :
    (outerLoss * (delta : ENNReal) ^ (10 * P.eta j)) *
        frostmanMultiplicityRHS delta actualVolume sourceEpsilon gamma <=
      frostmanMultiplicityRHS delta actualVolume targetEpsilon
        (gamma - sectionEightFixedNu P) := by
  have hscalar :
      outerLoss * (delta : ENNReal) ^ (10 * P.eta j) <=
        (delta : ENNReal) ^ (7 * P.eta j) :=
    three_eta_loss_mul_ten_eta_gain_le_seven_eta_gain hdelta houter
  have hshift := fixedNu_shift_cost_le_three_eta_stage
    P j hj hbeta hgamma
  have heta : 0 <= P.eta j := (P.eta_pos j).le
  have hcost :
      2 * sectionEightFixedNu P +
          P.eta 0 * sectionEightFixedNu P / 2 <=
        7 * P.eta j := by
    linarith
  exact
    scalar_mul_frostmanMultiplicityRHS_le_improved_of_positive_power_gain
      hdelta hdeltaOne hvolumeTop hscalar hvolume
      (sectionEightFixedNu_pos P).le hsourceTarget hcost

#print axioms eta_zero_le_eta_of_stage_le
#print axioms sectionEightFixedNu_pos
#print axioms three_loss_add_fixedNu_cost_le_ten_gain
#print axioms
  scalar_mul_frostmanMultiplicityRHS_le_improved_of_positive_power_gain
#print axioms three_eta_loss_mul_ten_eta_gain_le_seven_eta_gain
#print axioms
  sectionEight_outerThree_middleTen_fixedPositive_improvement

end

end Family8Section8FixedPositiveSelfImprovementBudgetV3
