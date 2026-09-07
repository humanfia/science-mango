import Family8Grounding.Family8ParameterLadderV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Family8LowFreshCardScaleParameterLadderBudgetV1

open Family8ParameterLadderV1

private theorem eta_zero_le_eta_of_stage_le
    {epsilon0 beta gamma : ℝ}
    (P : ParameterLadder epsilon0 beta gamma)
    (stage : ℕ)
    (hstage : stage ≤ P.N) :
    P.eta 0 ≤ P.eta stage := by
  revert hstage
  induction stage with
  | zero =>
      intro _hstage
      exact le_rfl
  | succ j ih =>
      intro hstage
      exact (ih (by omega)).trans (P.eta_mono j (by omega))

/--
The low-gate exponent ledger needed to absorb the source-mass exponent, the
`etaKT / 2` fresh-loss allowance, and two `eta 0`-scale constants into the
stage output exponent.
-/
theorem lowGate_freshCardScale_exponent_budget
    {epsilon0 beta gamma etaSource etaKT : ℝ}
    (P : ParameterLadder epsilon0 beta gamma)
    (stage : ℕ)
    (hstage : stage ≤ P.N)
    (hbeta : 0 < beta)
    (hlow : gamma ≤ (2 : ℝ) / 3)
    (hetaSource : etaSource ≤ P.eta 0)
    (hetaKT : etaKT ≤ P.epsilon ^ 2 * P.eta 0 / 32) :
    2 * etaSource + etaKT / 2 + P.eta 0 + P.eta 0 ≤
      10 * P.eta stage / (P.epsilon * beta) := by
  have heta0 : 0 < P.eta 0 := P.eta_pos 0
  have hetaStage : 0 < P.eta stage := P.eta_pos stage
  have hepsilonOne : P.epsilon ≤ 1 := by
    nlinarith [P.epsilon_gap, hlow, hbeta]
  have hbetaOne : beta ≤ 1 := by
    nlinarith [P.epsilon_gap, P.epsilon_pos, hlow]
  have hepsilonBetaOne : P.epsilon * beta ≤ 1 := by
    calc
      P.epsilon * beta ≤ 1 * 1 :=
        mul_le_mul hepsilonOne hbetaOne hbeta.le (by norm_num)
      _ = 1 := by norm_num
  have hepsilonSqOne : P.epsilon ^ 2 ≤ 1 := by
    have hmul : 0 ≤ P.epsilon * (1 - P.epsilon) :=
      mul_nonneg P.epsilon_pos.le (sub_nonneg.mpr hepsilonOne)
    nlinarith
  have hcapLeEta0 : P.epsilon ^ 2 * P.eta 0 / 32 ≤ P.eta 0 := by
    have hscaled := mul_le_mul_of_nonneg_right hepsilonSqOne heta0.le
    nlinarith
  have hetaKT0 : etaKT ≤ P.eta 0 := hetaKT.trans hcapLeEta0
  have heta0Stage : P.eta 0 ≤ P.eta stage :=
    eta_zero_le_eta_of_stage_le P stage hstage
  have hcost :
      2 * etaSource + etaKT / 2 + P.eta 0 + P.eta 0 ≤
        5 * P.eta stage := by
    nlinarith
  have hden : 0 < P.epsilon * beta := mul_pos P.epsilon_pos hbeta
  have hten :
      10 * P.eta stage ≤ 10 * P.eta stage / (P.epsilon * beta) := by
    apply (le_div_iff₀ hden).2
    calc
      (10 * P.eta stage) * (P.epsilon * beta) ≤
          (10 * P.eta stage) * 1 :=
        mul_le_mul_of_nonneg_left hepsilonBetaOne (by positivity)
      _ = 10 * P.eta stage := by ring
  calc
    2 * etaSource + etaKT / 2 + P.eta 0 + P.eta 0 ≤
        5 * P.eta stage := hcost
    _ ≤ 10 * P.eta stage := by nlinarith
    _ ≤ 10 * P.eta stage / (P.epsilon * beta) := hten

/--
The same fresh-card exponent ledger in the full paper range `gamma <= 1`.
The older low-gamma theorem used `gamma <= 2 / 3` only to bound both
`epsilon` and `beta` by one.  The parameter-ladder gap and `0 < beta`
already give those two bounds from `gamma <= 1`, so no low/high gamma split
is needed by this scalar estimate.
-/
theorem lowGate_freshCardScale_exponent_budget_of_gamma_le_one
    {epsilon0 beta gamma etaSource etaKT : ℝ}
    (P : ParameterLadder epsilon0 beta gamma)
    (stage : ℕ)
    (hstage : stage ≤ P.N)
    (hbeta : 0 < beta)
    (hgammaOne : gamma ≤ 1)
    (hetaSource : etaSource ≤ P.eta 0)
    (hetaKT : etaKT ≤ P.epsilon ^ 2 * P.eta 0 / 32) :
    2 * etaSource + etaKT / 2 + P.eta 0 + P.eta 0 ≤
      10 * P.eta stage / (P.epsilon * beta) := by
  have heta0 : 0 < P.eta 0 := P.eta_pos 0
  have hetaStage : 0 < P.eta stage := P.eta_pos stage
  have hepsilonOne : P.epsilon ≤ 1 := by
    nlinarith [P.epsilon_gap, hgammaOne, hbeta]
  have hbetaOne : beta ≤ 1 := by
    nlinarith [P.epsilon_gap, P.epsilon_pos, hgammaOne]
  have hepsilonBetaOne : P.epsilon * beta ≤ 1 := by
    calc
      P.epsilon * beta ≤ 1 * 1 :=
        mul_le_mul hepsilonOne hbetaOne hbeta.le (by norm_num)
      _ = 1 := by norm_num
  have hepsilonSqOne : P.epsilon ^ 2 ≤ 1 := by
    have hmul : 0 ≤ P.epsilon * (1 - P.epsilon) :=
      mul_nonneg P.epsilon_pos.le (sub_nonneg.mpr hepsilonOne)
    nlinarith
  have hcapLeEta0 : P.epsilon ^ 2 * P.eta 0 / 32 ≤ P.eta 0 := by
    have hscaled := mul_le_mul_of_nonneg_right hepsilonSqOne heta0.le
    nlinarith
  have hetaKT0 : etaKT ≤ P.eta 0 := hetaKT.trans hcapLeEta0
  have heta0Stage : P.eta 0 ≤ P.eta stage :=
    eta_zero_le_eta_of_stage_le P stage hstage
  have hcost :
      2 * etaSource + etaKT / 2 + P.eta 0 + P.eta 0 ≤
        5 * P.eta stage := by
    nlinarith
  have hden : 0 < P.epsilon * beta := mul_pos P.epsilon_pos hbeta
  have hten :
      10 * P.eta stage ≤ 10 * P.eta stage / (P.epsilon * beta) := by
    apply (le_div_iff₀ hden).2
    calc
      (10 * P.eta stage) * (P.epsilon * beta) ≤
          (10 * P.eta stage) * 1 :=
        mul_le_mul_of_nonneg_left hepsilonBetaOne (by positivity)
      _ = 10 * P.eta stage := by ring
  calc
    2 * etaSource + etaKT / 2 + P.eta 0 + P.eta 0 ≤
        5 * P.eta stage := hcost
    _ ≤ 10 * P.eta stage := by nlinarith
    _ ≤ 10 * P.eta stage / (P.epsilon * beta) := hten

#print axioms lowGate_freshCardScale_exponent_budget
#print axioms lowGate_freshCardScale_exponent_budget_of_gamma_le_one

end Family8LowFreshCardScaleParameterLadderBudgetV1
