import Family8Grounding.Family8LowFreshCorrelatedPowerBudgetsV1
import Mathlib.Tactic

/-!
# Low-fresh DSO outer-loss ledger

The low fresh branch contributes the literal first loss

`2 * sourceKatzTaoFreshLoss A`

and the factor-two count comparison contributes
`2 ^ (1 - gamma / 2)`.  The correlated budget already supplies one
sixteen-bound, so these two fixed factors must be absorbed together rather
than charged separately.  This leaves the exponent

`etaKT / 2 + 2 * eta 0`,

which fits inside the official `3 * eta j` DSO allocation.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8LowFreshDSOOuterLossLedgerV1

open Family8LowFreshCorrelatedPowerBudgetsV1
open Family8ParameterLadderV1
open Family8ScaleContainedB2NativeFreshKatzTaoEndpointV1

noncomputable section

/-- Pure scalar form of the low-fresh outer-loss ledger.  The single
sixteen-budget absorbs both literal factors of two. -/
theorem lowFresh_outerLoss_le_threeEta_of_power_budgets
    {delta : NNReal} {freshLoss : ENNReal}
    {etaKT eta0 etaStage gamma : Real}
    (hdelta : 0 < delta)
    (heta0 : 0 < eta0)
    (hgamma0 : 0 <= gamma)
    (hfresh : freshLoss <=
      (delta : ENNReal) ^ (-(etaKT / 2 + eta0)))
    (hsixteen : (16 : ENNReal) <=
      (delta : ENNReal) ^ (-eta0))
    (hexponent : etaKT / 2 + 2 * eta0 <= 3 * etaStage) :
    ((2 * freshLoss) * (2 : ENNReal) ^ (1 - gamma / 2)) <=
      (delta : ENNReal) ^ (-3 * etaStage) := by
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ (∞ : ENNReal) :=
    ENNReal.coe_ne_top
  have hdOne : (delta : ENNReal) <= 1 := by
    by_contra hnot
    have honeDelta : 1 < (delta : ENNReal) := lt_of_not_ge hnot
    have hpowerLt :
        (delta : ENNReal) ^ (-eta0) < 1 :=
      ENNReal.rpow_lt_one_of_one_lt_of_neg honeDelta (by linarith)
    have himpossible : (16 : ENNReal) < 1 :=
      hsixteen.trans_lt hpowerLt
    norm_num at himpossible
  have htwoPower :
      (2 : ENNReal) ^ (1 - gamma / 2) <= 2 := by
    calc
      (2 : ENNReal) ^ (1 - gamma / 2) <=
          (2 : ENNReal) ^ (1 : Real) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := by norm_num
  have hfixed :
      (2 : ENNReal) * (2 : ENNReal) ^ (1 - gamma / 2) <= 16 := by
    calc
      (2 : ENNReal) * (2 : ENNReal) ^ (1 - gamma / 2) <=
          2 * 2 := mul_le_mul' le_rfl htwoPower
      _ <= 16 := by norm_num
  have hfixedPower :
      (2 : ENNReal) * (2 : ENNReal) ^ (1 - gamma / 2) <=
        (delta : ENNReal) ^ (-eta0) :=
    hfixed.trans hsixteen
  calc
    ((2 * freshLoss) * (2 : ENNReal) ^ (1 - gamma / 2)) =
        ((2 : ENNReal) * (2 : ENNReal) ^ (1 - gamma / 2)) *
          freshLoss := by ac_rfl
    _ <= (delta : ENNReal) ^ (-eta0) *
        (delta : ENNReal) ^ (-(etaKT / 2 + eta0)) :=
      mul_le_mul' hfixedPower hfresh
    _ = (delta : ENNReal) ^ (-(etaKT / 2 + 2 * eta0)) := by
      rw [show -(etaKT / 2 + 2 * eta0) =
        -eta0 + -(etaKT / 2 + eta0) by ring,
        ENNReal.rpow_add _ _ hd0 hdTop]
    _ <= (delta : ENNReal) ^ (-3 * etaStage) := by
      apply ENNReal.rpow_le_rpow_of_exponent_ge hdOne
      linarith

/-- Transitive form of the ladder monotonicity, kept local to this scalar
connector so it does not import a geometric Section 8 orchestration. -/
private theorem eta_zero_le_eta_of_stage_le
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (j : Nat) (hj : j <= P.N) :
    P.eta 0 <= P.eta j := by
  revert hj
  induction j with
  | zero =>
      intro _hj
      exact le_rfl
  | succ j ih =>
      intro hj
      exact (ih (by omega)).trans (P.eta_mono j (by omega))

/-- The correlated Native fresh budgets furnish exactly the aggregate loss
field required by the low branch of the loss-aware DSO record.  The usual
paper-range condition `0 <= beta` is stated explicitly: together with the
ladder gap it is the source of `0 <= gamma`, which controls the count rpow. -/
theorem lowFreshCorrelatedPowerBudgets_native_outerLoss
    {delta : NNReal} {epsilon0 beta gamma etaKT outputEta : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (j : Nat) (hj : j <= P.N)
    (hdelta : 0 < delta)
    (hbeta0 : 0 <= beta)
    (hgammaOne : gamma <= 1)
    (hetaKT : etaKT <= P.epsilon ^ 2 * P.eta 0 / 32)
    (B : LowFreshCorrelatedPowerBudgets
      delta etaKT outputEta (P.eta 0)
        ((delta : ENNReal) ^ (-(etaKT / 8)))) :
    ((2 * (sourceKatzTaoFreshLoss
          ((delta : ENNReal) ^ (-(etaKT / 8))) : ENNReal)) *
        (2 : ENNReal) ^ (1 - gamma / 2)) <=
      (delta : ENNReal) ^ (-3 * P.eta j) := by
  have hgamma0 : 0 <= gamma := by
    nlinarith [P.epsilon_gap, P.epsilon_pos]
  have hepsilonOne : P.epsilon <= 1 := by
    nlinarith [P.epsilon_gap]
  have hepsilonSqOne : P.epsilon ^ 2 <= 1 := by
    have hproduct : 0 <= P.epsilon * (1 - P.epsilon) :=
      mul_nonneg P.epsilon_pos.le (sub_nonneg.mpr hepsilonOne)
    nlinarith
  have hetaKTLeEta0 : etaKT <= P.eta 0 := by
    have hscaled : P.epsilon ^ 2 * P.eta 0 <= P.eta 0 := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hepsilonSqOne (P.eta_pos 0).le
    have hscaled0 : 0 <= P.epsilon ^ 2 * P.eta 0 :=
      mul_nonneg (sq_nonneg _) (P.eta_pos 0).le
    have hdiv : P.epsilon ^ 2 * P.eta 0 / 32 <=
        P.epsilon ^ 2 * P.eta 0 := by
      nlinarith
    exact hetaKT.trans (hdiv.trans hscaled)
  have heta0Stage : P.eta 0 <= P.eta j :=
    eta_zero_le_eta_of_stage_le P j hj
  have hexponent :
      etaKT / 2 + 2 * P.eta 0 <= 3 * P.eta j := by
    nlinarith [hetaKTLeEta0, heta0Stage, (P.eta_pos j).le]
  exact lowFresh_outerLoss_le_threeEta_of_power_budgets
    hdelta (P.eta_pos 0) hgamma0
      B.fresh_loss_budget B.sixteen_budget hexponent

#print axioms lowFresh_outerLoss_le_threeEta_of_power_budgets
#print axioms lowFreshCorrelatedPowerBudgets_native_outerLoss

end
end Family8LowFreshDSOOuterLossLedgerV1
