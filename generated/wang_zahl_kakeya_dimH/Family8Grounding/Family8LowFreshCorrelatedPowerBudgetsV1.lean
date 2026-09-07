import Family8Grounding.Family8ExplicitConcentrationFreshPowerBudgetsV4
import Family8Grounding.Family8ScaleContainedB2NativeFreshKatzTaoEndpointV1
import Family8Grounding.Family8ParameterLadderV1
import Mathlib.Tactic

/-!
# Correlated power budgets for the low fresh endpoint

The sampled Katz--Tao coefficient, its fresh loss, and the density gate must
all concern one literal coefficient.  We therefore fix

`A = delta ^ (-(etaKT / 8))`

once and prove every scalar premise needed by the low fresh endpoint below
one explicit positive threshold.  There is no selection, Katz--Tao, or
geometric hypothesis in this module.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8LowFreshCorrelatedPowerBudgetsV1

open Family8ScaleContainedB2NativeFreshKatzTaoEndpointV1
open Family8B2NormalizedConflictKatzTaoCapV6
open Family8ExplicitConcentrationFreshPowerBudgetsV4
open Family8ParameterLadderV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-- The two endpoint files use the same literal fresh-loss formula.  This
bridge keeps the low branch on its native endpoint object while reusing the
scalar estimate proved for the earlier endpoint. -/
theorem native_sourceKatzTaoFreshLoss_eq_fresh (C : ENNReal) :
    sourceKatzTaoFreshLoss C =
      Family8ScaleContainedB2FreshKatzTaoEndpointV1.sourceKatzTaoFreshLoss C := by
  rfl

/-- The finite coefficient left after replacing the literal fresh ceiling by
one copy of its sampled Katz--Tao coefficient. -/
def lowFreshReturnLossFixedConstant : ENNReal :=
  480000 * 128 + 2

theorem lowFreshReturnLossFixedConstant_ne_top :
    lowFreshReturnLossFixedConstant ≠ ∞ := by
  norm_num [lowFreshReturnLossFixedConstant]

/-- A single return-loss threshold absorbs both the fixed fresh-ceiling
coefficient and the separate factor sixteen used by the card lower bound. -/
def lowFreshReturnLossThreshold (eta0 : Real) : NNReal :=
  min
    (finiteConstantSmallDeltaThreshold
      lowFreshReturnLossFixedConstant eta0)
    (finiteConstantSmallDeltaThreshold 16 eta0)

theorem lowFreshReturnLossThreshold_pos (eta0 : Real) :
    0 < lowFreshReturnLossThreshold eta0 := by
  rw [lowFreshReturnLossThreshold, lt_min_iff]
  exact ⟨finiteConstantSmallDeltaThreshold_pos _ _,
    finiteConstantSmallDeltaThreshold_pos _ _⟩

/-- The common small-scale threshold for the density budget, the coefficient
budget, and the two return-loss estimates. -/
def lowFreshCorrelatedPowerThreshold
    (etaKT eta0 : Real) : NNReal :=
  min
    (explicitConcentrationFreshDensityThreshold (etaKT / 8))
    (min
      (explicitConcentrationFreshCoefficientThreshold (7 * etaKT / 8))
      (lowFreshReturnLossThreshold eta0))

theorem lowFreshCorrelatedPowerThreshold_pos
    (etaKT eta0 : Real) :
    0 < lowFreshCorrelatedPowerThreshold etaKT eta0 := by
  rw [lowFreshCorrelatedPowerThreshold, lt_min_iff, lt_min_iff]
  exact ⟨explicitConcentrationFreshDensityThreshold_pos _,
    explicitConcentrationFreshCoefficientThreshold_pos _,
    lowFreshReturnLossThreshold_pos _⟩

/-- The six scalar facts consumed downstream, all for the same literal `A`.
Keeping `A` as an explicit parameter makes definitional identity visible to
the eventual selection wrapper. -/
structure LowFreshCorrelatedPowerBudgets
    (delta : NNReal) (etaKT outputEta eta0 : Real) (A : ENNReal) : Prop where
  coefficient_ne_top : A ≠ ∞
  one_le_coefficient : 1 ≤ A
  coefficient_budget :
    128 * A ≤ ((delta / 8 : NNReal) : ENNReal) ^ (-etaKT)
  fresh_loss_budget :
    (sourceKatzTaoFreshLoss A : ENNReal) ≤
      (delta : ENNReal) ^ (-(etaKT / 2 + eta0))
  sixteen_budget :
    (16 : ENNReal) ≤ (delta : ENNReal) ^ (-eta0)
  density_budget :
    (((delta / 8 : NNReal) : ENNReal) ^ etaKT) *
        (2 * (128 * (sourceKatzTaoFreshLoss A : ENNReal))) ≤
      (delta : ENNReal) ^ outputEta

/-- All low-fresh scalar premises are automatic below one explicit positive
threshold.  The only inputs are positivity, the small output-exponent share,
and the paper ladder supplying the positive reserve `P.eta 0`.

The density estimate uses the V4 sampled-fresh theorem with
`sampleEta = absorbEta = etaKT / 8` and `tail = 1`; its factor `32` is then
weakened to the required factor `2`.  The coefficient estimate spends the
remaining `7 * etaKT / 8`.
-/
theorem lowFreshCorrelatedPowerBudgets_of_le_threshold
    {delta : NNReal} {epsilon0 beta gamma etaKT outputEta : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hdelta : 0 < delta)
    (hetaKT : 0 < etaKT)
    (houtputShare : 16 * outputEta ≤ etaKT)
    (hsmall : delta ≤
      lowFreshCorrelatedPowerThreshold etaKT (P.eta 0)) :
    LowFreshCorrelatedPowerBudgets delta etaKT outputEta (P.eta 0)
      ((delta : ENNReal) ^ (-(etaKT / 8))) := by
  let d : ENNReal := (delta : ENNReal)
  let A : ENNReal := d ^ (-(etaKT / 8))
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hetaEight : 0 < etaKT / 8 := by linarith
  have hetaSevenEighths : 0 < 7 * etaKT / 8 := by linarith
  have heta0 : 0 < P.eta 0 := P.eta_pos 0
  have hsmallDensity : delta ≤
      explicitConcentrationFreshDensityThreshold (etaKT / 8) :=
    hsmall.trans (min_le_left _ _)
  have hsmallCoefficient : delta ≤
      explicitConcentrationFreshCoefficientThreshold (7 * etaKT / 8) :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallReturn : delta ≤ lowFreshReturnLossThreshold (P.eta 0) :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdeltaOne : delta ≤ 1 := by
    exact hsmallDensity.trans
      (finiteConstantSmallDeltaThreshold_le_one
        explicitConcentrationFreshDensityConstant hetaEight)
  have hdOne : d ≤ 1 := by
    dsimp only [d]
    exact_mod_cast hdeltaOne
  have hAfinite : A ≠ ∞ := by
    dsimp only [A]
    exact ENNReal.rpow_ne_top_of_ne_zero hd0 hdTop
  have hAone : 1 ≤ A := by
    dsimp only [A]
    exact ENNReal.one_le_rpow_of_pos_of_le_one_of_neg
      (ENNReal.coe_pos.mpr hdelta) hdOne (by linarith)
  have hApower : A ≤ d ^ (-(etaKT / 8)) := by
    exact le_rfl
  have hcoefficient :
      128 * A ≤ ((delta / 8 : NNReal) : ENNReal) ^ (-etaKT) := by
    exact explicitConcentration_fresh_coefficient_power_budget
      hdelta hdeltaOne hetaKT.le hApower hetaSevenEighths
      hsmallCoefficient (by linarith)
  have hreturnConstant : lowFreshReturnLossFixedConstant ≤
      d ^ (-(P.eta 0)) := by
    exact finiteConstant_le_delta_negativePower
      lowFreshReturnLossFixedConstant_ne_top heta0 hdelta
        (hsmallReturn.trans (min_le_left _ _))
  have hfreshSharp : (sourceKatzTaoFreshLoss A : ENNReal) ≤
      d ^ (-(etaKT / 8 + P.eta 0)) := by
    calc
      (sourceKatzTaoFreshLoss A : ENNReal) ≤
          lowFreshReturnLossFixedConstant * A := by
        simpa only [lowFreshReturnLossFixedConstant,
          native_sourceKatzTaoFreshLoss_eq_fresh] using
          (sourceKatzTaoFreshLoss_coe_le_fixed_mul hAfinite hAone)
      _ ≤ d ^ (-(P.eta 0)) * d ^ (-(etaKT / 8)) :=
        mul_le_mul' hreturnConstant le_rfl
      _ = d ^ (-(etaKT / 8 + P.eta 0)) := by
        rw [show -(etaKT / 8 + P.eta 0) =
          -(P.eta 0) + -(etaKT / 8) by ring,
          ENNReal.rpow_add _ _ hd0 hdTop]
  have hfresh : (sourceKatzTaoFreshLoss A : ENNReal) ≤
      d ^ (-(etaKT / 2 + P.eta 0)) := by
    exact hfreshSharp.trans
      (ENNReal.rpow_le_rpow_of_exponent_ge hdOne (by linarith))
  have hsixteen : (16 : ENNReal) ≤ d ^ (-(P.eta 0)) := by
    exact finiteConstant_le_delta_negativePower (by norm_num) heta0 hdelta
      (hsmallReturn.trans (min_le_right _ _))
  have hdensityThirtyTwo :
      ((((delta / 8 : NNReal) : ENNReal) ^ etaKT) *
          (128 * (sourceKatzTaoFreshLoss A : ENNReal))) *
        (32 * (1 : ENNReal)) ≤ d ^ outputEta := by
    simpa only [native_sourceKatzTaoFreshLoss_eq_fresh] using
      (explicitConcentration_fresh_density_power_budget
        (targetEta := etaKT) (sampleEta := etaKT / 8)
        (sourceEta := outputEta) (absorbEta := etaKT / 8)
        (Csample := A) (tail := 1)
        hdelta hdeltaOne hetaKT.le hAfinite hAone hAone hApower
        hetaEight hsmallDensity (by linarith))
  have hdensity :
      (((delta / 8 : NNReal) : ENNReal) ^ etaKT) *
          (2 * (128 * (sourceKatzTaoFreshLoss A : ENNReal))) ≤
        d ^ outputEta := by
    calc
      (((delta / 8 : NNReal) : ENNReal) ^ etaKT) *
          (2 * (128 * (sourceKatzTaoFreshLoss A : ENNReal))) =
        ((((delta / 8 : NNReal) : ENNReal) ^ etaKT) *
          (128 * (sourceKatzTaoFreshLoss A : ENNReal))) * 2 := by ring
      _ ≤ ((((delta / 8 : NNReal) : ENNReal) ^ etaKT) *
          (128 * (sourceKatzTaoFreshLoss A : ENNReal))) *
          (32 * (1 : ENNReal)) := by
        exact mul_le_mul' le_rfl (by norm_num)
      _ ≤ d ^ outputEta := hdensityThirtyTwo
  exact {
    coefficient_ne_top := hAfinite
    one_le_coefficient := hAone
    coefficient_budget := hcoefficient
    fresh_loss_budget := hfresh
    sixteen_budget := hsixteen
    density_budget := hdensity
  }

#print axioms lowFreshReturnLossFixedConstant_ne_top
#print axioms native_sourceKatzTaoFreshLoss_eq_fresh
#print axioms lowFreshReturnLossThreshold_pos
#print axioms lowFreshCorrelatedPowerThreshold_pos
#print axioms lowFreshCorrelatedPowerBudgets_of_le_threshold

end
end Family8LowFreshCorrelatedPowerBudgetsV1
