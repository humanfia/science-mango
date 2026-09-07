import Family8Grounding.Family8MassRetainingNormalizedSelectedKatzTaoEndpointV4
import Family8Grounding.Family8ExplicitConcentrationFreshPowerBudgetsV4
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

/-!
# Generic power budgets for a mass-retaining normalized selection

This add-only successor does not import the failed V1--V2 rewriting drafts.
It absorbs the selected-mass loss and the fixed normalization factor `128`
below one explicit positive small-scale threshold.
-/

open scoped ENNReal NNReal

namespace Family8MassRetainingNormalizedSelectedKatzTaoGenericPowerBudgetsV3

open Family8ExplicitConcentrationFreshPowerBudgetsV4
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

def massRetainingNormalizedSelectedScalarThreshold
    (densityAbsorbEta coefficientAbsorbEta : Real) : NNReal :=
  min
    (finiteConstantSmallDeltaThreshold 128 densityAbsorbEta)
    (finiteConstantSmallDeltaThreshold 128 coefficientAbsorbEta)

theorem massRetainingNormalizedSelectedScalarThreshold_pos
    (densityAbsorbEta coefficientAbsorbEta : Real) :
    0 < massRetainingNormalizedSelectedScalarThreshold
      densityAbsorbEta coefficientAbsorbEta := by
  rw [massRetainingNormalizedSelectedScalarThreshold, lt_min_iff]
  exact ⟨finiteConstantSmallDeltaThreshold_pos _ _,
    finiteConstantSmallDeltaThreshold_pos _ _⟩

/-- A power cap on the literal selected-mass loss gives the exact density
budget exposed by the same-selected endpoint. -/
theorem normalizedSelected_density_budget_of_power
    {delta : NNReal} {loss : Nat}
    {targetEta lossEta sourceEta densityAbsorbEta coefficientAbsorbEta : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (htargetEta : 0 ≤ targetEta)
    (hloss : (loss : ENNReal) ≤ (delta : ENNReal) ^ (-lossEta))
    (hdensityAbsorbEta : 0 < densityAbsorbEta)
    (hsmall : delta ≤ massRetainingNormalizedSelectedScalarThreshold
      densityAbsorbEta coefficientAbsorbEta)
    (hbudget : sourceEta + lossEta + densityAbsorbEta ≤ targetEta) :
    (((delta / 8 : NNReal) : ENNReal) ^ targetEta) *
        (128 * (loss : ENNReal)) ≤
      (delta : ENNReal) ^ sourceEta := by
  let d : ENNReal := (delta : ENNReal)
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hdOne : d ≤ 1 := by
    dsimp only [d]
    exact_mod_cast hdeltaOne
  have hscale : (((delta / 8 : NNReal) : ENNReal)) ≤ d := by
    dsimp only [d]
    exact_mod_cast
      (div_le_self (show 0 ≤ delta from bot_le)
        (by norm_num : (1 : NNReal) ≤ 8))
  have hscalePower :
      (((delta / 8 : NNReal) : ENNReal) ^ targetEta) ≤ d ^ targetEta :=
    ENNReal.rpow_le_rpow hscale htargetEta
  have hconstant : (128 : ENNReal) ≤ d ^ (-densityAbsorbEta) := by
    exact finiteConstant_le_delta_negativePower (by norm_num)
      hdensityAbsorbEta hdelta
      (hsmall.trans (min_le_left _ _))
  have hfinalPower :
      d ^ (targetEta - densityAbsorbEta - lossEta) ≤ d ^ sourceEta :=
    ENNReal.rpow_le_rpow_of_exponent_ge hdOne (by linarith)
  calc
    (((delta / 8 : NNReal) : ENNReal) ^ targetEta) *
          (128 * (loss : ENNReal)) ≤
        d ^ targetEta *
          (d ^ (-densityAbsorbEta) * d ^ (-lossEta)) := by
      exact mul_le_mul' hscalePower (mul_le_mul' hconstant hloss)
    _ = (d ^ targetEta * d ^ (-densityAbsorbEta)) *
          d ^ (-lossEta) := by ac_rfl
    _ = d ^ (targetEta + (-densityAbsorbEta)) *
          d ^ (-lossEta) := by
      congr 1
      exact (ENNReal.rpow_add targetEta (-densityAbsorbEta)
        hd0 hdTop).symm
    _ = d ^ (targetEta - densityAbsorbEta - lossEta) := by
      exact (ENNReal.rpow_add
        (targetEta - densityAbsorbEta) (-lossEta) hd0 hdTop).symm
    _ ≤ d ^ sourceEta := hfinalPower

/-- A power cap on the pre-normalization Katz--Tao constant gives the exact
coefficient budget exposed by the same-selected endpoint. -/
theorem normalizedSelected_coefficient_budget_of_power
    {delta : NNReal} {C : ENNReal}
    {targetEta coefficientEta densityAbsorbEta coefficientAbsorbEta : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (htargetEta : 0 ≤ targetEta)
    (hCpower : C ≤ (delta : ENNReal) ^ (-coefficientEta))
    (hcoefficientAbsorbEta : 0 < coefficientAbsorbEta)
    (hsmall : delta ≤ massRetainingNormalizedSelectedScalarThreshold
      densityAbsorbEta coefficientAbsorbEta)
    (hbudget : coefficientEta + coefficientAbsorbEta ≤ targetEta) :
    128 * C ≤
      ((delta / 8 : NNReal) : ENNReal) ^ (-targetEta) := by
  exact explicitConcentration_fresh_coefficient_power_budget
    hdelta hdeltaOne htargetEta hCpower hcoefficientAbsorbEta
      (by
        simpa [explicitConcentrationFreshCoefficientThreshold,
          massRetainingNormalizedSelectedScalarThreshold] using
            hsmall.trans (min_le_right _ _))
      hbudget

/-- Both numerical endpoint budgets at once. -/
theorem normalizedSelected_scalar_budgets_of_power
    {delta : NNReal} {loss : Nat} {C sourceDensity : ENNReal}
    {targetEta lossEta sourceEta coefficientEta
      densityAbsorbEta coefficientAbsorbEta : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (htargetEta : 0 ≤ targetEta)
    (hloss : (loss : ENNReal) ≤ (delta : ENNReal) ^ (-lossEta))
    (hsourceDensity : (delta : ENNReal) ^ sourceEta ≤ sourceDensity)
    (hCpower : C ≤ (delta : ENNReal) ^ (-coefficientEta))
    (hdensityAbsorbEta : 0 < densityAbsorbEta)
    (hcoefficientAbsorbEta : 0 < coefficientAbsorbEta)
    (hsmall : delta ≤ massRetainingNormalizedSelectedScalarThreshold
      densityAbsorbEta coefficientAbsorbEta)
    (hdensityBudget :
      sourceEta + lossEta + densityAbsorbEta ≤ targetEta)
    (hcoefficientBudget :
      coefficientEta + coefficientAbsorbEta ≤ targetEta) :
    ((((delta / 8 : NNReal) : ENNReal) ^ targetEta) *
          (128 * (loss : ENNReal)) ≤ sourceDensity) ∧
      (128 * C ≤
        ((delta / 8 : NNReal) : ENNReal) ^ (-targetEta)) := by
  refine ⟨?_, ?_⟩
  · exact (normalizedSelected_density_budget_of_power
      hdelta hdeltaOne htargetEta hloss hdensityAbsorbEta hsmall
        hdensityBudget).trans hsourceDensity
  · exact normalizedSelected_coefficient_budget_of_power
      hdelta hdeltaOne htargetEta hCpower hcoefficientAbsorbEta hsmall
        hcoefficientBudget

#print axioms massRetainingNormalizedSelectedScalarThreshold_pos
#print axioms normalizedSelected_density_budget_of_power
#print axioms normalizedSelected_coefficient_budget_of_power
#print axioms normalizedSelected_scalar_budgets_of_power

end
end Family8MassRetainingNormalizedSelectedKatzTaoGenericPowerBudgetsV3
