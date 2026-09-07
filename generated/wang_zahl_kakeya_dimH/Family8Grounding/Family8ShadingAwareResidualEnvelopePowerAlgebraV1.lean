import Family8Grounding.Family8CardWeightedEq46CoefficientPowerEnvelopeV1
import Mathlib.Tactic

/-!
# Scalar power algebra for the shading-aware Equation (46) residual

This file combines independently produced power bounds for the literal
selection/fibre cap, the intermediate radius, assembly loss, selected-parent
cardinality, and Katz--Tao constant.  The second theorem feeds the resulting
coefficient into the actual low-beta residual and the source Frostman mass
floor.  It neither assumes nor packages an Equation (46) budget.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open scoped ENNReal NNReal

namespace Family8ShadingAwareResidualEnvelopePowerAlgebraV1

noncomputable section

/-- Product of the five literal shading-aware Eq46 coefficients is controlled
by the sum of their delta-power exponents. -/
theorem shadingAwareEq46Coefficient_le_delta_negativePower
    {delta rho : NNReal} {sourceCap loss parentCard KT : ENNReal}
    {sourceCapExponent rhoExponent lossExponent parentExponent
      ktExponent : Real}
    (hdelta : 0 < delta) (hdeltaRho : delta ≤ rho)
    (hrhoExponent : 0 ≤ rhoExponent)
    (hsourceCap : sourceCap ≤
      (delta : ENNReal) ^ (-sourceCapExponent))
    (hloss : loss ≤ (delta : ENNReal) ^ (-lossExponent))
    (hparentCard : parentCard ≤
      (delta : ENNReal) ^ (-parentExponent))
    (hKT : KT ≤ (delta : ENNReal) ^ (-ktExponent)) :
    sourceCap *
        ((rho : ENNReal) ^ (-rhoExponent) *
          (loss * parentCard * KT)) ≤
      (delta : ENNReal) ^
        (-(sourceCapExponent + rhoExponent + lossExponent +
          parentExponent + ktExponent)) := by
  have hrho : 0 < rho := hdelta.trans_le hdeltaRho
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hrhoPowerNN : rho ^ (-rhoExponent) ≤
      delta ^ (-rhoExponent) :=
    NNReal.rpow_le_rpow_of_nonpos hdelta hdeltaRho
      (neg_nonpos.mpr hrhoExponent)
  have hrhoPower : (rho : ENNReal) ^ (-rhoExponent) ≤
      (delta : ENNReal) ^ (-rhoExponent) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hrho.ne' (-rhoExponent),
      ← ENNReal.coe_rpow_of_ne_zero hdelta.ne' (-rhoExponent)]
    exact ENNReal.coe_le_coe.mpr hrhoPowerNN
  calc
    sourceCap *
        ((rho : ENNReal) ^ (-rhoExponent) *
          (loss * parentCard * KT)) =
      sourceCap *
        ((rho : ENNReal) ^ (-rhoExponent) *
          (loss * (parentCard * KT))) := by ac_rfl
    _ ≤
      (delta : ENNReal) ^ (-sourceCapExponent) *
        ((delta : ENNReal) ^ (-rhoExponent) *
          ((delta : ENNReal) ^ (-lossExponent) *
            ((delta : ENNReal) ^ (-parentExponent) *
              (delta : ENNReal) ^ (-ktExponent)))) := by
        exact mul_le_mul' hsourceCap
          (mul_le_mul' hrhoPower
            (mul_le_mul' hloss (mul_le_mul' hparentCard hKT)))
    _ = (delta : ENNReal) ^
        (-(sourceCapExponent + rhoExponent + lossExponent +
          parentExponent + ktExponent)) := by
      rw [← ENNReal.rpow_add _ _ hd0 hdTop,
        ← ENNReal.rpow_add _ _ hd0 hdTop,
        ← ENNReal.rpow_add _ _ hd0 hdTop,
        ← ENNReal.rpow_add _ _ hd0 hdTop]
      congr 1
      ring

/-- The actual low-beta residual and the source Frostman mass floor turn the
coefficient power envelope into the scalar inequality consumed by the literal
shading-aware source cancellation. -/
theorem shadingAwareEq46Scalar_le_sourceMass_mul_inner_of_powerResidual
    {delta rho : NNReal}
    {sourceCap loss parentCard KT sourceMass inner : ENNReal}
    {sourceCapExponent rhoExponent lossExponent parentExponent
      ktExponent etaF : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaRho : delta ≤ rho) (hrhoExponent : 0 ≤ rhoExponent)
    (hsourceCap : sourceCap ≤
      (delta : ENNReal) ^ (-sourceCapExponent))
    (hloss : loss ≤ (delta : ENNReal) ^ (-lossExponent))
    (hparentCard : parentCard ≤
      (delta : ENNReal) ^ (-parentExponent))
    (hKT : KT ≤ (delta : ENNReal) ^ (-ktExponent))
    (hsourceMass : (delta : ENNReal) ^ (2 * etaF) ≤ sourceMass)
    (hresidual :
      (delta : ENNReal) ^
          (-(sourceCapExponent + rhoExponent + lossExponent +
            parentExponent + ktExponent)) ≤
        (delta : ENNReal) ^ 2 *
          ((delta : ENNReal) ^ (2 * etaF) * inner)) :
    sourceCap *
        ((rho : ENNReal) ^ (-rhoExponent) *
          (loss * parentCard * KT)) ≤
      sourceMass * inner := by
  have hcoefficient :=
    shadingAwareEq46Coefficient_le_delta_negativePower
      hdelta hdeltaRho hrhoExponent hsourceCap hloss hparentCard hKT
  have hdOne : (delta : ENNReal) ≤ 1 :=
    ENNReal.coe_le_coe.mpr hdeltaOne
  have hdeltaSq : (delta : ENNReal) ^ (2 : Nat) ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left' hdOne 2
  calc
    sourceCap *
        ((rho : ENNReal) ^ (-rhoExponent) *
          (loss * parentCard * KT)) ≤
      (delta : ENNReal) ^
        (-(sourceCapExponent + rhoExponent + lossExponent +
          parentExponent + ktExponent)) := hcoefficient
    _ ≤ (delta : ENNReal) ^ 2 *
          ((delta : ENNReal) ^ (2 * etaF) * inner) := hresidual
    _ ≤ 1 * (sourceMass * inner) :=
      mul_le_mul' hdeltaSq (mul_le_mul' hsourceMass le_rfl)
    _ = sourceMass * inner := one_mul _

#print axioms shadingAwareEq46Coefficient_le_delta_negativePower
#print axioms
  shadingAwareEq46Scalar_le_sourceMass_mul_inner_of_powerResidual

end
end Family8ShadingAwareResidualEnvelopePowerAlgebraV1
