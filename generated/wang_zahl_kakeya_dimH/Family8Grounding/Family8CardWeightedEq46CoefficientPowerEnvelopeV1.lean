import Family8Grounding.Family8LongIntervalOrdinaryFiberCapNumericsV1
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open scoped ENNReal NNReal

namespace Family8CardWeightedEq46CoefficientPowerEnvelopeV1

open Family8LongIntervalOrdinaryFiberCapNumericsV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# Unified power envelope for the card-weighted Equation (46) coefficient

The normalized parent-card cancellation leaves the fixed factor
`ordinaryFiberNatCapFixedConstant * 1024`, one source Katz--Tao power, one
intermediate-scale loss, and three independently meaningful loss constants.
This file absorbs the fixed factor at an explicit small scale and combines
the remaining powers.  It does not estimate or replace the actual
Proposition 6.6 inner factor.
-/

def cardWeightedEq46FixedConstant : ENNReal :=
  ordinaryFiberNatCapFixedConstant * 1024

def cardWeightedEq46FixedConstantThreshold (absorbExponent : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    cardWeightedEq46FixedConstant absorbExponent

theorem cardWeightedEq46FixedConstant_ne_top :
    cardWeightedEq46FixedConstant ≠ ∞ := by
  norm_num [cardWeightedEq46FixedConstant,
    ordinaryFiberNatCapFixedConstant]

theorem cardWeightedEq46FixedConstantThreshold_pos
    (absorbExponent : Real) :
    0 < cardWeightedEq46FixedConstantThreshold absorbExponent :=
  finiteConstantSmallDeltaThreshold_pos _ _

/-- The exact coefficient left after the active-parent-card cancellation is
bounded by one global source-scale power.  The tau loss is transported to
delta using only `delta <= tau`; no `tau^-2` parent-card loss occurs. -/
theorem cardWeightedEq46Coefficient_le_delta_negativePower
    {delta tau : NNReal} {loss CKT KT : ENNReal}
    {etaKT tauExponent lossExponent coarseKTExponent innerKTExponent
      constantAbsorbExponent : Real}
    (hdelta : 0 < delta) (hdeltaTau : delta ≤ tau)
    (htauExponent : 0 ≤ tauExponent)
    (hloss : loss ≤ (delta : ENNReal) ^ (-lossExponent))
    (hCKT : CKT ≤ (delta : ENNReal) ^ (-coarseKTExponent))
    (hKT : KT ≤ (delta : ENNReal) ^ (-innerKTExponent))
    (hconstantAbsorbExponent : 0 < constantAbsorbExponent)
    (hsmall : delta ≤
      cardWeightedEq46FixedConstantThreshold constantAbsorbExponent) :
    ((ordinaryFiberNatCapFixedConstant *
          (delta : ENNReal) ^ (-etaKT)) *
        (tau : ENNReal) ^ (-tauExponent)) *
          (loss * (1024 * CKT) * KT) ≤
      (delta : ENNReal) ^
        (-(etaKT + tauExponent + lossExponent + coarseKTExponent +
          innerKTExponent + constantAbsorbExponent)) := by
  have htau : 0 < tau := hdelta.trans_le hdeltaTau
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hconstant : cardWeightedEq46FixedConstant ≤
      (delta : ENNReal) ^ (-constantAbsorbExponent) :=
    finiteConstant_le_delta_negativePower
      cardWeightedEq46FixedConstant_ne_top hconstantAbsorbExponent
        hdelta hsmall
  have htauPowerNN : tau ^ (-tauExponent) ≤
      delta ^ (-tauExponent) :=
    NNReal.rpow_le_rpow_of_nonpos hdelta hdeltaTau
      (neg_nonpos.mpr htauExponent)
  have htauPower : (tau : ENNReal) ^ (-tauExponent) ≤
      (delta : ENNReal) ^ (-tauExponent) := by
    rw [← ENNReal.coe_rpow_of_ne_zero htau.ne' (-tauExponent),
      ← ENNReal.coe_rpow_of_ne_zero hdelta.ne' (-tauExponent)]
    exact ENNReal.coe_le_coe.mpr htauPowerNN
  calc
    ((ordinaryFiberNatCapFixedConstant *
          (delta : ENNReal) ^ (-etaKT)) *
        (tau : ENNReal) ^ (-tauExponent)) *
          (loss * (1024 * CKT) * KT) =
        cardWeightedEq46FixedConstant *
          ((delta : ENNReal) ^ (-etaKT) *
            ((tau : ENNReal) ^ (-tauExponent) *
              (loss * (CKT * KT)))) := by
      unfold cardWeightedEq46FixedConstant
      ring
    _ ≤ (delta : ENNReal) ^ (-constantAbsorbExponent) *
          ((delta : ENNReal) ^ (-etaKT) *
            ((delta : ENNReal) ^ (-tauExponent) *
              ((delta : ENNReal) ^ (-lossExponent) *
                ((delta : ENNReal) ^ (-coarseKTExponent) *
                  (delta : ENNReal) ^ (-innerKTExponent))))) := by
      exact mul_le_mul' hconstant
        (mul_le_mul' le_rfl
          (mul_le_mul' htauPower
            (mul_le_mul' hloss (mul_le_mul' hCKT hKT))))
    _ = (delta : ENNReal) ^
        (-(etaKT + tauExponent + lossExponent + coarseKTExponent +
          innerKTExponent + constantAbsorbExponent)) := by
      rw [← ENNReal.rpow_add _ _ hd0 hdTop,
        ← ENNReal.rpow_add _ _ hd0 hdTop,
        ← ENNReal.rpow_add _ _ hd0 hdTop,
        ← ENNReal.rpow_add _ _ hd0 hdTop,
        ← ENNReal.rpow_add _ _ hd0 hdTop]
      congr 1
      ring

#print axioms cardWeightedEq46FixedConstant_ne_top
#print axioms cardWeightedEq46FixedConstantThreshold_pos
#print axioms cardWeightedEq46Coefficient_le_delta_negativePower

end
end Family8CardWeightedEq46CoefficientPowerEnvelopeV1
