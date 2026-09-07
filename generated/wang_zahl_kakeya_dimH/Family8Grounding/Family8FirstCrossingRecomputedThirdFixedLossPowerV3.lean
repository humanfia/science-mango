import Family8Grounding.Family8Fixed432ConflictLossAwareThirdLossPowerV2
import Family8Grounding.Family8FrostmanRHSScaleVolumeAlgebraV3
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

/-!
# Fixed-loss power from the recomputed-third base gate, V3

V2 omitted the positive-base argument of an `NNReal.rpow` monotonicity
lemma and is not imported.  This clean statement converts the exact
recomputed-third base gate into the fixed loss power needed by the aggregate.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8FirstCrossingRecomputedThirdFixedLossPowerV3

open Family8EighthSelectedThirdFactorLossAbsorptionV2
open Family8Fixed432ConflictLossAwareThirdLossPowerV2
open Family8FrostmanRHSScaleVolumeAlgebraV3
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

def recomputedThirdFixedLossPowerThreshold
    (etaThird absorbExponent innerEpsilon gamma : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    (((8 : ENNReal) ^ etaThird) *
      eighthSelectedThird432NormalizationLoss innerEpsilon gamma)
    absorbExponent

theorem recomputedThirdFixedLossPowerThreshold_pos
    (etaThird absorbExponent innerEpsilon gamma : Real) :
    0 < recomputedThirdFixedLossPowerThreshold
      etaThird absorbExponent innerEpsilon gamma := by
  exact finiteConstantSmallDeltaThreshold_pos _ _

theorem fixed432Loss_le_delta_negativePower_of_recomputedBaseGate
    {delta rho : NNReal} {loss : ENNReal}
    {etaSource etaThird absorbExponent innerEpsilon gamma : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (hrho : 0 < rho) (hdeltaRho : delta <= rho)
    (hetaSource : 0 <= etaSource) (hetaThird : 0 <= etaThird)
    (habsorb : 0 < absorbExponent)
    (hbase : loss * 2097152 * (delta : ENNReal) ^ (-etaSource) <=
      (((rho / 8 : NNReal) : ENNReal) ^ (-etaThird)))
    (hsmall : delta <= recomputedThirdFixedLossPowerThreshold
      etaThird absorbExponent innerEpsilon gamma) :
    eighthSelectedThirdFixedLoss (432 * loss) innerEpsilon gamma <=
      (delta : ENNReal) ^ (-(etaThird + absorbExponent)) := by
  have hdeltaOneENN : (delta : ENNReal) <= 1 := by
    exact_mod_cast hdeltaOne
  have hdeltaSource : (1 : ENNReal) <=
      (delta : ENNReal) ^ (-etaSource) := by
    rw [show (1 : ENNReal) = (delta : ENNReal) ^ (0 : Real) by
      simp]
    exact ENNReal.rpow_le_rpow_of_exponent_ge hdeltaOneENN (by linarith)
  have hfactor : (1 : ENNReal) <=
      2097152 * (delta : ENNReal) ^ (-etaSource) := by
    calc
      (1 : ENNReal) = 1 * 1 := by rw [one_mul]
      _ <= 2097152 * (delta : ENNReal) ^ (-etaSource) :=
        mul_le_mul' (by norm_num) hdeltaSource
  have hlossRadius : loss <=
      (((rho / 8 : NNReal) : ENNReal) ^ (-etaThird)) := by
    calc
      loss = loss * 1 := by rw [mul_one]
      _ <= loss * (2097152 *
          (delta : ENNReal) ^ (-etaSource)) :=
        mul_le_mul' le_rfl hfactor
      _ = loss * 2097152 *
          (delta : ENNReal) ^ (-etaSource) := by ac_rfl
      _ <= (((rho / 8 : NNReal) : ENNReal) ^ (-etaThird)) := hbase
  have hrhoPower : (rho : ENNReal) ^ (-etaThird) <=
      (delta : ENNReal) ^ (-etaThird) := by
    rw [<- ENNReal.coe_rpow_of_ne_zero hrho.ne' (-etaThird),
      <- ENNReal.coe_rpow_of_ne_zero hdelta.ne' (-etaThird)]
    exact ENNReal.coe_le_coe.mpr
      (NNReal.rpow_le_rpow_of_nonpos hdelta hdeltaRho
        (neg_nonpos.mpr hetaThird))
  have hloss : loss <= (delta : ENNReal) ^ (-etaThird) *
      (8 : ENNReal) ^ etaThird := by
    calc
      loss <= (((rho / 8 : NNReal) : ENNReal) ^ (-etaThird)) :=
        hlossRadius
      _ = (rho : ENNReal) ^ (-etaThird) *
          (8 : ENNReal) ^ etaThird := by
        rw [coe_div_eight_rpow]
        congr 2
        ring
      _ <= (delta : ENNReal) ^ (-etaThird) *
          (8 : ENNReal) ^ etaThird := mul_le_mul' hrhoPower le_rfl
  have hconstant :
      ((8 : ENNReal) ^ etaThird) *
          eighthSelectedThird432NormalizationLoss innerEpsilon gamma <=
        (delta : ENNReal) ^ (-absorbExponent) := by
    exact finiteConstant_le_delta_negativePower
      (ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num))
        (eighthSelectedThird432NormalizationLoss_ne_top
          innerEpsilon gamma))
      habsorb hdelta hsmall
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  rw [eighthSelectedThirdFixedLoss_432_mul_eq]
  calc
    loss * eighthSelectedThird432NormalizationLoss innerEpsilon gamma <=
        ((delta : ENNReal) ^ (-etaThird) *
          (8 : ENNReal) ^ etaThird) *
            eighthSelectedThird432NormalizationLoss innerEpsilon gamma :=
      mul_le_mul' hloss le_rfl
    _ = (delta : ENNReal) ^ (-etaThird) *
        (((8 : ENNReal) ^ etaThird) *
          eighthSelectedThird432NormalizationLoss innerEpsilon gamma) := by
      ac_rfl
    _ <= (delta : ENNReal) ^ (-etaThird) *
        (delta : ENNReal) ^ (-absorbExponent) :=
      mul_le_mul' le_rfl hconstant
    _ = (delta : ENNReal) ^ (-(etaThird + absorbExponent)) := by
      rw [<- ENNReal.rpow_add _ _ hd0 hdTop]
      congr 1
      ring

#print axioms recomputedThirdFixedLossPowerThreshold_pos
#print axioms fixed432Loss_le_delta_negativePower_of_recomputedBaseGate

end
end Family8FirstCrossingRecomputedThirdFixedLossPowerV3
