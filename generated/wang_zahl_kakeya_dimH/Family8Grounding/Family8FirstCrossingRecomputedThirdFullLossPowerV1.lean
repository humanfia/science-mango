import Family8Grounding.Family8FirstCrossingRecomputedThirdFixedLossPowerV3
import Mathlib.Tactic

/-!
# Full recomputed-third loss power

The recomputed G2 base gate controls the variable conflict loss.  The V3
fixed-loss lemma absorbs that gate and the fixed factor `432`, but its output
still has to be multiplied by the genuine intermediate-radius factor
`rho ^ (-innerEpsilon)`.  This module performs exactly that final step.

In particular, the G2 gate remains an explicit hypothesis: no geometric
premise is hidden or discarded by this algebraic connector.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8FirstCrossingRecomputedThirdFullLossPowerV1

open Family8EighthNormalizedSelectedFrostmanThirdFactorV3
open Family8EighthSelectedThirdFactorLossAbsorptionV2
open Family8FirstCrossingRecomputedThirdFixedLossPowerV3

noncomputable section

/-- The recomputed G2 base gate, fixed-`432` threshold, scale ordering, and
the displayed exponent budget control the complete third-factor loss.

The term `innerEpsilon` is the exponent of the radius-dependent factor that
is absent from `eighthSelectedThirdFixedLoss`; it is therefore spent once in
the final budget. -/
theorem recomputedThird_fullLoss_le_delta_negativePower
    {delta rho : NNReal} {loss : ENNReal}
    {etaSource etaThird absorbExponent innerEpsilon gamma targetExponent : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (hrho : 0 < rho) (hdeltaRho : delta <= rho)
    (hetaSource : 0 <= etaSource) (hetaThird : 0 <= etaThird)
    (habsorb : 0 < absorbExponent)
    (hinnerEpsilon : 0 <= innerEpsilon)
    (hbase : loss * 2097152 * (delta : ENNReal) ^ (-etaSource) <=
      (((rho / 8 : NNReal) : ENNReal) ^ (-etaThird)))
    (hsmall : delta <= recomputedThirdFixedLossPowerThreshold
      etaThird absorbExponent innerEpsilon gamma)
    (hexponent : etaThird + absorbExponent + innerEpsilon <=
      targetExponent) :
    eighthSelectedThirdFactorLoss rho (432 * loss)
        innerEpsilon gamma <=
      (delta : ENNReal) ^ (-targetExponent) := by
  have hfixed :
      eighthSelectedThirdFixedLoss (432 * loss) innerEpsilon gamma <=
        (delta : ENNReal) ^ (-(etaThird + absorbExponent)) :=
    fixed432Loss_le_delta_negativePower_of_recomputedBaseGate
      hdelta hdeltaOne hrho hdeltaRho hetaSource hetaThird habsorb
        hbase hsmall
  have hrhoPower : (rho : ENNReal) ^ (-innerEpsilon) <=
      (delta : ENNReal) ^ (-innerEpsilon) := by
    rw [<- ENNReal.coe_rpow_of_ne_zero hrho.ne' (-innerEpsilon),
      <- ENNReal.coe_rpow_of_ne_zero hdelta.ne' (-innerEpsilon)]
    exact ENNReal.coe_le_coe.mpr
      (NNReal.rpow_le_rpow_of_nonpos hdelta hdeltaRho
        (neg_nonpos.mpr hinnerEpsilon))
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hdOneENN : (delta : ENNReal) <= 1 := by
    exact_mod_cast hdeltaOne
  rw [eighthSelectedThirdFactorLoss_eq_fixed_mul_rpow
    rho (432 * loss) innerEpsilon gamma hrho]
  calc
    eighthSelectedThirdFixedLoss (432 * loss) innerEpsilon gamma *
        (rho : ENNReal) ^ (-innerEpsilon) <=
      (delta : ENNReal) ^ (-(etaThird + absorbExponent)) *
        (delta : ENNReal) ^ (-innerEpsilon) :=
      mul_le_mul' hfixed hrhoPower
    _ = (delta : ENNReal) ^
        (-(etaThird + absorbExponent + innerEpsilon)) := by
      rw [<- ENNReal.rpow_add _ _ hd0 hdTop]
      congr 1
      ring
    _ <= (delta : ENNReal) ^ (-targetExponent) := by
      exact ENNReal.rpow_le_rpow_of_exponent_ge hdOneENN (by linarith)

#print axioms recomputedThird_fullLoss_le_delta_negativePower

end
end Family8FirstCrossingRecomputedThirdFullLossPowerV1
