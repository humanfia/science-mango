import Family8Grounding.Family8EighthSelectedThirdFactorLossAbsorptionV2
import Family8Grounding.Family8EighthSelectedThirdFixedPowerLossAbsorptionV1
import Family8Grounding.Family8FixedConflictLossPowerV3
import Mathlib.Tactic

/-!
# Power absorption for the geometric factor 432 in the third coefficient, V2

V1 is a frozen namespace-owner draft.  This successor imports and opens the
direct owner of the fixed third loss.  The datum-independent factor 432 is
placed in the finite normalization constant, so it costs no extra Frostman
epsilon exponent.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8Fixed432ConflictLossAwareThirdLossPowerV2

open Family8EighthNormalizedSelectedFrostmanThirdFactorV3
open Family8EighthSelectedThirdFactorLossAbsorptionV2
open Family8EighthSelectedThirdFixedPowerLossAbsorptionV1
open Family8FixedConflictLossPowerV3
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-- The fixed normalization coefficient after the exact geometric
neighborhood comparison. -/
def eighthSelectedThird432NormalizationLoss
    (epsilon gamma : Real) : ENNReal :=
  432 * eighthSelectedThirdNormalizationLoss epsilon gamma

theorem eighthSelectedThird432NormalizationLoss_ne_top
    (epsilon gamma : Real) :
    eighthSelectedThird432NormalizationLoss epsilon gamma ≠ ∞ := by
  unfold eighthSelectedThird432NormalizationLoss
  exact ENNReal.mul_ne_top (by norm_num)
    (eighthSelectedThirdNormalizationLoss_ne_top epsilon gamma)

/-- Multiplying the variable selection loss by 432 is exactly the same as
keeping the variable loss unchanged and multiplying the fixed normalization
constant by 432. -/
theorem eighthSelectedThirdFixedLoss_432_mul_eq
    (loss : ENNReal) (epsilon gamma : Real) :
    eighthSelectedThirdFixedLoss (432 * loss) epsilon gamma =
      loss * eighthSelectedThird432NormalizationLoss epsilon gamma := by
  rw [eighthSelectedThirdFixedLoss_eq_loss_mul_normalization]
  unfold eighthSelectedThird432NormalizationLoss
  ac_rfl

/-- A power-sized variable loss absorbs the extra geometric factor through
one datum-independent small-scale threshold. -/
theorem eighthSelectedThirdFixedLoss_432_mul_le_delta_negativePower
    {delta : NNReal} {loss : ENNReal}
    {epsilon gamma lossExponent absorbExponent : Real}
    (hdelta : 0 < delta)
    (hloss : loss ≤ (delta : ENNReal) ^ (-lossExponent))
    (habsorb : 0 < absorbExponent)
    (hsmall : delta ≤ finiteConstantSmallDeltaThreshold
      (eighthSelectedThird432NormalizationLoss epsilon gamma)
        absorbExponent) :
    eighthSelectedThirdFixedLoss (432 * loss) epsilon gamma ≤
      (delta : ENNReal) ^ (-(lossExponent + absorbExponent)) := by
  have hnormalization :
      eighthSelectedThird432NormalizationLoss epsilon gamma ≤
        (delta : ENNReal) ^ (-absorbExponent) :=
    finiteConstant_le_delta_negativePower
      (eighthSelectedThird432NormalizationLoss_ne_top epsilon gamma)
      habsorb hdelta hsmall
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  rw [eighthSelectedThirdFixedLoss_432_mul_eq]
  calc
    loss * eighthSelectedThird432NormalizationLoss epsilon gamma ≤
        (delta : ENNReal) ^ (-lossExponent) *
          (delta : ENNReal) ^ (-absorbExponent) :=
      mul_le_mul' hloss hnormalization
    _ = (delta : ENNReal) ^ (-(lossExponent + absorbExponent)) := by
      rw [← ENNReal.rpow_add _ _ hd0 hdTop]
      congr 1
      ring

/-- Uniform threshold combining the variable conflict-loss cap with the
fixed 432-normalization absorption. -/
def fixed432ConflictLossAwareThirdLossSmallDeltaThreshold
    (conflictAbsorb thirdAbsorb epsilon gamma : Real) : NNReal :=
  min (fixedConflictLossSmallDeltaThreshold conflictAbsorb)
    (finiteConstantSmallDeltaThreshold
      (eighthSelectedThird432NormalizationLoss epsilon gamma) thirdAbsorb)

theorem fixed432ConflictLossAwareThirdLossSmallDeltaThreshold_pos
    (conflictAbsorb thirdAbsorb epsilon gamma : Real) :
    0 < fixed432ConflictLossAwareThirdLossSmallDeltaThreshold
      conflictAbsorb thirdAbsorb epsilon gamma := by
  exact lt_min
    (fixedConflictLossSmallDeltaThreshold_pos _)
    (finiteConstantSmallDeltaThreshold_pos _ _)

/-- The exact fixed conflict loss, after multiplication by the geometric
factor 432, has the same three-term exponent budget as before. -/
theorem fixedConflict_432_lossAwareThirdLoss_le_delta_negativePower
    {delta : NNReal} {CKT : ENNReal}
    {etaKT conflictAbsorb thirdAbsorb epsilon gamma : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hetaKT : 0 ≤ etaKT)
    (hCKTfinite : CKT ≠ ∞)
    (hCKT : CKT ≤ (delta : ENNReal) ^ (-etaKT))
    (hconflictAbsorb : 0 < conflictAbsorb)
    (hthirdAbsorb : 0 < thirdAbsorb)
    (hsmall : delta ≤ fixed432ConflictLossAwareThirdLossSmallDeltaThreshold
      conflictAbsorb thirdAbsorb epsilon gamma) :
    eighthSelectedThirdFixedLoss
        (432 *
          (((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
            ENNReal)))
        epsilon gamma ≤
      (delta : ENNReal) ^
        (-((etaKT + conflictAbsorb) + thirdAbsorb)) := by
  have hloss :
      (((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
          ENNReal)) ≤
        (delta : ENNReal) ^ (-(etaKT + conflictAbsorb)) :=
    fixedConflictLoss_le_delta_negativePower
      hdelta hdeltaOne hetaKT hCKTfinite hCKT hconflictAbsorb
        (hsmall.trans (min_le_left _ _))
  exact eighthSelectedThirdFixedLoss_432_mul_le_delta_negativePower
    hdelta hloss hthirdAbsorb (hsmall.trans (min_le_right _ _))

#print axioms eighthSelectedThird432NormalizationLoss
#print axioms eighthSelectedThird432NormalizationLoss_ne_top
#print axioms eighthSelectedThirdFixedLoss_432_mul_eq
#print axioms eighthSelectedThirdFixedLoss_432_mul_le_delta_negativePower
#print axioms fixed432ConflictLossAwareThirdLossSmallDeltaThreshold_pos
#print axioms fixedConflict_432_lossAwareThirdLoss_le_delta_negativePower

end
end Family8Fixed432ConflictLossAwareThirdLossPowerV2
