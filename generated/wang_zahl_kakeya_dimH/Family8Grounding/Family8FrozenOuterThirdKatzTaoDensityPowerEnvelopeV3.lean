import Family8Grounding.Family8B2NormalizedConflictKatzTaoCapV6
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open scoped ENNReal NNReal

namespace Family8FrozenOuterThirdKatzTaoDensityPowerEnvelopeV3

open Family8B2NormalizedConflictKatzTaoCapV6
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# Power envelope for the fixed-conflict outer density scalar

The fixed normalized conflict loss costs one copy of the source Katz--Tao
constant. The `XUpper = 1024 * CKT` density term costs one more. All remaining
coefficients are fixed and are absorbed below one explicit small scale.

V1 and V2 are failed theorem-name/addition-order drafts and are not imported.
-/

def frozenOuterThirdKatzTaoDensityFixedConstant : ENNReal :=
  (480000 * 128 + 2) * 128 * 8 * 1024

def frozenOuterThirdKatzTaoDensitySmallDeltaThreshold
    (absorbEta : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    frozenOuterThirdKatzTaoDensityFixedConstant absorbEta

theorem frozenOuterThirdKatzTaoDensityFixedConstant_ne_top :
    frozenOuterThirdKatzTaoDensityFixedConstant ≠ ∞ := by
  norm_num [frozenOuterThirdKatzTaoDensityFixedConstant]

theorem frozenOuterThirdKatzTaoDensitySmallDeltaThreshold_pos
    (absorbEta : Real) :
    0 < frozenOuterThirdKatzTaoDensitySmallDeltaThreshold absorbEta :=
  finiteConstantSmallDeltaThreshold_pos _ _

theorem fixedConflict_densityScalar_le_fixed_mul_sq
    {CKT : ENNReal} (hCKTfinite : CKT ≠ ∞) (hCKTone : 1 ≤ CKT) :
    ((((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
          ENNReal) * 128) * (8 * (1024 * CKT))) ≤
      frozenOuterThirdKatzTaoDensityFixedConstant * CKT ^ (2 : Nat) := by
  have hscaledFinite : (128 : ENNReal) * CKT ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hCKTfinite
  have hclosed :
      ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
          ENNReal) ≤
        480000 * (128 * CKT) + 2 :=
    fixedKatzTaoClosedLoss_coe_le_add_two hscaledFinite
  have htwo : (2 : ENNReal) ≤ 2 * CKT := by
    have hmul := mul_le_mul' (show (2 : ENNReal) ≤ 2 from le_rfl) hCKTone
    simpa only [mul_one] using hmul
  have hlinear :
      480000 * (128 * CKT) + 2 ≤ (480000 * 128 + 2) * CKT := by
    calc
      480000 * (128 * CKT) + 2 ≤
          480000 * (128 * CKT) + 2 * CKT :=
        add_le_add le_rfl htwo
      _ = (480000 * 128 + 2) * CKT := by ring
  calc
    ((((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
          ENNReal) * 128) * (8 * (1024 * CKT))) ≤
        (((480000 * 128 + 2) * CKT) * 128) *
          (8 * (1024 * CKT)) := by
      exact mul_le_mul' (mul_le_mul' (hclosed.trans hlinear) le_rfl) le_rfl
    _ = frozenOuterThirdKatzTaoDensityFixedConstant * CKT ^ (2 : Nat) := by
      unfold frozenOuterThirdKatzTaoDensityFixedConstant
      ring

theorem fixedConflict_densityScalar_le_delta_negativePower
    {delta : NNReal} {CKT : ENNReal} {etaKT absorbEta : Real}
    (hdelta : 0 < delta)
    (hCKTfinite : CKT ≠ ∞) (hCKTone : 1 ≤ CKT)
    (hCKT : CKT ≤ (delta : ENNReal) ^ (-etaKT))
    (habsorbEta : 0 < absorbEta)
    (hsmall : delta ≤
      frozenOuterThirdKatzTaoDensitySmallDeltaThreshold absorbEta) :
    ((((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
          ENNReal) * 128) * (8 * (1024 * CKT))) ≤
      (delta : ENNReal) ^ (-(2 * etaKT + absorbEta)) := by
  have hfixed := fixedConflict_densityScalar_le_fixed_mul_sq
    hCKTfinite hCKTone
  have hsq : CKT ^ (2 : Nat) ≤
      ((delta : ENNReal) ^ (-etaKT)) ^ (2 : Nat) :=
    pow_le_pow_left' hCKT 2
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hpower : CKT ^ (2 : Nat) ≤
      (delta : ENNReal) ^ (-(2 * etaKT)) := by
    calc
      CKT ^ (2 : Nat) ≤ ((delta : ENNReal) ^ (-etaKT)) ^ (2 : Nat) := hsq
      _ = (delta : ENNReal) ^ ((-etaKT) * 2) := by
        rw [← ENNReal.rpow_natCast, ENNReal.rpow_mul]
        norm_num
      _ = (delta : ENNReal) ^ (-(2 * etaKT)) := by
        congr 1
        ring
  have hconstant : frozenOuterThirdKatzTaoDensityFixedConstant ≤
      (delta : ENNReal) ^ (-absorbEta) :=
    finiteConstant_le_delta_negativePower
      frozenOuterThirdKatzTaoDensityFixedConstant_ne_top
        habsorbEta hdelta hsmall
  calc
    ((((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
          ENNReal) * 128) * (8 * (1024 * CKT))) ≤
        frozenOuterThirdKatzTaoDensityFixedConstant * CKT ^ (2 : Nat) := hfixed
    _ ≤ (delta : ENNReal) ^ (-absorbEta) *
        (delta : ENNReal) ^ (-(2 * etaKT)) :=
      mul_le_mul' hconstant hpower
    _ = (delta : ENNReal) ^
        ((-absorbEta) + (-(2 * etaKT))) := by
      rw [ENNReal.rpow_add _ _ hd0 hdTop]
    _ = (delta : ENNReal) ^ (-(2 * etaKT + absorbEta)) := by
      congr 1
      ring

#print axioms frozenOuterThirdKatzTaoDensityFixedConstant_ne_top
#print axioms fixedConflict_densityScalar_le_fixed_mul_sq
#print axioms fixedConflict_densityScalar_le_delta_negativePower

end
end Family8FrozenOuterThirdKatzTaoDensityPowerEnvelopeV3
