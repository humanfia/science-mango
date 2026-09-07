import Family8Grounding.Family8B2NormalizedConflictKatzTaoCapV6
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

/-!
# Source-power bound for the fixed normalized conflict loss, V3

This scalar projection isolates the exact natural loss
`ceil (480000 * 128 * CKT) + 1`.  V1 and V2 are failed drafts and are not
imported.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8FixedConflictLossPowerV3

open Family8B2NormalizedConflictKatzTaoCapV6
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

def fixedConflictLossConstant : ENNReal :=
  480000 * 128 + 2

def fixedConflictLossSmallDeltaThreshold (absorbEta : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold fixedConflictLossConstant absorbEta

theorem fixedConflictLossConstant_ne_top :
    fixedConflictLossConstant ≠ ∞ := by
  norm_num [fixedConflictLossConstant]

theorem fixedConflictLossSmallDeltaThreshold_pos (absorbEta : Real) :
    0 < fixedConflictLossSmallDeltaThreshold absorbEta :=
  finiteConstantSmallDeltaThreshold_pos _ _

/-- The exact fixed conflict loss has one Katz--Tao exponent plus one fixed
coefficient-absorption exponent. -/
theorem fixedConflictLoss_le_delta_negativePower
    {delta : NNReal} {CKT : ENNReal}
    {etaKT absorbEta : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (hetaKT : 0 <= etaKT)
    (hCKTfinite : CKT ≠ ∞)
    (hCKT : CKT <= (delta : ENNReal) ^ (-etaKT))
    (habsorbEta : 0 < absorbEta)
    (hsmall : delta <= fixedConflictLossSmallDeltaThreshold absorbEta) :
    ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
        ENNReal) <=
      (delta : ENNReal) ^ (-(etaKT + absorbEta)) := by
  let d : ENNReal := (delta : ENNReal)
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hdOne : d <= 1 := by
    dsimp only [d]
    exact_mod_cast hdeltaOne
  have hscaledFinite : (128 : ENNReal) * CKT ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hCKTfinite
  have hclosed := fixedKatzTaoClosedLoss_coe_le_add_two hscaledFinite
  have hone : 1 <= d ^ (-etaKT) := by
    rw [← ENNReal.rpow_zero]
    exact ENNReal.rpow_le_rpow_of_exponent_ge hdOne (by linarith)
  have hconstant : fixedConflictLossConstant <= d ^ (-absorbEta) :=
    finiteConstant_le_delta_negativePower
      fixedConflictLossConstant_ne_top habsorbEta hdelta
        (by simpa only [fixedConflictLossSmallDeltaThreshold] using hsmall)
  calc
    ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
        ENNReal) <= 480000 * (128 * CKT) + 2 := hclosed
    _ <= 480000 * (128 * d ^ (-etaKT)) +
          2 * d ^ (-etaKT) := by
      apply add_le_add
      · gcongr
      · calc
          (2 : ENNReal) = 2 * 1 := by norm_num
          _ <= 2 * d ^ (-etaKT) := by gcongr
    _ = fixedConflictLossConstant * d ^ (-etaKT) := by
      unfold fixedConflictLossConstant
      ring
    _ <= d ^ (-absorbEta) * d ^ (-etaKT) := by
      gcongr
    _ = d ^ (-(etaKT + absorbEta)) := by
      rw [show -(etaKT + absorbEta) = -absorbEta + -etaKT by ring,
        ENNReal.rpow_add _ _ hd0 hdTop]

#print axioms fixedConflictLossConstant_ne_top
#print axioms fixedConflictLossSmallDeltaThreshold_pos
#print axioms fixedConflictLoss_le_delta_negativePower

end
end Family8FixedConflictLossPowerV3
