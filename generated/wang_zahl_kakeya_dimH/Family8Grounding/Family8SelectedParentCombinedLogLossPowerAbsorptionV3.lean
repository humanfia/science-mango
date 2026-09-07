import Family8Grounding.Family8SelectedParentAngleLogLossPowerAbsorptionV3
import Family8Grounding.Family8SelectedParentJohnPlankQuantitativeLossV10
import Mathlib.Tactic

/-!
# Simultaneous absorption of the selected-parent logarithmic losses, V3

Canonical successor to V2, replacing its only linter-rejected `convert`
sequence by an explicit exponent identity.  The actual selected-parent
Córdoba scalar carries the cubic side-label loss and the thresholded
angle-row loss.  Half of an arbitrary positive exponent is spent on each
loss, while an arbitrary finite fixed coefficient is absorbed as well.

No geometric or multiplicity estimate is assumed or produced here.
-/

open scoped ENNReal NNReal

namespace Family8SelectedParentCombinedLogLossPowerAbsorptionV3

open Family8SelectedParentAngleLogLossPowerAbsorptionV3
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankQuantitativeLossV10

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

/-- The product of both literal logarithmic losses, together with any fixed
finite coefficient, is absorbed by an arbitrary positive power of `rho`.
The two explicit threshold hypotheses record exactly where the exponent is
split between the side and angle losses. -/
theorem fixedConstant_mul_combinedSelectedParentLogLoss_le_rpow
    {rho : NNReal} {fixedConstant : ENNReal} {lossEta : Real}
    (hfixedFinite : fixedConstant ≠ ∞)
    (hlossEta : 0 < lossEta)
    (hrho : 0 < rho) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (hsideThreshold :
      rho ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold
        1 (lossEta / 2))
    (hangleThreshold :
      rho / 2 ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold
        fixedConstant (lossEta / 4)) :
    (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
        (fixedConstant *
          (threeSideDyadicRatioLoss
            (11943936 / (rho : Real)) : ENNReal)) ≤
      (rho : ENNReal) ^ (-lossEta) := by
  have hhalfEta : 0 < lossEta / 2 := by positivity
  have hside :=
    fixedConstant_mul_selectedParentLogarithmicSideBucketLoss_le_rpow
      (rho := rho) (fixedConstant := 1) (lossEta := lossEta / 2)
      (by simp) hhalfEta hrho hsideThreshold
  have hquarter : (lossEta / 2) / 2 = lossEta / 4 := by ring
  have hangleThreshold' :
      rho / 2 ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold
        fixedConstant ((lossEta / 2) / 2) := by
    rw [hquarter]
    exact hangleThreshold
  have hangle := fixedConstant_mul_angleRatioLoss_le_rpow
    (rho := rho) (fixedConstant := fixedConstant)
    (lossEta := lossEta / 2) hfixedFinite hhalfEta hrho hrhoHalf
    hangleThreshold'
  have hrho0 : (rho : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hrho.ne'
  have hrhoTop : (rho : ENNReal) ≠ ∞ := by simp
  calc
    (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
        (fixedConstant *
          (threeSideDyadicRatioLoss
            (11943936 / (rho : Real)) : ENNReal)) ≤
      (rho : ENNReal) ^ (-(lossEta / 2)) *
        (rho : ENNReal) ^ (-(lossEta / 2)) :=
      mul_le_mul' (by simpa only [one_mul] using hside) hangle
    _ = (rho : ENNReal) ^ (-lossEta) := by
      rw [← ENNReal.rpow_add _ _ hrho0 hrhoTop]
      congr 1
      ring

#print axioms fixedConstant_mul_combinedSelectedParentLogLoss_le_rpow

end

end Family8SelectedParentCombinedLogLossPowerAbsorptionV3
