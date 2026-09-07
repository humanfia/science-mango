import Family8Grounding.Family8SelectedParentAngleBucketLogarithmicLossV2
import Family8Grounding.Family8SelectedParentJohnPlankQuantitativeLossV10
import Mathlib.Tactic

/-!
# Absorbing the selected-parent angle logarithm, V3

Canonical successor to V2, using the explicit left-multiplication
monotonicity lemma.  The angle ratio loss is the controlled side loss at
`rho/2`, and `rho^2 <= rho/2` converts its half exponent to the full target
exponent without a new constant.
-/

open scoped ENNReal NNReal

namespace Family8SelectedParentAngleLogLossPowerAbsorptionV3

open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankQuantitativeLossV10

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

theorem angleRatioLoss_eq_sideBucketLoss_half
    {rho : NNReal} (hrho : 0 < rho) :
    threeSideDyadicRatioLoss (11943936 / (rho : Real)) =
      selectedParentLogarithmicSideBucketLoss (rho / 2) := by
  have hrhoReal : (rho : Real) ≠ 0 := by exact_mod_cast hrho.ne'
  have hratio :
      5971968 / (((rho / 2 : NNReal) : Real)) =
        11943936 / (rho : Real) := by
    norm_num [NNReal.coe_div]
    field_simp [hrhoReal]
    ring
  unfold selectedParentLogarithmicSideBucketLoss
  rw [hratio]

theorem halfScale_negativeHalfPower_le
    {rho : NNReal} {lossEta : Real}
    (hrho : 0 < rho) (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (hlossEta : 0 < lossEta) :
    (((rho / 2 : NNReal) : ENNReal) ^ (-(lossEta / 2))) <=
      (rho : ENNReal) ^ (-lossEta) := by
  have hbase : rho ^ (2 : Nat) <= rho / 2 := by
    calc
      rho ^ (2 : Nat) = rho * rho := by ring
      _ <= rho * (2 : NNReal)⁻¹ :=
        mul_le_mul_right hrhoHalf rho
      _ = rho / 2 := by rw [div_eq_mul_inv]
  have hpowNN :
      (rho / 2) ^ (-(lossEta / 2)) <=
        (rho ^ (2 : Nat)) ^ (-(lossEta / 2)) :=
    NNReal.rpow_le_rpow_of_nonpos (pow_pos hrho 2) hbase (by linarith)
  have hrhsNN :
      (rho ^ (2 : Nat)) ^ (-(lossEta / 2)) = rho ^ (-lossEta) := by
    rw [← NNReal.rpow_natCast]
    rw [← NNReal.rpow_mul]
    congr 1
    ring
  have hfinalNN : (rho / 2) ^ (-(lossEta / 2)) <= rho ^ (-lossEta) :=
    hpowNN.trans_eq hrhsNN
  rw [← ENNReal.coe_rpow_of_ne_zero
      (show rho / 2 ≠ 0 by positivity),
    ← ENNReal.coe_rpow_of_ne_zero hrho.ne']
  exact_mod_cast hfinalNN

theorem fixedConstant_mul_angleRatioLoss_le_rpow
    {rho : NNReal} {fixedConstant : ENNReal} {lossEta : Real}
    (hfixedFinite : fixedConstant ≠ ∞)
    (hlossEta : 0 < lossEta)
    (hrho : 0 < rho) (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (hrhoThreshold :
      rho / 2 <= selectedParentLogarithmicSideBucketAbsorptionThreshold
        fixedConstant (lossEta / 2)) :
    fixedConstant *
        (threeSideDyadicRatioLoss (11943936 / (rho : Real)) : ENNReal) <=
      (rho : ENNReal) ^ (-lossEta) := by
  have hhalfEta : 0 < lossEta / 2 := by positivity
  have hrhoHalfPos : 0 < rho / 2 := by positivity
  have habsorb :=
    fixedConstant_mul_selectedParentLogarithmicSideBucketLoss_le_rpow
      (rho := rho / 2) (fixedConstant := fixedConstant)
      (lossEta := lossEta / 2) hfixedFinite hhalfEta hrhoHalfPos
      hrhoThreshold
  rw [← angleRatioLoss_eq_sideBucketLoss_half hrho]
    at habsorb
  exact habsorb.trans
    (halfScale_negativeHalfPower_le hrho hrhoHalf hlossEta)

#print axioms angleRatioLoss_eq_sideBucketLoss_half
#print axioms halfScale_negativeHalfPower_le
#print axioms fixedConstant_mul_angleRatioLoss_le_rpow

end

end Family8SelectedParentAngleLogLossPowerAbsorptionV3
