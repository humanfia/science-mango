import Family8Grounding.Family8SelectedParentSideHullReserveProducerV1
import Mathlib.Tactic

/-!
# Exact scale exponents in the selected-side hull envelope

The geometric envelope is not merely a function of the aspect ratio
`rho / a`.  After cancelling the tube area, its true scale dependence is
`(rho * a)⁻¹`.  This file records that identity and its `beta/2` power so the
final exponent ledger cannot silently lose a power of `rho`.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8SelectedParentSideHullEnvelopeExponentV1

open Family8SelectedParentSideHullReserveProducerV1

noncomputable section

/-- The fixed numerical coefficient in the simplified side-hull envelope. -/
def selectedParentSideHullEnvelopeConstant : NNReal :=
  2 * 2304 ^ 2 * 286654464

/-- Exact cancellation of the literal tube area. -/
theorem selectedParentSideHullEnvelope_eq_constant_div_mul
    {rho a : NNReal} (hrho : 0 < rho) (ha : 0 < a) :
    selectedParentSideHullEnvelope rho a =
      (selectedParentSideHullEnvelopeConstant : ENNReal) /
        (((rho * a : NNReal) : ENNReal)) := by
  have hden : rho ^ (2 : Nat) / 2 ≠ 0 :=
    div_ne_zero (pow_ne_zero 2 hrho.ne') (by norm_num)
  have hra : rho * a ≠ 0 := mul_ne_zero hrho.ne' ha.ne'
  have hNN :
      ((2304 : NNReal) ^ 2 * (286654464 * rho / a)) /
          (rho ^ (2 : Nat) / 2) =
        selectedParentSideHullEnvelopeConstant / (rho * a) := by
    unfold selectedParentSideHullEnvelopeConstant
    field_simp [hrho.ne', ha.ne']
  have hcast := congrArg (fun x : NNReal => (x : ENNReal)) hNN
  simpa only [selectedParentSideHullEnvelope, ENNReal.coe_div hden,
    ENNReal.coe_div hra, ENNReal.coe_div ha.ne',
    ENNReal.coe_div (by norm_num : (2 : NNReal) ≠ 0), ENNReal.coe_mul, ENNReal.coe_pow,
    ENNReal.coe_ofNat] using hcast

/-- The exact power used by the dyadic joint payment.  Both `rho` and the
literal inner short side occur with exponent `-beta/2`. -/
theorem selectedParentSideHullEnvelope_rpow_eq
    {rho a : NNReal} (hrho : 0 < rho) (ha : 0 < a)
    {beta : Real} (hbeta0 : 0 ≤ beta) :
    (selectedParentSideHullEnvelope rho a) ^ (beta / 2) =
      (selectedParentSideHullEnvelopeConstant : ENNReal) ^ (beta / 2) *
        (((rho * a : NNReal) : ENNReal)) ^ (-(beta / 2)) := by
  have hp : 0 ≤ beta / 2 := by linarith
  rw [selectedParentSideHullEnvelope_eq_constant_div_mul hrho ha,
    ENNReal.div_rpow_of_nonneg _ _ hp, div_eq_mul_inv,
    ENNReal.rpow_neg]

/-- Expanded form of the exact dyadic residual. -/
theorem two_rpow_mul_sideHullEnvelope_rpow_mul_dyadicGain_eq
    {rho a : NNReal} (hrho : 0 < rho) (ha : 0 < a)
    {d0 : ENNReal} {beta : Real} (hbeta0 : 0 ≤ beta) :
    ((2 : ENNReal) ^ (beta / 2) *
        (selectedParentSideHullEnvelope rho a) ^ (beta / 2)) *
        d0 ^ (beta - 1) =
      ((2 : ENNReal) ^ (beta / 2) *
          (selectedParentSideHullEnvelopeConstant : ENNReal) ^
            (beta / 2)) *
        ((((rho * a : NNReal) : ENNReal)) ^ (-(beta / 2)) *
          d0 ^ (beta - 1)) := by
  rw [selectedParentSideHullEnvelope_rpow_eq hrho ha hbeta0]
  ac_rfl

#print axioms selectedParentSideHullEnvelope_eq_constant_div_mul
#print axioms selectedParentSideHullEnvelope_rpow_eq
#print axioms two_rpow_mul_sideHullEnvelope_rpow_mul_dyadicGain_eq

end
end Family8SelectedParentSideHullEnvelopeExponentV1
