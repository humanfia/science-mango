import Mathlib.Tactic

/-!
# Exact identity source-Frostman cancellation in the normalized third base budget
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8IdentitySourceFrostmanThirdBaseCancellationV2

/-- The transported source Katz--Tao volume coefficient and the identity
card-scale mass cancel exactly against the eighth-normalized base volume.
The only remaining input is the displayed scalar power comparison. -/
theorem sourceFrostman_cardScale_to_eighthNormalized_baseBudget
    {delta rho : NNReal} {C X : ENNReal} {card conflictThreshold : Nat}
    {etaSource etaThird : Real}
    (hX : X = (card : ENNReal) * (rho : ENNReal) ^ 2)
    (hC : C ≤ 128 * (delta : ENNReal) ^ (-etaSource) * X)
    (hpower :
      (conflictThreshold + 1 : Nat) * 2097152 *
          (delta : ENNReal) ^ (-etaSource) ≤
        (((rho / 8 : NNReal) : ENNReal) ^ (-etaThird))) :
    (conflictThreshold + 1 : Nat) * (128 * C) ≤
      (((rho / 8 : NNReal) : ENNReal) ^ (-etaThird)) *
        ((card : ENNReal) *
          ((((rho / 8 : NNReal) : ENNReal) ^ 2) / 2)) := by
  let L : ENNReal := (conflictThreshold + 1 : Nat)
  let dPower : ENNReal := (delta : ENNReal) ^ (-etaSource)
  let s : ENNReal := ((rho / 8 : NNReal) : ENNReal)
  have hscaleNN : (rho / 8) ^ (2 : Nat) / 2 =
      rho ^ (2 : Nat) / 128 := by
    apply NNReal.eq
    simp only [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
    ring
  have hscale : s ^ (2 : Nat) / 2 =
      (rho : ENNReal) ^ 2 / 128 := by
    simpa only [s,
      ENNReal.coe_div (by norm_num : (8 : NNReal) ≠ 0),
      ENNReal.coe_div (by norm_num : (2 : NNReal) ≠ 0),
      ENNReal.coe_div (by norm_num : (128 : NNReal) ≠ 0),
      ENNReal.coe_pow, ENNReal.coe_ofNat] using
        congrArg (fun z : NNReal => (z : ENNReal)) hscaleNN
  have hmass : (card : ENNReal) * (s ^ 2 / 2) = X / 128 := by
    rw [hscale, hX, ← mul_div_assoc]
  have hCscaled : L * (128 * C) ≤
      L * 16384 * dPower * X := by
    calc
      L * (128 * C) = L * 128 * C := by ac_rfl
      _ ≤ L * 128 * (128 * dPower * X) :=
        mul_le_mul' le_rfl hC
      _ = L * 16384 * dPower * X := by ring
  have hpower' : L * 2097152 * dPower ≤ s ^ (-etaThird) := by
    simpa only [L, dPower, s] using hpower
  have hpowerScaled :
      (L * 2097152 * dPower) * (X / 128) ≤
        s ^ (-etaThird) * (X / 128) :=
    mul_le_mul' hpower' le_rfl
  have hcancel : (X / 128) * 128 = X :=
    ENNReal.div_mul_cancel (by norm_num) (by norm_num)
  calc
    (conflictThreshold + 1 : Nat) * (128 * C) =
        L * (128 * C) := by rfl
    _ ≤ L * 16384 * dPower * X := hCscaled
    _ = (L * 2097152 * dPower) * (X / 128) := by
      calc
        L * 16384 * dPower * X =
            L * 16384 * dPower * ((X / 128) * 128) := by rw [hcancel]
        _ = (L * 2097152 * dPower) * (X / 128) := by ring
    _ ≤ s ^ (-etaThird) * (X / 128) := hpowerScaled
    _ = s ^ (-etaThird) *
        ((card : ENNReal) * (s ^ 2 / 2)) := by rw [hmass]

#print axioms sourceFrostman_cardScale_to_eighthNormalized_baseBudget

end Family8IdentitySourceFrostmanThirdBaseCancellationV2
