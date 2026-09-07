import Family8Grounding.Family8LocalFiberCapRelativeSquareCancellationV1
import Mathlib.Tactic

/-!
# Relative-power envelope for the doubled Katz--Tao fibre cap

The exact cap cancellation gives `M * (tau/rho)^2 <= 960000 C`.  This file
solves that inequality for `M` and inserts a relative power bound for `C`.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8KatzTaoDoubledFiberRelativePowerEnvelopeV4

open Family8LocalFiberCapRelativeSquareCancellationV1
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3

noncomputable section

theorem katzTaoDoubledFiberNatCap_le_fixed_mul_ratio_negativePower
    {tau rho : NNReal} {C : ENNReal} {kappa : Real}
    (htau : 0 < tau) (htauRho : tau <= rho)
    (hCone : 1 <= C) (hCfinite : C ≠ ∞)
    (hC : C <=
      (((tau : ENNReal) / (rho : ENNReal)) ^ (-kappa))) :
    (katzTaoDoubledFiberNatCap tau rho C : ENNReal) <=
      ordinaryFiberNatCapFixedConstant *
        (((tau : ENNReal) / (rho : ENNReal)) ^ (-(2 + kappa))) := by
  let q : ENNReal := (tau : ENNReal) / (rho : ENNReal)
  let M := katzTaoDoubledFiberNatCap tau rho C
  have hrho : 0 < rho := htau.trans_le htauRho
  have hq0 : q ≠ 0 := by
    dsimp only [q]
    apply ENNReal.div_ne_zero.mpr
    constructor
    · exact ENNReal.coe_ne_zero.mpr htau.ne'
    · exact ENNReal.coe_ne_top
  have hqTop : q ≠ ∞ := by
    dsimp only [q]
    exact ENNReal.div_ne_top ENNReal.coe_ne_top
      (ENNReal.coe_ne_zero.mpr hrho.ne')
  have hcap : (M : ENNReal) * q ^ (2 : Nat) <=
      ordinaryFiberNatCapFixedConstant * C := by
    simpa only [M, q] using
      katzTaoDoubledFiberNatCap_mul_relativeSquare_le_fixed
        htau htauRho hCone hCfinite
  have hcapReal : (M : ENNReal) * q ^ (((2 : Nat) : Real)) <=
      ordinaryFiberNatCapFixedConstant * C := by
    simpa only [ENNReal.rpow_natCast] using hcap
  have hcancel : q ^ (((2 : Nat) : Real)) * q ^ (-2 : Real) = 1 := by
    rw [← ENNReal.rpow_add (((2 : Nat) : Real)) (-2 : Real) hq0 hqTop]
    norm_num
  calc
    (M : ENNReal) = (M : ENNReal) * 1 := by simp
    _ = (M : ENNReal) *
        (q ^ (((2 : Nat) : Real)) * q ^ (-2 : Real)) := by
      rw [hcancel]
    _ = ((M : ENNReal) * q ^ (((2 : Nat) : Real))) *
          q ^ (-2 : Real) := by
      ac_rfl
    _ <= (ordinaryFiberNatCapFixedConstant * C) * q ^ (-2 : Real) :=
      mul_le_mul' hcapReal le_rfl
    _ <= (ordinaryFiberNatCapFixedConstant * q ^ (-kappa)) *
          q ^ (-2 : Real) := by
      exact mul_le_mul' (mul_le_mul' le_rfl hC) le_rfl
    _ = ordinaryFiberNatCapFixedConstant *
          q ^ (-(2 + kappa)) := by
      calc
        (ordinaryFiberNatCapFixedConstant * q ^ (-kappa)) *
            q ^ (-2 : Real) = ordinaryFiberNatCapFixedConstant *
              (q ^ (-kappa) * q ^ (-2 : Real)) := by ac_rfl
        _ = ordinaryFiberNatCapFixedConstant *
              q ^ (-(2 + kappa)) := by
          rw [← ENNReal.rpow_add (-kappa) (-2 : Real) hq0 hqTop]
          congr 2
          ring

#print axioms
  katzTaoDoubledFiberNatCap_le_fixed_mul_ratio_negativePower

end
end Family8KatzTaoDoubledFiberRelativePowerEnvelopeV4
