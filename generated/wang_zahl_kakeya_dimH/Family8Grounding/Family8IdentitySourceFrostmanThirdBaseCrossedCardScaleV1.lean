import Family8Grounding.Family8B2NormalizedConflictKatzTaoCapV6
import Family8Grounding.Family8IdentitySourceFrostmanKatzTaoCardScaleCancellationV2
import Mathlib.Tactic

/-!
# Crossed card-scale envelope for the identity source third-base budget

The normalized-conflict ceiling depends on the transported source
Katz--Tao constant.  Estimating that constant by a standalone delta power
throws away its correlation with the identity card-scale mass.  This file
keeps the exact inequality

`CKT * volume(unitBallBody) <= 128 * delta ^ (-etaSource) * X`

until the normalized third-base volume is formed.  A fourth card-scale
bound may then replace the one genuinely residual copy of `X` by
`1 / rho^4`.  The remaining scalar inequality is deliberately retained as
an explicit premise; no numerical gain is asserted here.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8IdentitySourceFrostmanThirdBaseCrossedCardScaleV1

open LeanEval.Analysis.WangZahlKakeya
open Family8B2NormalizedConflictKatzTaoCapV6
open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

/-- A fourth card-scale bound gives the exact upper envelope needed for the
one residual copy of the card-scale mass. -/
theorem cardScaleMass_le_one_div_fourth
    {rho : NNReal} {X : ENNReal} (hrho : 0 < rho)
    (hfourth : ((rho : ENNReal) ^ (4 : Nat)) * X <= 1) :
    X <= 1 / ((rho : ENNReal) ^ (4 : Nat)) := by
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (pow_ne_zero 4 (ENNReal.coe_ne_zero.mpr hrho.ne')))
    (Or.inl (ENNReal.pow_ne_top ENNReal.coe_ne_top))).2
  simpa only [mul_comm] using hfourth

/-- The conflict ceiling and the transported source coefficient are bounded
without first replacing `CKT` by a standalone delta power.  The remaining
copy of `X` is controlled by an arbitrary explicit upper envelope
`XUpper`; downstream code can supply it from a card-scale inequality. -/
theorem sourceFrostman_crossedCardScale_to_eighthNormalized_baseBudget
    {delta rho : NNReal} {CKT X XUpper : ENNReal} {card : Nat}
    {etaSource etaThird : Real}
    (hCKTfinite : CKT ≠ ∞)
    (hX : X = (card : ENNReal) * (rho : ENNReal) ^ 2)
    (hC : CKT * volume (unitBallBody : Set Space) <=
      128 * (delta : ENNReal) ^ (-etaSource) * X)
    (hXUpper : X <= XUpper)
    (hresidual :
      (480000 *
          (128 * (128 * (delta : ENNReal) ^ (-etaSource) * XUpper)) + 2) *
          2097152 * (delta : ENNReal) ^ (-etaSource) <=
        (((rho / 8 : NNReal) : ENNReal) ^ (-etaThird))) :
    ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
          ENNReal) *
        ((128 * CKT) * volume (unitBallBody : Set Space)) <=
      (((rho / 8 : NNReal) : ENNReal) ^ (-etaThird)) *
        ((card : ENNReal) *
          ((((rho / 8 : NNReal) : ENNReal) ^ 2) / 2)) := by
  let dPower : ENNReal := (delta : ENNReal) ^ (-etaSource)
  let s : ENNReal := ((rho / 8 : NNReal) : ENNReal)
  let L : ENNReal :=
    ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
      ENNReal)
  let B : ENNReal := 480000 * (128 * (128 * dPower * XUpper)) + 2
  have hunitOne : (1 : ENNReal) <=
      volume (unitBallBody : Set Space) := by
    rw [coe_unitBallBody, EuclideanSpace.volume_closedBall_fin_three]
    norm_num
    nlinarith [Real.pi_gt_three]
  have hCKTleProduct : CKT <=
      CKT * volume (unitBallBody : Set Space) := by
    calc
      CKT = CKT * 1 := by rw [mul_one]
      _ <= CKT * volume (unitBallBody : Set Space) :=
        mul_le_mul' le_rfl hunitOne
  have hCKTUpper : CKT <= 128 * dPower * XUpper := by
    calc
      CKT <= CKT * volume (unitBallBody : Set Space) := hCKTleProduct
      _ <= 128 * dPower * X := by
        simpa only [dPower] using hC
      _ <= 128 * dPower * XUpper := mul_le_mul' le_rfl hXUpper
  have hscaledFinite : (128 : ENNReal) * CKT ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hCKTfinite
  have hL : L <= B := by
    calc
      L <= 480000 * (128 * CKT) + 2 := by
        dsimp only [L]
        exact fixedKatzTaoClosedLoss_coe_le_add_two hscaledFinite
      _ <= 480000 * (128 * (128 * dPower * XUpper)) + 2 := by
        gcongr
  have hcoefficient : (128 * CKT) *
      volume (unitBallBody : Set Space) <= 16384 * dPower * X := by
    calc
      (128 * CKT) * volume (unitBallBody : Set Space) =
          128 * (CKT * volume (unitBallBody : Set Space)) := by ac_rfl
      _ <= 128 * (128 * dPower * X) := by
        exact mul_le_mul' le_rfl (by simpa only [dPower] using hC)
      _ = 16384 * dPower * X := by ring
  have hcrossed : L *
      ((128 * CKT) * volume (unitBallBody : Set Space)) <=
        B * (16384 * dPower * X) :=
    mul_le_mul' hL hcoefficient
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
  have hresidual' : B * 2097152 * dPower <= s ^ (-etaThird) := by
    simpa only [B, dPower, s] using hresidual
  have hscaled := mul_le_mul' hresidual' (le_refl (X / 128))
  have hcancel : (X / 128) * 128 = X :=
    ENNReal.div_mul_cancel (by norm_num) (by norm_num)
  have hfactor : B * (16384 * dPower * X) =
      (B * 2097152 * dPower) * (X / 128) := by
    calc
      B * (16384 * dPower * X) =
          B * (16384 * dPower * ((X / 128) * 128)) := by rw [hcancel]
      _ = (B * 2097152 * dPower) * (X / 128) := by ring
  calc
    ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
          ENNReal) *
        ((128 * CKT) * volume (unitBallBody : Set Space)) =
      L * ((128 * CKT) * volume (unitBallBody : Set Space)) := by rfl
    _ <= B * (16384 * dPower * X) := hcrossed
    _ = (B * 2097152 * dPower) * (X / 128) := hfactor
    _ <= s ^ (-etaThird) * (X / 128) := hscaled
    _ = s ^ (-etaThird) *
        ((card : ENNReal) * (s ^ 2 / 2)) := by rw [hmass]

/-- Canonical specialization of the crossed envelope using exactly the
fourth card-scale premise already present in the V3 composer. -/
theorem sourceFrostman_fourthCardScale_to_eighthNormalized_baseBudget
    {delta rho : NNReal} {CKT X : ENNReal} {card : Nat}
    {etaSource etaThird : Real}
    (hrho : 0 < rho) (hCKTfinite : CKT ≠ ∞)
    (hX : X = (card : ENNReal) * (rho : ENNReal) ^ 2)
    (hC : CKT * volume (unitBallBody : Set Space) <=
      128 * (delta : ENNReal) ^ (-etaSource) * X)
    (hfourth : ((rho : ENNReal) ^ (4 : Nat)) * X <= 1)
    (hresidual :
      (480000 *
          (128 * (128 * (delta : ENNReal) ^ (-etaSource) *
            (1 / ((rho : ENNReal) ^ (4 : Nat))))) + 2) *
          2097152 * (delta : ENNReal) ^ (-etaSource) <=
        (((rho / 8 : NNReal) : ENNReal) ^ (-etaThird))) :
    ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
          ENNReal) *
        ((128 * CKT) * volume (unitBallBody : Set Space)) <=
      (((rho / 8 : NNReal) : ENNReal) ^ (-etaThird)) *
        ((card : ENNReal) *
          ((((rho / 8 : NNReal) : ENNReal) ^ 2) / 2)) := by
  exact sourceFrostman_crossedCardScale_to_eighthNormalized_baseBudget
    hCKTfinite hX hC (cardScaleMass_le_one_div_fourth hrho hfourth)
      hresidual

#print axioms cardScaleMass_le_one_div_fourth
#print axioms sourceFrostman_crossedCardScale_to_eighthNormalized_baseBudget
#print axioms sourceFrostman_fourthCardScale_to_eighthNormalized_baseBudget

end
end Family8IdentitySourceFrostmanThirdBaseCrossedCardScaleV1
