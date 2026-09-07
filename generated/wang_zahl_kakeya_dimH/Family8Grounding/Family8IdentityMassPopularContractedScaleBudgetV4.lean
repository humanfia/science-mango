import Family8Grounding.Family8IdentityMassPopularNoKTPowerEnvelopeV3
import Mathlib.Tactic

/-!
# Contracted-John scale form of the identity mass-popular budgets

The pure envelopes are naturally written at the relative scale `q`.  The
fresh selector uses the literal contracted-John scale `(3/64) q`.  This file
performs that fixed-factor algebra exactly.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

open scoped ENNReal

namespace Family8IdentityMassPopularContractedScaleBudgetV4

open Family8IdentityMassPopularNoKTPowerEnvelopeV3

noncomputable section

/-- The nonnegative density gain loses no power when `q` is replaced by
`(3/64)q`. -/
theorem contractedScale_densityBudget_of_ratioEnvelope
    {loss q densityFloor : ENNReal} {eta p a : Real}
    (hgain : 0 ≤ eta - (p + a))
    (henvelope : identityMassPopularDensityFixedConstant *
        (loss * q ^ (eta - (p + a))) ≤ densityFloor) :
    16 * loss *
        (((((3 / 64 : ENNReal) * q) ^ (eta - (p + a))) * 93312) * 128) ≤
      densityFloor := by
  let c : ENNReal := 3 / 64
  let gain : Real := eta - (p + a)
  have hcOne : c ≤ 1 := by
    dsimp only [c]
    apply (ENNReal.div_le_iff_le_mul
      (Or.inl (by norm_num : (64 : ENNReal) ≠ 0))
      (Or.inl (by norm_num : (64 : ENNReal) ≠ ∞))).2
    norm_num
  have hcPower : c ^ gain ≤ 1 := ENNReal.rpow_le_one hcOne hgain
  have hscalePower : (c * q) ^ gain = c ^ gain * q ^ gain :=
    ENNReal.mul_rpow_of_nonneg c q hgain
  calc
    16 * loss * ((((c * q) ^ gain) * 93312) * 128) =
        identityMassPopularDensityFixedConstant *
          (loss * ((c * q) ^ gain)) := by
      unfold identityMassPopularDensityFixedConstant
      ring
    _ = identityMassPopularDensityFixedConstant *
          (loss * (c ^ gain * q ^ gain)) := by rw [hscalePower]
    _ ≤ identityMassPopularDensityFixedConstant *
          (loss * (1 * q ^ gain)) := by
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl
        (mul_le_mul' hcPower le_rfl))
    _ = identityMassPopularDensityFixedConstant *
          (loss * q ^ gain) := by ring
    _ ≤ densityFloor := henvelope

/-- The base budget has the exact residual gain
`eta - (2p+a) - 2`; the `32` fixed constant pays the remaining half-volume
normalizer. -/
theorem contractedScale_baseBudget_of_ratioEnvelope
    {loss q densityFloor : ENNReal} {eta p a : Real}
    (hq0 : q ≠ 0) (hqTop : q ≠ ∞)
    (henvelope : identityMassPopularBaseFixedConstant eta p a *
        (loss * q ^ (eta - (2 * p + a) - 2)) ≤ densityFloor) :
    16 * loss * (((3 / 64 : ENNReal) * q) ^ (-(2 * p + a))) ≤
      (((3 / 64 : ENNReal) * q) ^ (-eta)) *
        ((((3 / 64 : ENNReal) * q) ^ (2 : Nat)) / 2) * densityFloor := by
  let c : ENNReal := 3 / 64
  let gain : Real := eta - (2 * p + a) - 2
  have hc0 : c ≠ 0 := by norm_num [c]
  have hcTop : c ≠ ∞ := by
    dsimp only [c]
    exact ENNReal.div_ne_top (by norm_num) (by norm_num)
  have hscaleTop : c * q ≠ ∞ := ENNReal.mul_ne_top hcTop hqTop
  have hnegScale :
      (c * q) ^ (-(2 * p + a)) =
        c ^ (-(2 * p + a)) * q ^ (-(2 * p + a)) :=
    ENNReal.mul_rpow_of_ne_top hcTop hqTop _
  have hetaScale :
      (c * q) ^ (-eta) = c ^ (-eta) * q ^ (-eta) :=
    ENNReal.mul_rpow_of_ne_top hcTop hqTop _
  have hcPower :
      c ^ (-eta) * c ^ (2 : Nat) * c ^ gain =
        c ^ (-(2 * p + a)) := by
    rw [← ENNReal.rpow_natCast]
    rw [← ENNReal.rpow_add _ _ hc0 hcTop,
      ← ENNReal.rpow_add _ _ hc0 hcTop]
    dsimp only [gain]
    congr 1
    ring
  have hqPower :
      q ^ (-eta) * q ^ (2 : Nat) * q ^ gain =
        q ^ (-(2 * p + a)) := by
    rw [← ENNReal.rpow_natCast]
    rw [← ENNReal.rpow_add _ _ hq0 hqTop,
      ← ENNReal.rpow_add _ _ hq0 hqTop]
    dsimp only [gain]
    congr 1
    ring
  have hscaled := mul_le_mul' le_rfl henvelope
    (a := (((c * q) ^ (-eta)) * (((c * q) ^ (2 : Nat)) / 2)))
  calc
    16 * loss * ((c * q) ^ (-(2 * p + a))) =
        16 * loss *
          ((c ^ (-eta) * c ^ (2 : Nat) * c ^ gain) *
            (q ^ (-eta) * q ^ (2 : Nat) * q ^ gain)) := by
      rw [hnegScale, hcPower, hqPower]
    _ = (((c * q) ^ (-eta)) * (((c * q) ^ (2 : Nat)) / 2)) *
          (identityMassPopularBaseFixedConstant eta p a *
            (loss * q ^ gain)) := by
      rw [hetaScale]
      unfold identityMassPopularBaseFixedConstant
      dsimp only [gain]
      have htwo : ((1 : ENNReal) / 2) * 32 = 16 := by
        rw [ENNReal.div_eq_inv_mul, mul_one]
        calc
          (2 : ENNReal)⁻¹ * 32 =
              ((2 : ENNReal)⁻¹ * 2) * 16 := by ring
          _ = 1 * 16 := by
            rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
          _ = 16 := one_mul _
      rw [show ((c * q) ^ (2 : Nat)) =
          c ^ (2 : Nat) * q ^ (2 : Nat) by ring]
      rw [div_eq_mul_inv]
      calc
        16 * loss *
            ((c ^ (-eta) * c ^ (2 : Nat) *
                c ^ (eta - (2 * p + a) - 2)) *
              (q ^ (-eta) * q ^ (2 : Nat) *
                q ^ (eta - (2 * p + a) - 2))) =
          (c ^ (-eta) * q ^ (-eta) *
              (c ^ (2 : Nat) * q ^ (2 : Nat) * (1 / 2))) *
            (32 * c ^ (eta - (2 * p + a) - 2) *
              (loss * q ^ (eta - (2 * p + a) - 2))) := by
            rw [← htwo]
            ring
        _ = (c ^ (-eta) * q ^ (-eta) *
              (c ^ (2 : Nat) * q ^ (2 : Nat) * (2 : ENNReal)⁻¹)) *
            (32 * c ^ (eta - (2 * p + a) - 2) *
              (loss * q ^ (eta - (2 * p + a) - 2))) := by
          rw [div_eq_mul_inv, one_mul]
    _ ≤ (((c * q) ^ (-eta)) * (((c * q) ^ (2 : Nat)) / 2)) *
          densityFloor := hscaled
    _ = (((3 / 64 : ENNReal) * q) ^ (-eta)) *
        ((((3 / 64 : ENNReal) * q) ^ (2 : Nat)) / 2) * densityFloor := by
      dsimp only [c]

#print axioms contractedScale_densityBudget_of_ratioEnvelope
#print axioms contractedScale_baseBudget_of_ratioEnvelope

end
end Family8IdentityMassPopularContractedScaleBudgetV4
