import Family8Grounding.Family8ThreeScaleFrostmanFactorAlgebraV2
import Mathlib.Tactic

/-!
# Beta-to-gamma transport for one Section-8 factor, V3

For `X = b^2 n`, the exact gap factor between the beta and gamma
normalizations is `b^(2(gamma-beta)) * X^((gamma-beta)/2)`.  V1 and V2 are
failed drafts and are not imported.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open scoped ENNReal NNReal

namespace Family8SectionEightBetaGammaCardScaleBridgeV3

open Family8ThreeScaleFrostmanFactorAlgebraV2

noncomputable section

/-- Exact factorization of the beta Section-8 factor through its gamma
counterpart and the card-scale mass `X = b^2 n`. -/
theorem sectionEight_to_one_beta_eq_gap_mul_gamma
    {b : NNReal} {n : Nat} {beta gamma : Real}
    (hb : 0 < b) (hn : 0 < n) :
    sectionEightScaleCountFrostmanFactor b 1 n beta =
      (((b : ENNReal) ^ (2 * (gamma - beta))) *
        ((((b : ENNReal) ^ (2 : Nat)) * (n : ENNReal)) ^
          ((gamma - beta) / 2))) *
        sectionEightScaleCountFrostmanFactor b 1 n gamma := by
  let x : ENNReal := (b : ENNReal)
  let X : ENNReal := x ^ (2 : Nat) * (n : ENNReal)
  have hx0 : x ≠ 0 := ENNReal.coe_ne_zero.mpr hb.ne'
  have hxTop : x ≠ ∞ := ENNReal.coe_ne_top
  have hn0 : (n : ENNReal) ≠ 0 := by exact_mod_cast hn.ne'
  have hnTop : (n : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hX0 : X ≠ 0 := mul_ne_zero (pow_ne_zero _ hx0) hn0
  have hXTop : X ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top hxTop) hnTop
  unfold sectionEightScaleCountFrostmanFactor
  simp only [ENNReal.coe_one, div_one]
  change x ^ (-2 * beta) * X ^ (1 - beta / 2) =
    (x ^ (2 * (gamma - beta)) * X ^ ((gamma - beta) / 2)) *
      (x ^ (-2 * gamma) * X ^ (1 - gamma / 2))
  rw [show -2 * beta = 2 * (gamma - beta) + (-2 * gamma) by ring,
    ENNReal.rpow_add _ _ hx0 hxTop,
    show 1 - beta / 2 = (gamma - beta) / 2 +
      (1 - gamma / 2) by ring,
    ENNReal.rpow_add _ _ hX0 hXTop]
  ac_rfl

/-- A source-power upper bound for `b^2 n` pays exactly half the
beta-to-gamma gap times that card-scale exponent. -/
theorem sectionEight_to_one_beta_le_power_mul_gamma
    {delta b : NNReal} {n : Nat}
    {beta gamma cardScaleExponent : Real}
    (hb : 0 < b) (hbOne : b <= 1)
    (hn : 0 < n) (hbetaGamma : beta <= gamma)
    (hcardScale :
      ((b : ENNReal) ^ (2 : Nat)) * (n : ENNReal) <=
        (delta : ENNReal) ^ (-cardScaleExponent)) :
    sectionEightScaleCountFrostmanFactor b 1 n beta <=
      (delta : ENNReal) ^
          (-(cardScaleExponent * ((gamma - beta) / 2))) *
        sectionEightScaleCountFrostmanFactor b 1 n gamma := by
  let gapHalf : Real := (gamma - beta) / 2
  have hgapHalf : 0 <= gapHalf := by
    dsimp only [gapHalf]
    linarith
  have hbENNOne : (b : ENNReal) <= 1 := by exact_mod_cast hbOne
  have hbGap : (b : ENNReal) ^ (2 * (gamma - beta)) <= 1 := by
    rw [← ENNReal.rpow_zero]
    exact ENNReal.rpow_le_rpow_of_exponent_ge hbENNOne (by linarith)
  have hXGap :
      ((((b : ENNReal) ^ (2 : Nat)) * (n : ENNReal)) ^ gapHalf) <=
        ((delta : ENNReal) ^ (-cardScaleExponent)) ^ gapHalf :=
    ENNReal.rpow_le_rpow hcardScale hgapHalf
  have hgapPower :
      ((b : ENNReal) ^ (2 * (gamma - beta))) *
          ((((b : ENNReal) ^ (2 : Nat)) * (n : ENNReal)) ^ gapHalf) <=
        (delta : ENNReal) ^
          (-(cardScaleExponent * gapHalf)) := by
    calc
      ((b : ENNReal) ^ (2 * (gamma - beta))) *
          ((((b : ENNReal) ^ (2 : Nat)) * (n : ENNReal)) ^ gapHalf) <=
          1 * (((delta : ENNReal) ^ (-cardScaleExponent)) ^ gapHalf) :=
        mul_le_mul' hbGap hXGap
      _ = (delta : ENNReal) ^
          (-(cardScaleExponent * gapHalf)) := by
        rw [one_mul,
          show -(cardScaleExponent * gapHalf) =
            (-cardScaleExponent) * gapHalf by ring,
          ENNReal.rpow_mul]
  rw [sectionEight_to_one_beta_eq_gap_mul_gamma hb hn]
  exact mul_le_mul' hgapPower le_rfl

#print axioms sectionEight_to_one_beta_eq_gap_mul_gamma
#print axioms sectionEight_to_one_beta_le_power_mul_gamma

end
end Family8SectionEightBetaGammaCardScaleBridgeV3
