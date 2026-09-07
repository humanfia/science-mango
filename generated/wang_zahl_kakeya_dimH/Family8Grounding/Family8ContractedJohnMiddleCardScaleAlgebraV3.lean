import Family8Grounding.Family8ThreeScaleFrostmanFactorAlgebraV2
import Mathlib.Tactic

/-!
# Card-scale algebra for the contracted-John middle factor, V3

V1 used Boolean disequality and V2 had the wrong rewrite orientation in one
power combination; neither is imported.  This successor contains only the
three small scalar facts needed by the middle adapter.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8ContractedJohnMiddleCardScaleAlgebraV3

open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8ThreeScaleFrostmanFactorAlgebraV2

noncomputable section

/-- Exact expansion of the Frostman RHS at the paper card-scale volume. -/
theorem frostmanMultiplicityRHS_cardScale_eq
    {scale : NNReal} {tubeCount : Nat} {epsilon beta : Real}
    (hscale : 0 < scale) (hbetaTwo : beta <= 2) :
    frostmanMultiplicityRHS scale
        (proposition66ACardScaleVolume scale tubeCount) epsilon beta =
      (scale : ENNReal) ^ (2 - 3 * beta - epsilon) *
        (tubeCount : ENNReal) ^ (1 - beta / 2) := by
  let s : ENNReal := scale
  let p : Real := 1 - beta / 2
  have hp : 0 <= p := by
    dsimp only [p]
    linarith
  have hs0 : s ≠ 0 := by
    dsimp only [s]
    exact ENNReal.coe_ne_zero.mpr hscale.ne'
  have hsTop : s ≠ ∞ := by
    dsimp only [s]
    exact ENNReal.coe_ne_top
  have hsquare : (s ^ (2 : Nat)) ^ p = s ^ (2 * p) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  unfold frostmanMultiplicityRHS proposition66ACardScaleVolume
  change s ^ (-epsilon) * s ^ (-2 * beta) *
      ((s ^ (2 : Nat)) * (tubeCount : ENNReal)) ^ p = _
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp, hsquare]
  calc
    s ^ (-epsilon) * s ^ (-2 * beta) *
          (s ^ (2 * p) * (tubeCount : ENNReal) ^ p) =
        (s ^ (-epsilon) * s ^ (-2 * beta) * s ^ (2 * p)) *
          (tubeCount : ENNReal) ^ p := by
      ac_rfl
    _ = s ^ ((-epsilon) + (-2 * beta) + 2 * p) *
          (tubeCount : ENNReal) ^ p := by
      rw [← ENNReal.rpow_add (-epsilon) (-2 * beta) hs0 hsTop,
        ← ENNReal.rpow_add ((-epsilon) + (-2 * beta)) (2 * p) hs0 hsTop]
    _ = (scale : ENNReal) ^ (2 - 3 * beta - epsilon) *
          (tubeCount : ENNReal) ^ (1 - beta / 2) := by
      dsimp only [s, p]
      congr 2
      ring

/-- Changing the count exponent from `beta` to `gamma` costs exactly the
appropriate power of an available relative-scale cardinality envelope. -/
theorem count_power_beta_le_envelope_mul_gamma
    {q K : ENNReal} {tubeCount : Nat} {beta gamma kappa : Real}
    (htubeCount : 0 < tubeCount)
    (hgap : 0 <= gamma - beta)
    (hcount : (tubeCount : ENNReal) <=
      K * q ^ (-(2 + kappa))) :
    (tubeCount : ENNReal) ^ (1 - beta / 2) <=
      K ^ ((gamma - beta) / 2) *
        q ^ (-((2 + kappa) * ((gamma - beta) / 2))) *
          (tubeCount : ENNReal) ^ (1 - gamma / 2) := by
  let gapHalf : Real := (gamma - beta) / 2
  have hgapHalf : 0 <= gapHalf := by
    dsimp only [gapHalf]
    linarith
  have hn0 : (tubeCount : ENNReal) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt htubeCount
  have hnTop : (tubeCount : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hcountPower := ENNReal.rpow_le_rpow hcount hgapHalf
  have henvelope :
      (K * q ^ (-(2 + kappa))) ^ gapHalf =
        K ^ gapHalf * q ^ (-((2 + kappa) * gapHalf)) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hgapHalf, ← ENNReal.rpow_mul]
    congr 2
    ring
  rw [henvelope] at hcountPower
  calc
    (tubeCount : ENNReal) ^ (1 - beta / 2) =
        (tubeCount : ENNReal) ^ gapHalf *
          (tubeCount : ENNReal) ^ (1 - gamma / 2) := by
      rw [← ENNReal.rpow_add gapHalf (1 - gamma / 2) hn0 hnTop]
      congr 1
      dsimp only [gapHalf]
      ring
    _ <= (K ^ gapHalf * q ^ (-((2 + kappa) * gapHalf))) *
          (tubeCount : ENNReal) ^ (1 - gamma / 2) :=
      mul_le_mul' hcountPower le_rfl
    _ = K ^ ((gamma - beta) / 2) *
        q ^ (-((2 + kappa) * ((gamma - beta) / 2))) *
          (tubeCount : ENNReal) ^ (1 - gamma / 2) := by
      rfl

/-- The Section 8 factor is the scale-ratio power times the target count
power, in the exact exponent form needed by the middle adapter. -/
theorem sectionEightScaleCountFrostmanFactor_eq_ratio_count
    {fine coarse : NNReal} {tubeCount : Nat} {gamma : Real}
    (hfine : 0 < fine) (hcoarse : 0 < coarse)
    (hgammaTwo : gamma <= 2) :
    sectionEightScaleCountFrostmanFactor fine coarse tubeCount gamma =
      (((fine : ENNReal) / (coarse : ENNReal)) ^ (2 - 3 * gamma)) *
        (tubeCount : ENNReal) ^ (1 - gamma / 2) := by
  rw [sectionEightScaleCountFrostmanFactor_eq hfine hcoarse hgammaTwo]
  congr 2
  ring

#print axioms frostmanMultiplicityRHS_cardScale_eq
#print axioms count_power_beta_le_envelope_mul_gamma
#print axioms sectionEightScaleCountFrostmanFactor_eq_ratio_count

end
end Family8ContractedJohnMiddleCardScaleAlgebraV3
