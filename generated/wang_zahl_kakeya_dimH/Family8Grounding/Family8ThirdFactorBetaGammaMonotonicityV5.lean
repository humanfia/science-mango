import Family8Grounding.Family8ThreeScaleFrostmanFactorAlgebraV2
import Mathlib.Tactic

/-!
# A coupled beta-to-gamma comparison for the Section-8 third factor, V5

V1--V4 are failed elaboration drafts and are not imported.  This successor
records the exact coupled quotient `(b^6 * n)^((gamma-beta)/2)`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open scoped ENNReal NNReal

namespace Family8ThirdFactorBetaGammaMonotonicityV5

open Family8ThreeScaleFrostmanFactorAlgebraV2

noncomputable section

/-- On a nonempty outer-scale family, the coupled smallness of scale and
cardinality makes the literal Section-8 third factor monotone from `beta`
to `gamma`. -/
theorem sectionEightThirdFactor_beta_le_gamma_of_sixthPower_card
    {b : NNReal} {tubeCount : Nat} {beta gamma : Real}
    (hb : 0 < b) (hcount : 0 < tubeCount)
    (hbetaGamma : beta <= gamma) (hgammaTwo : gamma <= 2)
    (hsmall : (b : ENNReal) ^ (6 : Nat) * (tubeCount : ENNReal) <= 1) :
    sectionEightScaleCountFrostmanFactor b 1 tubeCount beta <=
      sectionEightScaleCountFrostmanFactor b 1 tubeCount gamma := by
  have hbetaTwo : beta <= 2 := hbetaGamma.trans hgammaTwo
  rw [sectionEightScaleCountFrostmanFactor_eq hb (by norm_num) hbetaTwo,
    sectionEightScaleCountFrostmanFactor_eq hb (by norm_num) hgammaTwo]
  simp only [ENNReal.coe_one, div_one]
  let gap : Real := (gamma - beta) / 2
  have hb0 : (b : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hb.ne'
  have hbTop : (b : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.coe_ne_top
  have hn0 : (tubeCount : ENNReal) ≠ 0 := by
    exact_mod_cast hcount.ne'
  have hnTop : (tubeCount : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.coe_ne_top
  have hgap : 0 <= gap := by
    dsimp only [gap]
    linarith
  have hgapPower :
      (((b : ENNReal) ^ (6 : Nat) * (tubeCount : ENNReal)) ^ gap) <= 1 := by
    calc
      ((b : ENNReal) ^ (6 : Nat) * (tubeCount : ENNReal)) ^ gap <=
          (1 : ENNReal) ^ gap := ENNReal.rpow_le_rpow hsmall hgap
      _ = 1 := ENNReal.one_rpow gap
  have hfactor :
      (b : ENNReal) ^ (-2 * beta + 2 * (1 - beta / 2)) *
          (tubeCount : ENNReal) ^ (1 - beta / 2) =
        ((b : ENNReal) ^ (-2 * gamma + 2 * (1 - gamma / 2)) *
            (tubeCount : ENNReal) ^ (1 - gamma / 2)) *
          (((b : ENNReal) ^ (6 : Nat) *
            (tubeCount : ENNReal)) ^ gap) := by
    symm
    calc
      ((b : ENNReal) ^ (-2 * gamma + 2 * (1 - gamma / 2)) *
            (tubeCount : ENNReal) ^ (1 - gamma / 2)) *
          (((b : ENNReal) ^ (6 : Nat) *
            (tubeCount : ENNReal)) ^ gap) =
        ((b : ENNReal) ^ (-2 * gamma + 2 * (1 - gamma / 2)) *
            (b : ENNReal) ^ ((6 : Real) * gap)) *
          ((tubeCount : ENNReal) ^ (1 - gamma / 2) *
            (tubeCount : ENNReal) ^ gap) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hgap,
            ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          ac_rfl
      _ = (b : ENNReal) ^
            ((-2 * gamma + 2 * (1 - gamma / 2)) + (6 : Real) * gap) *
          (tubeCount : ENNReal) ^ ((1 - gamma / 2) + gap) := by
          rw [← ENNReal.rpow_add _ _ hb0 hbTop,
            ← ENNReal.rpow_add _ _ hn0 hnTop]
      _ = (b : ENNReal) ^ (-2 * beta + 2 * (1 - beta / 2)) *
          (tubeCount : ENNReal) ^ (1 - beta / 2) := by
          congr 1 <;> dsimp only [gap] <;> ring
  calc
    (b : ENNReal) ^ (-2 * beta + 2 * (1 - beta / 2)) *
          (tubeCount : ENNReal) ^ (1 - beta / 2) =
        ((b : ENNReal) ^ (-2 * gamma + 2 * (1 - gamma / 2)) *
            (tubeCount : ENNReal) ^ (1 - gamma / 2)) *
          (((b : ENNReal) ^ (6 : Nat) *
            (tubeCount : ENNReal)) ^ gap) := hfactor
    _ <= ((b : ENNReal) ^ (-2 * gamma + 2 * (1 - gamma / 2)) *
            (tubeCount : ENNReal) ^ (1 - gamma / 2)) * 1 :=
      mul_le_mul' le_rfl hgapPower
    _ = (b : ENNReal) ^ (-2 * gamma + 2 * (1 - gamma / 2)) *
          (tubeCount : ENNReal) ^ (1 - gamma / 2) := mul_one _

#print axioms sectionEightThirdFactor_beta_le_gamma_of_sixthPower_card

end
end Family8ThirdFactorBetaGammaMonotonicityV5
