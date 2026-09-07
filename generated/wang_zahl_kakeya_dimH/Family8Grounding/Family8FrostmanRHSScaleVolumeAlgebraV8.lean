import Family8Grounding.Family8FrostmanRHSScaleVolumeAlgebraV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8FrostmanRHSScaleVolumeAlgebraV8

open Family8KatzTaoFrostmanPropertiesV1
open Family8FrostmanRHSScaleVolumeAlgebraV4

noncomputable section

/-! ## Honest scalar-power absorption into an improved exponent -/

/-- A scalar cap `K ≤ delta^-kappa` and a genuine source-volume floor
`delta^lambda ≤ V` absorb an exponent decrement `nu`.  The exact numerical
cost is

`kappa + 2 nu + lambda nu / 2 ≤ targetEpsilon - sourceEpsilon`.

This is the minimal algebraic obligation left after the V5 source-volume
connector; neither the improved multiplicity estimate nor `himprove` is an
input. -/
theorem scalar_mul_frostmanMultiplicityRHS_le_improved_of_power_budgets
    {delta : NNReal} {actualVolume scalar : ENNReal}
    {sourceEpsilon targetEpsilon gamma nu kappa lambda : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (hvolumeTop : actualVolume ≠ ∞)
    (hscalar : scalar <= (delta : ENNReal) ^ (-kappa))
    (hvolume : (delta : ENNReal) ^ lambda <= actualVolume)
    (hnu : 0 <= nu)
    (hbudget :
      kappa + 2 * nu + lambda * nu / 2 <=
        targetEpsilon - sourceEpsilon) :
    scalar *
        frostmanMultiplicityRHS delta actualVolume sourceEpsilon gamma <=
      frostmanMultiplicityRHS delta actualVolume targetEpsilon (gamma - nu) := by
  let d : ENNReal := (delta : ENNReal)
  let q : Real := nu / 2
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hdOne : d <= 1 := by
    dsimp only [d]
    exact_mod_cast hdeltaOne
  have hq : 0 <= q := by
    dsimp only [q]
    linarith
  have hdLambdaPos : 0 < d ^ lambda :=
    ENNReal.rpow_pos (ENNReal.coe_pos.mpr hdelta) hdTop
  have hvolumePos : 0 < actualVolume := hdLambdaPos.trans_le hvolume
  have hvolume0 : actualVolume ≠ 0 := hvolumePos.ne'
  have hvolumePow : d ^ (lambda * q) <= actualVolume ^ q := by
    calc
      d ^ (lambda * q) = (d ^ lambda) ^ q :=
        ENNReal.rpow_mul d lambda q
      _ <= actualVolume ^ q := ENNReal.rpow_le_rpow hvolume hq
  have hvolumeNeg :
      actualVolume ^ (-nu / 2) <= d ^ (-lambda * nu / 2) := by
    calc
      actualVolume ^ (-nu / 2) = actualVolume ^ (-q) := by
        congr 1
        dsimp only [q]
        ring
      _ = (actualVolume ^ q)⁻¹ := ENNReal.rpow_neg actualVolume q
      _ <= (d ^ (lambda * q))⁻¹ := ENNReal.inv_le_inv' hvolumePow
      _ = d ^ (-(lambda * q)) :=
        (ENNReal.rpow_neg d (lambda * q)).symm
      _ = d ^ (-lambda * nu / 2) := by
        congr 1
        dsimp only [q]
        ring
  have hexponent :
      0 <= -kappa + (targetEpsilon - sourceEpsilon - 2 * nu) +
        (-lambda * nu / 2) := by
    linarith
  have hfactor :
      scalar * d ^ (targetEpsilon - sourceEpsilon - 2 * nu) *
          actualVolume ^ (-nu / 2) <= 1 := by
    calc
      scalar * d ^ (targetEpsilon - sourceEpsilon - 2 * nu) *
            actualVolume ^ (-nu / 2) <=
          d ^ (-kappa) *
            d ^ (targetEpsilon - sourceEpsilon - 2 * nu) *
              d ^ (-lambda * nu / 2) := by
        exact mul_le_mul' (mul_le_mul' hscalar le_rfl) hvolumeNeg
      _ = d ^
          (-kappa + (targetEpsilon - sourceEpsilon - 2 * nu) +
            (-lambda * nu / 2)) := by
        rw [← ENNReal.rpow_add (-kappa)
          (targetEpsilon - sourceEpsilon - 2 * nu) hd0 hdTop,
          ← ENNReal.rpow_add
            (-kappa + (targetEpsilon - sourceEpsilon - 2 * nu))
            (-lambda * nu / 2) hd0 hdTop]
      _ <= 1 := ENNReal.rpow_le_one hdOne hexponent
  have hfactorization :
      scalar *
          frostmanMultiplicityRHS delta actualVolume sourceEpsilon gamma =
        frostmanMultiplicityRHS delta actualVolume targetEpsilon
            (gamma - nu) *
          (scalar * d ^
              (targetEpsilon - sourceEpsilon - 2 * nu) *
            actualVolume ^ (-nu / 2)) := by
    unfold frostmanMultiplicityRHS
    dsimp only [d]
    have hdCombine :
        (delta : ENNReal) ^ (-targetEpsilon) *
              (delta : ENNReal) ^ (-2 * (gamma - nu)) *
              (delta : ENNReal) ^
                (targetEpsilon - sourceEpsilon - 2 * nu) =
            (delta : ENNReal) ^ (-sourceEpsilon) *
              (delta : ENNReal) ^ (-2 * gamma) := by
      calc
        (delta : ENNReal) ^ (-targetEpsilon) *
              (delta : ENNReal) ^ (-2 * (gamma - nu)) *
              (delta : ENNReal) ^
                (targetEpsilon - sourceEpsilon - 2 * nu) =
            (delta : ENNReal) ^
              ((-targetEpsilon) + (-2 * (gamma - nu)) +
                (targetEpsilon - sourceEpsilon - 2 * nu)) := by
          rw [← ENNReal.rpow_add (-targetEpsilon)
            (-2 * (gamma - nu)) hd0 hdTop,
            ← ENNReal.rpow_add
              ((-targetEpsilon) + (-2 * (gamma - nu)))
              (targetEpsilon - sourceEpsilon - 2 * nu) hd0 hdTop]
        _ = (delta : ENNReal) ^
              ((-sourceEpsilon) + (-2 * gamma)) := by
          congr 1
          ring
        _ = (delta : ENNReal) ^ (-sourceEpsilon) *
              (delta : ENNReal) ^ (-2 * gamma) :=
          ENNReal.rpow_add (-sourceEpsilon) (-2 * gamma) hd0 hdTop
    have hvolumeCombine :
        actualVolume ^ (1 - (gamma - nu) / 2) *
            actualVolume ^ (-nu / 2) =
          actualVolume ^ (1 - gamma / 2) := by
      calc
        actualVolume ^ (1 - (gamma - nu) / 2) *
              actualVolume ^ (-nu / 2) =
            actualVolume ^
              ((1 - (gamma - nu) / 2) + (-nu / 2)) := by
          rw [← ENNReal.rpow_add (1 - (gamma - nu) / 2)
            (-nu / 2) hvolume0 hvolumeTop]
        _ = actualVolume ^ (1 - gamma / 2) := by
          congr 1
          ring
    rw [← hdCombine, ← hvolumeCombine]
    ac_rfl
  calc
    scalar *
          frostmanMultiplicityRHS delta actualVolume sourceEpsilon gamma =
        frostmanMultiplicityRHS delta actualVolume targetEpsilon
            (gamma - nu) *
          (scalar * d ^
              (targetEpsilon - sourceEpsilon - 2 * nu) *
            actualVolume ^ (-nu / 2)) := hfactorization
    _ <= frostmanMultiplicityRHS delta actualVolume targetEpsilon
          (gamma - nu) * 1 := mul_le_mul_right hfactor _
    _ = frostmanMultiplicityRHS delta actualVolume targetEpsilon
          (gamma - nu) := by simp

#print axioms
  scalar_mul_frostmanMultiplicityRHS_le_improved_of_power_budgets

end
end Family8FrostmanRHSScaleVolumeAlgebraV8
