import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace FamilyStickyCinematicL32RectangleScaleNormalizationV1

/-!
# Square-root scale normalization for cinematic rectangles

This module records the exact algebra used in Pramanik--Yang--Zahl,
arXiv:2207.02259v3, Lemma 3.15.  With

`L = sqrt (delta / t)` and `S = sqrt (delta * t)`, one has
`S * L = delta` and `t * L^2 = delta`.  These identities discharge the
constant comparisons in equations (3.9)--(3.10) rather than leaving them as
upstream hypotheses.
-/

/-- The rectangle base scale is positive. -/
theorem rectangleBaseScale_pos {delta t : Real}
    (hdelta : 0 < delta) (ht : 0 < t) :
    0 < Real.sqrt (delta / t) := by
  exact Real.sqrt_pos.2 (div_pos hdelta ht)

/-- The slope scale is positive. -/
theorem rectangleSlopeScale_pos {delta t : Real}
    (hdelta : 0 < delta) (ht : 0 < t) :
    0 < Real.sqrt (delta * t) := by
  exact Real.sqrt_pos.2 (mul_pos hdelta ht)

/-- Product of the slope and base square-root scales. -/
theorem slopeScale_mul_baseScale {delta t : Real}
    (hdelta : 0 < delta) (ht : 0 < t) :
    Real.sqrt (delta * t) * Real.sqrt (delta / t) = delta := by
  apply (sq_eq_sq₀
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (le_of_lt hdelta)).mp
  rw [mul_pow, Real.sq_sqrt (mul_nonneg (le_of_lt hdelta) (le_of_lt ht)),
    Real.sq_sqrt (div_nonneg (le_of_lt hdelta) (le_of_lt ht))]
  field_simp [ht.ne']

/-- Squaring the base scale and multiplying by `t` recovers `delta`. -/
theorem t_mul_baseScale_sq {delta t : Real}
    (hdelta : 0 < delta) (ht : 0 < t) :
    t * (Real.sqrt (delta / t)) ^ 2 = delta := by
  rw [Real.sq_sqrt (div_nonneg (le_of_lt hdelta) (le_of_lt ht))]
  field_simp [ht.ne']

/-- If `lambda >= 4`, two overlapping fine bases fit into the enlarged
`sqrt (lambda * delta / t)` base scale. -/
theorem two_baseScales_le_enlargedBaseScale
    {delta t lambda : Real}
    (hdelta : 0 < delta) (ht : 0 < t) (hlambda : 4 <= lambda) :
    2 * Real.sqrt (delta / t) <=
      Real.sqrt (lambda * delta / t) := by
  have hratio : 0 <= delta / t :=
    div_nonneg (le_of_lt hdelta) (le_of_lt ht)
  have henlarged : 0 <= lambda * delta / t := by
    positivity
  apply (sq_le_sq₀ (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt hratio, Real.sq_sqrt henlarged]
  have hscaled := mul_le_mul_of_nonneg_right hlambda hratio
  convert hscaled using 1 <;> ring

/-- Exact constant comparison used to turn a slope gap at most
`sqrt(delta*t)` into `100`-comparability. -/
theorem smallSlope_comparability_constant
    {delta t : Real} (hdelta : 0 < delta) (ht : 0 < t) :
    2 * delta +
        (Real.sqrt (delta * t) +
          (6 * t) * Real.sqrt (delta / t)) *
            Real.sqrt (delta / t) <=
      (100 - 1 : Real) * delta := by
  have hSL := slopeScale_mul_baseScale hdelta ht
  have htL := t_mul_baseScale_sq hdelta ht
  calc
    2 * delta +
        (Real.sqrt (delta * t) +
          (6 * t) * Real.sqrt (delta / t)) *
            Real.sqrt (delta / t) = 9 * delta := by
      rw [add_mul, hSL]
      nlinarith
    _ <= (100 - 1 : Real) * delta := by nlinarith

/-- Exact constant comparison used in the common-container slope upper
bound.  The paper assumes `lambda >= 100`; the algebra only needs
`lambda >= 12`. -/
theorem commonContainer_slopeRange_constant
    {delta t lambda : Real}
    (hdelta : 0 < delta) (ht : 0 < t) (hlambda : 12 <= lambda) :
    4 * (lambda * delta) +
        2 * (6 * t) * (Real.sqrt (delta / t)) ^ 2 <=
      (10 * lambda * Real.sqrt (delta * t)) *
        (Real.sqrt (delta / t) / 2) := by
  have hSL := slopeScale_mul_baseScale hdelta ht
  have htL := t_mul_baseScale_sq hdelta ht
  have hcurvatureTerm :
      2 * (6 * t) * (Real.sqrt (delta / t)) ^ 2 =
        12 * delta := by
    nlinarith
  calc
    4 * (lambda * delta) +
        2 * (6 * t) * (Real.sqrt (delta / t)) ^ 2 =
      (4 * lambda + 12) * delta := by
        rw [hcurvatureTerm]
        ring
    _ <= 5 * lambda * delta := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hlambda) (le_of_lt hdelta)]
    _ = 5 * lambda *
        (Real.sqrt (delta * t) * Real.sqrt (delta / t)) := by
      rw [hSL]
    _ = (10 * lambda * Real.sqrt (delta * t)) *
        (Real.sqrt (delta / t) / 2) := by
      ring

#print axioms rectangleBaseScale_pos
#print axioms rectangleSlopeScale_pos
#print axioms slopeScale_mul_baseScale
#print axioms t_mul_baseScale_sq
#print axioms two_baseScales_le_enlargedBaseScale
#print axioms smallSlope_comparability_constant
#print axioms commonContainer_slopeRange_constant

end FamilyStickyCinematicL32RectangleScaleNormalizationV1
