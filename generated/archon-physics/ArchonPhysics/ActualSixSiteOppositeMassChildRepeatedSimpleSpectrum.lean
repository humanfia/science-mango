import ArchonPhysics.ActualFourSitePositiveProjectorWitness
import ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedExactResonance

/-!
# Simple spectrum on the opposite-mass six-site resonance slice

For reciprocal masses `x = 6 / 5` and `y` strictly between `6 / 7` and
`6 / 5`, the non-universal cubic factor of the six-site characteristic
polynomial has positive discriminant.  Exact Bezout and coprimality
certificates then show that the full characteristic polynomial, including
the structural roots `0`, `1`, and `3`, is separable.  This supplies full
simple ordered spectrum at the interior exact resonance constructed in
`ActualSixSiteOppositeMassChildRepeatedExactResonance`.
-/

open scoped Matrix

namespace ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedSimpleSpectrum

open ArchonPhysics
open ArchonPhysics.ActualFourSitePositiveProjectorWitness
open ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedExactResonance
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open Polynomial Set

noncomputable section

/-- Coefficient of `E^2` in the fixed-`x = 6/5` cubic factor. -/
def oppositeFixedCubicA (y : Real) : Real :=
  -2 * ((6 : Real) / 5 + y + 2)

/-- Coefficient of `E` in the fixed-`x = 6/5` cubic factor. -/
def oppositeFixedCubicB (y : Real) : Real :=
  4 * ((6 : Real) / 5) * y + 6 * ((6 : Real) / 5) + 6 * y + 3

/-- Constant coefficient of the fixed-`x = 6/5` cubic factor. -/
def oppositeFixedCubicC (y : Real) : Real :=
  -(8 * ((6 : Real) / 5) * y + 2 * ((6 : Real) / 5) + 2 * y)

/-- The cubic non-universal factor as a polynomial in squared frequency. -/
def oppositeFixedCubicPolynomial (y : Real) : Real[X] :=
  X ^ 3 + C (oppositeFixedCubicA y) * X ^ 2 +
    C (oppositeFixedCubicB y) * X + C (oppositeFixedCubicC y)

@[simp] theorem oppositeFixedCubicPolynomial_eval (y energy : Real) :
    (oppositeFixedCubicPolynomial y).eval energy =
      oppositeSixSiteCubic ((6 : Real) / 5) y energy := by
  simp [oppositeFixedCubicPolynomial, oppositeFixedCubicA,
    oppositeFixedCubicB, oppositeFixedCubicC, oppositeSixSiteCubic]
  ring

/-- The ordinary monic-cubic discriminant on the fixed opposite slice. -/
def oppositeFixedCubicDiscriminant (y : Real) : Real :=
  let a := oppositeFixedCubicA y
  let b := oppositeFixedCubicB y
  let c := oppositeFixedCubicC y
  a ^ 2 * b ^ 2 - 4 * b ^ 3 - 4 * a ^ 3 * c - 27 * c ^ 2 +
    18 * a * b * c

/-- First coefficient in the exact cubic Bezout identity. -/
def oppositeFixedCubicBezoutA (y : Real) : Real[X] :=
  let a := oppositeFixedCubicA y
  let b := oppositeFixedCubicB y
  let c := oppositeFixedCubicC y
  C (-6 * (a ^ 2 - 3 * b)) * X + C (-4 * a ^ 3 + 15 * a * b - 27 * c)

/-- Second coefficient in the exact cubic Bezout identity. -/
def oppositeFixedCubicBezoutB (y : Real) : Real[X] :=
  let a := oppositeFixedCubicA y
  let b := oppositeFixedCubicB y
  let c := oppositeFixedCubicC y
  C (2 * (a ^ 2 - 3 * b)) * X ^ 2 +
    C (2 * a ^ 3 - 7 * a * b + 9 * c) * X +
    C (a ^ 2 * b + 3 * a * c - 4 * b ^ 2)

/-- Exact Bezout identity for an arbitrary point of the opposite slice. -/
theorem oppositeFixedCubic_bezout_identity (y : Real) :
    oppositeFixedCubicBezoutA y * oppositeFixedCubicPolynomial y +
        oppositeFixedCubicBezoutB y *
          (oppositeFixedCubicPolynomial y).derivative =
      C (oppositeFixedCubicDiscriminant y) := by
  simp [oppositeFixedCubicBezoutA, oppositeFixedCubicBezoutB,
    oppositeFixedCubicPolynomial, oppositeFixedCubicDiscriminant,
    oppositeFixedCubicA, oppositeFixedCubicB, oppositeFixedCubicC,
    Polynomial.C_ofNat]
  ring

/-- Expanded discriminant, centered at reciprocal mass one. -/
theorem oppositeFixedCubicDiscriminant_centered (y : Real) :
    oppositeFixedCubicDiscriminant y =
      (4 / 625 : Real) *
        (6615 - 4914 * (y - 1) + 11736 * (y - 1) ^ 2 +
          12440 * (y - 1) ^ 3 + 14900 * (y - 1) ^ 4) := by
  simp [oppositeFixedCubicDiscriminant, oppositeFixedCubicA,
    oppositeFixedCubicB, oppositeFixedCubicC]
  ring

/-- The cubic discriminant is strictly positive throughout the reciprocal
mass interval induced by the open raw-mass slice. -/
theorem oppositeFixedCubicDiscriminant_pos
    {y : Real} (hy : y ∈ Set.Ioo ((6 : Real) / 7) (6 / 5)) :
    0 < oppositeFixedCubicDiscriminant y := by
  rw [oppositeFixedCubicDiscriminant_centered]
  let z := y - 1
  have hzLower : -(1 : Real) / 7 < z := by
    dsimp [z]
    linarith [hy.1]
  have hzUpper : z < (1 : Real) / 5 := by
    dsimp [z]
    linarith [hy.2]
  have hzSq : 0 ≤ z ^ 2 := sq_nonneg z
  have hzFourth : 0 ≤ z ^ 4 := by positivity
  have hbracket :
      0 < 6615 - 4914 * z + 11736 * z ^ 2 +
        12440 * z ^ 3 + 14900 * z ^ 4 := by
    by_cases hz : 0 ≤ z
    · have hzCube : 0 ≤ z ^ 3 := by positivity
      nlinarith
    · have hzNeg : z < 0 := lt_of_not_ge hz
      have hquadratic : 0 ≤ z ^ 2 - z * ((1 : Real) / 7) + (1 / 7 : Real) ^ 2 := by
        nlinarith [sq_nonneg (z - (1 : Real) / 14)]
      have hzShift : 0 ≤ z + (1 : Real) / 7 := by
        linarith
      have hproduct :
          0 ≤ (z + (1 : Real) / 7) *
            (z ^ 2 - z * ((1 : Real) / 7) + (1 / 7 : Real) ^ 2) :=
        mul_nonneg hzShift hquadratic
      have hzCubeLower : -(1 : Real) / 343 ≤ z ^ 3 := by
        nlinarith [hproduct]
      nlinarith
  positivity

/-- The cubic factor has no repeated root on the reciprocal open interval. -/
theorem oppositeFixedCubicPolynomial_separable
    {y : Real} (hy : y ∈ Set.Ioo ((6 : Real) / 7) (6 / 5)) :
    (oppositeFixedCubicPolynomial y).Separable := by
  rw [Polynomial.separable_def']
  let d := oppositeFixedCubicDiscriminant y
  have hd : d ≠ 0 := ne_of_gt (oppositeFixedCubicDiscriminant_pos hy)
  refine ⟨C d⁻¹ * oppositeFixedCubicBezoutA y,
    C d⁻¹ * oppositeFixedCubicBezoutB y, ?_⟩
  calc
    (C d⁻¹ * oppositeFixedCubicBezoutA y) * oppositeFixedCubicPolynomial y +
          (C d⁻¹ * oppositeFixedCubicBezoutB y) *
            (oppositeFixedCubicPolynomial y).derivative =
        C d⁻¹ *
          (oppositeFixedCubicBezoutA y * oppositeFixedCubicPolynomial y +
            oppositeFixedCubicBezoutB y *
              (oppositeFixedCubicPolynomial y).derivative) := by ring
    _ = C d⁻¹ * C d := by
      rw [oppositeFixedCubic_bezout_identity]
    _ = 1 := by
      rw [← C_mul]
      simp [hd]

/-- Synthetic division of the cubic by a prospective linear root. -/
def oppositeFixedCubicTailAt (y r : Real) : Real[X] :=
  X ^ 2 + C (oppositeFixedCubicA y + r) * X +
    C (oppositeFixedCubicB y + oppositeFixedCubicA y * r + r ^ 2)

theorem oppositeFixedCubic_eq_eval_add_linear_mul_tail (y r : Real) :
    oppositeFixedCubicPolynomial y =
      C ((oppositeFixedCubicPolynomial y).eval r) +
        (X - C r) * oppositeFixedCubicTailAt y r := by
  simp [oppositeFixedCubicPolynomial, oppositeFixedCubicTailAt]
  ring

/-- A nonzero value at `r` makes `X-r` coprime to the cubic. -/
theorem linear_isCoprime_oppositeFixedCubic_of_eval_ne_zero
    (y r : Real) (h : (oppositeFixedCubicPolynomial y).eval r ≠ 0) :
    IsCoprime (X - C r) (oppositeFixedCubicPolynomial y) := by
  have hunit : IsUnit
      (C ((oppositeFixedCubicPolynomial y).eval r) : Real[X]) := by
    rw [Polynomial.isUnit_C]
    exact isUnit_iff_ne_zero.mpr h
  have hconstant : IsCoprime (X - C r)
      (C ((oppositeFixedCubicPolynomial y).eval r) : Real[X]) := by
    have hcoprime : IsCoprime (X - C r)
        (C ((oppositeFixedCubicPolynomial y).eval r) * 1 : Real[X]) :=
      (isCoprime_mul_unit_left_right hunit (X - C r) (1 : Real[X])).mpr
        isCoprime_one_right
    simpa using hcoprime
  rw [oppositeFixedCubic_eq_eval_add_linear_mul_tail]
  exact hconstant.add_mul_left_right (oppositeFixedCubicTailAt y r)

theorem oppositeFixedCubic_eval_zero (y : Real) :
    (oppositeFixedCubicPolynomial y).eval 0 =
      -((58 : Real) / 5 * y + 12 / 5) := by
  simp [oppositeFixedCubicPolynomial, oppositeFixedCubicA,
    oppositeFixedCubicB, oppositeFixedCubicC]
  ring

theorem oppositeFixedCubic_eval_one (y : Real) :
    (oppositeFixedCubicPolynomial y).eval 1 =
      ((12 : Real) - 14 * y) / 5 := by
  simp [oppositeFixedCubicPolynomial, oppositeFixedCubicA,
    oppositeFixedCubicB, oppositeFixedCubicC]
  ring

theorem oppositeFixedCubic_eval_three (y : Real) :
    (oppositeFixedCubicPolynomial y).eval 3 =
      (14 * y - (12 : Real)) / 5 := by
  simp [oppositeFixedCubicPolynomial, oppositeFixedCubicA,
    oppositeFixedCubicB, oppositeFixedCubicC]
  ring

/-- The full factored polynomial on the fixed opposite slice. -/
def oppositeFixedFullPolynomial (y : Real) : Real[X] :=
  X * (X - C 1) * (X - C 3) * oppositeFixedCubicPolynomial y

/-- All structural linear factors and the cubic are mutually coprime on the
open reciprocal interval, so the full degree-six polynomial is separable. -/
theorem oppositeFixedFullPolynomial_separable
    {y : Real} (hy : y ∈ Set.Ioo ((6 : Real) / 7) (6 / 5)) :
    (oppositeFixedFullPolynomial y).Separable := by
  have hyPos : 0 < y := lt_trans (by norm_num) hy.1
  have hq0 : (oppositeFixedCubicPolynomial y).eval 0 ≠ 0 := by
    rw [oppositeFixedCubic_eval_zero]
    nlinarith
  have hq1 : (oppositeFixedCubicPolynomial y).eval 1 ≠ 0 := by
    rw [oppositeFixedCubic_eval_one]
    nlinarith [hy.1]
  have hq3 : (oppositeFixedCubicPolynomial y).eval 3 ≠ 0 := by
    rw [oppositeFixedCubic_eval_three]
    nlinarith [hy.1]
  have hXone : IsCoprime (X : Real[X]) (X - C 1) := by
    simpa using Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (a := (0 : Real)) (b := (1 : Real)) (by norm_num)
  have hXthree : IsCoprime (X : Real[X]) (X - C 3) := by
    simpa using Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (a := (0 : Real)) (b := (3 : Real)) (by norm_num)
  have honeThree : IsCoprime (X - C (1 : Real)) (X - C 3) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by norm_num)
  have hlinear : (X * (X - C 1) * (X - C 3) : Real[X]).Separable :=
    (Polynomial.separable_X.mul Polynomial.separable_X_sub_C hXone).mul
      Polynomial.separable_X_sub_C (hXthree.mul_left honeThree)
  have hXq : IsCoprime (X : Real[X]) (oppositeFixedCubicPolynomial y) := by
    simpa using linear_isCoprime_oppositeFixedCubic_of_eval_ne_zero y 0 hq0
  have honeQ : IsCoprime (X - C (1 : Real))
      (oppositeFixedCubicPolynomial y) :=
    linear_isCoprime_oppositeFixedCubic_of_eval_ne_zero y 1 hq1
  have hthreeQ : IsCoprime (X - C (3 : Real))
      (oppositeFixedCubicPolynomial y) :=
    linear_isCoprime_oppositeFixedCubic_of_eval_ne_zero y 3 hq3
  exact hlinear.mul (oppositeFixedCubicPolynomial_separable hy)
    ((hXq.mul_left honeQ).mul_left hthreeQ)

/-- The inverse coordinate of every open raw-slice mass lies in the open
reciprocal interval used by the discriminant proof. -/
theorem inv_mem_opposite_reciprocal_interval
    {s : Real} (hs : s ∈ Set.Ioo ((5 : Real) / 6) (7 / 6)) :
    s⁻¹ ∈ Set.Ioo ((6 : Real) / 7) (6 / 5) := by
  have hsPos : 0 < s := lt_trans (by norm_num) hs.1
  constructor
  · simpa using (lt_inv_mul_iff₀ hsPos).2 (show s * ((6 : Real) / 7) < 1 by
      nlinarith [hs.2])
  · exact (inv_lt_iff_one_lt_mul₀ hsPos).2 (by nlinarith [hs.1])

/-- Exact polynomial identity for the physical characteristic polynomial
at every open point of the raw opposite-mass slice. -/
theorem oppositeSixSiteHarmonic_charpoly_eq_full
    {s : Real} (hs : s ∈ Set.Ioo ((5 : Real) / 6) (7 / 6)) :
    Matrix.charpoly (Matrix.of (oppositeSixSiteHarmonic s).val) =
      oppositeFixedFullPolynomial s⁻¹ := by
  apply Polynomial.funext
  intro energy
  rw [oppositeSixSiteHarmonic_charpoly_eval
    ⟨le_of_lt hs.1, le_of_lt hs.2⟩]
  simp [oppositeFixedFullPolynomial]

/-- Every open point of the raw slice has a simple full ordered spectrum. -/
theorem oppositeSixSiteHarmonic_simpleOrderedSpectrum
    {s : Real} (hs : s ∈ Set.Ioo ((5 : Real) / 6) (7 / 6)) :
    SimpleOrderedSpectrum (oppositeSixSiteHarmonic s) := by
  apply simpleOrderedSpectrum_of_charpoly_separable
  have hmatrix :
      Matrix.of (oppositeSixSiteHarmonic s).val =
        (oppositeSixSiteHarmonic s).1 := by
    ext i j
    rfl
  rw [← hmatrix, oppositeSixSiteHarmonic_charpoly_eq_full hs]
  exact oppositeFixedFullPolynomial_separable
    (inv_mem_opposite_reciprocal_interval hs)

/-- The interior exact resonance can be chosen with full simple ordered
spectrum, not merely simplicity of the two selected modes. -/
theorem exists_interior_simple_positive_oppositeChildRepeated_exactResonance :
    ∃ s ∈ Set.Ioo ((5 : Real) / 6) (7 / 6),
      oppositeChildRepeatedMismatch s = 0 ∧
      SimpleOrderedSpectrum (oppositeSixSiteHarmonic s) ∧
      0 < orderedModeFrequency (oppositeSixSiteHarmonic s) 0 ∧
      0 < orderedModeFrequency (oppositeSixSiteHarmonic s) 3 := by
  obtain ⟨s, hs, hres, hparent, hchild⟩ :=
    exists_interior_positive_oppositeChildRepeated_exactResonance
  exact ⟨s, hs, hres, oppositeSixSiteHarmonic_simpleOrderedSpectrum hs,
    hparent, hchild⟩

end

end ArchonPhysics.ActualSixSiteOppositeMassChildRepeatedSimpleSpectrum
