import ArchonPhysics.FrozenUniformMassMoments
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A concrete affine one-mass Fourier-decay certificate

The canonical mass coordinate is uniform on `[4/5, 6/5]`.  This file computes
the expectation of a constant complex weight times the Fourier character of
the affine one-coordinate mismatch `slope * mass + intercept`.  The compact
interval integral gives an exact endpoint formula and hence a fully explicit
`1 / |time|` estimate when the slope is nonzero.

This is deliberately a local model certificate.  In particular,
`affineOneMassMismatch` is not asserted to equal an eigenfrequency mismatch
of the random FPUT operator.  Using this result for such a mismatch still
requires a model-specific affine chart or comparison theorem.
-/

namespace ArchonPhysics.CanonicalUniformAffineMassFourierDecay

open ArchonPhysics
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- A nonconstant affine mismatch in one mass variable when `slope != 0`.
It is only a local comparison model, not the actual spectral mismatch. -/
def affineOneMassMismatch (slope intercept mass : Real) : Real :=
  slope * mass + intercept

/-- The Fourier character of the affine one-mass mismatch. -/
def affineOneMassCharacter
    (slope intercept time mass : Real) : Complex :=
  Complex.exp
    (Complex.I *
      ((time * affineOneMassMismatch slope intercept mass : Real) : Complex))

/-- Uniform one-coordinate expectation with a constant complex weight. -/
def uniformAffineOneMassExpectation
    (slope intercept time : Real) (weight : Complex) : Complex :=
  ∫ mass : Real, affineOneMassCharacter slope intercept time mass * weight
    ∂(RandomEnsemble.massCoordinateLaw)

/-- The same concrete expectation pulled back to coordinate `site` of the
canonical iid mass/phase sample space. -/
def canonicalAffineOneMassExpectation
    (site : Nat) (slope intercept time : Real) (weight : Complex) : Complex :=
  ∫ omega : RandomEnsemble.SampleSpace, affineOneMassCharacter slope intercept time
          (RandomEnsemble.massAt site omega) * weight
    ∂(RandomEnsemble.canonicalLaw)

/-- The affine phase splits into a constant intercept phase and a linear mass
phase. -/
theorem affineOneMassCharacter_eq_intercept_mul_linear
    (slope intercept time mass : Real) :
    affineOneMassCharacter slope intercept time mass =
      Complex.exp (Complex.I * ((time * intercept : Real) : Complex)) *
        Complex.exp
          ((Complex.I * ((time * slope : Real) : Complex)) * (mass : Complex)) := by
  rw [← Complex.exp_add]
  unfold affineOneMassCharacter affineOneMassMismatch
  congr 1
  push_cast
  ring

/-- Complex-valued version of the exact normalized set-integral formula for
the canonical one-coordinate mass law. -/
theorem integral_massCoordinateLaw_eq_fiveHalves_smul_setIntegral
    (f : Real -> Complex) :
    (∫ x, f x ∂(RandomEnsemble.massCoordinateLaw)) =
      (5 / 2 : Real) • (∫ x in RandomEnsemble.massSupport, f x) := by
  rw [RandomEnsemble.massCoordinateLaw, ProbabilityTheory.cond]
  simp only [integral_smul_measure]
  congr 1
  simp [RandomEnsemble.massSupport, RandomEnsemble.massLower,
    RandomEnsemble.massUpper, Real.volume_Icc]
  norm_num

/-- A complex-valued support integral is the usual positively oriented
interval integral. -/
theorem integral_massSupport_eq_intervalIntegral
    (f : Real -> Complex) :
    (∫ x in RandomEnsemble.massSupport, f x) =
      ∫ x in RandomEnsemble.massLower..RandomEnsemble.massUpper, f x := by
  rw [RandomEnsemble.massSupport, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le RandomEnsemble.massLower_le_massUpper]

/-- Exact compact-interval endpoint formula for the frozen uniform law. -/
theorem uniformAffineOneMassExpectation_eq_endpoint
    {slope intercept time : Real} (weight : Complex)
    (hfrequency : time * slope ≠ 0) :
    uniformAffineOneMassExpectation slope intercept time weight =
      (5 / 2 : Real) •
        (Complex.exp (Complex.I * ((time * intercept : Real) : Complex)) *
          ((Complex.exp
              ((Complex.I * ((time * slope : Real) : Complex)) *
                (RandomEnsemble.massUpper : Complex)) -
            Complex.exp
              ((Complex.I * ((time * slope : Real) : Complex)) *
                (RandomEnsemble.massLower : Complex))) /
            (Complex.I * ((time * slope : Real) : Complex))) * weight) := by
  have hcoefficient :
      Complex.I * ((time * slope : Real) : Complex) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hfrequency)
  rw [uniformAffineOneMassExpectation,
    integral_massCoordinateLaw_eq_fiveHalves_smul_setIntegral,
    integral_massSupport_eq_intervalIntegral]
  simp_rw [affineOneMassCharacter_eq_intercept_mul_linear]
  rw [show (fun mass : Real =>
      Complex.exp (Complex.I * ((time * intercept : Real) : Complex)) *
          Complex.exp
            ((Complex.I * ((time * slope : Real) : Complex)) * (mass : Complex)) *
        weight) =
      fun mass : Real =>
        Complex.exp (Complex.I * ((time * intercept : Real) : Complex)) *
          (Complex.exp
            ((Complex.I * ((time * slope : Real) : Complex)) * (mass : Complex)) *
          weight) by funext mass; simp only [mul_assoc]]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_mul_const,
    integral_exp_mul_complex hcoefficient]
  ring_nf

/-- Exact `1 / |time * slope|` endpoint bound.  The constant `5` is twice
the normalizing density `5/2` of `Uniform[4/5, 6/5]`. -/
theorem norm_uniformAffineOneMassExpectation_le
    {slope intercept time : Real} (weight : Complex)
    (hfrequency : time * slope ≠ 0) :
    norm (uniformAffineOneMassExpectation slope intercept time weight) <=
      5 * norm weight / abs (time * slope) := by
  rw [uniformAffineOneMassExpectation_eq_endpoint weight hfrequency]
  have hphaseNorm : forall mass : Real,
      norm (Complex.exp
        ((Complex.I * ((time * slope : Real) : Complex)) * (mass : Complex))) = 1 := by
    intro mass
    rw [show (Complex.I * ((time * slope : Real) : Complex)) * (mass : Complex) =
        Complex.I * (((time * slope) * mass : Real) : Complex) by
      push_cast
      ring]
    exact Complex.norm_exp_I_mul_ofReal _
  have hinterceptNorm :
      norm (Complex.exp
        (Complex.I * ((time * intercept : Real) : Complex))) = 1 :=
    Complex.norm_exp_I_mul_ofReal _
  have hdenominatorNorm :
      norm (Complex.I * ((time * slope : Real) : Complex)) =
        abs (time * slope) := by
    rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : Real) <= 5 / 2)]
  simp only [norm_mul, hinterceptNorm, one_mul, norm_div,
    hdenominatorNorm]
  have hsub :
      norm
          (Complex.exp
              ((Complex.I * ((time * slope : Real) : Complex)) *
                (RandomEnsemble.massUpper : Complex)) -
            Complex.exp
              ((Complex.I * ((time * slope : Real) : Complex)) *
                (RandomEnsemble.massLower : Complex))) <= 2 := by
    calc
      _ <= norm (Complex.exp
              ((Complex.I * ((time * slope : Real) : Complex)) *
                (RandomEnsemble.massUpper : Complex))) +
            norm (Complex.exp
              ((Complex.I * ((time * slope : Real) : Complex)) *
                (RandomEnsemble.massLower : Complex))) := norm_sub_le _ _
      _ = 2 := by rw [hphaseNorm, hphaseNorm]; norm_num
  have habsPositive : 0 < abs (time * slope) := abs_pos.mpr hfrequency
  calc
    (5 / 2 : Real) *
          (norm
              (Complex.exp
                  ((Complex.I * ((time * slope : Real) : Complex)) *
                    (RandomEnsemble.massUpper : Complex)) -
                Complex.exp
                  ((Complex.I * ((time * slope : Real) : Complex)) *
                    (RandomEnsemble.massLower : Complex))) /
            abs (time * slope) * norm weight) <=
        (5 / 2 : Real) * (2 / abs (time * slope) * norm weight) := by
      gcongr
    _ = 5 * norm weight / abs (time * slope) := by field_simp

/-- The canonical coordinate expectation is exactly the one-coordinate law
expectation; this is the only probabilistic transport used here. -/
theorem canonicalAffineOneMassExpectation_eq_uniform
    (site : Nat) (slope intercept time : Real) (weight : Complex) :
    canonicalAffineOneMassExpectation site slope intercept time weight =
      uniformAffineOneMassExpectation slope intercept time weight := by
  let f : Real -> Complex := fun mass =>
    affineOneMassCharacter slope intercept time mass * weight
  have hf : AEStronglyMeasurable f RandomEnsemble.massCoordinateLaw := by
    apply Continuous.aestronglyMeasurable
    unfold f affineOneMassCharacter affineOneMassMismatch
    fun_prop
  simpa [canonicalAffineOneMassExpectation, uniformAffineOneMassExpectation,
    f, Function.comp_def] using
    (RandomEnsemble.massAt_hasLaw site).integral_comp hf

/-- Explicit canonical `1 / |time * slope|` certificate. -/
theorem norm_canonicalAffineOneMassExpectation_le
    (site : Nat) {slope intercept time : Real} (weight : Complex)
    (hfrequency : time * slope ≠ 0) :
    norm (canonicalAffineOneMassExpectation
      site slope intercept time weight) <=
        5 * norm weight / abs (time * slope) := by
  rw [canonicalAffineOneMassExpectation_eq_uniform]
  exact norm_uniformAffineOneMassExpectation_le weight hfrequency

/-- With a fixed nonzero affine slope, the preceding estimate has the usual
explicit `constant / |time|` form. -/
theorem norm_canonicalAffineOneMassExpectation_le_div_abs_time
    (site : Nat) {slope intercept time : Real} (weight : Complex)
    (hslope : slope ≠ 0) (htime : time ≠ 0) :
    norm (canonicalAffineOneMassExpectation
      site slope intercept time weight) <=
        (5 * norm weight / abs slope) / abs time := by
  have hfrequency : time * slope ≠ 0 := mul_ne_zero htime hslope
  calc
    _ <= 5 * norm weight / abs (time * slope) :=
      norm_canonicalAffineOneMassExpectation_le site weight hfrequency
    _ = (5 * norm weight / abs slope) / abs time := by
      rw [abs_mul]
      field_simp [abs_ne_zero.mpr hslope, abs_ne_zero.mpr htime]

/-- Fully concrete local certificate: the canonical expectation of
`exp (I * time * (massAt site - 1))`.  This remains a one-coordinate affine
model and is not identified here with any eigenfrequency mismatch. -/
def canonicalCenteredMassFourierExpectation
    (site : Nat) (time : Real) : Complex :=
  canonicalAffineOneMassExpectation site 1 (-1) time 1

/-- The centered canonical uniform mass character has the explicit endpoint
bound `5 / |time|` at every nonzero time. -/
theorem norm_canonicalCenteredMassFourierExpectation_le
    (site : Nat) {time : Real} (htime : time ≠ 0) :
    norm (canonicalCenteredMassFourierExpectation site time) ≤
      5 / abs time := by
  simpa [canonicalCenteredMassFourierExpectation] using
    (norm_canonicalAffineOneMassExpectation_le_div_abs_time
      site (slope := (1 : Real)) (intercept := (-1 : Real))
      (weight := (1 : Complex)) one_ne_zero htime)

end

end ArchonPhysics.CanonicalUniformAffineMassFourierDecay
