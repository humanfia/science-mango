import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Algebra of a second-moment perturbation

This module isolates the exact quadratic identity behind a first Duhamel
correction.  For complex amplitudes `z`, `w` and a real parameter `epsilon`,
the squared norm of `z + epsilon * w` is an exact polynomial of degree two.

The identity is also summed over a finite type and integrated over an arbitrary
measure under explicit integrability assumptions on all three coefficients.
The integral can be read as an expectation when the supplied measure is a
probability measure.

No identification of `w` with a microscopic Duhamel term, derivation of a
collision kernel, stochastic independence, or limiting statement is made.
-/

namespace ArchonPhysics.DuhamelSecondMomentAlgebra

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

/-- The amplitude obtained by adding a real-scaled correction. -/
def perturbedAmplitude (epsilon : Real) (z w : Complex) : Complex :=
  z + (epsilon : Complex) * w

/-- Zeroth-order coefficient of the squared-norm expansion. -/
def secondMomentZeroth (z : Complex) : Real :=
  Complex.normSq z

/-- First-order interference coefficient `2 Re (z * conj w)`. -/
def secondMomentFirst (z w : Complex) : Real :=
  2 * (z * conj w).re

/-- Second-order coefficient of the squared-norm expansion. -/
def secondMomentSecond (w : Complex) : Real :=
  Complex.normSq w

/-- Exact zeroth/first/second-order expansion, with no remainder. -/
theorem normSq_perturbedAmplitude
    (z w : Complex) (epsilon : Real) :
    Complex.normSq (perturbedAmplitude epsilon z w) =
      secondMomentZeroth z + epsilon * secondMomentFirst z w +
        epsilon ^ 2 * secondMomentSecond w := by
  unfold perturbedAmplitude secondMomentZeroth secondMomentFirst secondMomentSecond
  rw [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_ofReal]
  simp only [map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero]
  ring

/-- The normalized finite average of a real observable.  On an empty type the
usual field convention makes this zero. -/
def finiteAverage {ι : Type*} [Fintype ι] (observable : ι → Real) : Real :=
  (Fintype.card ι : Real)⁻¹ * ∑ i, observable i

/-- Exact second-moment expansion after averaging over any finite mode set. -/
theorem finiteAverage_normSq_perturbedAmplitude
    {ι : Type*} [Fintype ι] (z w : ι → Complex) (epsilon : Real) :
    finiteAverage (fun i =>
        Complex.normSq (perturbedAmplitude epsilon (z i) (w i))) =
      finiteAverage (fun i => secondMomentZeroth (z i)) +
        epsilon * finiteAverage (fun i => secondMomentFirst (z i) (w i)) +
        epsilon ^ 2 * finiteAverage (fun i => secondMomentSecond (w i)) := by
  simp_rw [normSq_perturbedAmplitude]
  simp only [finiteAverage, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- Integral/expectation version of the exact expansion.  Square-integrability
cannot be replaced by mere integrability of `z` and `w`, so the three real
coefficient functions are assumed integrable explicitly. -/
theorem integral_normSq_perturbedAmplitude
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (z w : Ω → Complex) (epsilon : Real)
    (hzeroth : Integrable (fun x => secondMomentZeroth (z x)) μ)
    (hfirst : Integrable (fun x => secondMomentFirst (z x) (w x)) μ)
    (hsecond : Integrable (fun x => secondMomentSecond (w x)) μ) :
    (∫ x, Complex.normSq (perturbedAmplitude epsilon (z x) (w x)) ∂μ) =
      (∫ x, secondMomentZeroth (z x) ∂μ) +
        epsilon * (∫ x, secondMomentFirst (z x) (w x) ∂μ) +
        epsilon ^ 2 * (∫ x, secondMomentSecond (w x) ∂μ) := by
  calc
    (∫ x, Complex.normSq (perturbedAmplitude epsilon (z x) (w x)) ∂μ) =
        ∫ x, (secondMomentZeroth (z x) +
          epsilon * secondMomentFirst (z x) (w x)) +
          epsilon ^ 2 * secondMomentSecond (w x) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x =>
        normSq_perturbedAmplitude (z x) (w x) epsilon)
    _ = (∫ x, secondMomentZeroth (z x) +
          epsilon * secondMomentFirst (z x) (w x) ∂μ) +
        ∫ x, epsilon ^ 2 * secondMomentSecond (w x) ∂μ :=
      integral_add (hzeroth.add (hfirst.const_mul epsilon))
        (hsecond.const_mul (epsilon ^ 2))
    _ = _ := by
      rw [integral_add hzeroth (hfirst.const_mul epsilon),
        integral_const_mul, integral_const_mul]

end

end ArchonPhysics.DuhamelSecondMomentAlgebra
