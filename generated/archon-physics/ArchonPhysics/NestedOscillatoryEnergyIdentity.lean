import ArchonPhysics.NestedOscillatoryIntegral

/-!
# Energy identity for a return nested oscillatory integral

The second Picard feedback term contains a nested integral whose outer
mismatch is the negative of its inner mismatch.  This module proves the exact
finite-time shuffle identity behind that return term:

`2 Re nested(-Delta, Delta, T) = |oscillatoryIntegral Delta T|^2`.

The proof is valid for every real mismatch and every oriented finite time.
It uses no division by the mismatch and therefore includes exact resonance.
No kinetic or long-time conclusion is asserted.
-/

namespace ArchonPhysics.NestedOscillatoryEnergyIdentity

open MeasureTheory
open ArchonPhysics.NestedOscillatoryIntegral
open ArchonPhysics.NonresonantOscillatoryGain
open scoped ComplexConjugate Interval

noncomputable section

/-- Fundamental-theorem-of-calculus derivative of the one-step oscillatory
integral. -/
theorem hasDerivAt_oscillatoryIntegral
    (delta time : Real) :
    HasDerivAt (oscillatoryIntegral delta)
      (Complex.exp ((Complex.I * delta) * time)) time := by
  unfold oscillatoryIntegral
  have hcontinuous : Continuous (fun s : Real ↦
      Complex.exp ((Complex.I * delta) * s)) := by fun_prop
  exact intervalIntegral.integral_hasDerivAt_right
    (hcontinuous.intervalIntegrable (μ := volume) 0 time)
    hcontinuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    hcontinuous.continuousAt

/-- Triangular shuffle identity: the two possible time orderings partition
the product of the two one-step oscillatory integrals. -/
theorem nestedOscillatoryIntegral_add_swap
    (left right time : Real) :
    nestedOscillatoryIntegral left right time +
        nestedOscillatoryIntegral right left time =
      oscillatoryIntegral left time * oscillatoryIntegral right time := by
  unfold nestedOscillatoryIntegral
  rw [← intervalIntegral.integral_add
    (intervalIntegrable_nestedOscillatoryIntegrand left right 0 time)
    (intervalIntegrable_nestedOscillatoryIntegrand right left 0 time)]
  have hintegrand :
      (fun s : Real ↦
        Complex.exp ((Complex.I * left) * s) *
            oscillatoryIntegral right s +
          Complex.exp ((Complex.I * right) * s) *
            oscillatoryIntegral left s) =
      (fun s : Real ↦
        Complex.exp ((Complex.I * left) * s) *
            oscillatoryIntegral right s +
          oscillatoryIntegral left s *
            Complex.exp ((Complex.I * right) * s)) := by
    funext s
    ring
  rw [hintegrand]
  have hderiv (s : Real) :
      HasDerivAt
        (oscillatoryIntegral left * oscillatoryIntegral right)
        (Complex.exp ((Complex.I * left) * s) *
            oscillatoryIntegral right s +
          oscillatoryIntegral left s *
            Complex.exp ((Complex.I * right) * s)) s :=
    (hasDerivAt_oscillatoryIntegral left s).mul
      (hasDerivAt_oscillatoryIntegral right s)
  have hintegrable : IntervalIntegrable
      (fun s : Real ↦
        Complex.exp ((Complex.I * left) * s) *
            oscillatoryIntegral right s +
          oscillatoryIntegral left s *
            Complex.exp ((Complex.I * right) * s)) volume 0 time :=
    (continuous_nestedOscillatoryIntegrand left right).add
      ((continuous_oscillatoryIntegral_time left).mul
        (by fun_prop : Continuous (fun s : Real ↦
          Complex.exp ((Complex.I * right) * s))))
      |>.intervalIntegrable (μ := volume) 0 time
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs ↦ hderiv s) hintegrable]
  simp [oscillatoryIntegral, Pi.mul_apply]

/-- Complex conjugation reverses the one-step mismatch. -/
theorem star_oscillatoryIntegral_eq_neg
    (delta time : Real) :
    starRingEnd Complex (oscillatoryIntegral delta time) =
      oscillatoryIntegral (-delta) time := by
  unfold oscillatoryIntegral
  rw [← intervalIntegral.intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp
  rw [← Complex.exp_conj]
  congr 1
  simp

/-- Complex conjugation reverses both nested mismatches and hence exchanges
the two return time orderings. -/
theorem star_nestedOscillatoryIntegral_eq_neg
    (deltaOut deltaIn time : Real) :
    starRingEnd Complex
        (nestedOscillatoryIntegral deltaOut deltaIn time) =
      nestedOscillatoryIntegral (-deltaOut) (-deltaIn) time := by
  unfold nestedOscillatoryIntegral
  rw [← intervalIntegral.intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp
  rw [map_mul, ← Complex.exp_conj,
    star_oscillatoryIntegral_eq_neg]
  congr 2
  simp

/-- Exact return identity used by the second-order energy interference.  It
is division-free and covers both resonant and nonresonant mismatches. -/
theorem two_mul_re_nestedOscillatoryIntegral_neg_self
    (delta time : Real) :
    2 * (nestedOscillatoryIntegral (-delta) delta time).re =
      Complex.normSq (oscillatoryIntegral delta time) := by
  have hshuffle := nestedOscillatoryIntegral_add_swap (-delta) delta time
  have hnested :=
    star_nestedOscillatoryIntegral_eq_neg (-delta) delta time
  have hone := star_oscillatoryIntegral_eq_neg delta time
  simp only [neg_neg] at hnested
  rw [← hnested, ← hone] at hshuffle
  calc
    2 * (nestedOscillatoryIntegral (-delta) delta time).re =
        (nestedOscillatoryIntegral (-delta) delta time +
          starRingEnd Complex
            (nestedOscillatoryIntegral (-delta) delta time)).re := by
      simp
      ring
    _ = (starRingEnd Complex (oscillatoryIntegral delta time) *
          oscillatoryIntegral delta time).re := congrArg Complex.re hshuffle
    _ = Complex.normSq (oscillatoryIntegral delta time) := by
      rw [mul_comm, Complex.mul_conj]
      simp

end

end ArchonPhysics.NestedOscillatoryEnergyIdentity
