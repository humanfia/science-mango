import ArchonPhysics.ResonanceKernelLipschitz

/-!
# Quantitative empirical-measure transfer for the finite-time resonance peak

A discrete empirical phase-mismatch measure does not have a Lebesgue density.
Consequently, density convergence cannot be applied to it at a fixed finite
system size.  This module instead isolates an honest bounded-Lipschitz testing
hypothesis and records the price of testing against the time-dependent
normalized resonance peak.

At observation time `T > 0`, the peak has height at most `T / (2*pi)` and
Lipschitz constant at most `T^2 / pi`.  Thus a bounded-Lipschitz integral error
`epsilon` gives an error at most

`epsilon * (T / (2*pi) + T^2 / pi)`.

No convergence of a random-lattice empirical measure is proved or assumed
implicitly here: that model-specific probabilistic estimate must be supplied
as an explicit `boundedLipschitzIntegralError` hypothesis.
-/

namespace ArchonPhysics.QuantitativeEmpiricalResonanceTransfer

open Filter MeasureTheory
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.ResonanceKernelLipschitz
open ArchonPhysics.UniformCollisionDensityTransfer

noncomputable section

/-- An explicit integral-error hypothesis for bounded Lipschitz tests.

The convention used here is the sum of a supplied uniform-height bound and a
supplied real Lipschitz bound.  Integrability is included in the quantified
hypotheses so the definition remains meaningful for general measures.  The
applications below use finite measures, as empirical probability measures
are finite. -/
def boundedLipschitzIntegralError
    (mu nu : Measure Real) (epsilon : Real) : Prop :=
  forall (f : Real -> Real) (height slope : Real),
    Integrable f mu -> Integrable f nu ->
    0 <= height -> 0 <= slope ->
    (forall x, |f x| <= height) ->
    (forall x y, |f x - f y| <= slope * |x - y|) ->
    |(∫ x, f x ∂mu) - (∫ x, f x ∂nu)| <=
      epsilon * (height + slope)

/-- The bounded-Lipschitz size furnished by the elementary height and slope
bounds for the normalized finite-time resonance peak. -/
def resonanceKernelBLSize (T : Real) : Real :=
  T / (2 * Real.pi) + T ^ 2 / Real.pi

theorem resonanceKernelBLSize_nonneg {T : Real} (hT : 0 <= T) :
    0 <= resonanceKernelBLSize T := by
  unfold resonanceKernelBLSize
  positivity

/-- The exact displayed kernel size is bounded by the simpler polynomial
`T + T^2`.  This produces a convenient joint-scale hypothesis. -/
theorem resonanceKernelBLSize_le_time_add_sq {T : Real} (hT : 0 <= T) :
    resonanceKernelBLSize T <= T + T ^ 2 := by
  unfold resonanceKernelBLSize
  have hpi : 1 <= Real.pi := by linarith [Real.pi_gt_three]
  have htwoPi : 1 <= 2 * Real.pi := by linarith [Real.pi_gt_three]
  exact add_le_add (div_le_self hT htwoPi)
    (div_le_self (sq_nonneg T) hpi)

/-- A normalized finite-time resonance peak is integrable against every
finite measure, using its explicit global height bound. -/
theorem integrable_normalizedFiniteTimeResonanceKernel_finiteMeasure
    (mu : Measure Real) [IsFiniteMeasure mu]
    {T : Real} (hT : 0 < T) :
    Integrable
      (fun Omega : Real => normalizedFiniteTimeResonanceKernel Omega T) mu := by
  apply Integrable.of_bound
    (continuous_normalizedFiniteTimeResonanceKernel hT).aestronglyMeasurable
    (T / (2 * Real.pi))
  exact ae_of_all mu fun Omega => by
    rw [Real.norm_eq_abs]
    exact abs_normalizedFiniteTimeResonanceKernel_le_height Omega hT

/-- Fixed-time empirical/reference transfer.  The two summands in the bound
are respectively the peak-height and peak-slope costs. -/
theorem abs_integral_normalizedKernel_sub_le_of_boundedLipschitzError
    (mu nu : Measure Real) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    {epsilon T : Real} (hT : 0 < T)
    (hBL : boundedLipschitzIntegralError mu nu epsilon) :
    |(∫ Omega : Real,
        normalizedFiniteTimeResonanceKernel Omega T ∂mu) -
      (∫ Omega : Real,
        normalizedFiniteTimeResonanceKernel Omega T ∂nu)| <=
      epsilon * resonanceKernelBLSize T := by
  apply hBL
  · exact integrable_normalizedFiniteTimeResonanceKernel_finiteMeasure mu hT
  · exact integrable_normalizedFiniteTimeResonanceKernel_finiteMeasure nu hT
  · positivity
  · positivity
  · intro Omega
    exact abs_normalizedFiniteTimeResonanceKernel_le_height Omega hT
  · intro Omega Xi
    exact abs_normalizedFiniteTimeResonanceKernel_sub_le Omega Xi hT

/-- Joint transfer at varying system size and observation time, stated with
the exact bounded-Lipschitz size of the time-dependent peak. -/
theorem tendsto_integral_normalizedKernel_sub_zero
    {mu nu : Nat -> Measure Real}
    (hmuFinite : forall n, IsFiniteMeasure (mu n))
    (hnuFinite : forall n, IsFiniteMeasure (nu n))
    {epsilon time : Nat -> Real}
    (htime : forall n, 0 < time n)
    (hBL : forall n,
      boundedLipschitzIntegralError (mu n) (nu n) (epsilon n))
    (hscale : Tendsto
      (fun n => epsilon n * resonanceKernelBLSize (time n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (∫ Omega : Real,
          normalizedFiniteTimeResonanceKernel Omega (time n) ∂mu n) -
        (∫ Omega : Real,
          normalizedFiniteTimeResonanceKernel Omega (time n) ∂nu n))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero
    (g := fun n => epsilon n * resonanceKernelBLSize (time n))
  · intro n
    positivity
  · intro n
    rw [Real.norm_eq_abs]
    exact @abs_integral_normalizedKernel_sub_le_of_boundedLipschitzError
      (mu n) (nu n) (hmuFinite n) (hnuFinite n)
      (epsilon n) (time n) (htime n) (hBL n)
  · exact hscale

/-- Convenient joint-scale corollary.  It is enough that the empirical
bounded-Lipschitz error beats both peak height and peak slope, in the form
`epsilon_n * (T_n + T_n^2) -> 0`. -/
theorem tendsto_integral_normalizedKernel_sub_zero_of_error_mul_time_add_sq
    {mu nu : Nat -> Measure Real}
    (hmuFinite : forall n, IsFiniteMeasure (mu n))
    (hnuFinite : forall n, IsFiniteMeasure (nu n))
    {epsilon time : Nat -> Real}
    (hepsilon : forall n, 0 <= epsilon n)
    (htime : forall n, 0 < time n)
    (hBL : forall n,
      boundedLipschitzIntegralError (mu n) (nu n) (epsilon n))
    (hscale : Tendsto
      (fun n => epsilon n * (time n + time n ^ 2))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (∫ Omega : Real,
          normalizedFiniteTimeResonanceKernel Omega (time n) ∂mu n) -
        (∫ Omega : Real,
          normalizedFiniteTimeResonanceKernel Omega (time n) ∂nu n))
      atTop (nhds 0) := by
  apply tendsto_integral_normalizedKernel_sub_zero
    hmuFinite hnuFinite htime hBL
  apply squeeze_zero
    (g := fun n => epsilon n * (time n + time n ^ 2))
  · intro n
    exact mul_nonneg (hepsilon n)
      (resonanceKernelBLSize_nonneg (htime n).le)
  · intro n
    exact mul_le_mul_of_nonneg_left
      (resonanceKernelBLSize_le_time_add_sq (htime n).le)
      (hepsilon n)
  · exact hscale

/-- If the reference resonance action has a known limit, the empirical
action has the same limit once their quantitative difference tends to zero. -/
theorem tendsto_integral_normalizedKernel_of_reference
    {mu nu : Nat -> Measure Real} {time : Nat -> Real} {limit : Real}
    (hdifference : Tendsto
      (fun n =>
        (∫ Omega : Real,
          normalizedFiniteTimeResonanceKernel Omega (time n) ∂mu n) -
        (∫ Omega : Real,
          normalizedFiniteTimeResonanceKernel Omega (time n) ∂nu n))
      atTop (nhds 0))
    (href : Tendsto
      (fun n => ∫ Omega : Real,
        normalizedFiniteTimeResonanceKernel Omega (time n) ∂nu n)
      atTop (nhds limit)) :
    Tendsto
      (fun n => ∫ Omega : Real,
        normalizedFiniteTimeResonanceKernel Omega (time n) ∂mu n)
      atTop (nhds limit) := by
  convert hdifference.add href using 1 <;> simp

end

end ArchonPhysics.QuantitativeEmpiricalResonanceTransfer
