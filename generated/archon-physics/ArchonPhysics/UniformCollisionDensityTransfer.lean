import ArchonPhysics.NormalizedResonancePeakKernel

/-!
# Uniform phase-density transfer to the exact resonance value

The normalized finite-time resonance profile is a positive unit-mass kernel.
This module proves a stable transfer principle: if a sequence of integrable
phase-mismatch densities converges uniformly to an integrable density that is
continuous at zero, then testing the varying densities at any observation
times tending to infinity converges to the limiting density at exact
resonance.

For the random lattice, the remaining model-specific task is to prove that
the weighted empirical phase-mismatch data admit densities satisfying this
uniform approximation (or a weaker replacement).  It is not assumed here.
-/

namespace ArchonPhysics.UniformCollisionDensityTransfer

open Filter MeasureTheory
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.NormalizedResonancePeakKernel

noncomputable section

theorem normalizedFiniteTimeResonanceKernel_nonneg
    (Omega T : Real) :
    0 <= normalizedFiniteTimeResonanceKernel Omega T := by
  unfold normalizedFiniteTimeResonanceKernel
  exact div_nonneg (finiteTimeResonanceWeight_nonneg Omega T)
    (mul_nonneg (by norm_num) sincSquareMass_pos.le)

theorem continuous_normalizedSincSquareKernel :
    Continuous normalizedSincSquareKernel := by
  unfold normalizedSincSquareKernel
  exact continuous_const.mul continuous_sincSquareKernel

theorem continuous_normalizedFiniteTimeResonanceKernel
    {T : Real} (hT : 0 < T) :
    Continuous (fun Omega : Real =>
      normalizedFiniteTimeResonanceKernel Omega T) := by
  have hfun : (fun Omega : Real =>
      normalizedFiniteTimeResonanceKernel Omega T) =
      fun Omega => (T / 2) *
        normalizedSincSquareKernel ((T / 2) * Omega) := by
    funext Omega
    exact normalizedFiniteTimeResonanceKernel_eq_scaled Omega hT
  rw [hfun]
  exact continuous_const.mul
    (continuous_normalizedSincSquareKernel.comp
      (continuous_const.mul continuous_id))

theorem normalizedSincSquareKernel_le_massInverse (x : Real) :
    normalizedSincSquareKernel x <= sincSquareMass⁻¹ := by
  have hsinc_sq_le_one : Real.sinc x ^ 2 <= 1 := by
    have hleft := Real.neg_one_le_sinc x
    have hright := Real.sinc_le_one x
    have hsum : 0 <= Real.sinc x + 1 := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hright) hsum]
  unfold normalizedSincSquareKernel sincSquareKernel
  simpa using mul_le_mul_of_nonneg_left hsinc_sq_le_one
    (inv_nonneg.mpr sincSquareMass_pos.le)

theorem normalizedFiniteTimeResonanceKernel_le
    (Omega : Real) {T : Real} (hT : 0 < T) :
    normalizedFiniteTimeResonanceKernel Omega T <=
      (T / 2) * sincSquareMass⁻¹ := by
  rw [normalizedFiniteTimeResonanceKernel_eq_scaled Omega hT]
  exact mul_le_mul_of_nonneg_left
    (normalizedSincSquareKernel_le_massInverse ((T / 2) * Omega))
    (by positivity)

/-- Multiplication by one fixed positive-time resonance kernel preserves
integrability of an `L1` phase density. -/
theorem Integrable.normalizedFiniteTimeResonanceKernel_mul
    {density : Real -> Real} (hdensity : Integrable density)
    {T : Real} (hT : 0 < T) :
    Integrable (fun Omega : Real =>
      normalizedFiniteTimeResonanceKernel Omega T * density Omega) := by
  refine hdensity.bdd_mul
      (continuous_normalizedFiniteTimeResonanceKernel hT).aestronglyMeasurable
      (c := (T / 2) * sincSquareMass⁻¹) ?_
  filter_upwards with Omega
  rw [Real.norm_eq_abs,
    abs_of_nonneg (normalizedFiniteTimeResonanceKernel_nonneg Omega T)]
  exact normalizedFiniteTimeResonanceKernel_le Omega hT

/-- Unit mass makes the resonance action 1-Lipschitz with respect to the
global uniform norm on phase densities. -/
theorem abs_integral_kernel_mul_sub_le_uniform
    {rho sigma : Real -> Real} (hrho : Integrable rho)
    (hsigma : Integrable sigma) {T epsilon : Real} (hT : 0 < T)
    (_hepsilon : 0 <= epsilon)
    (huniform : forall Omega, |rho Omega - sigma Omega| <= epsilon) :
    |(∫ Omega : Real,
        normalizedFiniteTimeResonanceKernel Omega T * rho Omega) -
      (∫ Omega : Real,
        normalizedFiniteTimeResonanceKernel Omega T * sigma Omega)| <=
      epsilon := by
  let kernel : Real -> Real := fun Omega =>
    normalizedFiniteTimeResonanceKernel Omega T
  have hkernel : Integrable kernel :=
    integrable_normalizedFiniteTimeResonanceKernel hT
  have hkrho : Integrable (fun Omega => kernel Omega * rho Omega) :=
    Integrable.normalizedFiniteTimeResonanceKernel_mul hrho hT
  have hksigma : Integrable (fun Omega => kernel Omega * sigma Omega) :=
    Integrable.normalizedFiniteTimeResonanceKernel_mul hsigma hT
  rw [← integral_sub hkrho hksigma]
  calc
    |∫ Omega : Real,
        kernel Omega * rho Omega - kernel Omega * sigma Omega| =
        ‖∫ Omega : Real,
          kernel Omega * rho Omega - kernel Omega * sigma Omega‖ := by
      rw [Real.norm_eq_abs]
    _ <= ∫ Omega : Real,
        ‖kernel Omega * rho Omega - kernel Omega * sigma Omega‖ :=
      norm_integral_le_integral_norm _
    _ <= ∫ Omega : Real, epsilon * kernel Omega := by
      apply integral_mono (hkrho.sub hksigma).norm
        (hkernel.const_mul epsilon)
      intro Omega
      change ‖kernel Omega * rho Omega - kernel Omega * sigma Omega‖ <=
        epsilon * kernel Omega
      rw [← mul_sub, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (normalizedFiniteTimeResonanceKernel_nonneg Omega T)]
      calc
        kernel Omega * |rho Omega - sigma Omega| <=
            kernel Omega * epsilon :=
          mul_le_mul_of_nonneg_left (huniform Omega)
            (normalizedFiniteTimeResonanceKernel_nonneg Omega T)
        _ = epsilon * kernel Omega := by ring
    _ = epsilon := by
      rw [integral_const_mul,
        integral_normalizedFiniteTimeResonanceKernel_eq_one hT, mul_one]

/-- Joint transfer theorem for a varying phase density and a varying
observation time. -/
theorem tendsto_integral_kernel_mul_varying_density
    {time : Nat -> Real} (htime : Tendsto time atTop atTop)
    {rho : Real -> Real} (hrho : Integrable rho)
    (hcrho : ContinuousAt rho 0)
    {rhoSeq : Nat -> Real -> Real}
    (hrhoSeq : forall j, Integrable (rhoSeq j))
    {error : Nat -> Real} (herror_nonneg : forall j, 0 <= error j)
    (herror : Tendsto error atTop (nhds 0))
    (huniform : forall j Omega,
      |rhoSeq j Omega - rho Omega| <= error j) :
    Tendsto
      (fun j : Nat => ∫ Omega : Real,
        normalizedFiniteTimeResonanceKernel Omega (time j) *
          rhoSeq j Omega)
      atTop (nhds (rho 0)) := by
  have hfixed : Tendsto
      (fun j : Nat => ∫ Omega : Real,
        normalizedFiniteTimeResonanceKernel Omega (time j) * rho Omega)
      atTop (nhds (rho 0)) :=
    (tendsto_integral_normalizedFiniteTimeResonanceKernel
      hrho hcrho).comp htime
  have htime_pos : ∀ᶠ j : Nat in atTop, 0 < time j :=
    htime (eventually_gt_atTop 0)
  rw [Metric.tendsto_nhds]
  intro delta hdelta
  have hdelta_half : 0 < delta / 2 := by positivity
  have hfixed_eventually :=
    (Metric.tendsto_nhds.mp hfixed) (delta / 2) hdelta_half
  have herror_eventually :=
    (Metric.tendsto_nhds.mp herror) (delta / 2) hdelta_half
  filter_upwards [htime_pos, hfixed_eventually, herror_eventually]
      with j hjtime hjfixed hjerror
  have hkernel_error :
      dist
        (∫ Omega : Real,
          normalizedFiniteTimeResonanceKernel Omega (time j) *
            rhoSeq j Omega)
        (∫ Omega : Real,
          normalizedFiniteTimeResonanceKernel Omega (time j) * rho Omega) <=
        error j := by
    rw [Real.dist_eq]
    exact abs_integral_kernel_mul_sub_le_uniform
      (hrhoSeq j) hrho hjtime (herror_nonneg j) (huniform j)
  have hjerror_lt : error j < delta / 2 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (herror_nonneg j)] at hjerror
    exact hjerror
  calc
    dist
        (∫ Omega : Real,
          normalizedFiniteTimeResonanceKernel Omega (time j) *
            rhoSeq j Omega)
        (rho 0) <=
      dist
          (∫ Omega : Real,
            normalizedFiniteTimeResonanceKernel Omega (time j) *
              rhoSeq j Omega)
          (∫ Omega : Real,
            normalizedFiniteTimeResonanceKernel Omega (time j) * rho Omega) +
        dist
          (∫ Omega : Real,
            normalizedFiniteTimeResonanceKernel Omega (time j) * rho Omega)
          (rho 0) := dist_triangle _ _ _
    _ < delta := by linarith

end

end ArchonPhysics.UniformCollisionDensityTransfer
