import ArchonPhysics.SincSquareMassExact
import ArchonPhysics.UniformCollisionDensityTransfer
import ArchonPhysics.UniformOffResonanceDecay

/-!
# Local phase-density transfer with uniform L1 control

Global uniform convergence of phase-mismatch densities is stronger than what
random-lattice collision limits normally provide.  This module proves a more
local transfer principle.  It is enough to have uniform convergence on one
fixed neighbourhood of exact resonance together with a uniform `L1` bound on
the density error.  The inverse-time sinc-squared tail controls the complement.

The resulting deterministic theorem is directly suited to a future empirical
collision-density limit.  That model-specific limit is not assumed here.
-/

namespace ArchonPhysics.LocalCollisionDensityTransfer

open Filter MeasureTheory
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.SincSquareMassExact
open ArchonPhysics.UniformCollisionDensityTransfer
open ArchonPhysics.UniformOffResonanceDecay

noncomputable section

/-- Explicit normalized-kernel bound outside a gap of radius `delta`. -/
def offGapCoefficient (delta T : Real) : Real :=
  (2 / delta) ^ 2 / T / (2 * Real.pi)

theorem offGapCoefficient_nonneg {delta T : Real}
    (hdelta : 0 < delta) (hT : 0 < T) :
    0 <= offGapCoefficient delta T := by
  unfold offGapCoefficient
  positivity

theorem normalizedFiniteTimeResonanceKernel_le_offGapCoefficient
    {Omega delta T : Real} (hdelta : 0 < delta) (hT : 0 < T)
    (hgap : delta <= |Omega|) :
    normalizedFiniteTimeResonanceKernel Omega T <=
      offGapCoefficient delta T := by
  unfold normalizedFiniteTimeResonanceKernel offGapCoefficient
  rw [sincSquareMass_eq_pi]
  exact div_le_div_of_nonneg_right
    (finiteTimeResonanceWeight_le_inverseThreshold hT hdelta hgap)
    (mul_nonneg zero_le_two Real.pi_pos.le)

/-- A fixed-time error estimate requiring uniform density control only near
exact resonance and an `L1` bound globally. -/
theorem abs_integral_kernel_mul_sub_le_localUniform_add_L1
    {rho sigma : Real -> Real} (hrho : Integrable rho)
    (hsigma : Integrable sigma) {T delta epsilon L : Real}
    (hT : 0 < T) (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (_hL : 0 <= L)
    (hlocal : forall Omega, |Omega| < delta ->
      ‖rho Omega - sigma Omega‖ <= epsilon)
    (hL1 : (∫ Omega : Real, ‖rho Omega - sigma Omega‖) <= L) :
    |(∫ Omega : Real,
        normalizedFiniteTimeResonanceKernel Omega T * rho Omega) -
      (∫ Omega : Real,
        normalizedFiniteTimeResonanceKernel Omega T * sigma Omega)| <=
      epsilon + offGapCoefficient delta T * L := by
  let kernel : Real -> Real := fun Omega =>
    normalizedFiniteTimeResonanceKernel Omega T
  let coefficient := offGapCoefficient delta T
  have hkernel : Integrable kernel := by
    simpa [kernel] using integrable_normalizedFiniteTimeResonanceKernel hT
  have hkrho : Integrable (fun Omega => kernel Omega * rho Omega) := by
    simpa [kernel] using
      Integrable.normalizedFiniteTimeResonanceKernel_mul hrho hT
  have hksigma : Integrable (fun Omega => kernel Omega * sigma Omega) := by
    simpa [kernel] using
      Integrable.normalizedFiniteTimeResonanceKernel_mul hsigma hT
  have hdiff : Integrable (fun Omega : Real =>
      ‖rho Omega - sigma Omega‖) := by
    simpa only [Pi.sub_apply] using (hrho.sub hsigma).norm
  have hcoefficient : 0 <= coefficient := by
    exact offGapCoefficient_nonneg hdelta hT
  have hmajor : Integrable (fun Omega : Real =>
      epsilon * kernel Omega + coefficient *
        ‖rho Omega - sigma Omega‖) :=
    (hkernel.const_mul epsilon).add (hdiff.const_mul coefficient)
  rw [<- integral_sub hkrho hksigma]
  calc
    |(∫ Omega : Real,
        kernel Omega * rho Omega - kernel Omega * sigma Omega)| =
        ‖∫ Omega : Real,
          kernel Omega * rho Omega - kernel Omega * sigma Omega‖ := by
      rw [Real.norm_eq_abs]
    _ <= ∫ Omega : Real,
        ‖kernel Omega * rho Omega - kernel Omega * sigma Omega‖ :=
      norm_integral_le_integral_norm _
    _ <= ∫ Omega : Real,
        epsilon * kernel Omega + coefficient *
          ‖rho Omega - sigma Omega‖ := by
      apply integral_mono (hkrho.sub hksigma).norm hmajor
      intro Omega
      change ‖kernel Omega * rho Omega - kernel Omega * sigma Omega‖ <=
        epsilon * kernel Omega + coefficient *
          ‖rho Omega - sigma Omega‖
      have hkernel_nonneg : 0 <= kernel Omega :=
        normalizedFiniteTimeResonanceKernel_nonneg Omega T
      rw [<- mul_sub, norm_mul, Real.norm_of_nonneg hkernel_nonneg]
      by_cases hnear : |Omega| < delta
      · calc
          kernel Omega * ‖rho Omega - sigma Omega‖ <=
              kernel Omega * epsilon :=
            mul_le_mul_of_nonneg_left (hlocal Omega hnear) hkernel_nonneg
          _ = epsilon * kernel Omega := by ring
          _ <= epsilon * kernel Omega + coefficient *
              ‖rho Omega - sigma Omega‖ :=
            le_add_of_nonneg_right
              (mul_nonneg hcoefficient (norm_nonneg _))
      · have hgap : delta <= |Omega| := le_of_not_gt hnear
        calc
          kernel Omega * ‖rho Omega - sigma Omega‖ <=
              coefficient * ‖rho Omega - sigma Omega‖ :=
            mul_le_mul_of_nonneg_right
              (normalizedFiniteTimeResonanceKernel_le_offGapCoefficient
                hdelta hT hgap)
              (norm_nonneg _)
          _ <= epsilon * kernel Omega + coefficient *
              ‖rho Omega - sigma Omega‖ :=
            le_add_of_nonneg_left (mul_nonneg hepsilon hkernel_nonneg)
    _ = epsilon * (∫ Omega : Real, kernel Omega) +
        coefficient * (∫ Omega : Real,
          ‖rho Omega - sigma Omega‖) := by
      rw [integral_add (hkernel.const_mul epsilon)
        (hdiff.const_mul coefficient), integral_const_mul,
        integral_const_mul]
    _ = epsilon + coefficient * (∫ Omega : Real,
        ‖rho Omega - sigma Omega‖) := by
      have hmass : (∫ Omega : Real, kernel Omega) = 1 := by
        simpa [kernel] using
          integral_normalizedFiniteTimeResonanceKernel_eq_one hT
      rw [hmass, mul_one]
    _ <= epsilon + coefficient * L := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hL1 hcoefficient)
    _ = epsilon + offGapCoefficient delta T * L := by rfl

/-- Joint transfer for locally convergent densities with a uniform global
`L1` error bound. -/
theorem tendsto_integral_kernel_mul_varying_density_of_localUniform
    {time : Nat -> Real} (htime : Tendsto time atTop atTop)
    {rho : Real -> Real} (hrho : Integrable rho)
    (hcrho : ContinuousAt rho 0)
    {rhoSeq : Nat -> Real -> Real}
    (hrhoSeq : forall j, Integrable (rhoSeq j))
    {delta L : Real} (hdelta : 0 < delta) (hL : 0 <= L)
    {error : Nat -> Real} (herror_nonneg : forall j, 0 <= error j)
    (herror : Tendsto error atTop (nhds 0))
    (hlocal : forall j Omega, |Omega| < delta ->
      ‖rhoSeq j Omega - rho Omega‖ <= error j)
    (hL1 : forall j,
      (∫ Omega : Real, ‖rhoSeq j Omega - rho Omega‖) <= L) :
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
  have htail : Tendsto
      (fun j : Nat => offGapCoefficient delta (time j) * L)
      atTop (nhds 0) := by
    have hdiv := htime.const_div_atTop ((2 / delta) ^ 2)
    have hscaled := hdiv.mul_const ((2 * Real.pi)⁻¹ * L)
    simpa [offGapCoefficient, div_eq_mul_inv, mul_assoc] using hscaled
  have hbound : Tendsto
      (fun j : Nat => error j + offGapCoefficient delta (time j) * L)
      atTop (nhds 0) := by
    simpa using herror.add htail
  have htime_pos : ∀ᶠ j : Nat in atTop, 0 < time j :=
    htime (eventually_gt_atTop 0)
  rw [Metric.tendsto_nhds]
  intro eta heta
  have heta_half : 0 < eta / 2 := by positivity
  have hfixed_eventually :=
    (Metric.tendsto_nhds.mp hfixed) (eta / 2) heta_half
  have hbound_eventually :=
    (Metric.tendsto_nhds.mp hbound) (eta / 2) heta_half
  filter_upwards [htime_pos, hfixed_eventually, hbound_eventually]
      with j hjtime hjfixed hjbound
  have hkernel_error :
      dist
        (∫ Omega : Real,
          normalizedFiniteTimeResonanceKernel Omega (time j) *
            rhoSeq j Omega)
        (∫ Omega : Real,
          normalizedFiniteTimeResonanceKernel Omega (time j) * rho Omega) <=
        error j + offGapCoefficient delta (time j) * L := by
    rw [Real.dist_eq]
    exact abs_integral_kernel_mul_sub_le_localUniform_add_L1
      (hrhoSeq j) hrho hjtime hdelta (herror_nonneg j) hL
      (hlocal j) (hL1 j)
  have hcoefficient_nonneg :
      0 <= offGapCoefficient delta (time j) :=
    offGapCoefficient_nonneg hdelta hjtime
  have hbound_nonneg :
      0 <= error j + offGapCoefficient delta (time j) * L :=
    add_nonneg (herror_nonneg j) (mul_nonneg hcoefficient_nonneg hL)
  have hbound_lt :
      error j + offGapCoefficient delta (time j) * L < eta / 2 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hbound_nonneg] at hjbound
    exact hjbound
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
    _ < eta := by linarith

end

end ArchonPhysics.LocalCollisionDensityTransfer
