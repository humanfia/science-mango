import ArchonPhysics.PeriodicFourierGridQuadrature
import ArchonPhysics.ResonanceKernelLipschitz

/-!
# Finite-time FPUT collision quadrature

This module specializes periodic Fourier-grid quadrature to an integrand of
the form

`mark(k) * normalizedFiniteTimeResonanceKernel(mismatch(k), T)`.

The resonance peak has height `T/(2π)` and mismatch-Lipschitz constant
`T²/π`.  Consequently the full sampled collision integrand has an explicit
Lipschitz constant, and its finite-grid/continuum error is bounded without
interchanging the thermodynamic and long-time limits implicitly.

The `mark` can later be instantiated by the squared effective vertex times
the four-wave action flux.  This module does not assume a kinetic equation.
-/

namespace ArchonPhysics.FPUTFiniteTimeCollisionQuadrature

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge
open ArchonPhysics.Lattice
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.PeriodicFourierGridQuadrature
open ArchonPhysics.ResonanceKernelLipschitz
open ArchonPhysics.UniformCollisionDensityTransfer
open Set
open scoped BigOperators

noncomputable section

/-- A marked, normalized, finite-time collision integrand. -/
def finiteTimeMarkedCollisionIntegrand
    (mismatch mark : Real → Real) (T k : Real) : Real :=
  mark k * normalizedFiniteTimeResonanceKernel (mismatch k) T

/-- The explicit spatial Lipschitz constant of the marked collision
integrand.  The two terms respectively measure variation of the mark and of
the phase mismatch. -/
def finiteTimeMarkedCollisionLipschitzConstant
    (T markBound markSlope mismatchSlope : Real) : Real :=
  markSlope * (T / (2 * Real.pi)) +
    markBound * (T ^ 2 / Real.pi) * mismatchSlope

theorem finiteTimeMarkedCollisionLipschitzConstant_nonneg
    {T markBound markSlope mismatchSlope : Real}
    (hT : 0 ≤ T) (hmarkBound : 0 ≤ markBound)
    (hmarkSlope : 0 ≤ markSlope) (hmismatchSlope : 0 ≤ mismatchSlope) :
    0 ≤ finiteTimeMarkedCollisionLipschitzConstant
      T markBound markSlope mismatchSlope := by
  unfold finiteTimeMarkedCollisionLipschitzConstant
  positivity

/-- Product estimate combining the exact height and phase-Lipschitz costs of
the normalized squared-sinc kernel. -/
theorem abs_finiteTimeMarkedCollisionIntegrand_sub_le
    {mismatch mark : Real → Real}
    {T markBound markSlope mismatchSlope x y : Real}
    (hT : 0 < T) (hmarkBound : 0 ≤ markBound)
    (hmarkSlope : 0 ≤ markSlope) (_hmismatchSlope : 0 ≤ mismatchSlope)
    (hmarkBoundAt : |mark y| ≤ markBound)
    (hmarkLip : |mark x - mark y| ≤ markSlope * |x - y|)
    (hmismatchLip : |mismatch x - mismatch y| ≤
      mismatchSlope * |x - y|) :
    |finiteTimeMarkedCollisionIntegrand mismatch mark T x -
        finiteTimeMarkedCollisionIntegrand mismatch mark T y| ≤
      finiteTimeMarkedCollisionLipschitzConstant
        T markBound markSlope mismatchSlope * |x - y| := by
  let kernelX := normalizedFiniteTimeResonanceKernel (mismatch x) T
  let kernelY := normalizedFiniteTimeResonanceKernel (mismatch y) T
  have hheight : |kernelX| ≤ T / (2 * Real.pi) := by
    exact abs_normalizedFiniteTimeResonanceKernel_le_height (mismatch x) hT
  have hkernelLip : |kernelX - kernelY| ≤
      (T ^ 2 / Real.pi) * |mismatch x - mismatch y| := by
    exact abs_normalizedFiniteTimeResonanceKernel_sub_le
      (mismatch x) (mismatch y) hT
  unfold finiteTimeMarkedCollisionIntegrand
  change |mark x * kernelX - mark y * kernelY| ≤ _
  calc
    |mark x * kernelX - mark y * kernelY| =
        |(mark x - mark y) * kernelX + mark y * (kernelX - kernelY)| := by
      congr 1
      ring
    _ ≤ |(mark x - mark y) * kernelX| +
        |mark y * (kernelX - kernelY)| := abs_add_le _ _
    _ = |mark x - mark y| * |kernelX| +
        |mark y| * |kernelX - kernelY| := by rw [abs_mul, abs_mul]
    _ ≤ (markSlope * |x - y|) * (T / (2 * Real.pi)) +
        markBound * ((T ^ 2 / Real.pi) *
          (mismatchSlope * |x - y|)) := by
      apply add_le_add
      · exact mul_le_mul hmarkLip hheight (abs_nonneg _)
          (mul_nonneg hmarkSlope (abs_nonneg _))
      · exact mul_le_mul hmarkBoundAt
          (hkernelLip.trans (mul_le_mul_of_nonneg_left hmismatchLip (by positivity)))
          (abs_nonneg _)
          hmarkBound
    _ = finiteTimeMarkedCollisionLipschitzConstant
        T markBound markSlope mismatchSlope * |x - y| := by
      unfold finiteTimeMarkedCollisionLipschitzConstant
      ring

/-- Exact one-dimensional finite-grid/continuum error for a marked FPUT
collision slice.  The displayed constant exposes the joint-scale cost
`O((markSlope*T + markBound*mismatchSlope*T²)/N)`. -/
theorem abs_finiteTimeMarkedCollision_fourierGrid_sub_integral_le
    (N : Nat) [NeZero N]
    (mismatch mark : Real → Real)
    {T markBound markSlope mismatchSlope : Real}
    (hT : 0 < T) (hmarkBound : 0 ≤ markBound)
    (hmarkSlope : 0 ≤ markSlope) (hmismatchSlope : 0 ≤ mismatchSlope)
    (hmarkContinuous : Continuous mark)
    (hmismatchContinuous : Continuous mismatch)
    (hmarkEndpoint : mark 0 = mark (2 * Real.pi))
    (hmismatchEndpoint : mismatch 0 = mismatch (2 * Real.pi))
    (hmarkBoundOn : ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      |mark x| ≤ markBound)
    (hmarkLipOn : ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
        |mark x - mark y| ≤ markSlope * |x - y|)
    (hmismatchLipOn : ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
        |mismatch x - mismatch y| ≤ mismatchSlope * |x - y|) :
    |(2 * Real.pi / (N : Real)) *
        ∑ k : Site N,
          finiteTimeMarkedCollisionIntegrand mismatch mark T
            (gridWaveNumber N k) -
      ∫ x in (0 : Real)..(2 * Real.pi),
        finiteTimeMarkedCollisionIntegrand mismatch mark T x| ≤
      finiteTimeMarkedCollisionLipschitzConstant
          T markBound markSlope mismatchSlope *
        (2 * Real.pi) ^ 2 / (N : Real) := by
  apply abs_fourierGrid_sum_sub_integral_le_of_lipschitz
  · exact finiteTimeMarkedCollisionLipschitzConstant_nonneg
      hT.le hmarkBound hmarkSlope hmismatchSlope
  · simp [finiteTimeMarkedCollisionIntegrand,
      hmarkEndpoint, hmismatchEndpoint]
  · exact hmarkContinuous.mul
      ((continuous_normalizedFiniteTimeResonanceKernel hT).comp
        hmismatchContinuous) |>.continuousOn
  · intro x hx y hy
    exact abs_finiteTimeMarkedCollisionIntegrand_sub_le
      hT hmarkBound hmarkSlope hmismatchSlope
      (hmarkBoundOn y hy) (hmarkLipOn x hx y hy)
      (hmismatchLipOn x hx y hy)

end

end ArchonPhysics.FPUTFiniteTimeCollisionQuadrature
