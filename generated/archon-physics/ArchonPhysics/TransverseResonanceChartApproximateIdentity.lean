import ArchonPhysics.SincSquareMassExact
import ArchonPhysics.UniformCollisionDensityTransfer
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Approximate identity on a transverse resonance chart

A one-dimensional transverse chart converts a collision integral in a free
momentum into an integral in phase mismatch.  The chart data below record the
ordinary change-of-variables identity explicitly:

`mark(x) = density(mismatch(x)) * mismatchDerivative(x)`.

Under this identity, the normalized finite-time squared-sinc kernel converges
to the on-shell density `density 0`.  This is the rigorous scalar coarea step;
it neither assumes nor solves a kinetic equation.
-/

namespace ArchonPhysics.TransverseResonanceChartApproximateIdentity

open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.UniformCollisionDensityTransfer
open Filter MeasureTheory Set Topology

noncomputable section

/-- Data certifying a positively oriented transverse phase-mismatch chart.
The density is globally extended with support inside the chart image so the
interval mismatch integral equals the corresponding whole-line integral. -/
structure TransverseResonanceChart
    (mismatch mismatchDerivative mark density : Real → Real)
    (a b : Real) : Prop where
  mismatch_hasDeriv : ∀ x ∈ uIcc a b,
    HasDerivAt mismatch (mismatchDerivative x) x
  mismatchDerivative_continuous : ContinuousOn mismatchDerivative (uIcc a b)
  density_continuous : Continuous density
  density_integrable : Integrable density
  density_support : Function.support density ⊆ Ioc (mismatch a) (mismatch b)
  mark_factorization : ∀ x ∈ uIcc a b,
    mark x = density (mismatch x) * mismatchDerivative x

/-- Exact finite-time change of variables from a transverse free-momentum
chart to its phase-mismatch density. -/
theorem integral_collisionKernel_chart_eq_density
    {mismatch mismatchDerivative mark density : Real → Real}
    {a b T : Real}
    (chart : TransverseResonanceChart
      mismatch mismatchDerivative mark density a b)
    (hT : 0 < T) :
    (∫ x in a..b,
        normalizedFiniteTimeResonanceKernel (mismatch x) T * mark x) =
      ∫ Omega : Real,
        normalizedFiniteTimeResonanceKernel Omega T * density Omega := by
  let kernelDensity : Real → Real := fun Omega ↦
    normalizedFiniteTimeResonanceKernel Omega T * density Omega
  have hkernelDensityContinuous : Continuous kernelDensity :=
    (continuous_normalizedFiniteTimeResonanceKernel hT).mul
      chart.density_continuous
  have hchange := intervalIntegral.integral_comp_mul_deriv
    (a := a) (b := b) (f := mismatch) (f' := mismatchDerivative)
    (g := kernelDensity) chart.mismatch_hasDeriv
    chart.mismatchDerivative_continuous hkernelDensityContinuous
  have hleft :
      (∫ x in a..b,
          normalizedFiniteTimeResonanceKernel (mismatch x) T * mark x) =
        ∫ x in a..b,
          (kernelDensity ∘ mismatch) x * mismatchDerivative x := by
    apply intervalIntegral.integral_congr
    intro x hx
    change normalizedFiniteTimeResonanceKernel (mismatch x) T * mark x =
      kernelDensity (mismatch x) * mismatchDerivative x
    rw [chart.mark_factorization x hx]
    dsimp [kernelDensity]
    ring
  rw [hleft, hchange]
  apply intervalIntegral.integral_eq_integral_of_support_subset
  exact (Function.support_mul_subset_right
    (fun Omega ↦ normalizedFiniteTimeResonanceKernel Omega T)
    density).trans chart.density_support

/-- Long-time collision-kernel limit on one transverse chart. -/
theorem tendsto_integral_collisionKernel_chart
    {mismatch mismatchDerivative mark density : Real → Real}
    {a b : Real}
    (chart : TransverseResonanceChart
      mismatch mismatchDerivative mark density a b) :
    Tendsto
      (fun T : Real ↦ ∫ x in a..b,
        normalizedFiniteTimeResonanceKernel (mismatch x) T * mark x)
      atTop (nhds (density 0)) := by
  have hpeak := tendsto_integral_normalizedFiniteTimeResonanceKernel
    chart.density_integrable chart.density_continuous.continuousAt
  refine hpeak.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : Real)] with T hT
  exact (integral_collisionKernel_chart_eq_density chart hT).symm

end

end ArchonPhysics.TransverseResonanceChartApproximateIdentity
