import ArchonPhysics.EqualMassPeriodicFPUTUmklappOnShellJacobian
import ArchonPhysics.TransverseResonanceChartApproximateIdentity

/-!
# Equal-mass periodic FPUT: an Umklapp collision-density chart

This specializes the scalar transverse-chart theorem to the actual one-wrap
FPUT mismatch. A positive chart records precisely the remaining global
change-of-variables data: a continuous integrable mismatch density, support
inside the chart image, and factorization by the actual FPUT derivative.

At a nondegenerate resonant root the limiting density is identified with the
physical mark divided by the exact on-shell Jacobian. Thus the theorem below
contains neither an abstract mismatch nor an assumed kinetic equation.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTUmklappCollisionDensity

open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTUmklappOnShellJacobian
open ArchonPhysics.EqualMassPeriodicFPUTUmklappTransversality
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.TransverseResonanceChartApproximateIdentity
open Filter MeasureTheory Set Topology

noncomputable section

/-- Data for one positively oriented FPUT Umklapp collision chart. The
derivative sign is explicit; different monotonic branches are handled by
separate charts (and a decreasing branch can be reparametrized in reverse). -/
structure PositiveUmklappCollisionChart
    (k₀ k₁ : Real) (mark density : Real → Real) (a b : Real) : Prop where
  derivative_pos : ∀ x ∈ uIcc a b,
    0 < umklappK₂DerivativeFactor k₀ k₁ x
  density_continuous : Continuous density
  density_integrable : Integrable density
  density_support : Function.support density ⊆
    Ioc (umklappReducedFourWaveMismatch k₀ k₁ a)
      (umklappReducedFourWaveMismatch k₀ k₁ b)
  mark_factorization : ∀ x ∈ uIcc a b,
    mark x = density (umklappReducedFourWaveMismatch k₀ k₁ x) *
      umklappK₂DerivativeFactor k₀ k₁ x

/-- The FPUT-specific chart supplies all fields of the generic transverse
resonance chart; differentiability and derivative continuity are proved from
the acoustic dispersion rather than postulated. -/
theorem PositiveUmklappCollisionChart.toTransverseResonanceChart
    {k₀ k₁ : Real} {mark density : Real → Real} {a b : Real}
    (chart : PositiveUmklappCollisionChart k₀ k₁ mark density a b) :
    TransverseResonanceChart
      (fun x ↦ umklappReducedFourWaveMismatch k₀ k₁ x)
      (fun x ↦ umklappK₂DerivativeFactor k₀ k₁ x)
      mark density a b where
  mismatch_hasDeriv := fun x _ ↦
    hasDerivAt_umklappReducedFourWaveMismatch_k₂_factor k₀ k₁ x
  mismatchDerivative_continuous := by
    apply Continuous.continuousOn
    unfold umklappK₂DerivativeFactor
    fun_prop
  density_continuous := chart.density_continuous
  density_integrable := chart.density_integrable
  density_support := chart.density_support
  mark_factorization := chart.mark_factorization

/-- At a resonant point in a positive chart, the mismatch density at zero is
the physical mark divided by the closed-form Umklapp Jacobian. -/
theorem density_zero_eq_mark_div_exactJacobian
    {k₀ k₁ k₂ : Real} {mark density : Real → Real} {a b : Real}
    (chart : PositiveUmklappCollisionChart k₀ k₁ mark density a b)
    (hk₂ : k₂ ∈ uIcc a b)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁)
    (hresonant : umklappReducedFourWaveMismatch k₀ k₁ k₂ = 0) :
    density 0 = mark k₂ /
      (2 * Real.sqrt (umklappTransverseDiscriminant k₀ k₁)) := by
  have hfactorization := chart.mark_factorization k₂ hk₂
  rw [hresonant] at hfactorization
  have habs := abs_umklappK₂DerivativeFactor_of_resonant
    hdisc hresonant
  have hpositive := chart.derivative_pos k₂ hk₂
  rw [abs_of_pos hpositive] at habs
  have hdenominator :
      2 * Real.sqrt (umklappTransverseDiscriminant k₀ k₁) ≠ 0 := by
    positivity
  apply (eq_div_iff hdenominator).2
  rw [← habs]
  exact hfactorization.symm

/-- Long collision times select the exact Umklapp resonant root with the
physical inverse-Jacobian factor. -/
theorem tendsto_positiveUmklappCollisionChart_exactJacobian
    {k₀ k₁ k₂ : Real} {mark density : Real → Real} {a b : Real}
    (chart : PositiveUmklappCollisionChart k₀ k₁ mark density a b)
    (hk₂ : k₂ ∈ uIcc a b)
    (hdisc : 0 < umklappTransverseDiscriminant k₀ k₁)
    (hresonant : umklappReducedFourWaveMismatch k₀ k₁ k₂ = 0) :
    Tendsto
      (fun T : Real ↦ ∫ x in a..b,
        normalizedFiniteTimeResonanceKernel
          (umklappReducedFourWaveMismatch k₀ k₁ x) T * mark x)
      atTop
      (nhds (mark k₂ /
        (2 * Real.sqrt (umklappTransverseDiscriminant k₀ k₁)))) := by
  have hlimit := tendsto_integral_collisionKernel_chart
    chart.toTransverseResonanceChart
  rw [density_zero_eq_mark_div_exactJacobian
    chart hk₂ hdisc hresonant] at hlimit
  exact hlimit

end

end ArchonPhysics.EqualMassPeriodicFPUTUmklappCollisionDensity
