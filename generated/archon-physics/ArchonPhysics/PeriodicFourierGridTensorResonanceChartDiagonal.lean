import ArchonPhysics.PeriodicFourierGridTensorLipschitzQuadrature
import ArchonPhysics.TransverseResonanceChartApproximateIdentity

/-!
# Diagonal Fourier-grid limit on a transverse resonance chart

This module composes two deterministic analytic statements:

* a transverse resonance chart turns the normalized finite-time collision
  kernel into an approximate identity as `T → ∞`;
* coordinatewise Lipschitz control turns a two-dimensional periodic Fourier
  sum into its continuum integral with an explicit error.

The generic theorem first keeps an arbitrary error sequence `eₙ` visible.
The tensor corollaries then discharge it by

`eₙ = (2π)³ (L₁(n) + L₂(n)) / (n+1)`.

For finite-time integrands with coordinate moduli `Cᵢ Tₙ²`, the resulting
joint window is exactly `Tₙ²/(n+1) → 0`, together with `Tₙ → ∞`.
The identification of the two-dimensional continuum integral with the chart
integral is an explicit hypothesis.  No kinetic equation is assumed.
-/

namespace ArchonPhysics.PeriodicFourierGridTensorResonanceChartDiagonal

open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.PeriodicFourierGridTensorQuadrature
open ArchonPhysics.PeriodicFourierGridTensorLipschitzQuadrature
open ArchonPhysics.TransverseResonanceChartApproximateIdentity
open Filter MeasureTheory Set Topology

noncomputable section

/-- The continuum collision observable represented by one transverse chart. -/
def transverseChartCollisionObservable
    (mismatch mark : Real → Real) (a b T : Real) : Real :=
  ∫ x in a..b,
    normalizedFiniteTimeResonanceKernel (mismatch x) T * mark x

/-- The chart approximate identity, restated for the named continuum
observable. -/
theorem transverseChartCollisionObservable_tendsto_density_zero
    {mismatch mismatchDerivative mark density : Real → Real}
    {a b : Real}
    (chart : TransverseResonanceChart
      mismatch mismatchDerivative mark density a b) :
    Tendsto
      (transverseChartCollisionObservable mismatch mark a b)
      atTop (nhds (density 0)) := by
  change Tendsto
    (fun T : Real ↦ ∫ x in a..b,
      normalizedFiniteTimeResonanceKernel (mismatch x) T * mark x)
    atTop (nhds (density 0))
  exact tendsto_integral_collisionKernel_chart chart

/-! ## Generic vanishing-error diagonalization -/

/-- If a discrete collision observable is within `error n` of the continuum
chart observable at time `time n`, the error tends to zero, and the times tend
to infinity, then the discrete observable converges to the on-shell density
value `density 0`. -/
theorem discreteCollisionObservable_tendsto_density_zero_of_chart_error
    {mismatch mismatchDerivative mark density : Real → Real}
    {a b : Real}
    (chart : TransverseResonanceChart
      mismatch mismatchDerivative mark density a b)
    (time discrete error : Nat → Real)
    (htime : Tendsto time atTop atTop)
    (herrorBound : ∀ n,
      |discrete n -
        transverseChartCollisionObservable mismatch mark a b (time n)| ≤
          error n)
    (herror : Tendsto error atTop (nhds 0)) :
    Tendsto discrete atTop (nhds (density 0)) := by
  have habsDifference : Tendsto
      (fun n ↦
        |discrete n -
          transverseChartCollisionObservable mismatch mark a b (time n)|)
      atTop (nhds 0) := by
    apply squeeze_zero' (g := error)
    · exact Eventually.of_forall fun _ ↦ abs_nonneg _
    · exact Eventually.of_forall herrorBound
    · exact herror
  have hdifference : Tendsto
      (fun n ↦ discrete n -
        transverseChartCollisionObservable mismatch mark a b (time n))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habsDifference
  have hcontinuum : Tendsto
      (fun n ↦ transverseChartCollisionObservable
        mismatch mark a b (time n))
      atTop (nhds (density 0)) :=
    (transverseChartCollisionObservable_tendsto_density_zero chart).comp htime
  convert hdifference.add hcontinuum using 1 <;> simp

/-! ## Fourier-grid instantiations -/

/-- The generic joint tensor limit.  The exact continuum identification
`hcontinuumIdentification` is the model-specific bridge: it says that the
iterated Brillouin-zone integral of `F n` is represented by the stated
transverse chart at time `time n`. -/
theorem periodicFourierTensorGrid_tendsto_density_zero_of_lipschitzScale
    {mismatch mismatchDerivative mark density : Real → Real}
    {a b : Real}
    (chart : TransverseResonanceChart
      mismatch mismatchDerivative mark density a b)
    (time : Nat → Real) (F : Nat → Real → Real → Real)
    (L₁ L₂ : Nat → Real)
    (htime : Tendsto time atTop atTop)
    (hL₁ : ∀ n, 0 ≤ L₁ n) (hL₂ : ∀ n, 0 ≤ L₂ n)
    (hendpoint₂ : ∀ n x, F n x 0 = F n x (2 * Real.pi))
    (hcontinuous₂ : ∀ n x, ContinuousOn (fun y ↦ F n x y)
      (Icc (0 : Real) (2 * Real.pi)))
    (hlipschitz₂ : ∀ n x,
      ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ y' ∈ Icc (0 : Real) (2 * Real.pi),
        |F n x y - F n x y'| ≤ L₂ n * |y - y'|)
    (hendpoint₁ : ∀ n y, F n 0 y = F n (2 * Real.pi) y)
    (hlipschitz₁ : ∀ n, ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ x' ∈ Icc (0 : Real) (2 * Real.pi),
        |F n x y - F n x' y| ≤ L₁ n * |x - x'|)
    (hcontinuumIdentification : ∀ n,
      periodicFourierTensorIntervalIntegral (F n) =
        transverseChartCollisionObservable
          mismatch mark a b (time n))
    (hscale : Tendsto
      (fun n : Nat ↦ (L₁ n + L₂ n) / (((n + 1 : Nat) : Real)))
      atTop (nhds 0)) :
    Tendsto
      (fun n : Nat ↦
        periodicFourierTensorGridQuadrature (n + 1) (F n))
      atTop (nhds (density 0)) := by
  let error : Nat → Real := fun n ↦
    (2 * Real.pi) ^ 3 *
      ((L₁ n + L₂ n) / (((n + 1 : Nat) : Real)))
  apply discreteCollisionObservable_tendsto_density_zero_of_chart_error
    chart time
      (fun n ↦ periodicFourierTensorGridQuadrature (n + 1) (F n))
      error htime
  · intro n
    rw [← hcontinuumIdentification n]
    have hbound :=
      abs_periodicFourierTensorGridQuadrature_sub_integral_le_of_lipschitz
        (n + 1) (F n) (hL₁ n) (hL₂ n)
        (hendpoint₂ n) (hcontinuous₂ n) (hlipschitz₂ n)
        (hendpoint₁ n) (hlipschitz₁ n)
    exact hbound.trans_eq (by
      dsimp [error]
      ring)
  · dsimp [error]
    simpa using tendsto_const_nhds.mul hscale

/-- For coordinate Lipschitz constants `C₁ Tₙ²` and `C₂ Tₙ²`, the
transparent diagonal window is the conjunction of `Tₙ → ∞` and
`Tₙ²/(n+1) → 0`. -/
theorem periodicFourierTensorGrid_tendsto_density_zero_of_time_sq_div_volume
    {mismatch mismatchDerivative mark density : Real → Real}
    {a b : Real}
    (chart : TransverseResonanceChart
      mismatch mismatchDerivative mark density a b)
    (time : Nat → Real) (F : Nat → Real → Real → Real)
    {C₁ C₂ : Real} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (htime : Tendsto time atTop atTop)
    (hendpoint₂ : ∀ n x, F n x 0 = F n x (2 * Real.pi))
    (hcontinuous₂ : ∀ n x, ContinuousOn (fun y ↦ F n x y)
      (Icc (0 : Real) (2 * Real.pi)))
    (hlipschitz₂ : ∀ n x,
      ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ y' ∈ Icc (0 : Real) (2 * Real.pi),
        |F n x y - F n x y'| ≤
          (C₂ * (time n) ^ 2) * |y - y'|)
    (hendpoint₁ : ∀ n y, F n 0 y = F n (2 * Real.pi) y)
    (hlipschitz₁ : ∀ n, ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ x' ∈ Icc (0 : Real) (2 * Real.pi),
        |F n x y - F n x' y| ≤
          (C₁ * (time n) ^ 2) * |x - x'|)
    (hcontinuumIdentification : ∀ n,
      periodicFourierTensorIntervalIntegral (F n) =
        transverseChartCollisionObservable
          mismatch mark a b (time n))
    (htimeWindow : Tendsto
      (fun n : Nat ↦ (time n) ^ 2 / (((n + 1 : Nat) : Real)))
      atTop (nhds 0)) :
    Tendsto
      (fun n : Nat ↦
        periodicFourierTensorGridQuadrature (n + 1) (F n))
      atTop (nhds (density 0)) := by
  apply periodicFourierTensorGrid_tendsto_density_zero_of_lipschitzScale
    chart time F (fun n ↦ C₁ * (time n) ^ 2)
      (fun n ↦ C₂ * (time n) ^ 2) htime
      (fun n ↦ mul_nonneg hC₁ (sq_nonneg (time n)))
      (fun n ↦ mul_nonneg hC₂ (sq_nonneg (time n)))
      hendpoint₂ hcontinuous₂ hlipschitz₂
      hendpoint₁ hlipschitz₁ hcontinuumIdentification
  have hscaled : Tendsto
      (fun n : Nat ↦ (C₁ + C₂) *
        ((time n) ^ 2 / (((n + 1 : Nat) : Real))))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul htimeWindow
  have heq :
      (fun n : Nat ↦
        (C₁ * (time n) ^ 2 + C₂ * (time n) ^ 2) /
          (((n + 1 : Nat) : Real))) =
      (fun n : Nat ↦ (C₁ + C₂) *
        ((time n) ^ 2 / (((n + 1 : Nat) : Real)))) := by
    funext n
    ring
  rw [heq]
  exact hscaled

end

end ArchonPhysics.PeriodicFourierGridTensorResonanceChartDiagonal
