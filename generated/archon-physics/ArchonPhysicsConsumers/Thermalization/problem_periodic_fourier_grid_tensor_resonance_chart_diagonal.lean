import ArchonPhysics.PeriodicFourierGridTensorResonanceChartDiagonal

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.PeriodicFourierGridTensorQuadrature
open ArchonPhysics.PeriodicFourierGridTensorResonanceChartDiagonal
open ArchonPhysics.TransverseResonanceChartApproximateIdentity
open Filter MeasureTheory Set Topology

noncomputable section

theorem transverse_chart_discrete_vanishing_error_diagonal_consumer
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
    Tendsto discrete atTop (nhds (density 0)) :=
  discreteCollisionObservable_tendsto_density_zero_of_chart_error
    chart time discrete error htime herrorBound herror

theorem periodic_Fourier_tensor_chart_time_sq_diagonal_consumer
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
      atTop (nhds (density 0)) :=
  periodicFourierTensorGrid_tendsto_density_zero_of_time_sq_div_volume
    chart time F hC₁ hC₂ htime hendpoint₂ hcontinuous₂
      hlipschitz₂ hendpoint₁ hlipschitz₁
      hcontinuumIdentification htimeWindow

#print axioms transverse_chart_discrete_vanishing_error_diagonal_consumer
#print axioms periodic_Fourier_tensor_chart_time_sq_diagonal_consumer

end

end ArchonPhysicsConsumers.Thermalization
