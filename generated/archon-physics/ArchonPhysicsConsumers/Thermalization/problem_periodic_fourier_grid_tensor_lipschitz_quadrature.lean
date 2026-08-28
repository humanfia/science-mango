import ArchonPhysics.PeriodicFourierGridTensorLipschitzQuadrature

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge
open ArchonPhysics.PeriodicFourierGridTensorQuadrature
open ArchonPhysics.PeriodicFourierGridTensorLipschitzQuadrature
open Filter MeasureTheory Set Topology

noncomputable section

theorem periodic_Fourier_tensor_Lipschitz_error_consumer
    (N : Nat) [NeZero N] (F : Real → Real → Real)
    {L₁ L₂ : Real} (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hendpoint₂ : ∀ x, F x 0 = F x (2 * Real.pi))
    (hcontinuous₂ : ∀ x, ContinuousOn (fun y ↦ F x y)
      (Icc (0 : Real) (2 * Real.pi)))
    (hlipschitz₂ : ∀ x,
      ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ y' ∈ Icc (0 : Real) (2 * Real.pi),
        |F x y - F x y'| ≤ L₂ * |y - y'|)
    (hendpoint₁ : ∀ y, F 0 y = F (2 * Real.pi) y)
    (hlipschitz₁ : ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ x' ∈ Icc (0 : Real) (2 * Real.pi),
        |F x y - F x' y| ≤ L₁ * |x - x'|) :
    |periodicFourierTensorGridQuadrature N F -
      periodicFourierTensorIntervalIntegral F| ≤
      (2 * Real.pi) ^ 3 * (L₁ + L₂) / (N : Real) :=
  abs_periodicFourierTensorGridQuadrature_sub_integral_le_of_lipschitz
    N F hL₁ hL₂ hendpoint₂ hcontinuous₂ hlipschitz₂
      hendpoint₁ hlipschitz₁

theorem periodic_Fourier_tensor_time_sq_window_consumer
    (F : Nat → Real → Real → Real) (T : Nat → Real)
    {C₁ C₂ : Real} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hendpoint₂ : ∀ n x, F n x 0 = F n x (2 * Real.pi))
    (hcontinuous₂ : ∀ n x, ContinuousOn (fun y ↦ F n x y)
      (Icc (0 : Real) (2 * Real.pi)))
    (hlipschitz₂ : ∀ n x,
      ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ y' ∈ Icc (0 : Real) (2 * Real.pi),
        |F n x y - F n x y'| ≤
          (C₂ * (T n) ^ 2) * |y - y'|)
    (hendpoint₁ : ∀ n y, F n 0 y = F n (2 * Real.pi) y)
    (hlipschitz₁ : ∀ n, ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ x' ∈ Icc (0 : Real) (2 * Real.pi),
        |F n x y - F n x' y| ≤
          (C₁ * (T n) ^ 2) * |x - x'|)
    (htimeWindow : Tendsto
      (fun n : Nat ↦ (T n) ^ 2 / (((n + 1 : Nat) : Real)))
      atTop (nhds 0)) :
    Tendsto
      (fun n : Nat ↦
        |periodicFourierTensorGridQuadrature (n + 1) (F n) -
          periodicFourierTensorIntervalIntegral (F n)|)
      atTop (nhds 0) :=
  periodicFourierTensorQuadratureError_tendsto_zero_of_time_sq_div_volume
    F T hC₁ hC₂ hendpoint₂ hcontinuous₂ hlipschitz₂
      hendpoint₁ hlipschitz₁ htimeWindow

#print axioms periodic_Fourier_tensor_Lipschitz_error_consumer
#print axioms periodic_Fourier_tensor_time_sq_window_consumer

end

end ArchonPhysicsConsumers.Thermalization
