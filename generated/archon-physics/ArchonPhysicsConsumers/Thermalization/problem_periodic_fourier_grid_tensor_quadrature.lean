import ArchonPhysics.PeriodicFourierGridTensorQuadrature

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge
open ArchonPhysics.Lattice
open ArchonPhysics.PeriodicFourierGridTensorQuadrature
open Filter MeasureTheory Set Topology
open scoped BigOperators

noncomputable section

theorem periodic_Fourier_tensor_grid_error_consumer
    (N : Nat) [NeZero N] (F : Real → Real → Real)
    (hendpoint₂ : ∀ x, F x 0 = F x (2 * Real.pi))
    (hC2₂ : ∀ x, ContDiffOn Real 2 (fun y ↦ F x y)
      (uIcc (0 : Real) (2 * Real.pi)))
    {zeta₂ : Real}
    (hsecond₂ : ∀ x y,
      |iteratedDerivWithin 2 (fun z ↦ F x z)
        (uIcc (0 : Real) (2 * Real.pi)) y| ≤ zeta₂)
    (hendpoint₁ : ∀ y, F 0 y = F (2 * Real.pi) y)
    (hC2₁Marginal : ContDiffOn Real 2
      (secondCoordinateIntervalMarginal F)
      (uIcc (0 : Real) (2 * Real.pi)))
    {zeta₁ : Real}
    (hsecond₁Marginal : ∀ x,
      |iteratedDerivWithin 2 (secondCoordinateIntervalMarginal F)
        (uIcc (0 : Real) (2 * Real.pi)) x| ≤ zeta₁) :
    |periodicFourierTensorGridQuadrature N F -
      periodicFourierTensorIntervalIntegral F| ≤
      (2 * Real.pi) *
        (|2 * Real.pi - 0| ^ 3 * zeta₂ / (12 * (N : Real) ^ 2)) +
      |2 * Real.pi - 0| ^ 3 * zeta₁ / (12 * (N : Real) ^ 2) :=
  abs_periodicFourierTensorGridQuadrature_sub_integral_le
    N F hendpoint₂ hC2₂ hsecond₂ hendpoint₁
      hC2₁Marginal hsecond₁Marginal

theorem periodic_Fourier_tensor_joint_limit_consumer
    (F : Nat → Real → Real → Real)
    (zeta₁ zeta₂ : Nat → Real)
    (hendpoint₂ : ∀ n x, F n x 0 = F n x (2 * Real.pi))
    (hC2₂ : ∀ n x, ContDiffOn Real 2 (fun y ↦ F n x y)
      (uIcc (0 : Real) (2 * Real.pi)))
    (hsecond₂ : ∀ n x y,
      |iteratedDerivWithin 2 (fun z ↦ F n x z)
        (uIcc (0 : Real) (2 * Real.pi)) y| ≤ zeta₂ n)
    (hendpoint₁ : ∀ n y, F n 0 y = F n (2 * Real.pi) y)
    (hC2₁Marginal : ∀ n, ContDiffOn Real 2
      (secondCoordinateIntervalMarginal (F n))
      (uIcc (0 : Real) (2 * Real.pi)))
    (hsecond₁Marginal : ∀ n x,
      |iteratedDerivWithin 2 (secondCoordinateIntervalMarginal (F n))
        (uIcc (0 : Real) (2 * Real.pi)) x| ≤ zeta₁ n)
    (hcurvatureScale : Tendsto
      (fun n : Nat ↦
        ((2 * Real.pi) * zeta₂ n + zeta₁ n) /
          (((n + 1 : Nat) : Real) ^ 2)) atTop (nhds 0)) :
    Tendsto
      (fun n : Nat ↦
        |periodicFourierTensorGridQuadrature (n + 1) (F n) -
          periodicFourierTensorIntervalIntegral (F n)|)
      atTop (nhds 0) :=
  periodicFourierTensorQuadratureError_tendsto_zero
    F zeta₁ zeta₂ hendpoint₂ hC2₂ hsecond₂ hendpoint₁
      hC2₁Marginal hsecond₁Marginal hcurvatureScale

#print axioms periodic_Fourier_tensor_grid_error_consumer
#print axioms periodic_Fourier_tensor_joint_limit_consumer

end

end ArchonPhysicsConsumers.Thermalization
