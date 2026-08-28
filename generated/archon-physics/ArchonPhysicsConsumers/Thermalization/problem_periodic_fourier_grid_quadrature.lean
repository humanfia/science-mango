import ArchonPhysics.PeriodicFourierGridQuadrature

/-!
# Consumer: periodic Fourier-grid quadrature
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge
open ArchonPhysics.Lattice
open ArchonPhysics.PeriodicFourierGridQuadrature
open Set
open scoped BigOperators

noncomputable section

theorem periodic_Fourier_grid_thermodynamic_limit_error_consumer
    (N : Nat) [NeZero N] (f : Real → Real)
    (hendpoint : f 0 = f (2 * Real.pi))
    (hC2 : ContDiffOn Real 2 f (uIcc (0 : Real) (2 * Real.pi)))
    {zeta : Real}
    (hsecond : ∀ x,
      |iteratedDerivWithin 2 f (uIcc (0 : Real) (2 * Real.pi)) x| ≤ zeta) :
    |(2 * Real.pi / (N : Real)) *
        ∑ k : Site N, f (gridWaveNumber N k) -
      ∫ x in (0 : Real)..(2 * Real.pi), f x| ≤
      |2 * Real.pi - 0| ^ 3 * zeta / (12 * (N : Real) ^ 2) :=
  abs_fourierGrid_sum_sub_integral_le N f hendpoint hC2 hsecond

/-- Lower-regularity endpoint for time-dependent collision integrands: a
Lipschitz constant `L` costs only the explicit error `L(2π)²/N`. -/
theorem periodic_Fourier_grid_lipschitz_error_consumer
    (N : Nat) [NeZero N] (f : Real → Real) {L : Real}
    (hL : 0 ≤ L)
    (hendpoint : f 0 = f (2 * Real.pi))
    (hcontinuous : ContinuousOn f (Icc (0 : Real) (2 * Real.pi)))
    (hlipschitz : ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
        |f x - f y| ≤ L * |x - y|) :
    |(2 * Real.pi / (N : Real)) *
        ∑ k : Site N, f (gridWaveNumber N k) -
      ∫ x in (0 : Real)..(2 * Real.pi), f x| ≤
      L * (2 * Real.pi) ^ 2 / (N : Real) :=
  abs_fourierGrid_sum_sub_integral_le_of_lipschitz
    N f hL hendpoint hcontinuous hlipschitz

#print axioms periodic_Fourier_grid_thermodynamic_limit_error_consumer
#print axioms periodic_Fourier_grid_lipschitz_error_consumer

end

end ArchonPhysicsConsumers.Thermalization
