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

#print axioms periodic_Fourier_grid_thermodynamic_limit_error_consumer

end

end ArchonPhysicsConsumers.Thermalization
