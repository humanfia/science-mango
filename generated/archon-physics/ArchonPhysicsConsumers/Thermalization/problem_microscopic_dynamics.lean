import Mathlib
import ArchonPhysics

/-!
# Finite microscopic Hamiltonian dynamics

Consumer acceptance target for the local `ArchonPhysics` dependency.  It
combines finite-dimensional local well-posedness with conditional conservation
on a time segment.  It asserts neither global existence nor thermalization.
-/

namespace ArchonPhysics.Generated.MicroscopicDynamics

open Filter
open ArchonPhysics.MicroscopicDynamics

noncomputable section

/-- Every initial phase point has a unique local solution germ. -/
def HasUniqueLocalSolutionGerm {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (n : Nat) (lambda : Real) : Prop :=
  ∀ t₀ z₀, ∃ ε : Real, 0 < ε ∧ ∃ z : Real → PhaseSpace N,
    z t₀ = z₀ ∧
    (∀ t ∈ Set.Icc (t₀ - ε) (t₀ + ε),
      HasDerivWithinAt z (microscopicVectorField m n lambda (z t))
        (Set.Icc (t₀ - ε) (t₀ + ε)) t) ∧
    ∀ y : Real → PhaseSpace N,
      y t₀ = z₀ →
      (∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt y (microscopicVectorField m n lambda (y t)) t) →
      z =ᶠ[nhds t₀] y

/--
The generated dependency supplies a C¹ microscopic vector field, a unique local
solution germ through every initial condition, and energy--momentum conservation
between endpoints whenever the concrete ODE holds on their whole unoriented
interval.
-/
theorem microscopic_dynamics_physics_formalization_target
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (n : Nat) (lambda : Real) (hn : 1 ≤ n) :
    ContDiff Real 1 (microscopicVectorField m n lambda) ∧
      HasUniqueLocalSolutionGerm m n lambda ∧
      ∀ (z : Real → PhaseSpace N) (s t : Real),
        (∀ u ∈ Set.uIcc s t, IsClassicalSolutionAt m n lambda z u) →
          hamiltonianEnergy m n lambda (z s) =
              hamiltonianEnergy m n lambda (z t) ∧
            totalMomentum (z s) = totalMomentum (z t) := by
  refine ⟨microscopicVectorField_contDiff m n lambda, ?_, ?_⟩
  · intro t₀ z₀
    exact exists_unique_local_solution_germ m n lambda t₀ z₀
  · intro z s t h
    exact ⟨hamiltonianEnergy_eq_of_forall_mem_uIcc m n lambda hn z s t h,
      totalMomentum_eq_of_forall_mem_uIcc m n lambda z s t h⟩

end

end ArchonPhysics.Generated.MicroscopicDynamics
