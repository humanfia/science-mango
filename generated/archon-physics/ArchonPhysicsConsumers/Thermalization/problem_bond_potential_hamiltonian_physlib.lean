import ArchonPhysics.BondPotentialHamiltonianPhyslib

/-!
# Consumer: exact finite-chain equations for a differentiable bond potential
-/

namespace ArchonPhysicsConsumers.Thermalization.BondPotentialHamiltonianPhyslib

open Time
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ConcreteHamiltonGradients
open ArchonPhysics.BondPotentialHamiltonianPhyslib

noncomputable section

/-- Five-site exact Lennard--Jones Hamilton equations on a supplied
nonsingular trajectory.  This consumer intentionally assumes collision
avoidance and makes no kinetic-limit claim. -/
theorem fiveSite_lennardJones_explicit_equations
    (m : Lattice.PositiveMassConfig 5) (depth r₀ : Real)
    (p q : Time → HilbertConfiguration 5)
    (hq : ∀ t, LennardJonesBondsNonsingular r₀ (q t)) :
    SatisfiesHamiltonEquations m
        (LennardJonesPotential.bondPotential depth r₀) p q ↔
      (∀ t, ∂ₜ q t = inverseMassMomentum m (p t)) ∧
      (∀ t, ∂ₜ p t =
        -potentialGradient (lennardJonesDerivative depth r₀) (q t)) := by
  exact lennardJones_satisfiesHamiltonEquations_iff_explicit
    m depth r₀ p q hq


#print axioms fiveSite_lennardJones_explicit_equations

end

end ArchonPhysicsConsumers.Thermalization.BondPotentialHamiltonianPhyslib
