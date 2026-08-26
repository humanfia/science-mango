import ArchonPhysics.CoerciveLatticeEnergy
import Physlib.ClassicalMechanics.HamiltonsEquations

/-!
# Physlib adapter for the stabilized finite-chain Hamiltonian

This module instantiates Physlib's exact Hamilton-equation operator with the
coercive finite-chain energy.  It is intentionally a thin grounding layer: the
two gradient equations below come directly from
`ClassicalMechanics.hamiltonEqOp_eq_zero_iff_hamiltons_equations`.

No explicit gradient formula, solution existence, or global-flow claim is made
here.  Those are downstream obligations for the concrete lattice model.
-/

namespace ArchonPhysics.CoerciveHamiltonianPhyslib

open InnerProductSpace Time

noncomputable section

/-- The finite configuration space equipped with Mathlib's Euclidean Hilbert structure. -/
abbrev HilbertConfiguration (N : Nat) :=
  EuclideanSpace Real (Lattice.Site N)

/-- Forget only the Hilbert-space wrapper, retaining the same site coordinates. -/
def asConfiguration {N : Nat} (x : HilbertConfiguration N) :
    Lattice.Configuration N :=
  fun i => x i

/-- The autonomous coercive lattice energy in Physlib's Hamiltonian signature. -/
def hamiltonian {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real) :
    Time → HilbertConfiguration N → HilbertConfiguration N → Real :=
  fun _ p q => CoerciveLatticeEnergy.hamiltonian m kappa beta g
    (asConfiguration p) (asConfiguration q)

/-- The stabilized finite chain satisfies Physlib's Hamilton-equation operator. -/
def SatisfiesHamiltonEquations {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (p q : Time → HilbertConfiguration N) : Prop :=
  ClassicalMechanics.hamiltonEqOp
    (hamiltonian m kappa beta g) p q = 0

/--
The project-local predicate is exactly Physlib's pair of Hamilton equations.
-/
theorem satisfiesHamiltonEquations_iff {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (p q : Time → HilbertConfiguration N) :
    SatisfiesHamiltonEquations m kappa beta g p q ↔
      (∀ t, ∂ₜ q t =
        gradient
          (fun p' => hamiltonian m kappa beta g t p' (q t))
          (p t)) ∧
      (∀ t, ∂ₜ p t =
        -gradient
          (fun q' => hamiltonian m kappa beta g t (p t) q')
          (q t)) := by
  exact ClassicalMechanics.hamiltonEqOp_eq_zero_iff_hamiltons_equations
    (hamiltonian m kappa beta g) p q

/-- The Physlib Hamiltonian is definitionally the stabilized lattice energy. -/
theorem hamiltonian_apply {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (t : Time) (p q : HilbertConfiguration N) :
    hamiltonian m kappa beta g t p q =
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration p) (asConfiguration q) := by
  rfl

end


end ArchonPhysics.CoerciveHamiltonianPhyslib
