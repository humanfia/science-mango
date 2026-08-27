import ArchonPhysics.BondPotentialHamiltonians
import ArchonPhysics.ConcreteHamiltonGradients

/-!
# Physlib Hamilton equations for a differentiable periodic bond potential

This module lifts an arbitrary one-bond derivative formula to the exact
finite periodic-chain gradient and to Physlib's Hamilton equations.  The
Lennard--Jones specialization is valid at configurations whose physical bond
lengths are nonzero.  No trajectory existence, collision avoidance, kinetic
limit, random-phase propagation, or thermalization assertion is made.
-/

namespace ArchonPhysics.BondPotentialHamiltonianPhyslib

open InnerProductSpace
open Time
open ArchonPhysics.BondPotentialHamiltonians
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ConcreteHamiltonGradients

noncomputable section

/-- A supplied periodic bond Hamiltonian in Physlib's time-dependent
signature (the Hamiltonian is autonomous). -/
def hamiltonian {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (V : Real → Real) :
    Time → HilbertConfiguration N → HilbertConfiguration N → Real :=
  fun _ p q => periodicHamiltonian m V (asConfiguration p) (asConfiguration q)

/-- Physlib's Hamilton-equation predicate for a supplied periodic bond
potential. -/
def SatisfiesHamiltonEquations {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (V : Real → Real)
    (p q : Time → HilbertConfiguration N) : Prop :=
  ClassicalMechanics.hamiltonEqOp (hamiltonian m V) p q = 0

/-- The project-local predicate is exactly Physlib's pair of Hamilton
equations. -/
theorem satisfiesHamiltonEquations_iff {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (V : Real → Real)
    (p q : Time → HilbertConfiguration N) :
    SatisfiesHamiltonEquations m V p q ↔
      (∀ t, ∂ₜ q t =
        gradient (fun p' => hamiltonian m V t p' (q t)) (p t)) ∧
      (∀ t, ∂ₜ p t =
        -gradient (fun q' => hamiltonian m V t (p t) q') (q t)) := by
  exact ClassicalMechanics.hamiltonEqOp_eq_zero_iff_hamiltons_equations
    (hamiltonian m V) p q

/-- Explicit finite sum representing the gradient of a supplied bond
potential with derivative `V'`. -/
def potentialGradient {N : Nat} [NeZero N] (V' : Real → Real)
    (q : HilbertConfiguration N) : HilbertConfiguration N :=
  ∑ i : Lattice.Site N,
    V' (Lattice.forwardDifference (asConfiguration q) i) • bondDirection i

/-- One differentiable bond term has its expected two-site gradient. -/
theorem hasGradientAt_bondTerm {N : Nat} [NeZero N]
    (V V' : Real → Real) (q : HilbertConfiguration N)
    (i : Lattice.Site N)
    (hV : HasDerivAt V
      (V' (Lattice.forwardDifference (asConfiguration q) i))
      (Lattice.forwardDifference (asConfiguration q) i)) :
    HasGradientAt
      (fun y : HilbertConfiguration N =>
        V (Lattice.forwardDifference (asConfiguration y) i))
      (V' (Lattice.forwardDifference (asConfiguration q) i) •
        bondDirection i) q := by
  have h := HasDerivAt.hasGradientAt_comp_clm
    (bondFunctional i) (bondDirection i) q (bondFunctional_eq_toDual i)
    (by simpa using hV)
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y => by simp

/-- Pointwise differentiability of every occupied bond gives the exact
gradient of the finite periodic potential energy. -/
theorem hasGradientAt_periodicPotentialEnergy {N : Nat} [NeZero N]
    (V V' : Real → Real) (q : HilbertConfiguration N)
    (hV : ∀ i : Lattice.Site N,
      HasDerivAt V
        (V' (Lattice.forwardDifference (asConfiguration q) i))
        (Lattice.forwardDifference (asConfiguration q) i)) :
    HasGradientAt
      (fun y : HilbertConfiguration N =>
        periodicPotentialEnergy V (asConfiguration y))
      (potentialGradient V' q) q := by
  unfold periodicPotentialEnergy potentialGradient
  exact hasGradientAt_finset_sum
    (fun i _ => hasGradientAt_bondTerm V V' q i (hV i))

/-- Formula for the gradient of a differentiable finite periodic bond
energy. -/
theorem gradient_periodicPotentialEnergy {N : Nat} [NeZero N]
    (V V' : Real → Real) (q : HilbertConfiguration N)
    (hV : ∀ i : Lattice.Site N,
      HasDerivAt V
        (V' (Lattice.forwardDifference (asConfiguration q) i))
        (Lattice.forwardDifference (asConfiguration q) i)) :
    gradient
      (fun y : HilbertConfiguration N =>
        periodicPotentialEnergy V (asConfiguration y)) q =
      potentialGradient V' q :=
  (hasGradientAt_periodicPotentialEnergy V V' q hV).gradient

/-- The momentum gradient of a general bond Hamiltonian is the inverse-mass
velocity. -/
theorem gradient_hamiltonian_momentum {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (V : Real → Real)
    (t : Time) (p q : HilbertConfiguration N) :
    gradient (fun p' => hamiltonian m V t p' q) p =
      inverseMassMomentum m p := by
  change gradient
    (fun p' : HilbertConfiguration N =>
      Lattice.kineticEnergy m (asConfiguration p') +
        periodicPotentialEnergy V (asConfiguration q)) p = _
  rw [gradient_add_const, ArchonPhysics.ConcreteHamiltonGradients.gradient_kineticEnergy]

/-- The position gradient of a general bond Hamiltonian is the explicit sum
of bond forces. -/
theorem gradient_hamiltonian_position {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (V V' : Real → Real)
    (t : Time) (p q : HilbertConfiguration N)
    (hV : ∀ i : Lattice.Site N,
      HasDerivAt V
        (V' (Lattice.forwardDifference (asConfiguration q) i))
        (Lattice.forwardDifference (asConfiguration q) i)) :
    gradient (fun q' => hamiltonian m V t p q') q =
      potentialGradient V' q := by
  have hfun :
      (fun q' : HilbertConfiguration N => hamiltonian m V t p q') =
        fun q' => periodicPotentialEnergy V (asConfiguration q') +
          Lattice.kineticEnergy m (asConfiguration p) := by
    funext q'
    simp [hamiltonian, periodicHamiltonian, add_comm]
  rw [hfun, gradient_add_const, gradient_periodicPotentialEnergy V V' q hV]

/-- Physlib's abstract equations reduce to the explicit finite bond-force
equations whenever the derivative formula holds at every occupied bond along
the trajectory. -/
theorem satisfiesHamiltonEquations_iff_explicit_of_hasDeriv
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (V V' : Real → Real)
    (p q : Time → HilbertConfiguration N)
    (hV : ∀ t i,
      HasDerivAt V
        (V' (Lattice.forwardDifference (asConfiguration (q t)) i))
        (Lattice.forwardDifference (asConfiguration (q t)) i)) :
    SatisfiesHamiltonEquations m V p q ↔
      (∀ t, ∂ₜ q t = inverseMassMomentum m (p t)) ∧
      (∀ t, ∂ₜ p t = -potentialGradient V' (q t)) := by
  rw [satisfiesHamiltonEquations_iff]
  simp_rw [gradient_hamiltonian_momentum,
    gradient_hamiltonian_position m V V' _ _ _ (hV _)]

/-- The exact derivative of the displacement-form Lennard--Jones bond away
from the collision singularity. -/
def lennardJonesDerivative (depth r₀ x : Real) : Real :=
  LennardJonesPotential.radialDerivative depth r₀ (r₀ + x)

/-- Every actual LJ bond length along the supplied configuration is nonzero.
Positivity is physically preferable, but nonzeroness is the exact analytic
hypothesis needed by the derivative formula. -/
def LennardJonesBondsNonsingular {N : Nat} [NeZero N]
    (r₀ : Real) (q : HilbertConfiguration N) : Prop :=
  ∀ i : Lattice.Site N,
    r₀ + Lattice.forwardDifference (asConfiguration q) i ≠ 0

/-- A nonsingular LJ configuration supplies the pointwise derivative formula
required by the generic finite-chain gradient theorem. -/
theorem hasDerivAt_lennardJones_bonds {N : Nat} [NeZero N]
    (depth r₀ : Real) (q : HilbertConfiguration N)
    (hq : LennardJonesBondsNonsingular r₀ q) :
    ∀ i : Lattice.Site N,
      HasDerivAt (LennardJonesPotential.bondPotential depth r₀)
        (lennardJonesDerivative depth r₀
          (Lattice.forwardDifference (asConfiguration q) i))
        (Lattice.forwardDifference (asConfiguration q) i) := by
  intro i
  exact LennardJonesPotential.hasDerivAt_bondPotential_of_ne (hq i)

/-- Exact formula for the finite LJ potential gradient on the nonsingular
configuration domain. -/
theorem gradient_lennardJones_periodicPotentialEnergy
    {N : Nat} [NeZero N]
    (depth r₀ : Real) (q : HilbertConfiguration N)
    (hq : LennardJonesBondsNonsingular r₀ q) :
    gradient
      (fun y : HilbertConfiguration N =>
        LennardJonesPotential.periodicPotentialEnergy depth r₀
          (asConfiguration y)) q =
      potentialGradient (lennardJonesDerivative depth r₀) q := by
  exact gradient_periodicPotentialEnergy
    (LennardJonesPotential.bondPotential depth r₀)
    (lennardJonesDerivative depth r₀) q
    (hasDerivAt_lennardJones_bonds depth r₀ q hq)

/-- The generic Physlib Hamiltonian is definitionally the existing exact LJ
finite-chain Hamiltonian. -/
theorem hamiltonian_lennardJones_eq_core {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (t : Time) (p q : HilbertConfiguration N) :
    hamiltonian m (LennardJonesPotential.bondPotential depth r₀) t p q =
      LennardJonesPotential.periodicRandomMassHamiltonian
        m depth r₀ (asConfiguration p) (asConfiguration q) := by
  rfl

/-- Physlib's exact LJ equations become an explicit inverse-mass velocity and
the exact inverse-power bond force along every nonsingular trajectory. -/
theorem lennardJones_satisfiesHamiltonEquations_iff_explicit
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ : Real)
    (p q : Time → HilbertConfiguration N)
    (hq : ∀ t, LennardJonesBondsNonsingular r₀ (q t)) :
    SatisfiesHamiltonEquations m
        (LennardJonesPotential.bondPotential depth r₀) p q ↔
      (∀ t, ∂ₜ q t = inverseMassMomentum m (p t)) ∧
      (∀ t, ∂ₜ p t =
        -potentialGradient (lennardJonesDerivative depth r₀) (q t)) := by
  exact satisfiesHamiltonEquations_iff_explicit_of_hasDeriv
    m (LennardJonesPotential.bondPotential depth r₀)
      (lennardJonesDerivative depth r₀) p q
      (fun t => hasDerivAt_lennardJones_bonds depth r₀ (q t) (hq t))

end

end ArchonPhysics.BondPotentialHamiltonianPhyslib
