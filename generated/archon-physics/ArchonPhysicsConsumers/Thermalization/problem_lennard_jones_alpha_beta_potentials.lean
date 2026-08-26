import ArchonPhysics.BondPotentialHamiltonians
import ArchonPhysics.LennardJonesAlphaBetaBridge
import ArchonPhysics.LennardJonesTaylorRemainder

/-!
# Acceptance target: Lennard--Jones and FPUT alpha-beta bond potentials

This consumer locks the exact finite-dimensional statements used when the
nearest-neighbour bond law is changed from a polynomial alpha-beta potential to
an equilibrium-distance Lennard--Jones 12--6 potential. The collision
integral's Dirac resonance constraint is not a bond potential and is untouched.

The local coefficient bridge identifies the normalized fourth-order LJ
equilibrium jet with an alpha-beta polynomial. It deliberately makes no claim
that the full LJ potential is quartic or obeys a homogeneous amplitude law.
-/

namespace ArchonPhysicsConsumers.Thermalization.LennardJonesAlphaBetaPotentials

open ArchonPhysics
open Asymptotics
open scoped Topology

noncomputable section

/-- Formula and force law for the standard alpha-beta bond potential. -/
theorem alphaBeta_formula_and_derivative (alpha beta x : Real) :
    AlphaBetaPotential.potential alpha beta x =
        x ^ 2 / 2 + alpha * x ^ 3 / 3 + beta * x ^ 4 / 4 ∧
      AlphaBetaPotential.derivative alpha beta x =
        x + alpha * x ^ 2 + beta * x ^ 3 := by
  exact ⟨rfl, rfl⟩

/-- The derivative formula is an actual derivative statement. -/
theorem alphaBeta_hasDerivAt (alpha beta x : Real) :
    HasDerivAt (AlphaBetaPotential.potential alpha beta)
      (AlphaBetaPotential.derivative alpha beta x) x :=
  AlphaBetaPotential.hasDerivAt_potential alpha beta x

/-- Acceptance lock for the exact finite periodic alpha-beta Hamiltonian
rescaling. -/
theorem alphaBeta_periodicHamiltonian_rescale
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (alpha beta : Real) {epsilon : Real} (hepsilon : 0 ≤ epsilon)
    (p q : Lattice.Configuration N) :
    BondPotentialHamiltonians.alphaBetaHamiltonian m alpha beta
        (HamiltonianScaling.rescaleConfiguration epsilon p)
        (HamiltonianScaling.rescaleConfiguration epsilon q) =
      epsilon * BondPotentialHamiltonians.alphaBetaHamiltonian m
        (alpha * Real.sqrt epsilon) (beta * epsilon) p q :=
  BondPotentialHamiltonians.alphaBetaHamiltonian_rescale
    m alpha beta hepsilon p q

/-- Acceptance lock for the periodic coercive energy bound. -/
theorem alphaBeta_periodic_coercive
    {N : Nat} [NeZero N] {alpha beta : Real}
    (hbeta : 2 * alpha ^ 2 / 9 < beta)
    (q : Lattice.Configuration N) :
    AlphaBetaPotential.coercivityConstant alpha beta *
        (∑ i : Lattice.Site N, Lattice.forwardDifference q i ^ 2) ≤
      BondPotentialHamiltonians.alphaBetaPotentialEnergy alpha beta q :=
  BondPotentialHamiltonians.alphaBetaPotentialEnergy_lower_bound hbeta q

/-- The exact Lennard--Jones 12--6 formula and shifted-square factorization. -/
theorem lennardJones_formula_and_factor (depth r₀ r : Real) :
    LennardJonesPotential.rawPotential depth r₀ r =
        depth * ((r₀ / r) ^ 12 - 2 * (r₀ / r) ^ 6) ∧
      LennardJonesPotential.shiftedPotential depth r₀ r =
        depth * (((r₀ / r) ^ 6 - 1) ^ 2) := by
  exact ⟨rfl, LennardJonesPotential.shiftedPotential_factor depth r₀ r⟩

/-- Positive well depth makes the shifted LJ potential nonnegative at every
algebraic separation. Physical dynamics additionally use positive separation. -/
theorem lennardJones_shifted_nonnegative {depth : Real}
    (hdepth : 0 ≤ depth) (r₀ r : Real) :
    0 ≤ LennardJonesPotential.shiftedPotential depth r₀ r :=
  LennardJonesPotential.shiftedPotential_nonneg hdepth

/-- Equilibrium value and stationary first derivative. -/
theorem lennardJones_equilibrium {depth r₀ : Real} (hr₀ : 0 < r₀) :
    LennardJonesPotential.rawPotential depth r₀ r₀ = -depth ∧
      LennardJonesPotential.shiftedPotential depth r₀ r₀ = 0 ∧
      LennardJonesPotential.radialDerivative depth r₀ r₀ = 0 := by
  have hr₀Ne : r₀ ≠ 0 := ne_of_gt hr₀
  exact ⟨LennardJonesPotential.rawPotential_equilibrium hr₀Ne,
    LennardJonesPotential.shiftedPotential_equilibrium hr₀Ne,
    LennardJonesPotential.radialDerivative_equilibrium hr₀Ne⟩

/-- Physical bond admissibility supplies the domain for the exact bond-force
derivative formula. -/
theorem lennardJones_bond_hasDerivAt {depth r₀ x : Real}
    (hbond : LennardJonesPotential.BondAdmissible r₀ x) :
    HasDerivAt (LennardJonesPotential.bondPotential depth r₀)
      (LennardJonesPotential.radialDerivative depth r₀ (r₀ + x)) x :=
  LennardJonesPotential.hasDerivAt_bondPotential hbond

/-- The explicit first-through-fourth LJ derivative chain away from collision. -/
theorem lennardJones_derivative_chain {depth r₀ r : Real} (hr : r ≠ 0) :
    HasDerivAt (LennardJonesPotential.rawPotential depth r₀)
        (LennardJonesPotential.radialDerivative depth r₀ r) r ∧
      HasDerivAt (LennardJonesPotential.radialDerivative depth r₀)
        (LennardJonesPotential.radialSecondDerivative depth r₀ r) r ∧
      HasDerivAt (LennardJonesPotential.radialSecondDerivative depth r₀)
        (LennardJonesPotential.radialThirdDerivative depth r₀ r) r ∧
      HasDerivAt (LennardJonesPotential.radialThirdDerivative depth r₀)
        (LennardJonesPotential.radialFourthDerivative depth r₀ r) r := by
  exact ⟨LennardJonesPotential.hasDerivAt_rawPotential hr,
    LennardJonesPotential.hasDerivAt_radialDerivative hr,
    LennardJonesPotential.hasDerivAt_radialSecondDerivative hr,
    LennardJonesPotential.hasDerivAt_radialThirdDerivative hr⟩

/-- The exact derivative values fixing the fourth-order equilibrium Taylor jet. -/
theorem lennardJones_equilibrium_derivatives {depth r₀ : Real}
    (hr₀ : 0 < r₀) :
    LennardJonesPotential.radialDerivative depth r₀ r₀ = 0 ∧
      LennardJonesPotential.radialSecondDerivative depth r₀ r₀ =
        72 * depth / r₀ ^ 2 ∧
      LennardJonesPotential.radialThirdDerivative depth r₀ r₀ =
        -1512 * depth / r₀ ^ 3 ∧
      LennardJonesPotential.radialFourthDerivative depth r₀ r₀ =
        26712 * depth / r₀ ^ 4 := by
  have hr₀Ne : r₀ ≠ 0 := ne_of_gt hr₀
  exact ⟨LennardJonesPotential.radialDerivative_equilibrium hr₀Ne,
    LennardJonesPotential.radialSecondDerivative_equilibrium hr₀Ne,
    LennardJonesPotential.radialThirdDerivative_equilibrium hr₀Ne,
    LennardJonesPotential.radialFourthDerivative_equilibrium hr₀Ne⟩

/-- Formula and nonnegativity lock for the finite periodic LJ Hamiltonian. -/
theorem lennardJones_periodicHamiltonian
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {depth r₀ : Real} (hdepth : 0 ≤ depth)
    (p q : Lattice.Configuration N) :
    LennardJonesPotential.periodicRandomMassHamiltonian m depth r₀ p q =
        (∑ i : Lattice.Site N, p i ^ 2 / (2 * m.mass i)) +
          ∑ i : Lattice.Site N,
            LennardJonesPotential.shiftedPotential depth r₀
              (r₀ + Lattice.forwardDifference q i) ∧
      0 ≤ LennardJonesPotential.periodicRandomMassHamiltonian
        m depth r₀ p q := by
  exact ⟨LennardJonesPotential.periodicRandomMassHamiltonian_spec
      m depth r₀ p q,
    LennardJonesPotential.periodicRandomMassHamiltonian_nonneg
      m hdepth p q⟩

/-- Physical LJ configuration admissibility remains an explicit open-domain
condition on every actual bond length. -/
theorem lennardJones_admissibility
    {N : Nat} (r₀ : Real) (q : Lattice.Configuration N) :
    LennardJonesPotential.AdmissibleConfiguration r₀ q ↔
      ∀ i : Lattice.Site N,
        0 < r₀ + Lattice.forwardDifference q i :=
  LennardJonesPotential.admissibleConfiguration_iff r₀ q

/-- Exact normalized LJ coefficients and their strict alpha-beta coercivity. -/
theorem normalized_lennardJones_coefficients
    {depth r₀ : Real} (hdepth : 0 < depth) (hr₀ : 0 < r₀) :
    LennardJonesAlphaBetaBridge.normalizedAlpha depth r₀ =
        -21 / (2 * r₀) ∧
      LennardJonesAlphaBetaBridge.normalizedBeta depth r₀ =
        371 / (6 * r₀ ^ 2) ∧
      2 * LennardJonesAlphaBetaBridge.normalizedAlpha depth r₀ ^ 2 / 9 <
        LennardJonesAlphaBetaBridge.normalizedBeta depth r₀ := by
  exact ⟨LennardJonesAlphaBetaBridge.normalizedAlpha_eq hdepth hr₀,
    LennardJonesAlphaBetaBridge.normalizedBeta_eq hdepth hr₀,
    LennardJonesAlphaBetaBridge.normalized_coercive hdepth hr₀⟩

/-- The precise local statement: the normalized fourth-order equilibrium
polynomial, not the full LJ potential, is an alpha-beta potential. -/
theorem normalized_local_quartic_is_alphaBeta
    {depth r₀ : Real} (hdepth : 0 < depth) (hr₀ : 0 < r₀)
    (x : Real) :
    LennardJonesAlphaBetaBridge.normalizedLocalQuarticPotential depth r₀ x =
      AlphaBetaPotential.potential
        (LennardJonesAlphaBetaBridge.normalizedAlpha depth r₀)
        (LennardJonesAlphaBetaBridge.normalizedBeta depth r₀) x :=
  LennardJonesAlphaBetaBridge.normalizedLocalQuarticPotential_eq_alphaBetaPotential
    hdepth hr₀ x

/-- The exact LJ bond differs from its fourth-order local alpha-beta
polynomial by a remainder that is little-o of the fourth power at equilibrium. -/
theorem lennardJones_sub_localQuartic_isLittleO
    (depth : Real) {r₀ : Real} (hr₀ : 0 < r₀) :
    (fun x : Real =>
      LennardJonesPotential.bondPotential depth r₀ x -
        LennardJonesPotential.localAlphaBetaPotential depth r₀ x) =o[𝓝 0]
      (fun x : Real => x ^ 4) :=
  LennardJonesTaylorRemainder.bondPotential_sub_localAlphaBetaPotential_isLittleO
    depth (ne_of_gt hr₀)

#print axioms alphaBeta_periodicHamiltonian_rescale
#print axioms alphaBeta_periodic_coercive
#print axioms lennardJones_derivative_chain
#print axioms lennardJones_bond_hasDerivAt
#print axioms lennardJones_periodicHamiltonian
#print axioms normalized_lennardJones_coefficients
#print axioms normalized_local_quartic_is_alphaBeta
#print axioms lennardJones_sub_localQuartic_isLittleO

end

end ArchonPhysicsConsumers.Thermalization.LennardJonesAlphaBetaPotentials
