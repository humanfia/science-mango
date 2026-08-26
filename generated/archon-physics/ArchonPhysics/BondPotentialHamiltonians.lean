import ArchonPhysics.AlphaBetaPotential
import ArchonPhysics.CoerciveLatticeEnergy
import ArchonPhysics.HamiltonianScaling
import ArchonPhysics.LennardJonesPotential

/-!
# Periodic Hamiltonians for concrete bond potentials

This module lifts a real-valued single-bond potential to a finite periodic
chain with a fixed positive mass realization. It specializes the construction
to the FPUT alpha-beta potential, proves its coercive energy bounds and exact
square-root amplitude rescaling, and connects both concrete potentials to the
existing lattice-energy APIs.

The Lennard--Jones bridge is formula-level only. In particular, no homogeneous
amplitude-scaling law is asserted for that inverse-power potential.
-/

namespace ArchonPhysics.BondPotentialHamiltonians

noncomputable section

/-- Periodic potential energy obtained by summing a supplied bond potential. -/
def periodicPotentialEnergy {N : Nat} [NeZero N] (V : Real → Real)
    (q : Lattice.Configuration N) : Real :=
  ∑ i : Lattice.Site N, V (Lattice.forwardDifference q i)

/-- Positive-mass kinetic energy plus a supplied periodic bond energy. -/
def periodicHamiltonian {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (V : Real → Real)
    (p q : Lattice.Configuration N) : Real :=
  Lattice.kineticEnergy m p + periodicPotentialEnergy V q

/-- Periodic FPUT alpha-beta potential energy. -/
def alphaBetaPotentialEnergy {N : Nat} [NeZero N] (alpha beta : Real)
    (q : Lattice.Configuration N) : Real :=
  periodicPotentialEnergy (AlphaBetaPotential.potential alpha beta) q

/-- Periodic FPUT alpha-beta Hamiltonian with a fixed positive mass profile. -/
def alphaBetaHamiltonian {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (alpha beta : Real)
    (p q : Lattice.Configuration N) : Real :=
  periodicHamiltonian m (AlphaBetaPotential.potential alpha beta) p q

/-- Formula-level expansion of the periodic alpha-beta Hamiltonian. -/
theorem alphaBetaHamiltonian_spec {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (alpha beta : Real)
    (p q : Lattice.Configuration N) :
    alphaBetaHamiltonian m alpha beta p q =
      Lattice.kineticEnergy m p +
        ∑ i : Lattice.Site N,
          AlphaBetaPotential.potential alpha beta
            (Lattice.forwardDifference q i) := by
  rfl

/-- Bondwise coercivity sums to the entire periodic alpha-beta chain. -/
theorem alphaBetaPotentialEnergy_lower_bound {N : Nat} [NeZero N]
    {alpha beta : Real} (hbeta : 2 * alpha ^ 2 / 9 < beta)
    (q : Lattice.Configuration N) :
    AlphaBetaPotential.coercivityConstant alpha beta *
        (∑ i : Lattice.Site N, Lattice.forwardDifference q i ^ 2) ≤
      alphaBetaPotentialEnergy alpha beta q := by
  rw [Finset.mul_sum]
  unfold alphaBetaPotentialEnergy periodicPotentialEnergy
  exact Finset.sum_le_sum fun i _ =>
    AlphaBetaPotential.potential_lower_bound hbeta
      (Lattice.forwardDifference q i)

/-- The coercive alpha-beta periodic potential energy is nonnegative. -/
theorem alphaBetaPotentialEnergy_nonneg {N : Nat} [NeZero N]
    {alpha beta : Real} (hbeta : 2 * alpha ^ 2 / 9 < beta)
    (q : Lattice.Configuration N) :
    0 ≤ alphaBetaPotentialEnergy alpha beta q := by
  unfold alphaBetaPotentialEnergy periodicPotentialEnergy
  exact Finset.sum_nonneg fun i _ =>
    AlphaBetaPotential.potential_nonneg hbeta
      (Lattice.forwardDifference q i)

/-- The coercive finite alpha-beta Hamiltonian is nonnegative. -/
theorem alphaBetaHamiltonian_nonneg {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) {alpha beta : Real}
    (hbeta : 2 * alpha ^ 2 / 9 < beta)
    (p q : Lattice.Configuration N) :
    0 ≤ alphaBetaHamiltonian m alpha beta p q := by
  exact add_nonneg (Lattice.kineticEnergy_nonneg m p)
    (alphaBetaPotentialEnergy_nonneg hbeta q)

/-- The alpha-beta energy exactly recovers the earlier stabilized cubic family
under `alpha = kappa*g` and `beta = beta0*g²`. -/
theorem alphaBetaPotentialEnergy_eq_coerciveLatticeEnergy
    {N : Nat} [NeZero N] (kappa beta0 g : Real)
    (q : Lattice.Configuration N) :
    alphaBetaPotentialEnergy (kappa * g) (beta0 * g ^ 2) q =
      CoerciveLatticeEnergy.potentialEnergy kappa beta0 g q := by
  unfold alphaBetaPotentialEnergy periodicPotentialEnergy
  unfold CoerciveLatticeEnergy.potentialEnergy
  apply Finset.sum_congr rfl
  intro i _
  exact AlphaBetaPotential.potential_eq_coerciveCubicPotential
    kappa beta0 g (Lattice.forwardDifference q i)

/-- The corresponding finite positive-mass Hamiltonians agree exactly. -/
theorem alphaBetaHamiltonian_eq_coerciveLatticeEnergy
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (kappa beta0 g : Real) (p q : Lattice.Configuration N) :
    alphaBetaHamiltonian m (kappa * g) (beta0 * g ^ 2) p q =
      CoerciveLatticeEnergy.hamiltonian m kappa beta0 g p q := by
  unfold alphaBetaHamiltonian periodicHamiltonian
  unfold CoerciveLatticeEnergy.hamiltonian
  change Lattice.kineticEnergy m p +
      alphaBetaPotentialEnergy (kappa * g) (beta0 * g ^ 2) q =
    Lattice.kineticEnergy m p + CoerciveLatticeEnergy.potentialEnergy kappa beta0 g q
  rw [alphaBetaPotentialEnergy_eq_coerciveLatticeEnergy]

/-- Forward differences commute with pointwise square-root rescaling. -/
theorem forwardDifference_rescale {N : Nat} (epsilon : Real)
    (q : Lattice.Configuration N) (i : Lattice.Site N) :
    Lattice.forwardDifference
        (HamiltonianScaling.rescaleConfiguration epsilon q) i =
      Real.sqrt epsilon * Lattice.forwardDifference q i := by
  simp only [Lattice.forwardDifference, HamiltonianScaling.rescaleConfiguration]
  ring

/-- Positive-mass kinetic energy is quadratic under square-root rescaling. -/
theorem kineticEnergy_rescale {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) {epsilon : Real}
    (hepsilon : 0 ≤ epsilon) (p : Lattice.Configuration N) :
    Lattice.kineticEnergy m
        (HamiltonianScaling.rescaleConfiguration epsilon p) =
      epsilon * Lattice.kineticEnergy m p := by
  have hsqrt : Real.sqrt epsilon ^ 2 = epsilon := Real.sq_sqrt hepsilon
  unfold Lattice.kineticEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [HamiltonianScaling.rescaleConfiguration, mul_pow, hsqrt]
  ring

/-- Exact square-root amplitude rescaling of the periodic alpha-beta potential
energy. -/
theorem alphaBetaPotentialEnergy_rescale {N : Nat} [NeZero N]
    (alpha beta : Real) {epsilon : Real} (hepsilon : 0 ≤ epsilon)
    (q : Lattice.Configuration N) :
    alphaBetaPotentialEnergy alpha beta
        (HamiltonianScaling.rescaleConfiguration epsilon q) =
      epsilon * alphaBetaPotentialEnergy
        (alpha * Real.sqrt epsilon) (beta * epsilon) q := by
  unfold alphaBetaPotentialEnergy periodicPotentialEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [forwardDifference_rescale]
  exact AlphaBetaPotential.potential_sqrt_rescale_of_nonneg
    alpha beta (Lattice.forwardDifference q i) hepsilon

/-- Exact Hamiltonian law
`H_{alpha,beta}(sqrt(epsilon)p,sqrt(epsilon)q) =
epsilon H_{alpha sqrt(epsilon), beta epsilon}(p,q)`. -/
theorem alphaBetaHamiltonian_rescale {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (alpha beta : Real)
    {epsilon : Real} (hepsilon : 0 ≤ epsilon)
    (p q : Lattice.Configuration N) :
    alphaBetaHamiltonian m alpha beta
        (HamiltonianScaling.rescaleConfiguration epsilon p)
        (HamiltonianScaling.rescaleConfiguration epsilon q) =
      epsilon * alphaBetaHamiltonian m
        (alpha * Real.sqrt epsilon) (beta * epsilon) p q := by
  unfold alphaBetaHamiltonian periodicHamiltonian
  rw [kineticEnergy_rescale m hepsilon p]
  change epsilon * Lattice.kineticEnergy m p +
      alphaBetaPotentialEnergy alpha beta
        (HamiltonianScaling.rescaleConfiguration epsilon q) =
    epsilon * (Lattice.kineticEnergy m p +
      alphaBetaPotentialEnergy
        (alpha * Real.sqrt epsilon) (beta * epsilon) q)
  rw [alphaBetaPotentialEnergy_rescale alpha beta hepsilon q]
  ring

/-- The generic periodic potential construction agrees with the LJ core
potential-energy definition. -/
theorem periodicPotentialEnergy_lennardJones_eq_core
    {N : Nat} [NeZero N] (depth r₀ : Real)
    (q : Lattice.Configuration N) :
    periodicPotentialEnergy
        (LennardJonesPotential.bondPotential depth r₀) q =
      LennardJonesPotential.periodicPotentialEnergy depth r₀ q := by
  rfl

/-- The generic positive-mass Hamiltonian agrees exactly with the LJ core
Hamiltonian. No homogeneous rescaling consequence is attached to this bridge. -/
theorem periodicHamiltonian_lennardJones_eq_core
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (depth r₀ : Real) (p q : Lattice.Configuration N) :
    periodicHamiltonian m
        (LennardJonesPotential.bondPotential depth r₀) p q =
      LennardJonesPotential.periodicRandomMassHamiltonian
        m depth r₀ p q := by
  rfl

end

end ArchonPhysics.BondPotentialHamiltonians
