import ArchonPhysics.CoerciveCubicPotential
import ArchonPhysics.Lattice

/-!
# Coercive energy bounds for the stabilized finite chain

This module lifts the single-bond coercivity estimate to a finite periodic
lattice.  It proves the a priori energy bounds needed by a later ODE
continuation argument.  It does not assert that a global flow has already been
constructed: controlling the translation direction and carrying out the
continuation theorem remain separate obligations.
-/

namespace ArchonPhysics.CoerciveLatticeEnergy

open CoerciveCubicPotential

noncomputable section

/-- The stabilized potential energy, summed over all periodic bonds. -/
def potentialEnergy {N : Nat} [NeZero N] (kappa beta g : Real)
    (q : Lattice.Configuration N) : Real :=
  ∑ i : Lattice.Site N, potential kappa beta g (Lattice.forwardDifference q i)

/-- Kinetic plus stabilized bond energy for a finite periodic chain. -/
def hamiltonian {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (kappa beta g : Real) (p q : Lattice.Configuration N) : Real :=
  Lattice.kineticEnergy m p + potentialEnergy kappa beta g q

/-- The bondwise coercivity estimate sums to the whole periodic chain. -/
theorem potentialEnergy_lower_bound {N : Nat} [NeZero N]
    {kappa beta : Real} (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (g : Real) (q : Lattice.Configuration N) :
    coercivityConstant kappa beta *
        (∑ i : Lattice.Site N, Lattice.forwardDifference q i ^ 2) ≤
      potentialEnergy kappa beta g q := by
  rw [Finset.mul_sum]
  unfold potentialEnergy
  exact Finset.sum_le_sum fun i _ =>
    potential_lower_bound hbeta g (Lattice.forwardDifference q i)

/-- The stabilized total bond energy is nonnegative. -/
theorem potentialEnergy_nonneg {N : Nat} [NeZero N]
    {kappa beta : Real} (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (g : Real) (q : Lattice.Configuration N) :
    0 ≤ potentialEnergy kappa beta g q := by
  unfold potentialEnergy
  exact Finset.sum_nonneg fun i _ =>
    potential_nonneg hbeta g (Lattice.forwardDifference q i)

/-- The stabilized finite-chain Hamiltonian is nonnegative. -/
theorem hamiltonian_nonneg {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) {kappa beta : Real}
    (hbeta : 2 * kappa ^ 2 / 9 < beta) (g : Real)
    (p q : Lattice.Configuration N) :
    0 ≤ hamiltonian m kappa beta g p q := by
  exact add_nonneg (Lattice.kineticEnergy_nonneg m p)
    (potentialEnergy_nonneg hbeta g q)

/-- Kinetic energy is bounded by the conserved total-energy candidate. -/
theorem kineticEnergy_le_hamiltonian {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) {kappa beta : Real}
    (hbeta : 2 * kappa ^ 2 / 9 < beta) (g : Real)
    (p q : Lattice.Configuration N) :
    Lattice.kineticEnergy m p ≤ hamiltonian m kappa beta g p q := by
  exact le_add_of_nonneg_right (potentialEnergy_nonneg hbeta g q)

/-- Potential energy is bounded by the total-energy candidate. -/
theorem potentialEnergy_le_hamiltonian {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (p q : Lattice.Configuration N) :
    potentialEnergy kappa beta g q ≤ hamiltonian m kappa beta g p q := by
  exact le_add_of_nonneg_left (Lattice.kineticEnergy_nonneg m p)

/--
The total energy controls the squared periodic differences, uniformly in the
effective coupling `g`.
-/
theorem sum_sq_forwardDifference_le_energy_div {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) {kappa beta : Real}
    (hbeta : 2 * kappa ^ 2 / 9 < beta) (g : Real)
    (p q : Lattice.Configuration N) :
    (∑ i : Lattice.Site N, Lattice.forwardDifference q i ^ 2) ≤
      hamiltonian m kappa beta g p q / coercivityConstant kappa beta := by
  have hc : 0 < coercivityConstant kappa beta := coercivityConstant_pos hbeta
  apply (le_div_iff₀ hc).2
  calc
    (∑ i : Lattice.Site N, Lattice.forwardDifference q i ^ 2) *
          coercivityConstant kappa beta =
        coercivityConstant kappa beta *
          (∑ i : Lattice.Site N, Lattice.forwardDifference q i ^ 2) := by
            rw [mul_comm]
    _ ≤ potentialEnergy kappa beta g q := potentialEnergy_lower_bound hbeta g q
    _ ≤ hamiltonian m kappa beta g p q :=
      potentialEnergy_le_hamiltonian m kappa beta g p q

/-- Every momentum coordinate is controlled by the total energy. -/
theorem momentum_sq_le_mass_mul_energy {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) {kappa beta : Real}
    (hbeta : 2 * kappa ^ 2 / 9 < beta) (g : Real)
    (p q : Lattice.Configuration N) (i : Lattice.Site N) :
    p i ^ 2 ≤ 2 * m.mass i * hamiltonian m kappa beta g p q := by
  have hden : 0 < 2 * m.mass i := mul_pos (by norm_num) (m.mass_pos i)
  have hterm_nonneg : forall j : Lattice.Site N,
      0 ≤ p j ^ 2 / (2 * m.mass j) := by
    intro j
    exact div_nonneg (sq_nonneg (p j))
      (le_of_lt (mul_pos (by norm_num) (m.mass_pos j)))
  have hterm :
      p i ^ 2 / (2 * m.mass i) ≤ Lattice.kineticEnergy m p := by
    unfold Lattice.kineticEnergy
    exact Finset.single_le_sum (fun j _ => hterm_nonneg j) (Finset.mem_univ i)
  have hdiv :
      p i ^ 2 / (2 * m.mass i) ≤ hamiltonian m kappa beta g p q :=
    hterm.trans (kineticEnergy_le_hamiltonian m hbeta g p q)
  have hmul := (div_le_iff₀ hden).1 hdiv
  nlinarith [m.mass_pos i]

/-- Formula-level lock for the stabilized lattice energy. -/
theorem energy_spec {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (p q : Lattice.Configuration N) :
    potentialEnergy kappa beta g q =
        ∑ i : Lattice.Site N,
          potential kappa beta g (Lattice.forwardDifference q i) ∧
      hamiltonian m kappa beta g p q =
        Lattice.kineticEnergy m p + potentialEnergy kappa beta g q := by
  exact ⟨rfl, rfl⟩

end

end ArchonPhysics.CoerciveLatticeEnergy
