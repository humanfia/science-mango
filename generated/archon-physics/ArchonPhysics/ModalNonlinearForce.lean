import ArchonPhysics.ModeCoupling

/-!
# Exact finite modal expansion of the nonlinear bond force

For the stabilized cubic-leading potential, the nonlinear part of the
mass-weighted force contains a quadratic bond term and a cubic bond term.
This module proves, at fixed finite volume and fixed positive masses, that the
projection of those terms onto a selected normal mode is exactly the ordered
finite sum built from `ModeCoupling.interactionTensor`.

This is an algebraic identity.  It makes no resonance, kinetic-limit,
nondegeneracy, or thermalization assertion.
-/

namespace ArchonPhysics.ModalNonlinearForce

open ArchonPhysics
open ModeCoupling
open ReducedModeTransform

noncomputable section

/-- A bond polynomial with one distinguished modal leg. -/
def distinguishedBondPolynomial {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (amplitude : WeightedConfiguration N) (k : Lattice.Site N)
    (n : Nat) : Real :=
  ∑ j, bondModeCoefficient m j k *
    (Lattice.forwardDifference (physicalReconstruction m amplitude) j) ^ n

/-- Ordered tensor contraction with one distinguished modal leg. -/
def distinguishedTensorContraction {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (amplitude : WeightedConfiguration N) (k : Lattice.Site N)
    (n : Nat) : Real :=
  ∑ modes : Fin n → Lattice.Site N,
    interactionTensor m (n + 1) (Fin.cons k modes) *
      ∏ r, amplitude (modes r)

/-- Expanding the physical bond polynomial gives precisely the interaction
tensor contraction with the observed mode in the first slot. -/
theorem distinguishedBondPolynomial_eq_tensorContraction
    {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (amplitude : WeightedConfiguration N) (k : Lattice.Site N) :
    distinguishedBondPolynomial m amplitude k n =
      distinguishedTensorContraction m amplitude k n := by
  classical
  unfold distinguishedBondPolynomial distinguishedTensorContraction
  simp_rw [forwardDifference_physicalReconstruction]
  calc
    ∑ j, bondModeCoefficient m j k *
          (∑ mode, amplitude mode * bondModeCoefficient m j mode) ^ n =
        ∑ j, bondModeCoefficient m j k *
          ∑ modes : Fin n → Lattice.Site N,
            ∏ r, amplitude (modes r) * bondModeCoefficient m j (modes r) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Fintype.sum_pow]
    _ = ∑ j, ∑ modes : Fin n → Lattice.Site N,
          bondModeCoefficient m j k *
            (∏ r, amplitude (modes r) * bondModeCoefficient m j (modes r)) := by
      simp only [Finset.mul_sum]
    _ = ∑ j, ∑ modes : Fin n → Lattice.Site N,
          bondModeCoefficient m j k *
            ((∏ r, amplitude (modes r)) *
              ∏ r, bondModeCoefficient m j (modes r)) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro modes hmodes
      rw [Finset.prod_mul_distrib]
    _ = ∑ modes : Fin n → Lattice.Site N, ∑ j,
          (bondModeCoefficient m j k *
              ∏ r, bondModeCoefficient m j (modes r)) *
            ∏ r, amplitude (modes r) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro modes hmodes
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ modes : Fin n → Lattice.Site N,
          interactionTensor m (n + 1) (Fin.cons k modes) *
            ∏ r, amplitude (modes r) := by
      apply Finset.sum_congr rfl
      intro modes hmodes
      unfold interactionTensor
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]

/-- The nonlinear modal force obtained by projecting the quadratic and cubic
bond forces.  The minus sign is the Hamiltonian force convention. -/
def projectedNonlinearBondForce {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (amplitude : WeightedConfiguration N) (k : Lattice.Site N) : Real :=
  -(kappa * g * distinguishedBondPolynomial m amplitude k 2) -
    beta * g ^ 2 * distinguishedBondPolynomial m amplitude k 3

/-- The same nonlinear force written as exact three- and four-leg tensor
contractions. -/
def tensorNonlinearForce {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (amplitude : WeightedConfiguration N) (k : Lattice.Site N) : Real :=
  -(kappa * g * distinguishedTensorContraction m amplitude k 2) -
    beta * g ^ 2 * distinguishedTensorContraction m amplitude k 3

/-- Exact finite identification of the projected nonlinear bond force with
the modal interaction tensors. -/
theorem projectedNonlinearBondForce_eq_tensorNonlinearForce
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (amplitude : WeightedConfiguration N) (k : Lattice.Site N) :
    projectedNonlinearBondForce m kappa beta g amplitude k =
      tensorNonlinearForce m kappa beta g amplitude k := by
  unfold projectedNonlinearBondForce tensorNonlinearForce
  rw [distinguishedBondPolynomial_eq_tensorContraction,
    distinguishedBondPolynomial_eq_tensorContraction]

end

end ArchonPhysics.ModalNonlinearForce
