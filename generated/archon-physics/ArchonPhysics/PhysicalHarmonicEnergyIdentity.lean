import ArchonPhysics.RandomMassMeasurableHarmonicEnergy

/-!
# Physical identification of the ordered harmonic-energy sum

The globally measurable ordered-mode observable is defined in mass-weighted
coordinates.  This module closes the deterministic algebraic bridge back to
the original canonical variables.  It proves that

* `‖M⁻¹ᐟ² p‖² / 2` is exactly the physical kinetic energy, and
* `⟨M¹ᐟ² q, Hₘ M¹ᐟ² q⟩ / 2` is exactly the sum of harmonic bond energies.

Consequently, on a simple spectrum, the sum of all ordered physical modal
energies is the original-coordinate harmonic Hamiltonian.  No limiting or
thermalization assertion is made here.
-/

open scoped Matrix

namespace ArchonPhysics.PhysicalHarmonicEnergyIdentity

open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassMeasurableHarmonicEnergy
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.SpectralBandEnergyObservable
open MeasureTheory

noncomputable section

/-- The physical harmonic nearest-neighbour potential
`(1/2) * sum_i (q_{i+1}-q_i)^2`. -/
def harmonicBondEnergy {N : Nat} [NeZero N]
    (q : Lattice.Configuration N) : Real :=
  ∑ i : Lattice.Site N, Lattice.forwardDifference q i ^ 2 / 2

/-- The harmonic Hamiltonian in the original canonical coordinates. -/
def physicalHarmonicHamiltonian {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (p q : Lattice.Configuration N) : Real :=
  Lattice.kineticEnergy m p + harmonicBondEnergy q

/-- Inverse-square-root mass weighting followed by square-root mass weighting
cancels exactly, coordinate by coordinate. -/
theorem inverseSqrtMassAction_sqrtMassTransform
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (q : HilbertConfiguration N) :
    Lattice.inverseSqrtMassAction m
        (WithLp.ofLp (sqrtMassTransform m q)) =
      asConfiguration q := by
  funext i
  simp only [Lattice.inverseSqrtMassAction, sqrtMassTransform_apply,
    asConfiguration]
  exact inv_mul_cancel_left₀
    (Real.sqrt_ne_zero'.2 (m.mass_pos i)) (q i)

/-- The weighted difference of `M¹ᐟ² q` is the original physical forward
difference of `q`. -/
theorem massWeightedDifference_mulVec_sqrtMassTransform
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (q : HilbertConfiguration N) :
    Matrix.mulVec (massWeightedDifferenceMatrix m)
        (WithLp.ofLp (sqrtMassTransform m q)) =
      Lattice.forwardDifference (asConfiguration q) := by
  rw [ArchonPhysics.ModeCoupling.weightedDifference_mulVec_eq_forwardDifference]
  rw [inverseSqrtMassAction_sqrtMassTransform]

/-- The Euclidean kinetic term in mass-weighted momentum coordinates is
exactly the physical kinetic energy `sum_i p_i^2/(2m_i)`. -/
theorem coordinateEnergy_inverseSqrtMassTransform_div_two
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (p : HilbertConfiguration N) :
    coordinateEnergy (inverseSqrtMassTransform m p) / 2 =
      Lattice.kineticEnergy m (asConfiguration p) := by
  unfold coordinateEnergy Lattice.kineticEnergy dotProduct
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [inverseSqrtMassTransform_apply]
  change
    (((Real.sqrt (m.mass i))⁻¹ * p i) *
        ((Real.sqrt (m.mass i))⁻¹ * p i)) / 2 =
      p i ^ 2 / (2 * m.mass i)
  have hm0 : m.mass i ≠ 0 := ne_of_gt (m.mass_pos i)
  have hs0 : Real.sqrt (m.mass i) ≠ 0 :=
    Real.sqrt_ne_zero'.2 (m.mass_pos i)
  have hs2 : Real.sqrt (m.mass i) ^ 2 = m.mass i :=
    Real.sq_sqrt (le_of_lt (m.mass_pos i))
  field_simp [hs0, hm0]
  nlinarith [hs2]

/-- The mass-weighted harmonic quadratic form is exactly twice the physical
harmonic bond energy. -/
theorem massWeighted_harmonicQuadraticForm_div_two
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (q : HilbertConfiguration N) :
    ((sqrtMassTransform m q : Lattice.Configuration N) ⬝ᵥ
        (massWeightedHarmonicMatrix m *ᵥ
          (sqrtMassTransform m q : Lattice.Configuration N))) / 2 =
      harmonicBondEnergy (asConfiguration q) := by
  let D := massWeightedDifferenceMatrix m
  let x : Lattice.Configuration N :=
    (sqrtMassTransform m q : Lattice.Configuration N)
  have hDx : Matrix.mulVec D x =
      Lattice.forwardDifference (asConfiguration q) := by
    exact massWeightedDifference_mulVec_sqrtMassTransform m q
  have hquad :
      x ⬝ᵥ (massWeightedHarmonicMatrix m *ᵥ x) =
        (Matrix.mulVec D x) ⬝ᵥ (Matrix.mulVec D x) := by
    calc
      x ⬝ᵥ (massWeightedHarmonicMatrix m *ᵥ x) =
          x ⬝ᵥ (Matrix.transpose D *ᵥ (D *ᵥ x)) := by
            rw [massWeightedHarmonicMatrix_eq_transpose_mul_self,
              ← Matrix.mulVec_mulVec]
      _ = (Matrix.mulVec D x) ⬝ᵥ (Matrix.mulVec D x) :=
        Matrix.dotProduct_transpose_mulVec D x (Matrix.mulVec D x)
  rw [show (sqrtMassTransform m q : Lattice.Configuration N) = x by rfl]
  rw [hquad, hDx]
  unfold harmonicBondEnergy dotProduct
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [pow_two]

/-- At zero effective coupling the stabilized potential reduces exactly to
the harmonic bond energy. -/
theorem potentialEnergy_zero_eq_harmonicBondEnergy
    {N : Nat} [NeZero N] (kappa beta : Real)
    (q : Lattice.Configuration N) :
    CoerciveLatticeEnergy.potentialEnergy kappa beta 0 q =
      harmonicBondEnergy q := by
  unfold CoerciveLatticeEnergy.potentialEnergy harmonicBondEnergy
    CoerciveCubicPotential.potential
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The mass-weighted expression appearing in the ordered spectral
decomposition is precisely the original-coordinate harmonic Hamiltonian. -/
theorem massWeightedEnergy_eq_physicalHarmonicHamiltonian
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (position momentum : HilbertConfiguration N) :
    (coordinateEnergy (inverseSqrtMassTransform m momentum) +
        (sqrtMassTransform m position : Lattice.Configuration N) ⬝ᵥ
          (massWeightedHarmonicMatrix m *ᵥ
            (sqrtMassTransform m position : Lattice.Configuration N))) / 2 =
      physicalHarmonicHamiltonian m
        (asConfiguration momentum) (asConfiguration position) := by
  rw [add_div]
  rw [coordinateEnergy_inverseSqrtMassTransform_div_two,
    massWeighted_harmonicQuadraticForm_div_two]
  rfl

variable {Omega : Type*} [MeasurableSpace Omega]

omit [MeasurableSpace Omega] in
/-- On a simple spectrum, all ordered physical modal energies sum exactly to
the original-coordinate harmonic Hamiltonian. -/
theorem sum_harmonicOrderedPhysicalModeEnergy_eq_physical_of_simple
    {N : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (position momentum : Omega → HilbertConfiguration N)
    (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitianSample massSample omega)) :
    (∑ k : Fin (Fintype.card (Lattice.Site N)),
      harmonicOrderedPhysicalModeEnergy
        massSample position momentum omega k) =
      physicalHarmonicHamiltonian (massSample omega)
        (asConfiguration (momentum omega))
        (asConfiguration (position omega)) := by
  rw [sum_harmonicOrderedPhysicalModeEnergy_of_simple
    massSample position momentum omega hsimple]
  exact massWeightedEnergy_eq_physicalHarmonicHamiltonian
    (massSample omega) (position omega) (momentum omega)

/-- For an iid positive-mass ensemble with at least two sites, the exact
original-coordinate harmonic-energy sum holds almost surely. -/
theorem sum_harmonicOrderedPhysicalModeEnergy_eq_physical_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (position momentum : Omega → HilbertConfiguration N) :
    ∀ᵐ omega ∂ensemble.probability,
      (∑ k : Fin (Fintype.card (Lattice.Site N)),
        harmonicOrderedPhysicalModeEnergy
          (ensemble.restrictPositiveMass (N := N))
          position momentum omega k) =
        physicalHarmonicHamiltonian
          (ensemble.restrictPositiveMass (N := N) omega)
          (asConfiguration (momentum omega))
          (asConfiguration (position omega)) := by
  filter_upwards [simpleOrderedSpectrum_ae ensemble hN] with omega hsimple
  exact sum_harmonicOrderedPhysicalModeEnergy_eq_physical_of_simple
    (ensemble.restrictPositiveMass (N := N))
    position momentum omega hsimple

end

end ArchonPhysics.PhysicalHarmonicEnergyIdentity
