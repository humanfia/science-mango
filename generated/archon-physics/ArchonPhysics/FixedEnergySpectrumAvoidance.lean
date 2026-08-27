import ArchonPhysics.MeasurableOrderedModeCoupling
import ArchonPhysics.RandomMassSimpleSpectrum

/-!
# Almost-sure avoidance of a fixed positive harmonic energy

For a fixed nonzero energy `E`, evaluate the characteristic polynomial of
the symbolic inverse-mass weighted cycle at `E`.  This is a multivariate
polynomial in the inverse masses.  It is nonzero because its zero-weight
specialization is `E ^ N`.  Coordinatewise inversion and absolute
continuity of every finite iid mass law therefore make its zero event null.

The square Gram identity `charpoly (DᵀD) = charpoly (DDᵀ)` then transfers
this edge-space statement exactly to the physical mass-weighted harmonic
matrix.  Consequently every ordered harmonic eigenvalue avoids `E` almost
surely.  No spectral simplicity, thermodynamic limit, or unproved regularity
assumption is used.
-/

namespace ArchonPhysics.FixedEnergySpectrumAvoidance

open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedCycleBridge
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.RandomMassResultantBridge
open MeasureTheory

noncomputable section

/-- The characteristic polynomial of the symbolic inverse-mass weighted
cycle, evaluated at a fixed energy. -/
def symbolicFixedEnergyCharacteristic {N : Nat} [NeZero N] (E : Real) :
    MvPolynomial (Fin N) Real :=
  (symbolicWeightedCycleLaplacian (N := N)).charpoly.eval (MvPolynomial.C E)

/-- Evaluating the mass variables specializes the symbolic fixed-energy
characteristic determinant to the concrete weighted cycle. -/
theorem eval_symbolicFixedEnergyCharacteristic {N : Nat} [NeZero N]
    (E : Real) (x : Fin N → Real) :
    MvPolynomial.eval x (symbolicFixedEnergyCharacteristic (N := N) E) =
      (weightedCycleLaplacian (weightsOfCoordinates x)).charpoly.eval E := by
  unfold symbolicFixedEnergyCharacteristic
  calc
    MvPolynomial.eval x
        (Polynomial.eval (MvPolynomial.C E)
          (symbolicWeightedCycleLaplacian (N := N)).charpoly) =
      Polynomial.eval₂ (MvPolynomial.eval x)
        (MvPolynomial.eval x (MvPolynomial.C E))
        (symbolicWeightedCycleLaplacian (N := N)).charpoly := by
          symm
          exact Polynomial.eval₂_at_apply (MvPolynomial.eval x) (MvPolynomial.C E)
    _ = Polynomial.eval
        (MvPolynomial.eval x (MvPolynomial.C E))
        (Polynomial.map (MvPolynomial.eval x)
          (symbolicWeightedCycleLaplacian (N := N)).charpoly) :=
      Polynomial.eval₂_eq_eval_map (MvPolynomial.eval x)
    _ = (weightedCycleLaplacian (weightsOfCoordinates x)).charpoly.eval E := by
      rw [← Matrix.charpoly_map, evaluate_symbolicWeightedCycleLaplacian]
      simp

/-- At every nonzero fixed energy the symbolic characteristic determinant is
not the zero multivariate polynomial.  The witness is the zero edge-weight
specialization, whose characteristic polynomial is `X ^ N`. -/
theorem symbolicFixedEnergyCharacteristic_ne_zero {N : Nat} [NeZero N]
    {E : Real} (hE : E ≠ 0) :
    symbolicFixedEnergyCharacteristic (N := N) E ≠ 0 := by
  intro hzero
  have hspecial := eval_symbolicFixedEnergyCharacteristic (N := N) E (fun _ ↦ 0)
  have hmatrix :
      weightedCycleLaplacian (weightsOfCoordinates (fun _ : Fin N ↦ 0)) = 0 := by
    change differenceMatrix * Matrix.diagonal (fun _ ↦ 0) *
      Matrix.transpose differenceMatrix = 0
    simp
  rw [hzero] at hspecial
  simp only [map_zero] at hspecial
  rw [hmatrix, Matrix.charpoly_zero, Polynomial.eval_X_pow] at hspecial
  exact (pow_ne_zero _ hE) hspecial.symm

/-- The physical mass-weighted harmonic Gram matrix and the inverse-mass
edge Gram matrix have identical characteristic polynomials. -/
theorem harmonic_charpoly_eq_weightedCycle_inverseMass
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    (massWeightedHarmonicMatrix m).charpoly =
      (weightedCycleLaplacian
        (weightsOfCoordinates (inverseMassCoordinates m))).charpoly := by
  calc
    (massWeightedHarmonicMatrix m).charpoly =
        (massWeightedDifferenceMatrix m *
          Matrix.transpose (massWeightedDifferenceMatrix m)).charpoly :=
      Matrix.charpoly_mul_comm
        (Matrix.transpose (massWeightedDifferenceMatrix m))
        (massWeightedDifferenceMatrix m)
    _ = (weightedCycleLaplacian (fun i ↦ (m.mass i)⁻¹)).charpoly := by
      rw [massWeighted_selfTranspose_eq_weightedCycleLaplacian]
    _ = (weightedCycleLaplacian
          (weightsOfCoordinates (inverseMassCoordinates m))).charpoly := by
      rw [weightsOfCoordinates_inverseMassCoordinates]

/-- Every ordered Hermitian eigenvalue is a root of the matrix
characteristic polynomial. -/
theorem charpoly_eval_orderedEigenvalue_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) (k : Fin (Fintype.card ι)) :
    (Matrix.charpoly A.1).eval (orderedEigenvalue A k) = 0 := by
  have hmem : (orderedEigenvalue A k) ∈ (Matrix.charpoly A.1).roots := by
    rw [A.property.roots_charpoly_eq_eigenvalues₀]
    simp [orderedEigenvalue]
  exact (Polynomial.mem_roots (Matrix.charpoly_monic A.1).ne_zero).mp hmem

/-- For any verified iid mass-phase ensemble, a fixed nonzero energy is
almost surely not a root of the edge-space characteristic polynomial. -/
theorem probability_weightedCycle_charpoly_eval_eq_zero
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) {N : Nat} [NeZero N]
    {E : Real} (hE : E ≠ 0) :
    ensemble.probability
      {omega |
        Polynomial.eval E
          (Matrix.charpoly
            (weightedCycleLaplacian
              (weightsOfCoordinates
                (coordinatewiseInv (ensemble.restrictMassFin (N := N) omega))))) = 0} = 0 := by
  simpa only [eval_symbolicFixedEnergyCharacteristic] using
    ensemble.probability_eval_inverse_restrictMassFin_eq_zero
      (symbolicFixedEnergyCharacteristic (N := N) E)
      (symbolicFixedEnergyCharacteristic_ne_zero (N := N) hE)

/-- Fixed nonzero energies are almost surely absent from the physical
mass-weighted harmonic characteristic spectrum. -/
theorem probability_harmonic_charpoly_eval_eq_zero
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) {N : Nat} [NeZero N]
    {E : Real} (hE : E ≠ 0) :
    ensemble.probability
      {omega |
        (massWeightedHarmonicMatrix
          (ensemble.restrictPositiveMass (N := N) omega)).charpoly.eval E = 0} = 0 := by
  apply measure_mono_null (t :=
    {omega |
      MvPolynomial.eval
        (coordinatewiseInv (ensemble.restrictMassFin (N := N) omega))
        (symbolicFixedEnergyCharacteristic (N := N) E) = 0})
  · intro omega homega
    change (massWeightedHarmonicMatrix
      (ensemble.restrictPositiveMass (N := N) omega)).charpoly.eval E = 0 at homega
    change MvPolynomial.eval
      (coordinatewiseInv (ensemble.restrictMassFin (N := N) omega))
      (symbolicFixedEnergyCharacteristic (N := N) E) = 0
    rw [eval_symbolicFixedEnergyCharacteristic]
    rw [← RandomMassSimpleSpectrum.inverseMassCoordinates_restrictPositiveMass]
    rw [← harmonic_charpoly_eq_weightedCycle_inverseMass]
    exact homega
  · exact ensemble.probability_eval_inverse_restrictMassFin_eq_zero
      (symbolicFixedEnergyCharacteristic (N := N) E)
      (symbolicFixedEnergyCharacteristic_ne_zero (N := N) hE)

/-- The event that some ordered physical mode has a prescribed nonzero
squared frequency has probability zero. -/
theorem probability_exists_orderedEigenvalue_eq_fixedEnergy
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) {N : Nat} [NeZero N]
    {E : Real} (hE : E ≠ 0) :
    ensemble.probability
      {omega | ∃ k : Fin (Fintype.card (Lattice.Site N)),
        orderedEigenvalue
          (harmonicHermitian
            (ensemble.restrictPositiveMass (N := N) omega)) k = E} = 0 := by
  apply measure_mono_null (t :=
    {omega |
      (massWeightedHarmonicMatrix
        (ensemble.restrictPositiveMass (N := N) omega)).charpoly.eval E = 0})
  · rintro omega ⟨k, hk⟩
    change (massWeightedHarmonicMatrix
      (ensemble.restrictPositiveMass (N := N) omega)).charpoly.eval E = 0
    rw [← hk]
    exact charpoly_eval_orderedEigenvalue_eq_zero
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega)) k
  · exact probability_harmonic_charpoly_eval_eq_zero ensemble hE

/-- Almost surely, every ordered physical mode avoids a prescribed nonzero
squared frequency. -/
theorem orderedEigenvalue_ne_fixedEnergy_ae
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) {N : Nat} [NeZero N]
    {E : Real} (hE : E ≠ 0) :
    ∀ᵐ omega ∂ensemble.probability,
      ∀ k : Fin (Fintype.card (Lattice.Site N)),
        orderedEigenvalue
          (harmonicHermitian
            (ensemble.restrictPositiveMass (N := N) omega)) k ≠ E := by
  have hnull := probability_exists_orderedEigenvalue_eq_fixedEnergy
    ensemble (N := N) hE
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with omega homega
  simpa only [Set.mem_ofPred_eq, not_exists] using homega

/-- Canonical frozen iid masses almost surely avoid every prescribed positive
energy at every ordered mode of a fixed positive volume. -/
theorem canonical_orderedEigenvalue_ne_fixedPositiveEnergy_ae
    {N : Nat} [NeZero N] {E : Real} (hE : 0 < E) :
    ∀ᵐ omega ∂( RandomEnsemble.canonicalLaw),
      ∀ k : Fin (Fintype.card (Lattice.Site N)),
        orderedEigenvalue
          (harmonicHermitian
            (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
              (N := N) omega)) k ≠ E :=
  orderedEigenvalue_ne_fixedEnergy_ae
    canonicalIIDMassPhaseEnsemble (N := N) hE.ne'

end

end ArchonPhysics.FixedEnergySpectrumAvoidance
