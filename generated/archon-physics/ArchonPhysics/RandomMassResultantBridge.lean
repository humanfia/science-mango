import ArchonPhysics.MassWeightedCycleBridge

/-!
# Random-mass positive-spectrum degeneracy implies resultant degeneracy

This module composes the Gram multiplicity transfer with the inverse-mass
weighted-cycle identity.  It does not assert a probability law: it is the
deterministic event inclusion needed before applying absolute continuity and
the multivariate-polynomial zero-set theorem.
-/

namespace ArchonPhysics.RandomMassResultantBridge

open ArchonPhysics.HarmonicModes
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.GramMultiplicityTransfer
open ArchonPhysics.MassWeightedCycleBridge

noncomputable section

/-- A repeated strictly positive eigenvalue of the mass-weighted harmonic
matrix, represented without choosing an eigenbasis. -/
def HasRepeatedPositiveHarmonicEigenvalue {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) : Prop :=
  ∃ lambda : Real, 0 < lambda ∧ ∃ v : Fin 2 → Lattice.Configuration N,
    LinearIndependent Real v ∧
      ∀ j, Matrix.mulVec (massWeightedHarmonicMatrix m) (v j) =
        lambda • (v j)

/-- Repeated positive harmonic spectrum is contained in the geometric
multiplicity-two event for the inverse-mass polynomial matrix. -/
theorem weightedCycle_geometricMultiplicityTwo_of_repeatedPositiveHarmonic
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (h : HasRepeatedPositiveHarmonicEigenvalue m) :
    HasGeometricMultiplicityTwo
      (weightedCycleLaplacian (fun i ↦ (m.mass i)⁻¹)) := by
  rcases h with ⟨lambda, hlambda, v, hv, heigen⟩
  rw [← massWeighted_selfTranspose_eq_weightedCycleLaplacian]
  apply selfTranspose_geometricMultiplicityTwo_of_transposeSelf
    (massWeightedDifferenceMatrix m) hlambda.ne' v hv
  simpa [massWeightedHarmonicMatrix] using heigen

/-- Inverse masses in the fixed `Fin N` coordinate enumeration. -/
def inverseMassCoordinates {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) : Fin N → Real :=
  fun k ↦ (m.mass ((siteEquivFin N).symm k))⁻¹

theorem weightsOfCoordinates_inverseMassCoordinates
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    weightsOfCoordinates (inverseMassCoordinates m) = fun i ↦ (m.mass i)⁻¹ := by
  ext i
  simp [weightsOfCoordinates, inverseMassCoordinates]

/-- A repeated positive harmonic eigenvalue forces the symbolic resultant to
vanish at the inverse-mass coordinates. -/
theorem certificate_vanishes_of_repeatedPositiveHarmonic
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (h : HasRepeatedPositiveHarmonicEigenvalue m) :
    MvPolynomial.eval (inverseMassCoordinates m)
      (symbolicRepeatedRootCertificate (N := N)) = 0 := by
  apply certificate_vanishes_of_geometricMultiplicityTwo
  rw [weightsOfCoordinates_inverseMassCoordinates]
  exact weightedCycle_geometricMultiplicityTwo_of_repeatedPositiveHarmonic m h

end

end ArchonPhysics.RandomMassResultantBridge
