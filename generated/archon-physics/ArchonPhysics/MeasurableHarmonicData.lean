import ArchonPhysics.HarmonicModes
import ArchonPhysics.RandomEnsemble

/-!
# Measurable finite-volume harmonic data

This module maps a measurable finite positive-mass sample to the two matrices
used by `ArchonPhysics.HarmonicModes` and proves measurability both entrywise
and as finite Pi-valued matrices.  It then records measurable spectral
invariants which do not depend on signs or choices inside degenerate
eigenspaces: the trace, determinant, next-to-leading characteristic-polynomial
coefficient, and constant characteristic-polynomial coefficient.

The proofs use the product measurable structure on finite matrices together
with Mathlib's measurability of square root, inversion, finite sums and finite
products.  Determinant measurability is grounded directly in
`Matrix.det_apply'`.

Mathlib supplies the ordered enumeration
`Matrix.IsHermitian.eigenvalues₀` (with `eigenvalues₀_antitone`), but no
continuity or measurability theorem for this enumeration as the matrix varies
is used or supplied here.  This missing bridge, and measurable eigenbasis
selection, are deliberately not encoded as assumptions or structure fields.
-/

namespace ArchonPhysics.MeasurableHarmonicData

open HarmonicModes

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]
variable {N : Nat} [NeZero N]

/-- Entry formula for the inverse-square-root mass-weighted difference matrix. -/
theorem massWeightedDifferenceMatrix_apply (m : Lattice.PositiveMassConfig N)
    (i j : Lattice.Site N) :
    massWeightedDifferenceMatrix m i j =
      differenceMatrix i j * (Real.sqrt (m.mass j))⁻¹ := by
  simp [massWeightedDifferenceMatrix]

/-- Entry formula for the mass-weighted harmonic Gram matrix. -/
theorem massWeightedHarmonicMatrix_apply (m : Lattice.PositiveMassConfig N)
    (i j : Lattice.Site N) :
    massWeightedHarmonicMatrix m i j =
      ∑ k, massWeightedDifferenceMatrix m k i * massWeightedDifferenceMatrix m k j := by
  simp [massWeightedHarmonicMatrix, Matrix.mul_apply]

/-- A finite positive-mass sample whose mass coordinates are measurable gives
a measurable inverse-square-root weighted difference matrix. -/
theorem measurable_massWeightedDifferenceMatrix_of_coordinate
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (hmass : ∀ i, Measurable fun omega ↦ (massSample omega).mass i) :
    Measurable fun omega i j ↦ massWeightedDifferenceMatrix (massSample omega) i j := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  simp_rw [massWeightedDifferenceMatrix_apply]
  exact measurable_const.mul ((hmass j).sqrt.inv)

/-- A finite positive-mass sample whose mass coordinates are measurable gives
a measurable mass-weighted harmonic matrix. -/
theorem measurable_massWeightedHarmonicMatrix_of_coordinate
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (hmass : ∀ i, Measurable fun omega ↦ (massSample omega).mass i) :
    Measurable fun omega i j ↦ massWeightedHarmonicMatrix (massSample omega) i j := by
  have hDifference :=
    measurable_massWeightedDifferenceMatrix_of_coordinate massSample hmass
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  simp_rw [massWeightedHarmonicMatrix_apply]
  exact Finset.measurable_sum Finset.univ fun k _ ↦
    ((measurable_pi_apply i).comp ((measurable_pi_apply k).comp hDifference)).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hDifference))

/-- Trace of the sampled mass-weighted harmonic matrix. -/
def harmonicTrace (massSample : Omega → Lattice.PositiveMassConfig N) (omega : Omega) : Real :=
  Matrix.trace (massWeightedHarmonicMatrix (massSample omega))

/-- Determinant of the sampled mass-weighted harmonic matrix. -/
def harmonicDet (massSample : Omega → Lattice.PositiveMassConfig N) (omega : Omega) : Real :=
  Matrix.det (massWeightedHarmonicMatrix (massSample omega))

/-- The trace is a measurable, eigenbasis-independent spectral invariant. -/
theorem measurable_harmonicTrace_of_coordinate
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (hmass : ∀ i, Measurable fun omega ↦ (massSample omega).mass i) :
    Measurable (harmonicTrace massSample) := by
  have hMatrix := measurable_massWeightedHarmonicMatrix_of_coordinate massSample hmass
  unfold harmonicTrace Matrix.trace
  exact Finset.measurable_sum Finset.univ fun i _ ↦
    (measurable_pi_apply i).comp ((measurable_pi_apply i).comp hMatrix)

/-- The determinant is a measurable, eigenbasis-independent spectral invariant. -/
theorem measurable_harmonicDet_of_coordinate
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (hmass : ∀ i, Measurable fun omega ↦ (massSample omega).mass i) :
    Measurable (harmonicDet massSample) := by
  have hMatrix := measurable_massWeightedHarmonicMatrix_of_coordinate massSample hmass
  unfold harmonicDet
  simp_rw [Matrix.det_apply']
  exact Finset.measurable_sum Finset.univ fun sigma _ ↦
    measurable_const.mul (Finset.measurable_prod Finset.univ fun i _ ↦
      (measurable_pi_apply i).comp
        ((measurable_pi_apply (sigma i)).comp hMatrix))

/-- The next-to-leading characteristic-polynomial coefficient is measurable.
This is obtained from the trace identity and makes no eigenvector choice. -/
theorem measurable_harmonicCharpolyNextCoeff_of_coordinate
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (hmass : ∀ i, Measurable fun omega ↦ (massSample omega).mass i) :
    Measurable fun omega ↦
      (massWeightedHarmonicMatrix (massSample omega)).charpoly.nextCoeff := by
  have hTrace := measurable_harmonicTrace_of_coordinate massSample hmass
  have hFunction :
      (fun omega ↦ (massWeightedHarmonicMatrix (massSample omega)).charpoly.nextCoeff) =
        fun omega ↦ -harmonicTrace massSample omega := by
    funext omega
    unfold harmonicTrace
    rw [Matrix.trace_eq_neg_charpoly_nextCoeff]
    simp
  rw [hFunction]
  exact hTrace.neg

/-- The constant characteristic-polynomial coefficient is measurable.
This is obtained from the determinant identity and makes no eigenvector choice. -/
theorem measurable_harmonicCharpolyCoeffZero_of_coordinate
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (hmass : ∀ i, Measurable fun omega ↦ (massSample omega).mass i) :
    Measurable fun omega ↦
      (massWeightedHarmonicMatrix (massSample omega)).charpoly.coeff 0 := by
  have hDet := measurable_harmonicDet_of_coordinate massSample hmass
  let sign : Real := (-1) ^ Fintype.card (Lattice.Site N)
  have hsign : sign ≠ 0 := by
    simp [sign]
  have hFunction :
      (fun omega ↦ (massWeightedHarmonicMatrix (massSample omega)).charpoly.coeff 0) =
        fun omega ↦ harmonicDet massSample omega / sign := by
    funext omega
    apply (eq_div_iff hsign).2
    rw [mul_comm]
    exact (Matrix.det_eq_sign_charpoly_coeff
      (massWeightedHarmonicMatrix (massSample omega))).symm
  rw [hFunction]
  exact hDet.div_const sign

/-- The finite inverse-square-root weighted difference matrix obtained from an
`IIDMassPhaseEnsemble`. -/
def sampledMassWeightedDifferenceMatrix (ensemble : IIDMassPhaseEnsemble Omega)
    (omega : Omega) : Matrix (Lattice.Site N) (Lattice.Site N) Real :=
  massWeightedDifferenceMatrix (ensemble.restrictPositiveMass omega)

/-- The finite mass-weighted harmonic matrix obtained from an
`IIDMassPhaseEnsemble`. -/
def sampledMassWeightedHarmonicMatrix (ensemble : IIDMassPhaseEnsemble Omega)
    (omega : Omega) : Matrix (Lattice.Site N) (Lattice.Site N) Real :=
  massWeightedHarmonicMatrix (ensemble.restrictPositiveMass omega)

/-- The finite weighted difference matrix of any verified ensemble is measurable. -/
theorem measurable_sampledMassWeightedDifferenceMatrix
    (ensemble : IIDMassPhaseEnsemble Omega) :
    Measurable fun omega i j ↦
      sampledMassWeightedDifferenceMatrix (N := N) ensemble omega i j := by
  apply measurable_massWeightedDifferenceMatrix_of_coordinate
  intro i
  simpa using ensemble.mass_measurable i.val

/-- The finite harmonic matrix of any verified ensemble is measurable. -/
theorem measurable_sampledMassWeightedHarmonicMatrix
    (ensemble : IIDMassPhaseEnsemble Omega) :
    Measurable fun omega i j ↦
      sampledMassWeightedHarmonicMatrix (N := N) ensemble omega i j := by
  apply measurable_massWeightedHarmonicMatrix_of_coordinate
  intro i
  simpa using ensemble.mass_measurable i.val

/-- Canonical-product specialization of weighted-difference-matrix measurability. -/
theorem measurable_canonicalMassWeightedDifferenceMatrix :
    Measurable fun omega i j ↦
      sampledMassWeightedDifferenceMatrix (N := N)
        canonicalIIDMassPhaseEnsemble omega i j :=
  measurable_sampledMassWeightedDifferenceMatrix canonicalIIDMassPhaseEnsemble

/-- Canonical-product specialization of harmonic-matrix measurability. -/
theorem measurable_canonicalMassWeightedHarmonicMatrix :
    Measurable fun omega i j ↦
      sampledMassWeightedHarmonicMatrix (N := N)
        canonicalIIDMassPhaseEnsemble omega i j :=
  measurable_sampledMassWeightedHarmonicMatrix canonicalIIDMassPhaseEnsemble

end

end ArchonPhysics.MeasurableHarmonicData
