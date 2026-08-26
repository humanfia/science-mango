import ArchonPhysics.HermitianEigenvalueMultiplicity
import ArchonPhysics.InverseMassPolynomialAvoidance
import ArchonPhysics.MeasurableOrderedSpectrum
import ArchonPhysics.PathLaplacianResultant
import ArchonPhysics.RandomMassResultantBridge

/-!
# Almost-sure simplicity of the positive random-mass harmonic spectrum

This module closes the finite-dimensional generic-spectrum chain for the
verified iid mass ensemble.  The broken-cycle path specialization proves that
the symbolic resultant is nonzero.  Coordinatewise inversion preserves
Lebesgue-null polynomial zero sets, so the inverse mass vector avoids the
resultant zero set almost surely.  The deterministic Gram bridge then excludes
every two-dimensional positive eigenspace of the harmonic matrix.

The final ordered formulation uses Mathlib's Hermitian eigenbasis: equal
positive ordered eigenvalues at distinct indices would give precisely such a
two-dimensional eigenspace.
-/

namespace ArchonPhysics.RandomMassSimpleSpectrum

open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HermitianEigenvalueMultiplicity
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.PathLaplacianResultant
open ArchonPhysics.RandomMassResultantBridge
open MeasureTheory

noncomputable section

/-- For the canonical `Fin N` enumeration, inverse masses of the finite
positive-mass configuration are exactly the coordinatewise inverses of the
finite iid mass vector. -/
theorem inverseMassCoordinates_restrictPositiveMass
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) {N : Nat} [NeZero N]
    (omega : Omega) :
    inverseMassCoordinates
        (ensemble.restrictPositiveMass (N := N) omega) =
      coordinatewiseInv (ensemble.restrictMassFin (N := N) omega) := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    ext k
    simp only [coordinatewiseInv_apply]
    change (ensemble.mass ((ZMod.finEquiv (n + 1)) k).val omega)⁻¹ =
      (ensemble.mass k.val omega)⁻¹
    change (ensemble.mass k.val omega)⁻¹ = (ensemble.mass k.val omega)⁻¹
    rfl

/-- For every chain of length at least two, the event that the mass-weighted
harmonic matrix has a repeated strictly positive eigenvalue has probability
zero. -/
theorem probability_repeatedPositiveHarmonicEigenvalue_eq_zero
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) {N : Nat} [NeZero N]
    (hN : 2 ≤ N) :
    ensemble.probability
        {omega |
          HasRepeatedPositiveHarmonicEigenvalue
            (ensemble.restrictPositiveMass (N := N) omega)} = 0 := by
  apply measure_mono_null (t :=
    {omega |
      MvPolynomial.eval
        (coordinatewiseInv (ensemble.restrictMassFin (N := N) omega))
        (symbolicRepeatedRootCertificate (N := N)) = 0})
  · intro omega homega
    have hcertificate := certificate_vanishes_of_repeatedPositiveHarmonic
      (ensemble.restrictPositiveMass (N := N) omega) homega
    rwa [inverseMassCoordinates_restrictPositiveMass] at hcertificate
  · exact ensemble.probability_eval_inverse_restrictMassFin_eq_zero
      (symbolicRepeatedRootCertificate (N := N))
      (symbolicRepeatedRootCertificate_ne_zero hN)

/-- Almost-sure form: every positive harmonic eigenspace has dimension at
most one. -/
theorem not_repeatedPositiveHarmonicEigenvalue_ae
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) {N : Nat} [NeZero N]
    (hN : 2 ≤ N) :
    ∀ᵐ omega ∂ensemble.probability,
      ¬ HasRepeatedPositiveHarmonicEigenvalue
        (ensemble.restrictPositiveMass (N := N) omega) := by
  exact measure_eq_zero_iff_ae_notMem.mp
    (probability_repeatedPositiveHarmonicEigenvalue_eq_zero ensemble hN)

/-- A duplicate positive entry of the decreasing ordered Hermitian spectrum
forces a repeated positive harmonic eigenvalue. -/
theorem repeatedPositiveHarmonic_of_orderedEigenvalue_eq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {i j : Fin (Fintype.card (Lattice.Site N))}
    (hne : i ≠ j)
    (hpositive : 0 <
      orderedEigenvalue
        ⟨HarmonicModes.massWeightedHarmonicMatrix m,
          (HarmonicModes.massWeightedHarmonicMatrix_posSemidef m).isHermitian⟩ i)
    (hequal :
      orderedEigenvalue
          ⟨HarmonicModes.massWeightedHarmonicMatrix m,
            (HarmonicModes.massWeightedHarmonicMatrix_posSemidef m).isHermitian⟩ i =
        orderedEigenvalue
          ⟨HarmonicModes.massWeightedHarmonicMatrix m,
            (HarmonicModes.massWeightedHarmonicMatrix_posSemidef m).isHermitian⟩ j) :
    HasRepeatedPositiveHarmonicEigenvalue m := by
  let A := HarmonicModes.massWeightedHarmonicMatrix m
  let hA : A.IsHermitian :=
    (HarmonicModes.massWeightedHarmonicMatrix_posSemidef m).isHermitian
  obtain ⟨v, hv, heigen⟩ :=
    exists_linearIndependent_eigenvectors_of_eigenvalues₀_eq hA
      (by simpa [orderedEigenvalue, A, hA] using hequal) hne
  refine ⟨hA.eigenvalues₀ i, ?_, v, hv, heigen⟩
  simpa [orderedEigenvalue, A, hA] using hpositive

/-- Basis-free ordered formulation of failure of positive spectral
simplicity. -/
def HasOrderedPositiveDuplicate {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) : Prop :=
  let A : HermitianMatrix (Lattice.Site N) :=
    ⟨HarmonicModes.massWeightedHarmonicMatrix m,
      (HarmonicModes.massWeightedHarmonicMatrix_posSemidef m).isHermitian⟩
  ∃ i j : Fin (Fintype.card (Lattice.Site N)),
    i ≠ j ∧ 0 < orderedEigenvalue A i ∧
      orderedEigenvalue A i = orderedEigenvalue A j

theorem repeatedPositiveHarmonic_of_orderedPositiveDuplicate
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (h : HasOrderedPositiveDuplicate m) :
    HasRepeatedPositiveHarmonicEigenvalue m := by
  rcases h with ⟨i, j, hne, hpositive, hequal⟩
  exact repeatedPositiveHarmonic_of_orderedEigenvalue_eq m hne hpositive hequal

/-- The positive ordered harmonic spectrum of every verified iid ensemble is
almost surely simple. -/
theorem probability_orderedPositiveDuplicate_eq_zero
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) {N : Nat} [NeZero N]
    (hN : 2 ≤ N) :
    ensemble.probability
        {omega |
          HasOrderedPositiveDuplicate
            (ensemble.restrictPositiveMass (N := N) omega)} = 0 := by
  apply measure_mono_null (t :=
    {omega |
      HasRepeatedPositiveHarmonicEigenvalue
        (ensemble.restrictPositiveMass (N := N) omega)})
  · intro omega homega
    exact repeatedPositiveHarmonic_of_orderedPositiveDuplicate _ homega
  · exact probability_repeatedPositiveHarmonicEigenvalue_eq_zero ensemble hN

/-- Final canonical-ensemble statement: for iid masses uniform on
`[4/5, 6/5]`, distinct ordered indices cannot carry the same positive harmonic
eigenvalue, almost surely. -/
theorem canonical_probability_orderedPositiveDuplicate_eq_zero
    {N : Nat} [NeZero N] (hN : 2 ≤ N) :
    RandomEnsemble.canonicalLaw
        {omega |
          HasOrderedPositiveDuplicate
            (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
              (N := N) omega)} = 0 :=
  probability_orderedPositiveDuplicate_eq_zero
    canonicalIIDMassPhaseEnsemble hN

end

end ArchonPhysics.RandomMassSimpleSpectrum
