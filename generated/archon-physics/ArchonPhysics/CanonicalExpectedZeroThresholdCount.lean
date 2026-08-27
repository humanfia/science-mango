import ArchonPhysics.CanonicalThresholdCountConcentrationInterface
import ArchonPhysics.RandomMassOrderedProjectorBridge

/-!
# Canonical expected threshold count at and below zero

The harmonic matrix is positive semidefinite for every positive mass sample.
Thus every strictly negative threshold has count zero deterministically.  At
threshold zero, the deterministic one-dimensional translation kernel and the
almost-sure full spectral simplicity of the canonical iid ensemble imply that
exactly one of the `N` ordered eigenvalues is counted.  The normalized count
is therefore almost surely, and in expectation, exactly `1 / N`.
-/

namespace ArchonPhysics.CanonicalExpectedZeroThresholdCount

open ArchonPhysics.CanonicalThresholdCountConcentrationInterface
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.RandomMassAcousticCountingComparison
open ArchonPhysics.RandomMassOrderedProjectorBridge
open MeasureTheory

noncomputable section

/-- A nonnegative finite ordered spectrum with a unique zero eigenvalue has
threshold count one at zero. -/
theorem orderedEigenvalueThresholdCount_zero_eq_one
    {index : Type*} [Fintype index] [DecidableEq index]
    (A : HermitianMatrix index)
    (hnonneg : ∀ k : Fin (Fintype.card index), 0 ≤ orderedEigenvalue A k)
    (hzero : ∃! z : Fin (Fintype.card index), orderedEigenvalue A z = 0) :
    orderedEigenvalueThresholdCount A 0 = 1 := by
  rcases hzero with ⟨z, hz, hunique⟩
  unfold orderedEigenvalueThresholdCount
  have hindices : orderedEigenvalueThresholdIndices A 0 = {z} := by
    ext k
    rw [mem_orderedEigenvalueThresholdIndices_iff]
    simp only [Finset.mem_singleton]
    constructor
    · intro hk
      exact hunique k (le_antisymm hk (hnonneg k))
    · intro hk
      subst k
      exact hz.le
  rw [hindices]
  simp

/-- A nonnegative finite ordered spectrum has no eigenvalue at or below any
strictly negative threshold. -/
theorem orderedEigenvalueThresholdCount_eq_zero_of_lt_zero
    {index : Type*} [Fintype index] [DecidableEq index]
    (A : HermitianMatrix index)
    (hnonneg : ∀ k : Fin (Fintype.card index), 0 ≤ orderedEigenvalue A k)
    {E : Real} (hE : E < 0) :
    orderedEigenvalueThresholdCount A E = 0 := by
  unfold orderedEigenvalueThresholdCount
  rw [Finset.card_eq_zero]
  ext k
  rw [mem_orderedEigenvalueThresholdIndices_iff]
  constructor
  · intro hk
    exact (not_le.mpr (hE.trans_le (hnonneg k)) hk).elim
  · intro hk
    simp at hk

/-- For `N ≥ 2`, the canonical normalized harmonic threshold count at zero
is almost surely exactly the single translation mode divided by volume. -/
theorem canonicalNormalizedHarmonicThresholdCount_zero_ae
    {N : Nat} [NeZero N] (hN : 2 ≤ N) :
    ∀ᵐ omega ∂(RandomEnsemble.canonicalLaw),
      canonicalNormalizedHarmonicThresholdCount N 0 omega =
        1 / (N : Real) := by
  filter_upwards [existsUnique_orderedZeroMode_ae
    canonicalIIDMassPhaseEnsemble (N := N) hN] with omega hzero
  have hzero' : ∃! k : Fin (Fintype.card (Lattice.Site N)),
      orderedEigenvalue
        (harmonicHermitian
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega)) k = 0 := by
    simpa [harmonicOrderedEigenvalue, harmonicHermitianSample,
      harmonicHermitian] using hzero
  have hnonneg : ∀ k : Fin (Fintype.card (Lattice.Site N)),
      0 ≤ orderedEigenvalue
        (harmonicHermitian
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega)) k := by
    intro k
    simpa [harmonicOrderedEigenvalue, harmonicHermitianSample,
      harmonicHermitian] using
      harmonicOrderedEigenvalue_nonneg
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N)) omega k
  rw [canonicalNormalizedHarmonicThresholdCount_eq]
  rw [orderedEigenvalueThresholdCount_zero_eq_one _ hnonneg hzero']
  norm_num

/-- The canonical expected normalized threshold count at zero is exactly
`1 / N` for every volume `N ≥ 2`. -/
theorem expected_canonicalNormalizedHarmonicThresholdCount_zero
    {N : Nat} [NeZero N] (hN : 2 ≤ N) :
    (∫ omega, canonicalNormalizedHarmonicThresholdCount N 0 omega
      ∂(RandomEnsemble.canonicalLaw)) = 1 / (N : Real) := by
  rw [integral_congr_ae
    (canonicalNormalizedHarmonicThresholdCount_zero_ae (N := N) hN)]
  simp

/-- At every strictly negative threshold the canonical normalized harmonic
count is zero for every sample, without an almost-sure qualifier. -/
theorem canonicalNormalizedHarmonicThresholdCount_eq_zero_of_lt_zero
    (N : Nat) [NeZero N] {E : Real} (hE : E < 0)
    (omega : RandomEnsemble.SampleSpace) :
    canonicalNormalizedHarmonicThresholdCount N E omega = 0 := by
  have hnonneg : ∀ k : Fin (Fintype.card (Lattice.Site N)),
      0 ≤ orderedEigenvalue
        (harmonicHermitian
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega)) k := by
    intro k
    simpa [harmonicOrderedEigenvalue, harmonicHermitianSample,
      harmonicHermitian] using
      harmonicOrderedEigenvalue_nonneg
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N)) omega k
  rw [canonicalNormalizedHarmonicThresholdCount_eq]
  rw [orderedEigenvalueThresholdCount_eq_zero_of_lt_zero _ hnonneg hE]
  norm_num

/-- Consequently the expected canonical normalized count is zero at every
strictly negative threshold. -/
theorem expected_canonicalNormalizedHarmonicThresholdCount_eq_zero_of_lt_zero
    (N : Nat) [NeZero N] {E : Real} (hE : E < 0) :
    (∫ omega, canonicalNormalizedHarmonicThresholdCount N E omega
      ∂(RandomEnsemble.canonicalLaw)) = 0 := by
  rw [integral_congr_ae (ae_of_all _
    (canonicalNormalizedHarmonicThresholdCount_eq_zero_of_lt_zero N hE))]
  simp

end

end ArchonPhysics.CanonicalExpectedZeroThresholdCount
