import ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
import ArchonPhysics.CanonicalThresholdCountConcentrationInterface
import ArchonPhysics.HarmonicNormalizedEdgeFrame
import ArchonPhysics.RandomMassAcousticCountingComparison

/-!
# Exact ordered-rank / empirical-IDS identity

For a simple Hermitian spectrum listed in decreasing order, the spectral
sublevel set at the `k`-th eigenvalue is exactly the final interval `Ici k`.
Consequently its cardinality is `card index - k`, including the threshold
eigenvalue itself.  This gives an exact finite-volume bridge between the
normalized decreasing rank and the complementary empirical scalar IDS.

The final two results specialize this deterministic fact to the frozen
random-mass harmonic matrix.  The physical threshold is written as the
square of the ordered frequency, and the last theorem uses the canonical
normalized harmonic threshold-count observable directly.
-/

namespace ArchonPhysics.OrderedRankThresholdCountIdentity

open ArchonPhysics
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalThresholdCountConcentrationInterface
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassAcousticCountingComparison

noncomputable section

variable {index : Type*} [Fintype index] [DecidableEq index]

/-- In a simple decreasingly ordered spectrum, lying below the `k`-th
eigenvalue is equivalent to having index at least `k`. -/
theorem orderedEigenvalue_le_orderedEigenvalue_iff
    (A : HermitianMatrix index) (hsimple : SimpleOrderedSpectrum A)
    (k j : Fin (Fintype.card index)) :
    orderedEigenvalue A j <= orderedEigenvalue A k <-> k <= j := by
  constructor
  · intro hle
    by_contra hnot
    have hjk : j < k := lt_of_not_ge hnot
    have hreverse : orderedEigenvalue A k <= orderedEigenvalue A j := by
      simpa [orderedEigenvalue] using
        A.property.eigenvalues₀_antitone (le_of_lt hjk)
    have heq : orderedEigenvalue A j = orderedEigenvalue A k :=
      le_antisymm hle hreverse
    have hjkeq : j = k := hsimple heq
    exact (ne_of_lt hjk) hjkeq
  · intro hkj
    simpa [orderedEigenvalue] using
      A.property.eigenvalues₀_antitone hkj

/-- The complete spectral sublevel set at the `k`-th simple eigenvalue is the
final interval of ordered indices beginning at `k`. -/
theorem orderedEigenvalueThresholdIndices_at_orderedEigenvalue
    (A : HermitianMatrix index) (hsimple : SimpleOrderedSpectrum A)
    (k : Fin (Fintype.card index)) :
    orderedEigenvalueThresholdIndices A (orderedEigenvalue A k) =
      Finset.Ici k := by
  ext j
  simp [orderedEigenvalueThresholdIndices,
    orderedEigenvalue_le_orderedEigenvalue_iff A hsimple k j]

/-- Exact finite-dimensional threshold count at a simple ordered
eigenvalue.  The `<=` threshold convention includes index `k`. -/
theorem orderedEigenvalueThresholdCount_at_orderedEigenvalue
    (A : HermitianMatrix index) (hsimple : SimpleOrderedSpectrum A)
    (k : Fin (Fintype.card index)) :
    orderedEigenvalueThresholdCount A (orderedEigenvalue A k) =
      Fintype.card index - k.val := by
  rw [orderedEigenvalueThresholdCount,
    orderedEigenvalueThresholdIndices_at_orderedEigenvalue A hsimple k]
  simp

/-- Exact complementarity between decreasing normalized rank and the
normalized empirical scalar sublevel count. -/
theorem normalizedFinRank_eq_one_sub_normalizedThresholdCount
    (A : HermitianMatrix index) (hsimple : SimpleOrderedSpectrum A)
    (k : Fin (Fintype.card index)) :
    (k.val : Real) / (Fintype.card index : Real) =
      1 - (orderedEigenvalueThresholdCount A (orderedEigenvalue A k) : Real) /
        (Fintype.card index : Real) := by
  rw [orderedEigenvalueThresholdCount_at_orderedEigenvalue A hsimple k]
  have hk : k.val <= Fintype.card index := Nat.le_of_lt k.isLt
  rw [Nat.cast_sub hk]
  have hcardNat : 0 < Fintype.card index := Nat.zero_lt_of_lt k.isLt
  have hcard : (Fintype.card index : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hcardNat)
  field_simp
  ring

/-- Random-mass harmonic specialization at the ordered squared frequency. -/
theorem harmonicThresholdCount_at_orderedEigenvalue
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (k : OrderedModeIndex N) :
    orderedEigenvalueThresholdCount (harmonicHermitian m)
        (orderedEigenvalue (harmonicHermitian m) k) = N - k.val := by
  simpa [Lattice.Site, ZMod.card] using
    orderedEigenvalueThresholdCount_at_orderedEigenvalue
      (harmonicHermitian m) hsimple k

/-- The same exact harmonic count with the threshold expressed as the square
of the physical ordered mode frequency. -/
theorem harmonicThresholdCount_at_orderedFrequency_sq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (k : OrderedModeIndex N) :
    orderedEigenvalueThresholdCount (harmonicHermitian m)
        (orderedModeFrequency (harmonicHermitian m) k ^ 2) = N - k.val := by
  rw [orderedModeFrequency_sq_eq_orderedEigenvalue]
  exact harmonicThresholdCount_at_orderedEigenvalue m hsimple k

/-- The marked-measure rank coordinate is exactly one minus the empirical
scalar IDS at the corresponding squared mode frequency. -/
theorem normalizedOrderedRank_eq_one_sub_harmonicThresholdCount
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (k : OrderedModeIndex N) :
    normalizedOrderedRank k =
      1 - (orderedEigenvalueThresholdCount (harmonicHermitian m)
          (orderedModeFrequency (harmonicHermitian m) k ^ 2) : Real) /
        (N : Real) := by
  rw [orderedModeFrequency_sq_eq_orderedEigenvalue]
  simpa [normalizedOrderedRank, Lattice.Site, ZMod.card] using
    normalizedFinRank_eq_one_sub_normalizedThresholdCount
      (harmonicHermitian m) hsimple k

/-- Canonical iid realization form of the exact rank/empirical-IDS bridge. -/
theorem canonicalNormalizedHarmonicThresholdCount_at_orderedFrequency_sq
    {N : Nat} [NeZero N]
    (omega : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)))
    (k : OrderedModeIndex N) :
    normalizedOrderedRank k =
      1 - canonicalNormalizedHarmonicThresholdCount N
        (orderedModeFrequency
          (harmonicHermitian
            (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)) k ^ 2)
        omega := by
  rw [canonicalNormalizedHarmonicThresholdCount_eq]
  exact normalizedOrderedRank_eq_one_sub_harmonicThresholdCount
    (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)
    hsimple k

end
end ArchonPhysics.OrderedRankThresholdCountIdentity
