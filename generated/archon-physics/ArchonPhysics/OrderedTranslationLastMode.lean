import ArchonPhysics.TranslationZeroModeEnergy

/-!
# The translation zero mode is the last ordered harmonic mode

Mathlib enumerates Hermitian eigenvalues in decreasing order.  A positive
semidefinite harmonic matrix has nonnegative eigenvalues and the periodic
chain always has a translation eigenvalue equal to zero.  Hence its last
ordered eigenvalue is deterministically zero, without choosing a random zero
index.  Under simple spectrum, the first `N - 1` ordered indices are exactly
the strictly positive modes.

This removes an unnecessary sample-dependent indexing choice from the later
random initial-data construction.
-/

namespace ArchonPhysics.OrderedTranslationLastMode

open ArchonPhysics
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.TranslationZeroModeEnergy

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The maximal index in the decreasing ordered spectrum. -/
def lastOrderedIndex : Fin (Fintype.card ι) :=
  ⟨Fintype.card ι - 1, by
    have hcard : 0 < Fintype.card ι := Fintype.card_pos
    omega⟩

omit [DecidableEq ι] in
/-- Every ordered index precedes the last one. -/
theorem le_lastOrderedIndex (k : Fin (Fintype.card ι)) :
    k ≤ lastOrderedIndex (ι := ι) := by
  apply Fin.le_iff_val_le_val.mpr
  change k.val ≤ Fintype.card ι - 1
  omega

/-- The last decreasing eigenvalue is below every ordered eigenvalue. -/
theorem orderedEigenvalue_last_le
    (A : HermitianMatrix ι) (k : Fin (Fintype.card ι)) :
    orderedEigenvalue A (lastOrderedIndex (ι := ι)) ≤
      orderedEigenvalue A k := by
  exact A.2.eigenvalues₀_antitone (le_lastOrderedIndex k)

/-- For a nonnegative ordered spectrum containing zero, the last entry is
exactly zero. -/
theorem orderedEigenvalue_last_eq_zero_of_nonneg_of_exists_zero
    (A : HermitianMatrix ι)
    (hnonneg : ∀ k, 0 ≤ orderedEigenvalue A k)
    (hzero : ∃ k, orderedEigenvalue A k = 0) :
    orderedEigenvalue A (lastOrderedIndex (ι := ι)) = 0 := by
  obtain ⟨z, hz⟩ := hzero
  apply le_antisymm
  · exact (orderedEigenvalue_last_le A z).trans_eq hz
  · exact hnonneg _

/-- The fixed last index of every positive-mass periodic chain is a
translation zero mode. -/
theorem harmonic_lastOrderedEigenvalue_eq_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    orderedEigenvalue (harmonicHermitian m)
      (lastOrderedIndex (ι := Lattice.Site N)) = 0 := by
  apply orderedEigenvalue_last_eq_zero_of_nonneg_of_exists_zero
  · intro k
    let sample : Unit → Lattice.PositiveMassConfig N := fun _ ↦ m
    simpa [harmonicOrderedEigenvalue, harmonicHermitianSample,
      harmonicHermitian, sample] using
      (harmonicOrderedEigenvalue_nonneg sample () k)
  · let sample : Unit → Lattice.PositiveMassConfig N := fun _ ↦ m
    obtain ⟨k, hk⟩ := exists_harmonicOrderedEigenvalue_eq_zero sample ()
    exact ⟨k, by
      simpa [harmonicOrderedEigenvalue, harmonicHermitianSample,
        harmonicHermitian, sample] using hk⟩

/-- On a simple harmonic spectrum, the positive ordered sector is the full
index set with the fixed last index erased. -/
theorem positiveModeIndices_eq_univ_erase_last
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m)) :
    positiveModeIndices (harmonicHermitian m) =
      Finset.univ.erase (lastOrderedIndex (ι := Lattice.Site N)) := by
  exact positiveModeIndices_eq_univ_erase_zeroMode m hsimple _
    (harmonic_lastOrderedEigenvalue_eq_zero m)

/-- Under simple spectrum, an ordered harmonic frequency is positive exactly
when its index is not the deterministic last index. -/
theorem orderedModeFrequency_pos_iff_ne_last
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (k : Fin (Fintype.card (Lattice.Site N))) :
    0 < orderedModeFrequency (harmonicHermitian m) k ↔
      k ≠ lastOrderedIndex (ι := Lattice.Site N) := by
  rw [← mem_positiveModeIndices_iff,
    positiveModeIndices_eq_univ_erase_last m hsimple]
  simp

end

end ArchonPhysics.OrderedTranslationLastMode
