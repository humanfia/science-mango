import ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison

/-!
# Finite-volume acoustic threshold counting for random masses

For a Hermitian matrix, `orderedEigenvalueThresholdIndices A E` is the set of
all indices in its complete decreasing ordered spectrum whose eigenvalue is at
most `E`.  Thus multiplicities are retained, and the zero mode is not removed
(in particular it is counted whenever it lies below the chosen threshold).

The uniform random-mass spectrum comparison gives finite-volume inclusions

`clean(mLower * E) ⊆ random(E) ⊆ clean(mUpper * E)`.

Taking cardinalities gives the corresponding counting inequalities.  On the
frozen iid support `[4/5, 6/5]`, the two clean thresholds are `(4/5) * E` and
`(6/5) * E`.  No explicit sine formula, density-of-states limit,
localization, or thermodynamic-limit assertion is made here.
-/

namespace ArchonPhysics.RandomMassAcousticCountingComparison

open ArchonPhysics
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison

noncomputable section

/-- Indices, with multiplicity, of the complete decreasing ordered spectrum
whose eigenvalue is at most `E`.  No index (including the zero mode) is
discarded by definition. -/
def orderedEigenvalueThresholdIndices
    {index : Type*} [Fintype index] [DecidableEq index]
    (A : HermitianMatrix index) (E : Real) :
    Finset (Fin (Fintype.card index)) :=
  Finset.univ.filter fun k ↦ orderedEigenvalue A k ≤ E

@[simp] theorem mem_orderedEigenvalueThresholdIndices_iff
    {index : Type*} [Fintype index] [DecidableEq index]
    (A : HermitianMatrix index) (E : Real)
    (k : Fin (Fintype.card index)) :
    k ∈ orderedEigenvalueThresholdIndices A E ↔
      orderedEigenvalue A k ≤ E := by
  simp [orderedEigenvalueThresholdIndices]

/-- Cardinality of the complete spectral sublevel set, retaining
multiplicities and the zero mode. -/
def orderedEigenvalueThresholdCount
    {index : Type*} [Fintype index] [DecidableEq index]
    (A : HermitianMatrix index) (E : Real) : Nat :=
  (orderedEigenvalueThresholdIndices A E).card

/-- A pointwise implication between ordered spectral sublevels induces the
corresponding finite-index-set inclusion. -/
theorem orderedEigenvalueThresholdIndices_subset_of_pointwise
    {index : Type*} [Fintype index] [DecidableEq index]
    {A B : HermitianMatrix index} {EA EB : Real}
    (h : ∀ k : Fin (Fintype.card index),
      orderedEigenvalue A k ≤ EA → orderedEigenvalue B k ≤ EB) :
    orderedEigenvalueThresholdIndices A EA ⊆
      orderedEigenvalueThresholdIndices B EB := by
  intro k hk
  rw [mem_orderedEigenvalueThresholdIndices_iff] at hk ⊢
  exact h k hk

/-- A pointwise implication between ordered spectral sublevels gives the
corresponding cardinal inequality. -/
theorem orderedEigenvalueThresholdCount_le_of_pointwise
    {index : Type*} [Fintype index] [DecidableEq index]
    {A B : HermitianMatrix index} {EA EB : Real}
    (h : ∀ k : Fin (Fintype.card index),
      orderedEigenvalue A k ≤ EA → orderedEigenvalue B k ≤ EB) :
    orderedEigenvalueThresholdCount A EA ≤
      orderedEigenvalueThresholdCount B EB := by
  exact Finset.card_le_card
    (orderedEigenvalueThresholdIndices_subset_of_pointwise h)

/-- Under a positive coordinatewise mass box, the clean sublevel set at
`mLower * E` lies in the random sublevel set at `E`, which in turn lies in the
clean sublevel set at `mUpper * E`. -/
theorem massBox_orderedEigenvalueThresholdIndices_sandwich
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (mLower mUpper : Real) (hmLower : 0 < mLower)
    (hmUpper : 0 < mUpper)
    (hmassLower : ∀ i, mLower ≤ m.mass i)
    (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (E : Real) :
    orderedEigenvalueThresholdIndices
        (cleanCycleHarmonicHermitian N) (mLower * E) ⊆
      orderedEigenvalueThresholdIndices (harmonicHermitian m) E ∧
    orderedEigenvalueThresholdIndices (harmonicHermitian m) E ⊆
      orderedEigenvalueThresholdIndices
        (cleanCycleHarmonicHermitian N) (mUpper * E) := by
  constructor
  · apply orderedEigenvalueThresholdIndices_subset_of_pointwise
    intro k hk
    have hcompare := orderedEigenvalue_harmonic_compare_clean
      m mLower mUpper hmLower hmUpper hmassLower hmassUpper k
    calc
      orderedEigenvalue (harmonicHermitian m) k ≤
          mLower⁻¹ * orderedEigenvalue
            (cleanCycleHarmonicHermitian N) k := hcompare.2
      _ ≤ mLower⁻¹ * (mLower * E) :=
        mul_le_mul_of_nonneg_left hk (inv_nonneg.mpr hmLower.le)
      _ = E := by field_simp [ne_of_gt hmLower]
  · apply orderedEigenvalueThresholdIndices_subset_of_pointwise
    intro k hk
    have hcompare := orderedEigenvalue_harmonic_compare_clean
      m mLower mUpper hmLower hmUpper hmassLower hmassUpper k
    have hscaled : mUpper⁻¹ * orderedEigenvalue
        (cleanCycleHarmonicHermitian N) k ≤ E :=
      hcompare.1.trans hk
    calc
      orderedEigenvalue (cleanCycleHarmonicHermitian N) k =
          mUpper * (mUpper⁻¹ * orderedEigenvalue
            (cleanCycleHarmonicHermitian N) k) := by
              field_simp [ne_of_gt hmUpper]
      _ ≤ mUpper * E := mul_le_mul_of_nonneg_left hscaled hmUpper.le

/-- Cardinal form of the mass-box spectral sublevel sandwich. -/
theorem massBox_orderedEigenvalueThresholdCount_sandwich
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (mLower mUpper : Real) (hmLower : 0 < mLower)
    (hmUpper : 0 < mUpper)
    (hmassLower : ∀ i, mLower ≤ m.mass i)
    (hmassUpper : ∀ i, m.mass i ≤ mUpper)
    (E : Real) :
    orderedEigenvalueThresholdCount
        (cleanCycleHarmonicHermitian N) (mLower * E) ≤
      orderedEigenvalueThresholdCount (harmonicHermitian m) E ∧
    orderedEigenvalueThresholdCount (harmonicHermitian m) E ≤
      orderedEigenvalueThresholdCount
        (cleanCycleHarmonicHermitian N) (mUpper * E) := by
  obtain ⟨hleft, hright⟩ :=
    massBox_orderedEigenvalueThresholdIndices_sandwich
      m mLower mUpper hmLower hmUpper hmassLower hmassUpper E
  exact ⟨Finset.card_le_card hleft, Finset.card_le_card hright⟩

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Frozen-support specialization of the finite index-set inclusions. -/
theorem iid_orderedEigenvalueThresholdIndices_sandwich
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega) (E : Real) :
    orderedEigenvalueThresholdIndices
        (cleanCycleHarmonicHermitian N) ((4 / 5 : Real) * E) ⊆
      orderedEigenvalueThresholdIndices
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := N) omega)) E ∧
    orderedEigenvalueThresholdIndices
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := N) omega)) E ⊆
      orderedEigenvalueThresholdIndices
        (cleanCycleHarmonicHermitian N) ((6 / 5 : Real) * E) := by
  simpa [RandomEnsemble.massLower, RandomEnsemble.massUpper] using
    massBox_orderedEigenvalueThresholdIndices_sandwich
      (ensemble.restrictPositiveMass (N := N) omega)
      RandomEnsemble.massLower RandomEnsemble.massUpper
      RandomEnsemble.massLower_pos
      (RandomEnsemble.massLower_pos.trans_le
        RandomEnsemble.massLower_le_massUpper)
      (fun i ↦ by simpa using (ensemble.mass_mem_support i.val omega).1)
      (fun i ↦ by simpa using (ensemble.mass_mem_support i.val omega).2) E

/-- Frozen-support specialization of the finite counting inequalities:
`count_clean((4/5)E) ≤ count_random(E) ≤ count_clean((6/5)E)`. -/
theorem iid_orderedEigenvalueThresholdCount_sandwich
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega) (E : Real) :
    orderedEigenvalueThresholdCount
        (cleanCycleHarmonicHermitian N) ((4 / 5 : Real) * E) ≤
      orderedEigenvalueThresholdCount
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := N) omega)) E ∧
    orderedEigenvalueThresholdCount
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := N) omega)) E ≤
      orderedEigenvalueThresholdCount
        (cleanCycleHarmonicHermitian N) ((6 / 5 : Real) * E) := by
  simpa [RandomEnsemble.massLower, RandomEnsemble.massUpper] using
    massBox_orderedEigenvalueThresholdCount_sandwich
      (ensemble.restrictPositiveMass (N := N) omega)
      RandomEnsemble.massLower RandomEnsemble.massUpper
      RandomEnsemble.massLower_pos
      (RandomEnsemble.massLower_pos.trans_le
        RandomEnsemble.massLower_le_massUpper)
      (fun i ↦ by simpa using (ensemble.mass_mem_support i.val omega).1)
      (fun i ↦ by simpa using (ensemble.mass_mem_support i.val omega).2) E

end

end ArchonPhysics.RandomMassAcousticCountingComparison
