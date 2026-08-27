import ArchonPhysics.SingleMassThresholdCountSensitivity

/-!
# Threshold-count sensitivity under finitely many mass replacements

This module iterates the deterministic one-site threshold-count estimate along
a finite hybrid chain.  If two positive mass configurations can differ only
on a finite set `S`, then both the dual and physical harmonic sublevel counts
differ by at most `S.card`.  A normalized real-valued corollary divides this
bound by the nonzero system size.  No probabilistic concentration input is
used.
-/

namespace ArchonPhysics.MultiMassThresholdCountSensitivity

open ArchonPhysics
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.RandomMassAcousticCountingComparison
open ArchonPhysics.SingleMassThresholdCountSensitivity
open ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison

noncomputable section

/-- Hybrid configuration which takes masses from `m'` on `S` and from `m`
off `S`. -/
def massHybrid {N : Nat} (m m' : Lattice.PositiveMassConfig N)
    (S : Finset (Lattice.Site N)) : Lattice.PositiveMassConfig N where
  mass i := if i ∈ S then m'.mass i else m.mass i
  mass_pos i := by
    by_cases hi : i ∈ S
    · simpa [hi] using m'.mass_pos i
    · simpa [hi] using m.mass_pos i

@[simp] theorem massHybrid_empty
    {N : Nat} (m m' : Lattice.PositiveMassConfig N) :
    massHybrid m m' ∅ = m := by
  cases m with
  | mk mass mass_pos =>
      rw [Lattice.PositiveMassConfig.mk.injEq]
      funext i
      simp [massHybrid]

/-- Adding `i` to the replaced set changes the hybrid at no site other than
`i`. -/
theorem massHybrid_insert_eq_off
    {N : Nat} (m m' : Lattice.PositiveMassConfig N)
    (S : Finset (Lattice.Site N)) (i : Lattice.Site N) :
    ∀ j, j ≠ i →
      (massHybrid m m' S).mass j =
        (massHybrid m m' (insert i S)).mass j := by
  intro j hj
  simp [massHybrid, hj]

/-- Once all possible disagreement sites have been replaced, the hybrid is
the right-hand configuration. -/
theorem massHybrid_eq_right_of_eq_off
    {N : Nat} (m m' : Lattice.PositiveMassConfig N)
    (S : Finset (Lattice.Site N))
    (hoff : ∀ i, i ∉ S → m.mass i = m'.mass i) :
    massHybrid m m' S = m' := by
  cases m' with
  | mk mass' mass_pos' =>
      rw [Lattice.PositiveMassConfig.mk.injEq]
      funext i
      by_cases hi : i ∈ S
      · simp [massHybrid, hi]
      · simpa [massHybrid, hi] using hoff i hi

/-- Abstract hybrid-chain principle: a natural-valued observable which
changes by at most one under a one-site replacement changes by at most the
cardinality of the replacement set. -/
theorem count_massHybrid_sensitivity
    {N : Nat}
    (count : Lattice.PositiveMassConfig N → Nat)
    (hsingle : ∀ (a b : Lattice.PositiveMassConfig N)
      (i : Lattice.Site N),
      (∀ j, j ≠ i → a.mass j = b.mass j) →
      count a ≤ count b + 1 ∧ count b ≤ count a + 1)
    (m m' : Lattice.PositiveMassConfig N)
    (S : Finset (Lattice.Site N)) :
    count m ≤ count (massHybrid m m' S) + S.card ∧
      count (massHybrid m m' S) ≤ count m + S.card := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp
  | @insert i S hi ih =>
      have hstep := hsingle (massHybrid m m' S)
        (massHybrid m m' (insert i S)) i
        (massHybrid_insert_eq_off m m' S i)
      obtain ⟨ihForward, ihReverse⟩ := ih
      obtain ⟨hstepForward, hstepReverse⟩ := hstep
      rw [Finset.card_insert_of_notMem hi]
      constructor <;> omega

/-- Finite-support version of the abstract hybrid-chain principle. -/
theorem count_finset_sensitivity_of_single_mass
    {N : Nat}
    (count : Lattice.PositiveMassConfig N → Nat)
    (hsingle : ∀ (a b : Lattice.PositiveMassConfig N)
      (i : Lattice.Site N),
      (∀ j, j ≠ i → a.mass j = b.mass j) →
      count a ≤ count b + 1 ∧ count b ≤ count a + 1)
    (m m' : Lattice.PositiveMassConfig N)
    (S : Finset (Lattice.Site N))
    (hoff : ∀ i, i ∉ S → m.mass i = m'.mass i) :
    count m ≤ count m' + S.card ∧
      count m' ≤ count m + S.card := by
  have hhybrid := count_massHybrid_sensitivity count hsingle m m' S
  rw [massHybrid_eq_right_of_eq_off m m' S hoff] at hhybrid
  exact hhybrid

/-- Multi-site Hamming--Lipschitz bound for the dual harmonic threshold
count. -/
theorem dualMass_orderedEigenvalueThresholdCount_finset_sensitivity
    {N : Nat} [NeZero N]
    (m m' : Lattice.PositiveMassConfig N)
    (S : Finset (Lattice.Site N))
    (hoff : ∀ i, i ∉ S → m.mass i = m'.mass i) (E : Real) :
    orderedEigenvalueThresholdCount
        (dualMassWeightedHarmonicHermitian m) E ≤
      orderedEigenvalueThresholdCount
        (dualMassWeightedHarmonicHermitian m') E + S.card ∧
    orderedEigenvalueThresholdCount
        (dualMassWeightedHarmonicHermitian m') E ≤
      orderedEigenvalueThresholdCount
        (dualMassWeightedHarmonicHermitian m) E + S.card := by
  apply count_finset_sensitivity_of_single_mass
    (count := fun a => orderedEigenvalueThresholdCount
      (dualMassWeightedHarmonicHermitian a) E)
    (m := m) (m' := m') (S := S)
  · intro a b i hab
    exact dualMass_orderedEigenvalueThresholdCount_single_mass_sensitivity
      a b i hab E
  · exact hoff

/-- Multi-site Hamming--Lipschitz bound for the physical harmonic threshold
count. -/
theorem harmonic_orderedEigenvalueThresholdCount_finset_sensitivity
    {N : Nat} [NeZero N]
    (m m' : Lattice.PositiveMassConfig N)
    (S : Finset (Lattice.Site N))
    (hoff : ∀ i, i ∉ S → m.mass i = m'.mass i) (E : Real) :
    orderedEigenvalueThresholdCount (harmonicHermitian m) E ≤
        orderedEigenvalueThresholdCount (harmonicHermitian m') E + S.card ∧
      orderedEigenvalueThresholdCount (harmonicHermitian m') E ≤
        orderedEigenvalueThresholdCount (harmonicHermitian m) E + S.card := by
  apply count_finset_sensitivity_of_single_mass
    (count := fun a =>
      orderedEigenvalueThresholdCount (harmonicHermitian a) E)
    (m := m) (m' := m') (S := S)
  · intro a b i hab
    exact harmonic_orderedEigenvalueThresholdCount_single_mass_sensitivity
      a b i hab E
  · exact hoff

/-- Paired natural-number estimates imply the corresponding normalized
absolute-value estimate over a nonzero system size. -/
theorem normalizedNat_abs_sub_le
    {N a b r : Nat} [NeZero N]
    (hab : a ≤ b + r) (hba : b ≤ a + r) :
    |(a : Real) / (N : Real) - (b : Real) / (N : Real)| ≤
      (r : Real) / (N : Real) := by
  have hab' : (a : Real) ≤ (b : Real) + (r : Real) := by
    exact_mod_cast hab
  have hba' : (b : Real) ≤ (a : Real) + (r : Real) := by
    exact_mod_cast hba
  have habs : |(a : Real) - (b : Real)| ≤ (r : Real) := by
    rw [abs_le]
    constructor <;> linarith
  have hN : 0 < (N : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [← sub_div, abs_div, abs_of_pos hN]
  exact (div_le_div_iff_of_pos_right hN).2 habs

/-- Normalized dual threshold counts differ by at most `S.card / N`. -/
theorem dualMass_normalizedThresholdCount_finset_sensitivity
    {N : Nat} [NeZero N]
    (m m' : Lattice.PositiveMassConfig N)
    (S : Finset (Lattice.Site N))
    (hoff : ∀ i, i ∉ S → m.mass i = m'.mass i) (E : Real) :
    |(orderedEigenvalueThresholdCount
          (dualMassWeightedHarmonicHermitian m) E : Real) / (N : Real) -
        (orderedEigenvalueThresholdCount
          (dualMassWeightedHarmonicHermitian m') E : Real) / (N : Real)| ≤
      (S.card : Real) / (N : Real) := by
  obtain ⟨hForward, hReverse⟩ :=
    dualMass_orderedEigenvalueThresholdCount_finset_sensitivity
      m m' S hoff E
  exact normalizedNat_abs_sub_le hForward hReverse

/-- Normalized physical threshold counts differ by at most `S.card / N`. -/
theorem harmonic_normalizedThresholdCount_finset_sensitivity
    {N : Nat} [NeZero N]
    (m m' : Lattice.PositiveMassConfig N)
    (S : Finset (Lattice.Site N))
    (hoff : ∀ i, i ∉ S → m.mass i = m'.mass i) (E : Real) :
    |(orderedEigenvalueThresholdCount (harmonicHermitian m) E : Real) /
          (N : Real) -
        (orderedEigenvalueThresholdCount (harmonicHermitian m') E : Real) /
          (N : Real)| ≤
      (S.card : Real) / (N : Real) := by
  obtain ⟨hForward, hReverse⟩ :=
    harmonic_orderedEigenvalueThresholdCount_finset_sensitivity
      m m' S hoff E
  exact normalizedNat_abs_sub_le hForward hReverse

end

end ArchonPhysics.MultiMassThresholdCountSensitivity
