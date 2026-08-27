import ArchonPhysics.CleanCycleAcousticCountEnvelope
import ArchonPhysics.PositiveRankOneEigenvalueInterlacing

/-!
# Threshold-count sensitivity under one mass replacement

This module turns one-step interlacing of finite decreasing spectra into a
cardinality estimate for spectral sublevel sets.  If two length-`n` sequences
`a`, `b` satisfy

`a_k <= b_k` and `b_(k+1) <= a_k`,

then their threshold counts obey

`count_b(E) <= count_a(E) <= count_b(E) + 1`.

The result is then applied to a positive rank-one Hermitian update and to the
dual and physical periodic harmonic matrices when two positive mass profiles
agree away from one site.  The symmetric final statements do not prescribe
which of the two masses is larger.  Multiplicities and the zero mode are
retained, and no simple-spectrum or probabilistic hypothesis is used.
-/

namespace ArchonPhysics.SingleMassThresholdCountSensitivity

open ArchonPhysics
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.PositiveRankOneEigenvalueInterlacing
open ArchonPhysics.RandomMassAcousticCountingComparison
open ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison

noncomputable section

/-- Indices of a finite real sequence lying at or below a threshold. -/
def finiteSequenceThresholdIndices {n : Nat} (a : Fin n -> Real)
    (E : Real) : Finset (Fin n) :=
  Finset.univ.filter fun k => a k <= E

@[simp] theorem mem_finiteSequenceThresholdIndices_iff
    {n : Nat} (a : Fin n -> Real) (E : Real) (k : Fin n) :
    k ∈ finiteSequenceThresholdIndices a E ↔ a k <= E := by
  simp [finiteSequenceThresholdIndices]

/-- Cardinality, with multiplicity, of a finite sequence sublevel set. -/
def finiteSequenceThresholdCount {n : Nat} (a : Fin n -> Real)
    (E : Real) : Nat :=
  (finiteSequenceThresholdIndices a E).card

/-- Pointwise order reverses the order of sublevel counts. -/
theorem finiteSequenceThresholdCount_le_of_pointwise
    {n : Nat} {a b : Fin n -> Real} {E : Real}
    (hab : forall k, a k <= b k) :
    finiteSequenceThresholdCount b E <=
      finiteSequenceThresholdCount a E := by
  apply Finset.card_le_card
  intro k hk
  rw [mem_finiteSequenceThresholdIndices_iff] at hk ⊢
  exact (hab k).trans hk

/-- The shifted half of an interlacing relation loses at most the final
index when finite sublevel sets are compared. -/
theorem finiteSequenceThresholdCount_le_add_one_of_shifted_interlace
    {n : Nat} {a b : Fin n -> Real} {E : Real}
    (hshift : forall (k : Fin n) (hk : k.val + 1 < n),
      b ⟨k.val + 1, hk⟩ <= a k) :
    finiteSequenceThresholdCount a E <=
      finiteSequenceThresholdCount b E + 1 := by
  cases n with
  | zero =>
      simp [finiteSequenceThresholdCount, finiteSequenceThresholdIndices]
  | succ n =>
      let sCast : Finset (Fin n) :=
        Finset.univ.filter ((fun k : Fin (n + 1) => a k <= E) ∘ Fin.castSucc)
      let sSucc : Finset (Fin n) :=
        Finset.univ.filter fun k => b k.succ <= E
      have hsubset : sCast ⊆ sSucc := by
        intro k hk
        simp only [sCast, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] at hk
        simp only [sSucc, Finset.mem_filter, Finset.mem_univ, true_and]
        have hinterlace : b k.succ <= a k.castSucc := by
          have hk' : k.castSucc.val + 1 < n + 1 := by
            exact Nat.succ_lt_succ k.isLt
          have hindex :
              (⟨k.castSucc.val + 1, hk'⟩ : Fin (n + 1)) = k.succ := by
            exact Fin.ext (by rfl)
          rw [← hindex]
          exact hshift k.castSucc hk'
        exact hinterlace.trans hk
      have hcard : sCast.card <= sSucc.card :=
        Finset.card_le_card hsubset
      have haDecomp :
          finiteSequenceThresholdCount a E =
            sCast.card + (if a (Fin.last n) <= E then 1 else 0) := by
        unfold finiteSequenceThresholdCount finiteSequenceThresholdIndices
        rw [Fin.univ_castSuccEmb]
        by_cases hlast : a (Fin.last n) <= E
        · rw [Finset.filter_cons_of_pos
              (fun k : Fin (n + 1) => a k <= E) (Fin.last n)
              (Finset.univ.map Fin.castSuccEmb) (by simp) hlast,
            Finset.card_cons, Finset.filter_map, Finset.card_map]
          rw [if_pos hlast]
          rfl
        · rw [Finset.filter_cons_of_neg
              (fun k : Fin (n + 1) => a k <= E) (Fin.last n)
              (Finset.univ.map Fin.castSuccEmb) (by simp) hlast,
            Finset.filter_map, Finset.card_map]
          rw [if_neg hlast]
          change sCast.card = sCast.card + 0
          exact (Nat.add_zero _).symm
      have hbDecomp :
          finiteSequenceThresholdCount b E =
            (if b 0 <= E then 1 else 0) + sSucc.card := by
        simpa only [finiteSequenceThresholdCount,
          finiteSequenceThresholdIndices, sSucc] using
          (Fin.card_filter_univ_succ'
            (p := fun k : Fin (n + 1) => b k <= E))
      rw [haDecomp, hbDecomp]
      split_ifs <;> omega

/-- Generic interlacing-to-count principle for finite real sequences. -/
theorem finiteSequenceThresholdCount_sandwich_of_interlace
    {n : Nat} {a b : Fin n -> Real} {E : Real}
    (hpoint : forall k, a k <= b k)
    (hshift : forall (k : Fin n) (hk : k.val + 1 < n),
      b ⟨k.val + 1, hk⟩ <= a k) :
    finiteSequenceThresholdCount b E <=
        finiteSequenceThresholdCount a E ∧
      finiteSequenceThresholdCount a E <=
        finiteSequenceThresholdCount b E + 1 :=
  ⟨finiteSequenceThresholdCount_le_of_pointwise hpoint,
    finiteSequenceThresholdCount_le_add_one_of_shifted_interlace hshift⟩

/-- Hermitian ordered spectra satisfying one-step interlacing have threshold
counts differing by at most one in the oriented sense. -/
theorem orderedEigenvalueThresholdCount_sandwich_of_interlace
    {index : Type*} [Fintype index] [DecidableEq index]
    {A B : HermitianMatrix index} {E : Real}
    (hinterlace : forall k : Fin (Fintype.card index),
      orderedEigenvalue A k <= orderedEigenvalue B k ∧
        forall hk : k.val + 1 < Fintype.card index,
          orderedEigenvalue B ⟨k.val + 1, hk⟩ <=
            orderedEigenvalue A k) :
    orderedEigenvalueThresholdCount B E <=
        orderedEigenvalueThresholdCount A E ∧
      orderedEigenvalueThresholdCount A E <=
        orderedEigenvalueThresholdCount B E + 1 := by
  simpa only [orderedEigenvalueThresholdCount,
    orderedEigenvalueThresholdIndices, finiteSequenceThresholdCount,
    finiteSequenceThresholdIndices] using
    (finiteSequenceThresholdCount_sandwich_of_interlace
      (a := fun k => orderedEigenvalue A k)
      (b := fun k => orderedEigenvalue B k)
      (E := E) (fun k => (hinterlace k).1)
      (fun k hk => (hinterlace k).2 hk))

/-- Threshold-count form of positive rank-one Cauchy interlacing. -/
theorem orderedEigenvalueThresholdCount_positive_rankOne_update_sandwich
    {index : Type*} [Fintype index] [DecidableEq index]
    (A C : Matrix index index Real)
    (hA : A.IsHermitian) (hC : C.IsHermitian)
    (c : Real) (hc : 0 <= c) (v : index -> Real)
    (hupdate : C = A + c • Matrix.vecMulVec v v) (E : Real) :
    orderedEigenvalueThresholdCount ⟨C, hC⟩ E <=
        orderedEigenvalueThresholdCount ⟨A, hA⟩ E ∧
      orderedEigenvalueThresholdCount ⟨A, hA⟩ E <=
        orderedEigenvalueThresholdCount ⟨C, hC⟩ E + 1 := by
  apply orderedEigenvalueThresholdCount_sandwich_of_interlace
  intro k
  exact orderedEigenvalues_interlace_positive_rankOne_update
    A C hA hC c hc v hupdate k

/-- If one mass is increased, the dual harmonic threshold count can increase
by at most one and cannot decrease. -/
theorem dualMass_orderedEigenvalueThresholdCount_sandwich_of_single_mass_le
    {N : Nat} [NeZero N]
    (m m' : Lattice.PositiveMassConfig N) (i : Lattice.Site N)
    (hoff : forall j, j ≠ i -> m.mass j = m'.mass j)
    (hmass : m.mass i <= m'.mass i) (E : Real) :
    orderedEigenvalueThresholdCount
        (dualMassWeightedHarmonicHermitian m) E <=
      orderedEigenvalueThresholdCount
        (dualMassWeightedHarmonicHermitian m') E ∧
    orderedEigenvalueThresholdCount
        (dualMassWeightedHarmonicHermitian m') E <=
      orderedEigenvalueThresholdCount
        (dualMassWeightedHarmonicHermitian m) E + 1 := by
  apply orderedEigenvalueThresholdCount_sandwich_of_interlace
  intro k
  exact dualMass_orderedEigenvalues_interlace_of_single_mass_le
    m m' i hoff hmass k

/-- Physical-site version of the oriented single-mass threshold-count
interlacing statement. -/
theorem harmonic_orderedEigenvalueThresholdCount_sandwich_of_single_mass_le
    {N : Nat} [NeZero N]
    (m m' : Lattice.PositiveMassConfig N) (i : Lattice.Site N)
    (hoff : forall j, j ≠ i -> m.mass j = m'.mass j)
    (hmass : m.mass i <= m'.mass i) (E : Real) :
    orderedEigenvalueThresholdCount (harmonicHermitian m) E <=
        orderedEigenvalueThresholdCount (harmonicHermitian m') E ∧
      orderedEigenvalueThresholdCount (harmonicHermitian m') E <=
        orderedEigenvalueThresholdCount (harmonicHermitian m) E + 1 := by
  apply orderedEigenvalueThresholdCount_sandwich_of_interlace
  intro k
  exact harmonic_orderedEigenvalues_interlace_of_single_mass_le
    m m' i hoff hmass k

/-- Replacing one mass changes the dual harmonic threshold count by at most
one, expressed without integer subtraction as two natural-number bounds. -/
theorem dualMass_orderedEigenvalueThresholdCount_single_mass_sensitivity
    {N : Nat} [NeZero N]
    (m m' : Lattice.PositiveMassConfig N) (i : Lattice.Site N)
    (hoff : forall j, j ≠ i -> m.mass j = m'.mass j) (E : Real) :
    orderedEigenvalueThresholdCount
        (dualMassWeightedHarmonicHermitian m) E <=
        orderedEigenvalueThresholdCount
          (dualMassWeightedHarmonicHermitian m') E + 1 ∧
      orderedEigenvalueThresholdCount
          (dualMassWeightedHarmonicHermitian m') E <=
        orderedEigenvalueThresholdCount
          (dualMassWeightedHarmonicHermitian m) E + 1 := by
  by_cases hmass : m.mass i <= m'.mass i
  · obtain ⟨hmono, hone⟩ :=
      dualMass_orderedEigenvalueThresholdCount_sandwich_of_single_mass_le
        m m' i hoff hmass E
    exact ⟨hmono.trans (Nat.le_add_right _ _), hone⟩
  · have hmass' : m'.mass i <= m.mass i := le_of_not_ge hmass
    have hoff' : forall j, j ≠ i -> m'.mass j = m.mass j :=
      fun j hj => (hoff j hj).symm
    obtain ⟨hmono, hone⟩ :=
      dualMass_orderedEigenvalueThresholdCount_sandwich_of_single_mass_le
        m' m i hoff' hmass' E
    exact ⟨hone, hmono.trans (Nat.le_add_right _ _)⟩

/-- Replacing one mass changes the physical harmonic threshold count by at
most one.  This statement retains multiplicities and requires no simple
spectrum. -/
theorem harmonic_orderedEigenvalueThresholdCount_single_mass_sensitivity
    {N : Nat} [NeZero N]
    (m m' : Lattice.PositiveMassConfig N) (i : Lattice.Site N)
    (hoff : forall j, j ≠ i -> m.mass j = m'.mass j) (E : Real) :
    orderedEigenvalueThresholdCount (harmonicHermitian m) E <=
        orderedEigenvalueThresholdCount (harmonicHermitian m') E + 1 ∧
      orderedEigenvalueThresholdCount (harmonicHermitian m') E <=
        orderedEigenvalueThresholdCount (harmonicHermitian m) E + 1 := by
  by_cases hmass : m.mass i <= m'.mass i
  · obtain ⟨hmono, hone⟩ :=
      harmonic_orderedEigenvalueThresholdCount_sandwich_of_single_mass_le
        m m' i hoff hmass E
    exact ⟨hmono.trans (Nat.le_add_right _ _), hone⟩
  · have hmass' : m'.mass i <= m.mass i := le_of_not_ge hmass
    have hoff' : forall j, j ≠ i -> m'.mass j = m.mass j :=
      fun j hj => (hoff j hj).symm
    obtain ⟨hmono, hone⟩ :=
      harmonic_orderedEigenvalueThresholdCount_sandwich_of_single_mass_le
        m' m i hoff' hmass' E
    exact ⟨hone, hmono.trans (Nat.le_add_right _ _)⟩

end

end ArchonPhysics.SingleMassThresholdCountSensitivity
