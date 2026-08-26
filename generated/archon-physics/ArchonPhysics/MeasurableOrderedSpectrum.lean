import ArchonPhysics.MeasurableHarmonicData
import ArchonPhysics.ReducedHarmonicSpectrum

/-!
# Measurable ordered harmonic spectrum interface

Mathlib provides the decreasing enumeration
`Matrix.IsHermitian.eigenvalues₀`, but the current dependency does not provide
a theorem saying that this enumeration is continuous or measurable as the
matrix varies.  This module therefore isolates the exact missing Weyl
perturbation bridge as `OrderedSpectrumContinuous`.  From that quantitative
topological input it proves measurability of every ordered eigenvalue and its
nonnegative square-root frequency.

No measurable eigenbasis is selected.  Positive modes are represented by a
finite set of indices with strictly positive square-root frequency.  For the
periodic random-mass chain this cleanly excludes every zero eigenvalue,
including the translation mode, without identifying a random eigenvector.
-/

namespace ArchonPhysics.MeasurableOrderedSpectrum

open ArchonPhysics
open HarmonicModes
open MeasurableHarmonicData

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Finite real Hermitian matrices, with the induced Borel/measurable
structure from their entries. -/
abbrev HermitianMatrix (ι : Type*) [Fintype ι] :=
  {A : ι → ι → Real // Matrix.IsHermitian A}

/-- The decreasingly ordered eigenvalue supplied by Mathlib. -/
def orderedEigenvalue (A : HermitianMatrix ι)
    (k : Fin (Fintype.card ι)) : Real :=
  A.property.eigenvalues₀ k

/-- The full finite ordered eigenvalue vector. -/
def orderedEigenvalues (A : HermitianMatrix ι) :
    Fin (Fintype.card ι) → Real :=
  orderedEigenvalue A

/-- Nonnegative square-root frequency attached to one ordered eigenvalue.
For positive-semidefinite samples this is the physical harmonic frequency. -/
def orderedModeFrequency (A : HermitianMatrix ι)
    (k : Fin (Fintype.card ι)) : Real :=
  Real.sqrt (orderedEigenvalue A k)

/-- The finite realization-dependent set of strictly positive modes. -/
def positiveModeIndices (A : HermitianMatrix ι) :
    Finset (Fin (Fintype.card ι)) :=
  Finset.univ.filter fun k ↦ 0 < orderedModeFrequency A k

@[simp] theorem mem_positiveModeIndices_iff (A : HermitianMatrix ι)
    (k : Fin (Fintype.card ι)) :
    k ∈ positiveModeIndices A ↔ 0 < orderedModeFrequency A k := by
  simp [positiveModeIndices]

/-- The precise missing generic perturbation input: every coordinate of the
ordered Hermitian spectrum is continuous in the ambient finite matrix
topology.  A future Weyl/min-max theorem can inhabit this proposition without
changing downstream probability code. -/
def OrderedSpectrumContinuous (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ k : Fin (Fintype.card ι),
    Continuous fun A : HermitianMatrix ι ↦ orderedEigenvalue A k

omit [Fintype ι] [DecidableEq ι] in
/-- Entrywise measurability gives measurability into the Hermitian subtype. -/
theorem measurable_hermitianSample_of_entries
    (A : Omega → Matrix ι ι Real)
    (hA : ∀ omega, (A omega).IsHermitian)
    (hentry : ∀ i j, Measurable fun omega ↦ A omega i j) :
    Measurable fun omega ↦ (⟨A omega, hA omega⟩ : HermitianMatrix ι) := by
  apply Measurable.subtype_mk
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact hentry i j

/-- A measurable Hermitian sample has measurable ordered eigenvalues once the
generic continuous-spectrum bridge is available. -/
theorem measurable_orderedEigenvalues
    (hcontinuous : OrderedSpectrumContinuous ι)
    (sample : Omega → HermitianMatrix ι)
    (hsample : Measurable sample) :
    Measurable fun omega ↦ orderedEigenvalues (sample omega) := by
  apply measurable_pi_lambda
  intro k
  exact (hcontinuous k).measurable.comp hsample

/-- Ordered square-root frequency data is measurable under the same bridge. -/
theorem measurable_orderedModeFrequencies
    (hcontinuous : OrderedSpectrumContinuous ι)
    (sample : Omega → HermitianMatrix ι)
    (hsample : Measurable sample) :
    Measurable fun omega k ↦ orderedModeFrequency (sample omega) k := by
  apply measurable_pi_lambda
  intro k
  exact ((hcontinuous k).measurable.comp hsample).sqrt

/-- Membership of a fixed index in the positive-mode set is a measurable
event; this is the event-level interface needed by filtered empirical sums. -/
theorem measurableSet_mem_positiveModeIndices
    (hcontinuous : OrderedSpectrumContinuous ι)
    (sample : Omega → HermitianMatrix ι)
    (hsample : Measurable sample)
    (k : Fin (Fintype.card ι)) :
    MeasurableSet {omega | k ∈ positiveModeIndices (sample omega)} := by
  have hfrequency :
      Measurable fun omega ↦ orderedModeFrequency (sample omega) k :=
    (hcontinuous k).measurable.comp hsample |>.sqrt
  have hevent :
      {omega | k ∈ positiveModeIndices (sample omega)} =
        (fun omega ↦ orderedModeFrequency (sample omega) k) ⁻¹' Set.Ioi 0 := by
    ext omega
    simp [positiveModeIndices]
  rw [hevent]
  exact measurableSet_Ioi.preimage hfrequency

/-- Hermitian-subtype realization of the mass-weighted harmonic matrix. -/
def harmonicHermitianSample {N : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (omega : Omega) : HermitianMatrix (Lattice.Site N) :=
  ⟨massWeightedHarmonicMatrix (massSample omega),
    (massWeightedHarmonicMatrix_posSemidef (massSample omega)).isHermitian⟩

/-- Measurability of the harmonic Hermitian sample follows from the already
verified entry formulas. -/
theorem measurable_harmonicHermitianSample {N : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (hmass : ∀ i, Measurable fun omega ↦ (massSample omega).mass i) :
    Measurable (harmonicHermitianSample massSample) := by
  apply Measurable.subtype_mk
  exact measurable_massWeightedHarmonicMatrix_of_coordinate massSample hmass

/-- Ordered squared harmonic frequency for a positive-mass realization. -/
def harmonicOrderedEigenvalue {N : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (omega : Omega) (k : Fin (Fintype.card (Lattice.Site N))) : Real :=
  orderedEigenvalue (harmonicHermitianSample massSample omega) k

/-- Ordered harmonic frequency for a positive-mass realization. -/
def harmonicOrderedModeFrequency {N : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (omega : Omega) (k : Fin (Fintype.card (Lattice.Site N))) : Real :=
  orderedModeFrequency (harmonicHermitianSample massSample omega) k

/-- Conditional measurable ordered spectrum for the concrete harmonic sample.
The sole remaining input is the generic matrix-continuity bridge, not a
model-specific probability assumption. -/
theorem measurable_harmonicOrderedEigenvalues {N : Nat} [NeZero N]
    (hcontinuous : OrderedSpectrumContinuous (Lattice.Site N))
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (hmass : ∀ i, Measurable fun omega ↦ (massSample omega).mass i) :
    Measurable fun omega k ↦ harmonicOrderedEigenvalue massSample omega k := by
  simpa [harmonicOrderedEigenvalue, orderedEigenvalues] using
    measurable_orderedEigenvalues hcontinuous
      (harmonicHermitianSample massSample)
      (measurable_harmonicHermitianSample massSample hmass)

/-- Conditional measurable ordered frequency vector for the harmonic sample. -/
theorem measurable_harmonicOrderedModeFrequencies {N : Nat} [NeZero N]
    (hcontinuous : OrderedSpectrumContinuous (Lattice.Site N))
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (hmass : ∀ i, Measurable fun omega ↦ (massSample omega).mass i) :
    Measurable fun omega k ↦ harmonicOrderedModeFrequency massSample omega k := by
  simpa [harmonicOrderedModeFrequency] using
    measurable_orderedModeFrequencies hcontinuous
      (harmonicHermitianSample massSample)
      (measurable_harmonicHermitianSample massSample hmass)

omit [MeasurableSpace Omega] in
/-- Every ordered eigenvalue of the harmonic Gram matrix is nonnegative. -/
theorem harmonicOrderedEigenvalue_nonneg {N : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (omega : Omega) (k : Fin (Fintype.card (Lattice.Site N))) :
    0 ≤ harmonicOrderedEigenvalue massSample omega k := by
  let hpos := massWeightedHarmonicMatrix_posSemidef (massSample omega)
  let e : Fin (Fintype.card (Lattice.Site N)) ≃ Lattice.Site N :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  have hk := hpos.eigenvalues_nonneg (e k)
  simpa [harmonicOrderedEigenvalue, orderedEigenvalue,
    harmonicHermitianSample, Matrix.IsHermitian.eigenvalues, e] using hk

omit [MeasurableSpace Omega] in
/-- The deterministic translation kernel forces at least one ordered harmonic
eigenvalue to vanish.  This proves that the positive-mode filter genuinely
removes a spectral zero mode without choosing an eigenvector measurably. -/
theorem exists_harmonicOrderedEigenvalue_eq_zero {N : Nat} [NeZero N]
    (massSample : Omega → Lattice.PositiveMassConfig N)
    (omega : Omega) :
    ∃ k : Fin (Fintype.card (Lattice.Site N)),
      harmonicOrderedEigenvalue massSample omega k = 0 := by
  let m := massSample omega
  let A := massWeightedHarmonicMatrix m
  let hA : A.IsHermitian :=
    (massWeightedHarmonicMatrix_posSemidef m).isHermitian
  have hdet : Matrix.det A = 0 := by
    by_contra hdet
    exact translationMode_ne_zero m
      (Matrix.eq_zero_of_mulVec_eq_zero hdet (translationMode_is_zero m))
  have hprod : ∏ i, hA.eigenvalues i = 0 := by
    have hprod' : (∏ i, (hA.eigenvalues i : Real)) = 0 :=
      hA.det_eq_prod_eigenvalues.symm.trans hdet
    simpa using hprod'
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hprod
  let e : Fin (Fintype.card (Lattice.Site N)) ≃ Lattice.Site N :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  refine ⟨e.symm i, ?_⟩
  simpa [harmonicOrderedEigenvalue, orderedEigenvalue,
    harmonicHermitianSample, Matrix.IsHermitian.eigenvalues, m, A, hA, e] using hi

/-- A positive-mode index has a strictly positive squared eigenvalue, hence
cannot represent any zero mode. -/
theorem orderedEigenvalue_pos_of_mem_positiveModeIndices
    (A : HermitianMatrix ι) (k : Fin (Fintype.card ι))
    (hk : k ∈ positiveModeIndices A) :
    0 < orderedEigenvalue A k := by
  exact Real.sqrt_pos.mp ((mem_positiveModeIndices_iff A k).mp hk)

end

end ArchonPhysics.MeasurableOrderedSpectrum
