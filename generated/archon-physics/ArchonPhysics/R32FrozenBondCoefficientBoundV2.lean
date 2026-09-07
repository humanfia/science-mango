import ArchonPhysics.R32BondRowPseudoinverse
import ArchonPhysics.R32FrozenEnergyDilution
import ArchonPhysics.HarmonicNormalizedEdgeFrame
import ArchonPhysics.OrderedSingleModeProjector

/-!
# R32 frozen free-bond coefficient bounds, corrected interface

For a fixed physical bond, the frozen free harmonic coefficient of ordered
mode `k` is

`sqrt (2 E_k) * u_k(j)`,

where `E_k` is the frozen quarter-contrast energy and `u_k` is the normalized
harmonic edge frame.  The positive-row pseudoinverse estimate and the
pointwise dilution `E_k <= 3 / (N - 1)` imply

`sum_k coefficient_k^2 <= 6 / (N - 1)`.

Finite Cauchy--Schwarz gives the corresponding coefficient `l1` bound.  The
elementary Lipschitz estimate for cosine then gives a deterministic time
Lipschitz bound, uniform in the phase and physical bond.  No probability or
concentration hypothesis appears in this module.
-/

open scoped BigOperators Matrix

namespace ArchonPhysics.R32FrozenBondCoefficientBoundV2

open ArchonPhysics
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.R32BondRowPseudoinverse
open ArchonPhysics.R32FrozenEnergyDilution

noncomputable section

/-- The coefficient of ordered mode `k` in a frozen freely evolving physical
bond. -/
def r32FrozenBondCoefficient {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (bond : Lattice.Site N)
    (k : HarmonicOrderedModeIndex N) : Real :=
  Real.sqrt (2 * frozenTwoBandEnergy N k) *
    harmonicNormalizedEdgeFrame m k bond

/-- The translation mode has exactly zero frozen bond coefficient. -/
@[simp] theorem r32FrozenBondCoefficient_last
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (bond : Lattice.Site N) :
    r32FrozenBondCoefficient m bond
      (lastOrderedIndex (ι := Lattice.Site N)) = 0 := by
  simp [r32FrozenBondCoefficient, frozenTwoBandEnergy]

/-- Squaring the physical coefficient recovers twice the modal energy times
the squared normalized edge-frame coordinate. -/
theorem r32FrozenBondCoefficient_sq
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (m : Lattice.PositiveMassConfig N) (bond : Lattice.Site N)
    (k : HarmonicOrderedModeIndex N) :
    r32FrozenBondCoefficient m bond k ^ 2 =
      (2 * frozenTwoBandEnergy N k) *
        harmonicNormalizedEdgeFrame m k bond ^ 2 := by
  unfold r32FrozenBondCoefficient
  rw [mul_pow, Real.sq_sqrt]
  exact mul_nonneg (by norm_num) (frozenTwoBandEnergy_nonneg hN k)

/-- The positive part of every normalized edge-frame row has squared mass at
most one.  This is the literal row-pseudoinverse estimate rewritten through
the edge-frame definition. -/
theorem sum_positive_harmonicNormalizedEdgeFrame_sq_le_one
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hsimple : OrderedSingleModeProjector.SimpleOrderedSpectrum
      (harmonicHermitian m))
    (bond : Lattice.Site N) :
    (∑ k ∈ positiveModeIndices (harmonicHermitian m),
      harmonicNormalizedEdgeFrame m k bond ^ 2) ≤ 1 := by
  calc
    (∑ k ∈ positiveModeIndices (harmonicHermitian m),
        harmonicNormalizedEdgeFrame m k bond ^ 2) =
        ∑ k ∈ positiveModeIndices (harmonicHermitian m),
          orderedRawEdgeMode m k bond ^ 2 /
            orderedModeFrequency (harmonicHermitian m) k ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkFrequency :
          0 < orderedModeFrequency (harmonicHermitian m) k :=
        (mem_positiveModeIndices_iff (harmonicHermitian m) k).mp hk
      have hkLast : k ≠ lastOrderedIndex (ι := Lattice.Site N) :=
        (orderedModeFrequency_pos_iff_ne_last m hsimple k).mp hkFrequency
      unfold harmonicNormalizedEdgeFrame
      rw [if_neg hkLast]
      field_simp [ne_of_gt hkFrequency]
    _ ≤ 1 :=
      sum_positive_orderedRawEdgeMode_sq_div_frequency_sq_le_one
        m hsimple bond

/-- Since the frozen translation coefficient vanishes, summing over all
ordered modes is the same as summing over the positive spectral sector. -/
theorem sum_sq_r32FrozenBondCoefficient_eq_sum_positive
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hsimple : OrderedSingleModeProjector.SimpleOrderedSpectrum
      (harmonicHermitian m))
    (bond : Lattice.Site N) :
    (∑ k : HarmonicOrderedModeIndex N,
      r32FrozenBondCoefficient m bond k ^ 2) =
      ∑ k ∈ positiveModeIndices (harmonicHermitian m),
        r32FrozenBondCoefficient m bond k ^ 2 := by
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _hkUniv hkNotPositive
  have hkLast : k = lastOrderedIndex (ι := Lattice.Site N) := by
    by_contra hkNeLast
    apply hkNotPositive
    rw [positiveModeIndices_eq_univ_erase_last m hsimple]
    simp [hkNeLast]
  subst k
  simp

/-- The frozen physical bond coefficients have inverse-volume squared `l2`
mass.  No spectral-gap lower bound occurs. -/
theorem sum_sq_r32FrozenBondCoefficient_le_six_div_pred
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (m : Lattice.PositiveMassConfig N)
    (hsimple : OrderedSingleModeProjector.SimpleOrderedSpectrum
      (harmonicHermitian m))
    (bond : Lattice.Site N) :
    (∑ k : HarmonicOrderedModeIndex N,
      r32FrozenBondCoefficient m bond k ^ 2) ≤
      6 / (((N - 1 : Nat) : Real)) := by
  rw [sum_sq_r32FrozenBondCoefficient_eq_sum_positive m hsimple bond]
  calc
    (∑ k ∈ positiveModeIndices (harmonicHermitian m),
        r32FrozenBondCoefficient m bond k ^ 2) ≤
        ∑ k ∈ positiveModeIndices (harmonicHermitian m),
          (6 / (((N - 1 : Nat) : Real))) *
            harmonicNormalizedEdgeFrame m k bond ^ 2 := by
      apply Finset.sum_le_sum
      intro k _hk
      rw [r32FrozenBondCoefficient_sq hN]
      calc
        (2 * frozenTwoBandEnergy N k) *
            harmonicNormalizedEdgeFrame m k bond ^ 2 ≤
            (2 * (3 / (((N - 1 : Nat) : Real)))) *
              harmonicNormalizedEdgeFrame m k bond ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (frozenTwoBandEnergy_le_three_div_pred hN k) (by norm_num))
            (sq_nonneg _)
        _ = (6 / (((N - 1 : Nat) : Real))) *
              harmonicNormalizedEdgeFrame m k bond ^ 2 := by
          ring
    _ = (6 / (((N - 1 : Nat) : Real))) *
        (∑ k ∈ positiveModeIndices (harmonicHermitian m),
          harmonicNormalizedEdgeFrame m k bond ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ (6 / (((N - 1 : Nat) : Real))) * 1 := by
      exact mul_le_mul_of_nonneg_left
        (sum_positive_harmonicNormalizedEdgeFrame_sq_le_one
          m hsimple bond) (by positivity)
    _ = 6 / (((N - 1 : Nat) : Real)) := by ring

/-- The `l1` size of the complete ordered coefficient vector. -/
def r32FrozenBondCoefficientL1 {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (bond : Lattice.Site N) : Real :=
  ∑ k : HarmonicOrderedModeIndex N,
    |r32FrozenBondCoefficient m bond k|

/-- Finite Cauchy--Schwarz turns the squared coefficient bound into
`l1 <= sqrt (6 N / (N - 1))`. -/
theorem r32FrozenBondCoefficientL1_le_sqrt_six_mul_card_div_pred
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (m : Lattice.PositiveMassConfig N)
    (hsimple : OrderedSingleModeProjector.SimpleOrderedSpectrum
      (harmonicHermitian m))
    (bond : Lattice.Site N) :
    r32FrozenBondCoefficientL1 m bond ≤
      Real.sqrt
        (6 * (N : Real) / (((N - 1 : Nat) : Real))) := by
  calc
    r32FrozenBondCoefficientL1 m bond =
        ∑ k ∈ (Finset.univ : Finset (HarmonicOrderedModeIndex N)),
          (1 : Real) * |r32FrozenBondCoefficient m bond k| := by
      simp [r32FrozenBondCoefficientL1]
    _ ≤ Real.sqrt
          (∑ _k ∈ (Finset.univ : Finset (HarmonicOrderedModeIndex N)),
            (1 : Real) ^ 2) *
        Real.sqrt
          (∑ k ∈ (Finset.univ : Finset (HarmonicOrderedModeIndex N)),
            |r32FrozenBondCoefficient m bond k| ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun _k : HarmonicOrderedModeIndex N ↦ (1 : Real))
        (fun k ↦ |r32FrozenBondCoefficient m bond k|)
    _ = Real.sqrt (N : Real) *
        Real.sqrt
          (∑ k : HarmonicOrderedModeIndex N,
            r32FrozenBondCoefficient m bond k ^ 2) := by
      simp [HarmonicOrderedModeIndex, sq_abs]
    _ ≤ Real.sqrt (N : Real) *
        Real.sqrt (6 / (((N - 1 : Nat) : Real))) := by
      exact mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt
          (sum_sq_r32FrozenBondCoefficient_le_six_div_pred
            hN m hsimple bond))
        (Real.sqrt_nonneg _)
    _ = Real.sqrt
        (6 * (N : Real) / (((N - 1 : Nat) : Real))) := by
      rw [← Real.sqrt_mul (by positivity : (0 : Real) ≤ N)]
      congr 1
      ring

/-- The deterministic free physical bond field with arbitrary real initial
phases (in radians). -/
def r32FrozenFreePhysicalBondField {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (bond : Lattice.Site N)
    (phase : HarmonicOrderedModeIndex N → Real) (time : Real) : Real :=
  ∑ k : HarmonicOrderedModeIndex N,
    r32FrozenBondCoefficient m bond k *
      Real.cos
        (orderedModeFrequency (harmonicHermitian m) k * time + phase k)

/-- A modal frequency ceiling and the coefficient `l1` norm give a
phase-uniform time-difference bound. -/
theorem abs_r32FrozenFreePhysicalBondField_sub_le_coefficientL1
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (bond : Lattice.Site N)
    (omegaMax : Real) (_homegaMax : 0 ≤ omegaMax)
    (hfrequency : ∀ k : HarmonicOrderedModeIndex N,
      orderedModeFrequency (harmonicHermitian m) k ≤ omegaMax)
    (phase : HarmonicOrderedModeIndex N → Real) (s t : Real) :
    |r32FrozenFreePhysicalBondField m bond phase t -
        r32FrozenFreePhysicalBondField m bond phase s| ≤
      omegaMax * r32FrozenBondCoefficientL1 m bond * |t - s| := by
  unfold r32FrozenFreePhysicalBondField
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ k : HarmonicOrderedModeIndex N,
        (r32FrozenBondCoefficient m bond k *
            Real.cos
              (orderedModeFrequency (harmonicHermitian m) k * t + phase k) -
          r32FrozenBondCoefficient m bond k *
            Real.cos
              (orderedModeFrequency (harmonicHermitian m) k * s + phase k))| ≤
        ∑ k : HarmonicOrderedModeIndex N,
          |r32FrozenBondCoefficient m bond k *
              Real.cos
                (orderedModeFrequency (harmonicHermitian m) k * t + phase k) -
            r32FrozenBondCoefficient m bond k *
              Real.cos
                (orderedModeFrequency (harmonicHermitian m) k * s + phase k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : HarmonicOrderedModeIndex N,
        |r32FrozenBondCoefficient m bond k| *
          (omegaMax * |t - s|) := by
      apply Finset.sum_le_sum
      intro k _hk
      rw [← mul_sub, abs_mul]
      have hfreqNonneg :
          0 ≤ orderedModeFrequency (harmonicHermitian m) k :=
        Real.sqrt_nonneg _
      calc
        |r32FrozenBondCoefficient m bond k| *
            |Real.cos
                (orderedModeFrequency (harmonicHermitian m) k * t + phase k) -
              Real.cos
                (orderedModeFrequency (harmonicHermitian m) k * s + phase k)| ≤
            |r32FrozenBondCoefficient m bond k| *
              |(orderedModeFrequency (harmonicHermitian m) k * t + phase k) -
                (orderedModeFrequency (harmonicHermitian m) k * s + phase k)| := by
          exact mul_le_mul_of_nonneg_left
            (Real.abs_cos_sub_cos_le _ _) (abs_nonneg _)
        _ = |r32FrozenBondCoefficient m bond k| *
              (orderedModeFrequency (harmonicHermitian m) k * |t - s|) := by
          rw [show
            (orderedModeFrequency (harmonicHermitian m) k * t + phase k) -
                (orderedModeFrequency (harmonicHermitian m) k * s + phase k) =
              orderedModeFrequency (harmonicHermitian m) k * (t - s) by ring,
            abs_mul, abs_of_nonneg hfreqNonneg]
        _ ≤ |r32FrozenBondCoefficient m bond k| *
              (omegaMax * |t - s|) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hfrequency k) (abs_nonneg _))
            (abs_nonneg _)
    _ = omegaMax * r32FrozenBondCoefficientL1 m bond * |t - s| := by
      unfold r32FrozenBondCoefficientL1
      rw [← Finset.sum_mul]
      ring

/-- Uniform deterministic time-Lipschitz bound for every bond and every phase
configuration.  The constant uses only `omegaMax` and finite
Cauchy--Schwarz. -/
theorem r32FrozenFreePhysicalBondField_timeLipschitz_uniform
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (m : Lattice.PositiveMassConfig N)
    (hsimple : OrderedSingleModeProjector.SimpleOrderedSpectrum
      (harmonicHermitian m))
    (omegaMax : Real) (homegaMax : 0 ≤ omegaMax)
    (hfrequency : ∀ k : HarmonicOrderedModeIndex N,
      orderedModeFrequency (harmonicHermitian m) k ≤ omegaMax)
    (bond : Lattice.Site N)
    (phase : HarmonicOrderedModeIndex N → Real) (s t : Real) :
    |r32FrozenFreePhysicalBondField m bond phase t -
        r32FrozenFreePhysicalBondField m bond phase s| ≤
      omegaMax *
        Real.sqrt (6 * (N : Real) / (((N - 1 : Nat) : Real))) *
          |t - s| := by
  calc
    |r32FrozenFreePhysicalBondField m bond phase t -
        r32FrozenFreePhysicalBondField m bond phase s| ≤
        omegaMax * r32FrozenBondCoefficientL1 m bond * |t - s| :=
      abs_r32FrozenFreePhysicalBondField_sub_le_coefficientL1
        m bond omegaMax homegaMax hfrequency phase s t
    _ ≤ omegaMax *
        Real.sqrt (6 * (N : Real) / (((N - 1 : Nat) : Real))) *
          |t - s| := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (r32FrozenBondCoefficientL1_le_sqrt_six_mul_card_div_pred
            hN m hsimple bond) homegaMax)
        (abs_nonneg _)

#print axioms sum_sq_r32FrozenBondCoefficient_le_six_div_pred
#print axioms r32FrozenBondCoefficientL1_le_sqrt_six_mul_card_div_pred
#print axioms r32FrozenFreePhysicalBondField_timeLipschitz_uniform

end

end ArchonPhysics.R32FrozenBondCoefficientBoundV2
