import ArchonPhysics.CanonicalScalarIDSAcousticBounds
import ArchonPhysics.RepeatedModeTupleInteractionBound

/-!
# Quadratic acoustic cumulative bound for repeated parent-child sectors

For the decay sign, equality of the parent label with either child leaves the
other child frequency as the absolute mismatch.  This file proves that the
per-site positive collision weight of either such sector below remaining-child
frequency `delta` is `O(delta^2)`, uniformly in the finite volume and in every
realization of an iid ensemble on the frozen mass support.

The extra power beyond the one-soft-leg bound comes from two independent
facts.  First, the remaining child contributes one explicit acoustic factor.
Second, after fixing that child, squared Cauchy--Schwarz and completeness give

`sum_k (sum_j u k j ^ 2 * u q j)^2 <= 1`.

Thus only the number of positive child modes below `delta` remains.  The
clean/random spectral comparison bounds that count by `N * delta`; the unique
translation zero mode is erased before counting, so there is no finite-volume
additive error.  No simplicity or delocalization hypothesis is used.
-/

namespace ArchonPhysics.RepeatedParentChildAcousticCumulativeBound

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionSoftLegBound
open ArchonPhysics.CanonicalScalarIDSAcousticBounds
open ArchonPhysics.CleanCycleAcousticCountEnvelope
open ArchonPhysics.ComplexRegularizedMarkedLegBridge
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.RandomMassAcousticCountingComparison
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.RepeatedModeTupleInteractionBound
open ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open scoped BigOperators Matrix

noncomputable section

section AbstractFixedChild

variable {mode bond : Type*} [Fintype mode] [DecidableEq mode]
  [Fintype bond] [DecidableEq bond]

omit [DecidableEq bond] in
/-- Fixed-child Bessel bound for repeated cubic coefficients.  Unlike the
fixed-common-label Parseval identity, its proof uses only Cauchy--Schwarz plus
both row and column normalization. -/
theorem sum_repeatedCubicCoefficient_sq_fixed_child_le_one
    (u : mode -> bond -> Real)
    (hcard : Fintype.card mode = Fintype.card bond)
    (horth : forall k q,
      ∑ j, u k j * u q j = if k = q then 1 else 0)
    (q : mode) :
    (∑ k, repeatedCubicCoefficient u k q ^ 2) <= 1 := by
  classical
  have hrow (k : mode) : (∑ j, u k j ^ 2) = 1 := by
    simpa [pow_two] using horth k k
  have hcolumn := column_orthonormal_of_orthonormal_of_card_eq
    u hcard horth
  calc
    (∑ k, repeatedCubicCoefficient u k q ^ 2) <=
        ∑ k, ∑ j, u k j ^ 2 * u q j ^ 2 := by
      apply Finset.sum_le_sum
      intro k _hk
      unfold repeatedCubicCoefficient
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (u k) (fun j => u k j * u q j)
      calc
        (∑ j, u k j ^ 2 * u q j) ^ 2 =
            (∑ j, u k j * (u k j * u q j)) ^ 2 := by
          congr 2
          funext j
          ring
        _ <= (∑ j, u k j ^ 2) *
            (∑ j, (u k j * u q j) ^ 2) := hcs
        _ = ∑ j, u k j ^ 2 * u q j ^ 2 := by
          rw [hrow, one_mul]
          apply Finset.sum_congr rfl
          intro j _hj
          ring
    _ = ∑ j, u q j ^ 2 * (∑ k, u k j ^ 2) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ = ∑ j, u q j ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _hj
      have hj := hcolumn j j
      have hj' : (∑ k, u k j ^ 2) = 1 := by
        rw [if_pos rfl] at hj
        simpa only [pow_two] using hj
      rw [hj', mul_one]
    _ = 1 := hrow q

end AbstractFixedChild

section PositiveAcousticCount

/-- Positive ordered modes below a frequency threshold.  The translation
zero mode is excluded explicitly by strict positivity. -/
def positiveOrderedFrequencySublevelIndices
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (delta : Real) : Finset (OrderedModeIndex N) :=
  Finset.univ.filter fun q =>
    0 < orderedModeFrequency (harmonicHermitian m) q ∧
      orderedModeFrequency (harmonicHermitian m) q <= delta

@[simp] theorem mem_positiveOrderedFrequencySublevelIndices_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (delta : Real) (q : OrderedModeIndex N) :
    q ∈ positiveOrderedFrequencySublevelIndices m delta ↔
      0 < orderedModeFrequency (harmonicHermitian m) q ∧
        orderedModeFrequency (harmonicHermitian m) q <= delta := by
  simp [positiveOrderedFrequencySublevelIndices]

/-- The cyclic-radius cardinal estimate also holds at radius zero. -/
theorem cleanCycleFinRadiusIndices_card_le_all
    (N r : Nat) [NeZero N] (hrN : r < N) :
    (cleanCycleFinRadiusIndices N r).card <= 2 * r + 1 := by
  by_cases hrpos : 0 < r
  · exact cleanCycleFinRadiusIndices_card_le N r hrpos hrN
  · have hr : r = 0 := Nat.eq_zero_of_not_pos hrpos
    subst r
    let z : Fin N := ⟨0, NeZero.pos N⟩
    have hsub : cleanCycleFinRadiusIndices N 0 ⊆ {z} := by
      intro k hk
      rw [mem_cleanCycleFinRadiusIndices_iff] at hk
      have hmin : min k.val (N - k.val) = 0 := by
        simpa [cycleModeRadius, finEquiv_val] using hk
      have hkzero : k.val = 0 := by
        by_cases hle : k.val <= N - k.val
        · rw [min_eq_left hle] at hmin
          exact hmin
        · rw [min_eq_right (Nat.le_of_not_ge hle)] at hmin
          have hklt : k.val < N := k.isLt
          omega
      have hkz : k = z := by
        apply Fin.ext
        exact hkzero
      simp [hkz]
    calc
      (cleanCycleFinRadiusIndices N 0).card <= ({z} : Finset (Fin N)).card :=
        Finset.card_le_card hsub
      _ = 2 * 0 + 1 := by simp

/-- Clean-cycle threshold count with the acoustic radius, including the
radius-zero case omitted by the older positive-radius wrapper. -/
theorem orderedEigenvalueThresholdCount_clean_le_acousticUpperEnvelope
    (N : Nat) [NeZero N] {E : Real} (hE : 0 < E) (hE1 : E <= 1) :
    orderedEigenvalueThresholdCount
        (cleanCycleHarmonicHermitian N) ((6 / 5 : Real) * E) <=
      2 * acousticUpperRadius E N + 1 := by
  let r := acousticUpperRadius E N
  have hrN : r < N := acousticUpperRadius_lt_volume N hE1
  have hgap : (6 / 5 : Real) * E <
      16 * (((r + 1 : Nat) : Real) ^ 2) / (N : Real) ^ 2 := by
    simpa [r] using clean_upper_energy_condition N hE
  rw [orderedEigenvalueThresholdCount_clean_eq_modeThresholdCount,
    cleanCycleModeThresholdCount_eq_finCount]
  exact (Finset.card_le_card
    (cleanCycleFinModeThresholdIndices_subset_radius
      N r ((6 / 5 : Real) * E) hgap)).trans
    (cleanCycleFinRadiusIndices_card_le_all N r hrN)

variable {Omega : Type*} [MeasurableSpace Omega]

/-- On the frozen iid mass box, the number of strictly positive ordered modes
with frequency at most `delta` is at most `2 * acousticUpperRadius delta^2 N`.
The missing `+1` is exactly the erased translation mode. -/
theorem iid_positiveOrderedFrequencySublevelIndices_card_le
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    {delta : Real} (hdelta : 0 < delta) (hdelta1 : delta <= 1) :
    (positiveOrderedFrequencySublevelIndices
      (ensemble.restrictPositiveMass (N := N) omega) delta).card <=
      2 * acousticUpperRadius (delta ^ 2) N := by
  let m := ensemble.restrictPositiveMass (N := N) omega
  let z : OrderedModeIndex N :=
    lastOrderedIndex (ι := Lattice.Site N)
  let randomThreshold := orderedEigenvalueThresholdIndices
    (harmonicHermitian m) (delta ^ 2)
  let cleanThreshold := orderedEigenvalueThresholdIndices
    (cleanCycleHarmonicHermitian N) ((6 / 5 : Real) * delta ^ 2)
  have hsoftRandom : positiveOrderedFrequencySublevelIndices m delta ⊆
      randomThreshold.erase z := by
    intro q hq
    rw [mem_positiveOrderedFrequencySublevelIndices_iff] at hq
    rw [Finset.mem_erase, mem_orderedEigenvalueThresholdIndices_iff]
    constructor
    · exact (orderedModeFrequency_pos_iff_ne_last_unconditional m q).mp hq.1
    · have hlambda : 0 <= orderedEigenvalue (harmonicHermitian m) q :=
        harmonicHermitian_orderedEigenvalue_nonneg m q
      have hsqrt : (Real.sqrt
          (orderedEigenvalue (harmonicHermitian m) q)) ^ 2 =
          orderedEigenvalue (harmonicHermitian m) q :=
        Real.sq_sqrt hlambda
      have hfreq0 : 0 <= orderedModeFrequency (harmonicHermitian m) q := by
        exact Real.sqrt_nonneg _
      change orderedEigenvalue (harmonicHermitian m) q <= delta ^ 2
      have hfreqle : Real.sqrt
          (orderedEigenvalue (harmonicHermitian m) q) <= delta := by
        simpa only [orderedModeFrequency] using hq.2
      have hsq : (Real.sqrt
          (orderedEigenvalue (harmonicHermitian m) q)) ^ 2 <= delta ^ 2 :=
        (sq_le_sq₀ (Real.sqrt_nonneg _) hdelta.le).2 hfreqle
      rwa [hsqrt] at hsq
  have hrandomClean : randomThreshold ⊆ cleanThreshold := by
    simpa [m, randomThreshold, cleanThreshold] using
      (iid_orderedEigenvalueThresholdIndices_sandwich
        ensemble (N := N) omega (delta ^ 2)).2
  have herase : randomThreshold.erase z ⊆ cleanThreshold.erase z := by
    intro q hq
    rw [Finset.mem_erase] at hq ⊢
    exact ⟨hq.1, hrandomClean hq.2⟩
  have hzClean : z ∈ cleanThreshold := by
    rw [mem_orderedEigenvalueThresholdIndices_iff]
    dsimp [z, cleanThreshold]
    have hnonempty :
        (orderedEigenvalueThresholdIndices
          (cleanCycleHarmonicHermitian N) 0).Nonempty := by
      apply Finset.card_pos.mp
      exact lt_of_lt_of_le Nat.zero_lt_one
        (one_le_orderedEigenvalueThresholdCount_clean_of_nonneg N
          (show (0 : Real) <= 0 by rfl))
    obtain ⟨q, hq⟩ := hnonempty
    rw [mem_orderedEigenvalueThresholdIndices_iff] at hq
    exact (orderedEigenvalue_last_le (cleanCycleHarmonicHermitian N) q).trans
      (hq.trans (by positivity))
  have hE : 0 < delta ^ 2 := sq_pos_of_pos hdelta
  have hE1 : delta ^ 2 <= 1 := by nlinarith
  have hcleanCount : cleanThreshold.card <=
      2 * acousticUpperRadius (delta ^ 2) N + 1 := by
    simpa [cleanThreshold, orderedEigenvalueThresholdCount,
      orderedEigenvalueThresholdIndices] using
      orderedEigenvalueThresholdCount_clean_le_acousticUpperEnvelope
        N hE hE1
  calc
    (positiveOrderedFrequencySublevelIndices m delta).card <=
        (randomThreshold.erase z).card := Finset.card_le_card hsoftRandom
    _ <= (cleanThreshold.erase z).card := Finset.card_le_card herase
    _ = cleanThreshold.card - 1 := Finset.card_erase_of_mem hzClean
    _ <= 2 * acousticUpperRadius (delta ^ 2) N := by omega

/-- Pure linear acoustic count after division by volume.  Strict positivity
removes the zero-mode correction and is essential for this exact form. -/
theorem iid_positiveOrderedFrequencySublevelIndices_card_div_volume_le
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    {delta : Real} (hdelta : 0 < delta) (hdelta1 : delta <= 1) :
    ((positiveOrderedFrequencySublevelIndices
      (ensemble.restrictPositiveMass (N := N) omega) delta).card : Real) /
        (N : Real) <= delta := by
  have hcard := iid_positiveOrderedFrequencySublevelIndices_card_le
    (N := N) (delta := delta) ensemble omega hdelta hdelta1
  have hradius : (acousticUpperRadius (delta ^ 2) N : Real) <=
      (Real.sqrt (delta ^ 2) / 2) * (N : Real) := by
    exact Nat.floor_le
      (mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (by norm_num))
        (Nat.cast_nonneg N))
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hsqrt : Real.sqrt (delta ^ 2) = delta := Real.sqrt_sq hdelta.le
  rw [hsqrt] at hradius
  have hcardReal :
      ((positiveOrderedFrequencySublevelIndices
        (ensemble.restrictPositiveMass (N := N) omega) delta).card : Real) <=
        2 * (acousticUpperRadius (delta ^ 2) N : Real) := by
    exact_mod_cast hcard
  rw [div_le_iff₀ hN]
  calc
    ((positiveOrderedFrequencySublevelIndices
      (ensemble.restrictPositiveMass (N := N) omega) delta).card : Real) <=
        2 * (acousticUpperRadius (delta ^ 2) N : Real) := hcardReal
    _ <= delta * (N : Real) := by nlinarith

end PositiveAcousticCount

section RepeatedParentChildWeight

/-- Positive collision weight on `mode 0 = mode 1` whose remaining child has
frequency at most `delta`. -/
def positiveRepeatedZeroOneSoftChildInteractionWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (delta : Real) : Real := by
  classical
  exact ∑ k, ∑ q,
    if IsPositiveOrderedTriple m ![k, k, q] ∧
        orderedModeFrequency (harmonicHermitian m) q <= delta then
      harmonicOrderedNormalizedInteractionWeight m ![k, k, q]
    else 0

/-- The analogous positive collision weight on `mode 0 = mode 2`; the
remaining child is now leg one. -/
def positiveRepeatedZeroTwoSoftChildInteractionWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (delta : Real) : Real := by
  classical
  exact ∑ k, ∑ q,
    if IsPositiveOrderedTriple m ![k, q, k] ∧
        orderedModeFrequency (harmonicHermitian m) q <= delta then
      harmonicOrderedNormalizedInteractionWeight m ![k, q, k]
    else 0

/-- Permutation symmetry identifies the two parent-child cumulative weights. -/
theorem positiveRepeatedZeroTwoSoftChildInteractionWeight_eq_zeroOne
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (delta : Real) :
    positiveRepeatedZeroTwoSoftChildInteractionWeight m delta =
      positiveRepeatedZeroOneSoftChildInteractionWeight m delta := by
  classical
  unfold positiveRepeatedZeroTwoSoftChildInteractionWeight
    positiveRepeatedZeroOneSoftChildInteractionWeight
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro q _hq
  rw [isPositive_repeated_zero_two_iff_zero_one]
  split_ifs
  · exact harmonicOrderedNormalizedInteractionWeight_repeated_zero_two_eq
      m k q
  · rfl

/-- The fixed-child abstract estimate specialized to the harmonic normalized
edge frame. -/
theorem sum_harmonicRepeatedCubicCoefficient_sq_fixed_child_le_one
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (q : OrderedModeIndex N) :
    (∑ k, repeatedCubicCoefficient
      (harmonicNormalizedEdgeFrame m) k q ^ 2) <= 1 := by
  exact sum_repeatedCubicCoefficient_sq_fixed_child_le_one
    (harmonicNormalizedEdgeFrame m) (by simp [Lattice.Site])
      (harmonicNormalizedEdgeFrame_orthonormal_unconditional m) q

/-- Deterministic cumulative estimate in terms of the number of positive
remaining-child modes below the cutoff. -/
theorem positiveRepeatedZeroOneSoftChildInteractionWeight_div_volume_le_count
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (delta ceiling : Real) (hdelta : 0 <= delta) (_hceiling : 0 <= ceiling)
    (hfrequency : forall k,
      orderedModeFrequency (harmonicHermitian m) k <= ceiling) :
    positiveRepeatedZeroOneSoftChildInteractionWeight m delta /
        (N : Real) <=
      (ceiling / 2) ^ 2 * (delta / 2) *
        (((positiveOrderedFrequencySublevelIndices m delta).card : Real) /
          (N : Real)) := by
  classical
  let soft := positiveOrderedFrequencySublevelIndices m delta
  let C := (ceiling / 2) ^ 2 * (delta / 2)
  have hC : 0 <= C := mul_nonneg (sq_nonneg _) (by positivity)
  have hweight : positiveRepeatedZeroOneSoftChildInteractionWeight m delta <=
      C * (soft.card : Real) := by
    unfold positiveRepeatedZeroOneSoftChildInteractionWeight
    calc
      (∑ k, ∑ q,
        if IsPositiveOrderedTriple m ![k, k, q] ∧
            orderedModeFrequency (harmonicHermitian m) q <= delta then
          harmonicOrderedNormalizedInteractionWeight m ![k, k, q]
        else 0) <=
          ∑ k, ∑ q,
            if q ∈ soft then
              C * repeatedCubicCoefficient
                (harmonicNormalizedEdgeFrame m) k q ^ 2
            else 0 := by
        apply Finset.sum_le_sum
        intro k _hk
        apply Finset.sum_le_sum
        intro q _hq
        by_cases hkeep : IsPositiveOrderedTriple m ![k, k, q] ∧
            orderedModeFrequency (harmonicHermitian m) q <= delta
        · rw [if_pos hkeep]
          have hsoft : q ∈ soft := by
            rw [mem_positiveOrderedFrequencySublevelIndices_iff]
            exact ⟨(mem_orderedPositiveModeIndices_iff m q).mp
              (hkeep.1 2), hkeep.2⟩
          rw [if_pos hsoft,
            harmonicOrderedNormalizedInteractionWeight_repeated_zero_one_eq]
          have hk0 := harmonicActiveNormalizedCoefficient_nonneg m k
          have hq0 := harmonicActiveNormalizedCoefficient_nonneg m q
          have hkb := harmonicActiveNormalizedCoefficient_le_half_ceiling
            m ceiling hfrequency k
          have hqbase := abs_activeOrderedEigenvalue_mul_inv_two_frequency_le
            m q
          change |harmonicActiveNormalizedCoefficient m q| <=
            orderedModeFrequency (harmonicHermitian m) q / 2 at hqbase
          rw [abs_of_nonneg hq0] at hqbase
          have hqb : harmonicActiveNormalizedCoefficient m q <= delta / 2 :=
            hqbase.trans
              (div_le_div_of_nonneg_right hkeep.2 (by norm_num))
          have hcoefficient :
              harmonicActiveNormalizedCoefficient m k ^ 2 *
                  harmonicActiveNormalizedCoefficient m q <= C := by
            dsimp [C]
            exact mul_le_mul
              (pow_le_pow_left₀ hk0 hkb 2) hqb hq0 (sq_nonneg _)
          exact mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg _)
        · rw [if_neg hkeep]
          split_ifs
          · positivity
          · rfl
      _ = ∑ q, if q ∈ soft then
          C * (∑ k, repeatedCubicCoefficient
            (harmonicNormalizedEdgeFrame m) k q ^ 2) else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro q _hq
        by_cases hqsoft : q ∈ soft
        · simp only [if_pos hqsoft, Finset.mul_sum]
        · simp [hqsoft]
      _ <= ∑ q, if q ∈ soft then C * 1 else 0 := by
        apply Finset.sum_le_sum
        intro q _hq
        by_cases hqsoft : q ∈ soft
        · rw [if_pos hqsoft, if_pos hqsoft]
          exact mul_le_mul_of_nonneg_left
            (sum_harmonicRepeatedCubicCoefficient_sq_fixed_child_le_one m q) hC
        · simp [hqsoft]
      _ = C * (soft.card : Real) := by
        rw [← Finset.sum_filter]
        simp [mul_comm]
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  calc
    positiveRepeatedZeroOneSoftChildInteractionWeight m delta /
        (N : Real) <= (C * (soft.card : Real)) / (N : Real) :=
      div_le_div_of_nonneg_right hweight hN.le
    _ = (ceiling / 2) ^ 2 * (delta / 2) *
        (((positiveOrderedFrequencySublevelIndices m delta).card : Real) /
          (N : Real)) := by
      dsimp [C, soft]
      ring

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Uniform quadratic acoustic cumulative bound for `mode 0 = mode 1` on the
frozen iid support.  The explicit constant is `5/8`. -/
theorem iid_positiveRepeatedZeroOneSoftChildInteractionWeight_div_volume_le_sq
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    {delta : Real} (hdelta : 0 < delta) (hdelta1 : delta <= 1) :
    positiveRepeatedZeroOneSoftChildInteractionWeight
        (ensemble.restrictPositiveMass (N := N) omega) delta /
          (N : Real) <=
      (5 / 8 : Real) * delta ^ 2 := by
  let m := ensemble.restrictPositiveMass (N := N) omega
  have hfrequency : forall k,
      orderedModeFrequency (harmonicHermitian m) k <= Real.sqrt 5 := by
    intro k
    exact iid_orderedModeFrequency_harmonic_le_sqrt_five
      ensemble omega k
  have hbase :=
    positiveRepeatedZeroOneSoftChildInteractionWeight_div_volume_le_count
      m delta (Real.sqrt 5) hdelta.le (Real.sqrt_nonneg 5) hfrequency
  have hcount :=
    iid_positiveOrderedFrequencySublevelIndices_card_div_volume_le
      (N := N) (delta := delta) ensemble omega hdelta hdelta1
  calc
    positiveRepeatedZeroOneSoftChildInteractionWeight m delta /
        (N : Real) <=
      (Real.sqrt 5 / 2) ^ 2 * (delta / 2) *
        (((positiveOrderedFrequencySublevelIndices m delta).card : Real) /
          (N : Real)) := hbase
    _ <= (Real.sqrt 5 / 2) ^ 2 * (delta / 2) * delta := by
      gcongr
    _ = (5 / 8 : Real) * delta ^ 2 := by
      have hsqrt : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      nlinarith

/-- The same uniform quadratic bound for `mode 0 = mode 2`. -/
theorem iid_positiveRepeatedZeroTwoSoftChildInteractionWeight_div_volume_le_sq
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    {delta : Real} (hdelta : 0 < delta) (hdelta1 : delta <= 1) :
    positiveRepeatedZeroTwoSoftChildInteractionWeight
        (ensemble.restrictPositiveMass (N := N) omega) delta /
          (N : Real) <=
      (5 / 8 : Real) * delta ^ 2 := by
  rw [positiveRepeatedZeroTwoSoftChildInteractionWeight_eq_zeroOne]
  exact iid_positiveRepeatedZeroOneSoftChildInteractionWeight_div_volume_le_sq
    ensemble omega hdelta hdelta1

end RepeatedParentChildWeight

end

end ArchonPhysics.RepeatedParentChildAcousticCumulativeBound
