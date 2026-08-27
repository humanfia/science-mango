import ArchonPhysics.FractionalResonanceKernelDecay
import ArchonPhysics.RepeatedParentChildAcousticCumulativeBound
import Mathlib.Data.Fin.Rev

/-!
# Fractional broadening decay for repeated parent-child planes

The full decay-channel equality planes `mode 0 = mode 1` and
`mode 0 = mode 2` are off shell by exactly the remaining positive child
frequency.  A fixed-child contraction bounds the sum over the common label,
while the acoustic counting estimate controls the negative half moment of the
remaining ordered frequency.  Combining these facts with the fractional
sinc-kernel tail gives a volume-uniform `O(T^{-1/2})` bound.

No simple-spectrum, inverse-participation, or delocalization hypothesis is
used.
-/

namespace ArchonPhysics.RepeatedParentChildFractionalBroadeningDecay

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionSoftLegBound
open ArchonPhysics.FractionalResonanceKernelDecay
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.RepeatedModeTupleInteractionBound
open ArchonPhysics.RepeatedParentChildAcousticCumulativeBound
open ArchonPhysics.UniformCollisionDensityTransfer
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open Filter
open scoped BigOperators

noncomputable section

/-! ## An elementary reciprocal-square-root sum -/

/-- One reciprocal square root is dominated by the corresponding telescoping
square-root increment. -/
theorem inv_sqrt_nat_succ_le_two_mul_sqrt_sub
    (d : Nat) :
    (Real.sqrt ((d + 1 : Nat) : Real))⁻¹ <=
      2 * (Real.sqrt ((d + 1 : Nat) : Real) - Real.sqrt (d : Real)) := by
  let a := Real.sqrt ((d + 1 : Nat) : Real)
  let b := Real.sqrt (d : Real)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hb : 0 <= b := by positivity
  have hba : b <= a := by
    dsimp [a, b]
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.le_succ d
  have haSq : a ^ 2 = (d + 1 : Nat) := by
    dsimp [a]
    rw [Real.sq_sqrt]
    positivity
  have hbSq : b ^ 2 = d := by
    dsimp [b]
    rw [Real.sq_sqrt]
    positivity
  have hab : 0 < a + b := add_pos_of_pos_of_nonneg ha hb
  have hdiff : a - b = (a + b)⁻¹ := by
    have haSq' : a ^ 2 = (d : Real) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using haSq
    have hmul : (a - b) * (a + b) = 1 := by
      nlinarith [haSq', hbSq]
    calc
      a - b = (a - b) * ((a + b) * (a + b)⁻¹) := by
        rw [mul_inv_cancel₀ hab.ne', mul_one]
      _ = ((a - b) * (a + b)) * (a + b)⁻¹ := by ring
      _ = (a + b)⁻¹ := by rw [hmul, one_mul]
  change a⁻¹ <= 2 * (a - b)
  rw [hdiff]
  have hdiv : (1 : Real) / a <= 2 / (a + b) := by
    rw [div_le_div_iff₀ ha hab]
    nlinarith
  simpa [one_div, div_eq_mul_inv] using hdiv

/-- The square-root increments telescope exactly on `Fin n`. -/
theorem sum_sqrt_nat_succ_sub_sqrt_eq (n : Nat) :
    (∑ i : Fin n,
      (Real.sqrt ((i.val + 1 : Nat) : Real) -
        Real.sqrt (i.val : Real))) = Real.sqrt (n : Real) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      ring

/-- Uniform integral-test bound for the discrete reciprocal square-root sum. -/
theorem sum_inv_sqrt_nat_succ_le_two_sqrt (n : Nat) :
    (∑ i : Fin n, (Real.sqrt ((i.val + 1 : Nat) : Real))⁻¹) <=
      2 * Real.sqrt (n : Real) := by
  calc
    (∑ i : Fin n, (Real.sqrt ((i.val + 1 : Nat) : Real))⁻¹) <=
        ∑ i : Fin n, 2 *
          (Real.sqrt ((i.val + 1 : Nat) : Real) -
            Real.sqrt (i.val : Real)) := by
      exact Finset.sum_le_sum fun i _hi =>
        inv_sqrt_nat_succ_le_two_mul_sqrt_sub i.val
    _ = 2 * (∑ i : Fin n,
        (Real.sqrt ((i.val + 1 : Nat) : Real) -
          Real.sqrt (i.val : Real))) := by rw [Finset.mul_sum]
    _ = 2 * Real.sqrt (n : Real) := by
      rw [sum_sqrt_nat_succ_sub_sqrt_eq]

/-! ## Ordered acoustic negative half moment -/

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Distance of an ordered label from the last (translation) label. -/
def orderedDistanceFromLast {N : Nat} [NeZero N]
    (q : OrderedModeIndex N) : Nat :=
  N - 1 - q.val

/-- Cardinality cast from the canonical ordered index type to `Fin N`. -/
def orderedModeIndexFinEquivForMoment
    (N : Nat) [NeZero N] : OrderedModeIndex N ≃ Fin N :=
  finCongr (by simp [Lattice.Site])

@[simp] theorem orderedModeIndexFinEquivForMoment_val
    {N : Nat} [NeZero N] (q : OrderedModeIndex N) :
    (orderedModeIndexFinEquivForMoment N q).val = q.val := by
  simp [orderedModeIndexFinEquivForMoment]

/-- Every positive mode supplies its complete final positive-index interval to
the frequency sublevel set at its own frequency. -/
theorem orderedDistanceFromLast_le_positiveFrequencySublevel_card
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (q : OrderedModeIndex N)
    (hq : 0 < orderedModeFrequency (harmonicHermitian m) q) :
    orderedDistanceFromLast q <=
      (positiveOrderedFrequencySublevelIndices m
        (orderedModeFrequency (harmonicHermitian m) q)).card := by
  let z : OrderedModeIndex N :=
    lastOrderedIndex (ι := Lattice.Site N)
  have hqz : q < z := by
    have hne : q ≠ z :=
      (orderedModeFrequency_pos_iff_ne_last_unconditional m q).mp hq
    exact lt_of_le_of_ne (le_lastOrderedIndex q) hne
  have hsub : Finset.Ico q z ⊆
      positiveOrderedFrequencySublevelIndices m
        (orderedModeFrequency (harmonicHermitian m) q) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [mem_positiveOrderedFrequencySublevelIndices_iff]
    constructor
    · exact (orderedModeFrequency_pos_iff_ne_last_unconditional m j).2
        (ne_of_lt hj.2)
    · unfold orderedModeFrequency
      exact Real.sqrt_le_sqrt
        ((harmonicHermitian m).property.eigenvalues₀_antitone hj.1)
  have hcard : (Finset.Ico q z).card = orderedDistanceFromLast q := by
    simp [orderedDistanceFromLast, z, lastOrderedIndex, Lattice.Site]
  rw [<- hcard]
  exact Finset.card_le_card hsub

/-- A positive ordered frequency is bounded below by its normalized distance
from the translation label whenever it lies in the acoustic unit band. -/
theorem iid_orderedDistanceFromLast_div_volume_le_frequency
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (q : OrderedModeIndex N)
    (hq : 0 < orderedModeFrequency
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega)) q)
    (hq1 : orderedModeFrequency
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega)) q <= 1) :
    (orderedDistanceFromLast q : Real) / (N : Real) <=
      orderedModeFrequency
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := N) omega)) q := by
  let m := ensemble.restrictPositiveMass (N := N) omega
  have hlower := orderedDistanceFromLast_le_positiveFrequencySublevel_card
    m q hq
  have hupper := iid_positiveOrderedFrequencySublevelIndices_card_div_volume_le
    (N := N)
    (delta := orderedModeFrequency (harmonicHermitian m) q)
    ensemble omega hq hq1
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  calc
    (orderedDistanceFromLast q : Real) / (N : Real) <=
        ((positiveOrderedFrequencySublevelIndices m
          (orderedModeFrequency (harmonicHermitian m) q)).card : Real) /
            (N : Real) := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hlower) hN.le
    _ <= orderedModeFrequency (harmonicHermitian m) q := hupper

/-- Pointwise rank majorant for the inverse square root of every positive
ordered frequency. -/
theorem iid_inv_sqrt_orderedModeFrequency_le_rankMajorant
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    (q : OrderedModeIndex N)
    (hq : 0 < orderedModeFrequency
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega)) q) :
    (Real.sqrt (orderedModeFrequency
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega)) q))⁻¹ <=
      Real.sqrt (N : Real) /
        Real.sqrt (orderedDistanceFromLast q : Real) := by
  let m := ensemble.restrictPositiveMass (N := N) omega
  let frequency := orderedModeFrequency (harmonicHermitian m) q
  let d := orderedDistanceFromLast q
  have hqne : q ≠ lastOrderedIndex (ι := Lattice.Site N) :=
    (orderedModeFrequency_pos_iff_ne_last_unconditional m q).mp hq
  have hdNat : 0 < d := by
    dsimp [d, orderedDistanceFromLast]
    have hqval : q.val < N - 1 := by
      have hle := le_lastOrderedIndex q
      have hneVal : q.val ≠ N - 1 := by
        intro heq
        apply hqne
        apply Fin.ext
        simpa [lastOrderedIndex, Lattice.Site] using heq
      have hleVal : q.val <= N - 1 := by
        simpa [lastOrderedIndex, Lattice.Site, Fin.le_iff_val_le_val] using hle
      exact lt_of_le_of_ne hleVal hneVal
    omega
  have hd : 0 < (d : Real) := by exact_mod_cast hdNat
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hfrequency : 0 < frequency := hq
  have hsqrtFrequency : 0 < Real.sqrt frequency := Real.sqrt_pos.2 hfrequency
  have hsqrtD : 0 < Real.sqrt (d : Real) := Real.sqrt_pos.2 hd
  by_cases hfrequencyOne : frequency <= 1
  · have hlower := iid_orderedDistanceFromLast_div_volume_le_frequency
      (N := N) ensemble omega q hq hfrequencyOne
    have hscaled : (d : Real) <= (N : Real) * frequency := by
      rw [div_le_iff₀ hN] at hlower
      simpa [d, frequency, mul_comm] using hlower
    have hroot : Real.sqrt (d : Real) <=
        Real.sqrt (N : Real) * Real.sqrt frequency := by
      calc
        Real.sqrt (d : Real) <= Real.sqrt ((N : Real) * frequency) :=
          Real.sqrt_le_sqrt hscaled
        _ = Real.sqrt (N : Real) * Real.sqrt frequency := by
          rw [Real.sqrt_mul (show 0 <= (N : Real) by positivity)]
    have hdiv : 1 / Real.sqrt frequency <=
        Real.sqrt (N : Real) / Real.sqrt (d : Real) :=
      (div_le_div_iff₀ hsqrtFrequency hsqrtD).2 (by simpa using hroot)
    simpa [m, frequency, d, one_div] using hdiv
  · have hone : 1 <= frequency := le_of_lt (lt_of_not_ge hfrequencyOne)
    have hsqrtOne : 1 <= Real.sqrt frequency := by
      simpa using Real.sqrt_le_sqrt hone
    have hinv : (Real.sqrt frequency)⁻¹ <= 1 := by
      exact inv_le_one_of_one_le₀ hsqrtOne
    have hdN : (d : Real) <= (N : Real) := by
      exact_mod_cast (show d <= N by dsimp [d, orderedDistanceFromLast]; omega)
    have hroot : Real.sqrt (d : Real) <= Real.sqrt (N : Real) :=
      Real.sqrt_le_sqrt hdN
    have honeRank : 1 <= Real.sqrt (N : Real) / Real.sqrt (d : Real) := by
      rw [le_div_iff₀ hsqrtD]
      simpa using hroot
    exact hinv.trans honeRank

/-- Uniform negative half moment of all strictly positive ordered frequencies.
The conservative explicit constant `2` is independent of volume and sample. -/
theorem iid_positiveOrderedFrequency_invSqrt_sum_div_volume_le_two
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega) :
    ((∑ q ∈ orderedPositiveModeIndices
      (ensemble.restrictPositiveMass (N := N) omega),
      (Real.sqrt (orderedModeFrequency
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := N) omega)) q))⁻¹) /
        (N : Real)) <= 2 := by
  let m := ensemble.restrictPositiveMass (N := N) omega
  let z : OrderedModeIndex N :=
    lastOrderedIndex (ι := Lattice.Site N)
  have hpositive : orderedPositiveModeIndices m = Finset.univ.erase z := by
    ext q
    rw [mem_orderedPositiveModeIndices_iff]
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact orderedModeFrequency_pos_iff_ne_last_unconditional m q
  have hpointwise :
      (∑ q ∈ orderedPositiveModeIndices m,
        (Real.sqrt (orderedModeFrequency (harmonicHermitian m) q))⁻¹) <=
        ∑ q ∈ Finset.univ.erase z,
          Real.sqrt (N : Real) /
            Real.sqrt (orderedDistanceFromLast q : Real) := by
    rw [hpositive]
    apply Finset.sum_le_sum
    intro q hq
    rw [Finset.mem_erase] at hq
    apply iid_inv_sqrt_orderedModeFrequency_le_rankMajorant
      (N := N) ensemble omega q
    exact (orderedModeFrequency_pos_iff_ne_last_unconditional m q).2 hq.1
  have hrankSum :
      (∑ q ∈ Finset.univ.erase z,
        Real.sqrt (N : Real) /
          Real.sqrt (orderedDistanceFromLast q : Real)) <=
        2 * (N : Real) := by
    cases N with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n =>
        have hrev :
            (∑ q ∈ Finset.univ.erase z,
              Real.sqrt ((n + 1 : Nat) : Real) /
                Real.sqrt (orderedDistanceFromLast q : Real)) =
              ∑ d ∈ (Finset.univ.erase (0 : Fin (n + 1))),
                Real.sqrt ((n + 1 : Nat) : Real) /
                  Real.sqrt (d.val : Real) := by
          let e : OrderedModeIndex (n + 1) ≃ Fin (n + 1) :=
            (orderedModeIndexFinEquivForMoment (n + 1)).trans Fin.revPerm
          have hez : e z = 0 := by
            apply Fin.ext
            simp [e, z, lastOrderedIndex, Fin.val_rev, Lattice.Site]
          apply Finset.sum_equiv e
          · intro q
            simp only [Finset.mem_erase, Finset.mem_univ, and_true]
            constructor
            · intro hq heq
              exact hq (e.injective (heq.trans hez.symm))
            · intro hq heq
              subst q
              exact hq hez
          · intro q _hq
            congr 2
            simp [e, orderedDistanceFromLast, Fin.val_rev]
        rw [hrev]
        have herase :
            (∑ d ∈ (Finset.univ.erase (0 : Fin (n + 1))),
              Real.sqrt ((n + 1 : Nat) : Real) /
                Real.sqrt (d.val : Real)) =
              Real.sqrt ((n + 1 : Nat) : Real) *
                ∑ i : Fin n,
                  (Real.sqrt ((i.val + 1 : Nat) : Real))⁻¹ := by
          rw [Finset.sum_erase Finset.univ (by simp)]
          rw [Fin.sum_univ_succ]
          simp [div_eq_mul_inv, Finset.mul_sum]
        rw [herase]
        calc
          Real.sqrt ((n + 1 : Nat) : Real) *
              ∑ i : Fin n,
                (Real.sqrt ((i.val + 1 : Nat) : Real))⁻¹ <=
              Real.sqrt ((n + 1 : Nat) : Real) *
                (2 * Real.sqrt (n : Real)) := by
            exact mul_le_mul_of_nonneg_left
              (sum_inv_sqrt_nat_succ_le_two_sqrt n) (Real.sqrt_nonneg _)
          _ <= 2 * ((n + 1 : Nat) : Real) := by
            have hn : (n : Real) <= (n + 1 : Nat) := by
              exact_mod_cast Nat.le_succ n
            have hmul : Real.sqrt ((n + 1 : Nat) : Real) *
                Real.sqrt (n : Real) <= (n + 1 : Nat) := by
              calc
                Real.sqrt ((n + 1 : Nat) : Real) * Real.sqrt (n : Real) <=
                    Real.sqrt ((n + 1 : Nat) : Real) *
                      Real.sqrt ((n + 1 : Nat) : Real) := by gcongr
                _ = (n + 1 : Nat) := by
                  nlinarith [Real.sq_sqrt
                    (show 0 <= ((n + 1 : Nat) : Real) by positivity)]
            nlinarith
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  rw [div_le_iff₀ hN]
  exact hpointwise.trans hrankSum

/-! ## Fractional kernel and broadened repeated planes -/

/-- Evenness of the normalized physical resonance kernel. -/
theorem normalizedFiniteTimeResonanceKernel_neg (Omega T : Real) :
    normalizedFiniteTimeResonanceKernel (-Omega) T =
      normalizedFiniteTimeResonanceKernel Omega T := by
  unfold normalizedFiniteTimeResonanceKernel
  rw [ArchonPhysics.ResonanceWeightSinc.finiteTimeResonanceWeight_neg]

/-- A convenient separated form of the fractional kernel estimate. -/
theorem frequency_mul_normalizedFiniteTimeResonanceKernel_le_invSqrt
    {frequency T : Real} (hfrequency : 0 < frequency) (hT : 0 < T) :
    frequency * normalizedFiniteTimeResonanceKernel frequency T <=
      2 / (Real.pi * Real.sqrt frequency * Real.sqrt T) := by
  have hbase := frequency_mul_normalizedFiniteTimeResonanceKernel_le_fractionalTail
    hfrequency hT
  have habs : |frequency * T / 2| = frequency * T / 2 := by
    rw [abs_of_nonneg]
    positivity
  rw [habs] at hbase
  have hroot : Real.sqrt (frequency * T / 2) <=
      Real.sqrt frequency * Real.sqrt T := by
    calc
      Real.sqrt (frequency * T / 2) <= Real.sqrt (frequency * T) := by
        apply Real.sqrt_le_sqrt
        nlinarith [mul_pos hfrequency hT]
      _ = Real.sqrt frequency * Real.sqrt T := by
        rw [Real.sqrt_mul hfrequency.le]
  have hdenom : 0 <= (Real.pi * frequency * T) := by positivity
  calc
    frequency * normalizedFiniteTimeResonanceKernel frequency T <=
        2 * Real.sqrt (frequency * T / 2) /
          (Real.pi * frequency * T) := hbase
    _ <= 2 * (Real.sqrt frequency * Real.sqrt T) /
          (Real.pi * frequency * T) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hroot (by norm_num)) hdenom
    _ = 2 / (Real.pi * Real.sqrt frequency * Real.sqrt T) := by
      have hsqrtFrequency : Real.sqrt frequency ≠ 0 :=
        (Real.sqrt_pos.2 hfrequency).ne'
      have hsqrtT : Real.sqrt T ≠ 0 := (Real.sqrt_pos.2 hT).ne'
      field_simp [hfrequency.ne', hT.ne', Real.pi_ne_zero,
        hsqrtFrequency, hsqrtT]
      rw [Real.sq_sqrt hfrequency.le, Real.sq_sqrt hT.le]

/-- Full normalized broadened collision sum on `mode 0 = mode 1`, using the
actual decay-channel mismatch. -/
def positiveRepeatedZeroOneBroadenedInteractionWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (T : Real) : Real := by
  classical
  exact ∑ k, ∑ q,
    if IsPositiveOrderedTriple m ![k, k, q] then
      harmonicOrderedNormalizedInteractionWeight m ![k, k, q] *
        normalizedFiniteTimeResonanceKernel
          (orderedThreeWaveMismatch m decayInteractionSign ![k, k, q]) T
    else 0

/-- Full normalized broadened collision sum on `mode 0 = mode 2`. -/
def positiveRepeatedZeroTwoBroadenedInteractionWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (T : Real) : Real := by
  classical
  exact ∑ k, ∑ q,
    if IsPositiveOrderedTriple m ![k, q, k] then
      harmonicOrderedNormalizedInteractionWeight m ![k, q, k] *
        normalizedFiniteTimeResonanceKernel
          (orderedThreeWaveMismatch m decayInteractionSign ![k, q, k]) T
    else 0

/-- The first broadened equality-plane weight is nonnegative. -/
theorem positiveRepeatedZeroOneBroadenedInteractionWeight_nonneg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) (T : Real) :
    0 <= positiveRepeatedZeroOneBroadenedInteractionWeight m T := by
  classical
  unfold positiveRepeatedZeroOneBroadenedInteractionWeight
  apply Finset.sum_nonneg
  intro k _hk
  apply Finset.sum_nonneg
  intro q _hq
  split_ifs
  · exact mul_nonneg
      (harmonicOrderedNormalizedInteractionWeight_nonneg m ![k, k, q])
      (normalizedFiniteTimeResonanceKernel_nonneg
        (orderedThreeWaveMismatch m decayInteractionSign ![k, k, q]) T)
  · rfl

/-- The second broadened equality-plane weight is nonnegative. -/
theorem positiveRepeatedZeroTwoBroadenedInteractionWeight_nonneg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) (T : Real) :
    0 <= positiveRepeatedZeroTwoBroadenedInteractionWeight m T := by
  classical
  unfold positiveRepeatedZeroTwoBroadenedInteractionWeight
  apply Finset.sum_nonneg
  intro k _hk
  apply Finset.sum_nonneg
  intro q _hq
  split_ifs
  · exact mul_nonneg
      (harmonicOrderedNormalizedInteractionWeight_nonneg m ![k, q, k])
      (normalizedFiniteTimeResonanceKernel_nonneg
        (orderedThreeWaveMismatch m decayInteractionSign ![k, q, k]) T)
  · rfl

/-- Permutation symmetry and the two exact mismatch reductions identify the
two broadened parent-child planes. -/
theorem positiveRepeatedZeroTwoBroadenedInteractionWeight_eq_zeroOne
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) (T : Real) :
    positiveRepeatedZeroTwoBroadenedInteractionWeight m T =
      positiveRepeatedZeroOneBroadenedInteractionWeight m T := by
  classical
  unfold positiveRepeatedZeroTwoBroadenedInteractionWeight
    positiveRepeatedZeroOneBroadenedInteractionWeight
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro q _hq
  rw [isPositive_repeated_zero_two_iff_zero_one]
  split_ifs
  · rw [harmonicOrderedNormalizedInteractionWeight_repeated_zero_two_eq]
    rw [orderedThreeWaveMismatch_decay_eq_neg_one_of_zero_eq_two
      m ![k, q, k] (by simp)]
    rw [orderedThreeWaveMismatch_decay_eq_neg_two_of_zero_eq_one
      m ![k, k, q] (by simp)]
    simp
  · rfl

/-- Explicit volume-uniform `O(T^{-1/2})` bound for the first full equality
plane on the frozen iid support. -/
theorem iid_positiveRepeatedZeroOneBroadenedInteractionWeight_div_volume_le
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    {T : Real} (hT : 0 < T) :
    positiveRepeatedZeroOneBroadenedInteractionWeight
        (ensemble.restrictPositiveMass (N := N) omega) T / (N : Real) <=
      5 / (2 * Real.pi * Real.sqrt T) := by
  classical
  let m := ensemble.restrictPositiveMass (N := N) omega
  let positive := orderedPositiveModeIndices m
  let C := 5 / (4 * Real.pi * Real.sqrt T)
  have hC : 0 <= C := by positivity
  have hsum : positiveRepeatedZeroOneBroadenedInteractionWeight m T <=
      C * (∑ q ∈ positive,
        (Real.sqrt (orderedModeFrequency (harmonicHermitian m) q))⁻¹) := by
    unfold positiveRepeatedZeroOneBroadenedInteractionWeight
    calc
      (∑ k, ∑ q,
        if IsPositiveOrderedTriple m ![k, k, q] then
          harmonicOrderedNormalizedInteractionWeight m ![k, k, q] *
            normalizedFiniteTimeResonanceKernel
              (orderedThreeWaveMismatch m decayInteractionSign ![k, k, q]) T
        else 0) <=
          ∑ k, ∑ q, if q ∈ positive then
            C * repeatedCubicCoefficient
              (ArchonPhysics.HarmonicNormalizedEdgeFrame.harmonicNormalizedEdgeFrame m)
              k q ^ 2 *
                (Real.sqrt
                  (orderedModeFrequency (harmonicHermitian m) q))⁻¹
            else 0 := by
        apply Finset.sum_le_sum
        intro k _hk
        apply Finset.sum_le_sum
        intro q _hq
        by_cases hpositive : IsPositiveOrderedTriple m ![k, k, q]
        · rw [if_pos hpositive]
          have hqpositive : q ∈ positive := hpositive 2
          rw [if_pos hqpositive]
          have hfrequency : 0 <
              orderedModeFrequency (harmonicHermitian m) q :=
            (mem_orderedPositiveModeIndices_iff m q).mp hqpositive
          rw [orderedThreeWaveMismatch_decay_eq_neg_two_of_zero_eq_one
            m ![k, k, q] (by simp),
            normalizedFiniteTimeResonanceKernel_neg]
          rw [harmonicOrderedNormalizedInteractionWeight_repeated_zero_one_eq]
          have hk0 := harmonicActiveNormalizedCoefficient_nonneg m k
          have hq0 := harmonicActiveNormalizedCoefficient_nonneg m q
          have hkb := harmonicActiveNormalizedCoefficient_le_half_ceiling
            m (Real.sqrt 5)
              (fun j => iid_orderedModeFrequency_harmonic_le_sqrt_five
                ensemble omega j) k
          have hqbase := abs_activeOrderedEigenvalue_mul_inv_two_frequency_le
            m q
          change |harmonicActiveNormalizedCoefficient m q| <=
            orderedModeFrequency (harmonicHermitian m) q / 2 at hqbase
          rw [abs_of_nonneg hq0] at hqbase
          have hcoef :
              harmonicActiveNormalizedCoefficient m k ^ 2 *
                  harmonicActiveNormalizedCoefficient m q <=
                (5 / 8 : Real) *
                  orderedModeFrequency (harmonicHermitian m) q := by
            have hkSq : harmonicActiveNormalizedCoefficient m k ^ 2 <=
                (Real.sqrt 5 / 2) ^ 2 :=
              pow_le_pow_left₀ hk0 hkb 2
            have hright : 0 <=
                orderedModeFrequency (harmonicHermitian m) q / 2 := by
              positivity
            calc
              harmonicActiveNormalizedCoefficient m k ^ 2 *
                  harmonicActiveNormalizedCoefficient m q <=
                  (Real.sqrt 5 / 2) ^ 2 *
                    (orderedModeFrequency (harmonicHermitian m) q / 2) :=
                mul_le_mul hkSq hqbase hq0 (sq_nonneg _)
              _ = (5 / 8 : Real) *
                  orderedModeFrequency (harmonicHermitian m) q := by
                nlinarith [Real.sq_sqrt (show (0 : Real) <= 5 by norm_num)]
          have hkernel :=
            frequency_mul_normalizedFiniteTimeResonanceKernel_le_invSqrt
              hfrequency hT
          have hkernel0 := normalizedFiniteTimeResonanceKernel_nonneg
            (orderedModeFrequency (harmonicHermitian m) q) T
          have hcubic := sq_nonneg
            (repeatedCubicCoefficient
              (ArchonPhysics.HarmonicNormalizedEdgeFrame.harmonicNormalizedEdgeFrame m)
              k q)
          calc
            harmonicActiveNormalizedCoefficient m k ^ 2 *
                  harmonicActiveNormalizedCoefficient m q *
                  repeatedCubicCoefficient
                    (ArchonPhysics.HarmonicNormalizedEdgeFrame.harmonicNormalizedEdgeFrame m)
                    k q ^ 2 *
                normalizedFiniteTimeResonanceKernel
                  (orderedModeFrequency (harmonicHermitian m) q) T <=
                ((5 / 8 : Real) *
                    orderedModeFrequency (harmonicHermitian m) q) *
                  repeatedCubicCoefficient
                    (ArchonPhysics.HarmonicNormalizedEdgeFrame.harmonicNormalizedEdgeFrame m)
                    k q ^ 2 *
                    normalizedFiniteTimeResonanceKernel
                      (orderedModeFrequency (harmonicHermitian m) q) T := by
              gcongr
            _ <= (5 / 8 : Real) *
                (2 / (Real.pi * Real.sqrt
                    (orderedModeFrequency (harmonicHermitian m) q) *
                    Real.sqrt T)) *
                  repeatedCubicCoefficient
                    (ArchonPhysics.HarmonicNormalizedEdgeFrame.harmonicNormalizedEdgeFrame m)
                    k q ^ 2 := by
              calc
                _ = (5 / 8 : Real) *
                    (orderedModeFrequency (harmonicHermitian m) q *
                      normalizedFiniteTimeResonanceKernel
                        (orderedModeFrequency (harmonicHermitian m) q) T) *
                      repeatedCubicCoefficient
                        (ArchonPhysics.HarmonicNormalizedEdgeFrame.harmonicNormalizedEdgeFrame m)
                        k q ^ 2 := by ring
                _ <= _ := by gcongr
            _ = C * repeatedCubicCoefficient
                (ArchonPhysics.HarmonicNormalizedEdgeFrame.harmonicNormalizedEdgeFrame m)
                k q ^ 2 *
                  (Real.sqrt
                    (orderedModeFrequency (harmonicHermitian m) q))⁻¹ := by
              dsimp [C]
              field_simp [Real.pi_ne_zero, (Real.sqrt_pos.2 hfrequency).ne',
                (Real.sqrt_pos.2 hT).ne']
              ring
        · rw [if_neg hpositive]
          split_ifs
          · positivity
          · rfl
      _ = ∑ q, if q ∈ positive then
          C * (∑ k, repeatedCubicCoefficient
            (ArchonPhysics.HarmonicNormalizedEdgeFrame.harmonicNormalizedEdgeFrame m)
            k q ^ 2) *
              (Real.sqrt
                (orderedModeFrequency (harmonicHermitian m) q))⁻¹ else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro q _hq
        by_cases hqpositive : q ∈ positive
        · simp only [if_pos hqpositive]
          rw [Finset.mul_sum, Finset.sum_mul]
        · simp [hqpositive]
      _ <= ∑ q, if q ∈ positive then
          C * 1 * (Real.sqrt
            (orderedModeFrequency (harmonicHermitian m) q))⁻¹ else 0 := by
        apply Finset.sum_le_sum
        intro q _hq
        by_cases hqpositive : q ∈ positive
        · rw [if_pos hqpositive, if_pos hqpositive]
          gcongr
          exact sum_harmonicRepeatedCubicCoefficient_sq_fixed_child_le_one m q
        · simp [hqpositive]
      _ = C * ∑ q ∈ positive,
          (Real.sqrt (orderedModeFrequency (harmonicHermitian m) q))⁻¹ := by
        simp [Finset.mul_sum]
  have hmoment :=
    iid_positiveOrderedFrequency_invSqrt_sum_div_volume_le_two
      (N := N) ensemble omega
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  calc
    positiveRepeatedZeroOneBroadenedInteractionWeight m T / (N : Real) <=
        (C * ∑ q ∈ positive,
          (Real.sqrt (orderedModeFrequency (harmonicHermitian m) q))⁻¹) /
            (N : Real) := div_le_div_of_nonneg_right hsum hN.le
    _ = C * ((∑ q ∈ positive,
          (Real.sqrt (orderedModeFrequency (harmonicHermitian m) q))⁻¹) /
            (N : Real)) := by ring
    _ <= C * 2 := mul_le_mul_of_nonneg_left hmoment hC
    _ = 5 / (2 * Real.pi * Real.sqrt T) := by
      dsimp [C]
      ring

/-- The same explicit bound for the second full equality plane. -/
theorem iid_positiveRepeatedZeroTwoBroadenedInteractionWeight_div_volume_le
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega)
    {T : Real} (hT : 0 < T) :
    positiveRepeatedZeroTwoBroadenedInteractionWeight
        (ensemble.restrictPositiveMass (N := N) omega) T / (N : Real) <=
      5 / (2 * Real.pi * Real.sqrt T) := by
  rw [positiveRepeatedZeroTwoBroadenedInteractionWeight_eq_zeroOne]
  exact iid_positiveRepeatedZeroOneBroadenedInteractionWeight_div_volume_le
    ensemble omega hT

/-- The explicit fractional ceiling tends to zero. -/
theorem repeatedParentChildFractionalCeiling_tendsto_zero :
    Tendsto (fun T : Real => 5 / (2 * Real.pi * Real.sqrt T))
      atTop (nhds 0) := by
  have hinv : Tendsto (fun T : Real => (Real.sqrt T)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have hconst : Tendsto (fun _T : Real => 5 / (2 * Real.pi))
      atTop (nhds (5 / (2 * Real.pi))) := tendsto_const_nhds
  convert hconst.mul hinv using 1
  · funext T
    ring
  · ring_nf

/-- The first full parent-child equality plane has vanishing normalized
broadened mass as observation time tends to infinity. -/
theorem iid_positiveRepeatedZeroOneBroadenedInteractionWeight_div_volume_tendsto_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega) :
    Tendsto
      (fun T : Real =>
        positiveRepeatedZeroOneBroadenedInteractionWeight
          (ensemble.restrictPositiveMass (N := N) omega) T / (N : Real))
      atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds repeatedParentChildFractionalCeiling_tendsto_zero
    (Eventually.of_forall fun T => ?_) ?_
  · exact div_nonneg
      (positiveRepeatedZeroOneBroadenedInteractionWeight_nonneg _ T)
      (Nat.cast_nonneg N)
  · filter_upwards [eventually_gt_atTop (0 : Real)] with T hT
    exact iid_positiveRepeatedZeroOneBroadenedInteractionWeight_div_volume_le
      ensemble omega hT

/-- The second full parent-child equality plane has the same vanishing
normalized broadened mass. -/
theorem iid_positiveRepeatedZeroTwoBroadenedInteractionWeight_div_volume_tendsto_zero
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega) :
    Tendsto
      (fun T : Real =>
        positiveRepeatedZeroTwoBroadenedInteractionWeight
          (ensemble.restrictPositiveMass (N := N) omega) T / (N : Real))
      atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds repeatedParentChildFractionalCeiling_tendsto_zero
    (Eventually.of_forall fun T => ?_) ?_
  · exact div_nonneg
      (positiveRepeatedZeroTwoBroadenedInteractionWeight_nonneg _ T)
      (Nat.cast_nonneg N)
  · filter_upwards [eventually_gt_atTop (0 : Real)] with T hT
    exact iid_positiveRepeatedZeroTwoBroadenedInteractionWeight_div_volume_le
      ensemble omega hT

end

end ArchonPhysics.RepeatedParentChildFractionalBroadeningDecay
