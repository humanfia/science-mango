import ArchonPhysics.CanonicalIIDCoerciveParentDistinctChildRepeatedClosure

/-!
# Aggregate IPR control of the parent-distinct child-repeated sector

The pointwise hypothesis `forall k, IPR k <= rho` is stronger than the
parent-distinct collision sum requires.  Parseval shows that the natural
quantity is instead the root-averaged off-diagonal repeated-cubic mass

`N⁻¹ * sum_k sum_{q != k} |sum_j u_k(j)^2 u_q(j)|^2`.

This file derives the parent-distinct kinetic estimate directly from that
aggregate.  It also bounds the aggregate by the mean IPR, giving a second
closure criterion that is strictly weaker than a uniform modewise IPR bound.
Neither aggregate is asserted to vanish for the canonical random-mass chain.

Orthogonality alone only gives an `O(1)` mean-IPR ceiling.  A concrete
rational two-mode orthonormal frame has strictly positive off-diagonal mean,
so even cancellation of the all-equal term is not a formal consequence of
orthogonality.  The final obstruction theorem records this without importing
an RPA or delocalization conclusion.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveParentDistinctAggregateIPRBound

open scoped BigOperators Matrix

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionSoftLegBound
open ArchonPhysics.CanonicalIIDCoerciveParentDistinctChildRepeatedClosure
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.RepeatedModeTupleInteractionBound
open ArchonPhysics.ResonanceKernelLipschitz
open ArchonPhysics.UniformCollisionDensityTransfer
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open Filter

noncomputable section

/-! ## Abstract root and aggregate Parseval quantities -/

variable {mode bond : Type*} [Fintype mode] [DecidableEq mode]
  [Fintype bond]

/-- Repeated-cubic mass for one root mode after deleting the all-equal
coefficient `q = k`. -/
def rootOffDiagonalRepeatedCubicMass
    (u : mode -> bond -> Real) (k : mode) : Real :=
  ∑ q, if q ≠ k then repeatedCubicCoefficient u k q ^ 2 else 0

/-- Total off-diagonal repeated-cubic mass. -/
def offDiagonalRepeatedCubicMass (u : mode -> bond -> Real) : Real :=
  ∑ k, rootOffDiagonalRepeatedCubicMass u k

/-- Natural root-mode average of the off-diagonal repeated-cubic mass. -/
def meanOffDiagonalRepeatedCubicMass
    (u : mode -> bond -> Real) : Real :=
  offDiagonalRepeatedCubicMass u / (Fintype.card mode : Real)

/-- Natural root-mode average of the inverse-participation ratios. -/
def meanInverseParticipationRatio
    (u : mode -> bond -> Real) : Real :=
  (∑ k, inverseParticipationRatio u k) /
    (Fintype.card mode : Real)

theorem rootOffDiagonalRepeatedCubicMass_nonneg
    (u : mode -> bond -> Real) (k : mode) :
    0 <= rootOffDiagonalRepeatedCubicMass u k := by
  unfold rootOffDiagonalRepeatedCubicMass
  positivity

theorem offDiagonalRepeatedCubicMass_nonneg
    (u : mode -> bond -> Real) :
    0 <= offDiagonalRepeatedCubicMass u := by
  unfold offDiagonalRepeatedCubicMass
  exact Finset.sum_nonneg fun k _hk =>
    rootOffDiagonalRepeatedCubicMass_nonneg u k

/-- Rootwise Parseval bound after deleting the diagonal coefficient. -/
theorem rootOffDiagonalRepeatedCubicMass_le_ipr
    (u : mode -> bond -> Real)
    (hcard : Fintype.card mode = Fintype.card bond)
    (horth : forall k q,
      ∑ j, u k j * u q j = if k = q then 1 else 0)
    (k : mode) :
    rootOffDiagonalRepeatedCubicMass u k <=
      inverseParticipationRatio u k := by
  unfold rootOffDiagonalRepeatedCubicMass
  calc
    (∑ q, if q ≠ k then repeatedCubicCoefficient u k q ^ 2 else 0) <=
        ∑ q, repeatedCubicCoefficient u k q ^ 2 := by
      apply Finset.sum_le_sum
      intro q _hq
      split_ifs
      · exact le_rfl
      · positivity
    _ = inverseParticipationRatio u k :=
      sum_repeatedCubicCoefficient_sq_eq_inverseParticipationRatio
        u hcard horth k

/-- Averaging over the root mode replaces the uniform IPR ceiling by the
strictly weaker mean IPR. -/
theorem meanOffDiagonalRepeatedCubicMass_le_meanIPR
    [Nonempty mode] (u : mode -> bond -> Real)
    (hcard : Fintype.card mode = Fintype.card bond)
    (horth : forall k q,
      ∑ j, u k j * u q j = if k = q then 1 else 0) :
    meanOffDiagonalRepeatedCubicMass u <=
      meanInverseParticipationRatio u := by
  have hcardpos : 0 < (Fintype.card mode : Real) := by
    exact_mod_cast Fintype.card_pos
  unfold meanOffDiagonalRepeatedCubicMass meanInverseParticipationRatio
    offDiagonalRepeatedCubicMass
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun k _hk =>
      rootOffDiagonalRepeatedCubicMass_le_ipr u hcard horth k) hcardpos.le

/-! ## Harmonic parent-distinct collision bound -/

/-- The off-diagonal repeated-cubic average of the canonical harmonic edge
frame. -/
def harmonicMeanOffDiagonalRepeatedCubicMass
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) : Real :=
  meanOffDiagonalRepeatedCubicMass (harmonicNormalizedEdgeFrame m)

/-- The mean IPR of the canonical harmonic edge frame. -/
def harmonicMeanInverseParticipationRatio
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) : Real :=
  meanInverseParticipationRatio (harmonicNormalizedEdgeFrame m)

/-- Static parent-distinct child-repeated interaction weight, before applying
the finite-time resonance kernel. -/
def positiveParentDistinctChildRepeatedInteractionWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) : Real := by
  classical
  exact ∑ k, ∑ q,
    if IsPositiveOrderedTriple m ![q, k, k] ∧ q ≠ k then
      harmonicOrderedNormalizedInteractionWeight m ![q, k, k]
    else 0

theorem positiveParentDistinctChildRepeatedInteractionWeight_nonneg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    0 <= positiveParentDistinctChildRepeatedInteractionWeight m := by
  classical
  unfold positiveParentDistinctChildRepeatedInteractionWeight
  apply Finset.sum_nonneg
  intro k _hk
  apply Finset.sum_nonneg
  intro q _hq
  split_ifs
  · exact harmonicOrderedNormalizedInteractionWeight_nonneg m _
  · exact le_rfl

/-- Per-root (equivalently per-volume) weight of the actual positive
parent-distinct child-repeated collision network.  This is the transparent
residual parameter that remains meaningful when localized and extended modes
coexist. -/
def harmonicMeanParentDistinctChildRepeatedInteractionWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) : Real :=
  positiveParentDistinctChildRepeatedInteractionWeight m / (N : Real)

theorem harmonicMeanParentDistinctChildRepeatedInteractionWeight_nonneg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    0 <= harmonicMeanParentDistinctChildRepeatedInteractionWeight m := by
  exact div_nonneg
    (positiveParentDistinctChildRepeatedInteractionWeight_nonneg m)
    (Nat.cast_nonneg N)

/-- Kernel height reduces the broadened parent-distinct sector to its exact
static off-diagonal interaction weight, without enlarging to the all-equal
plane. -/
theorem positiveParentDistinctChildRepeatedBroadenedInteractionWeight_le_static_height
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {T : Real} (hT : 0 < T) :
    positiveParentDistinctChildRepeatedBroadenedInteractionWeight m T <=
      positiveParentDistinctChildRepeatedInteractionWeight m *
        (T / (2 * Real.pi)) := by
  classical
  unfold positiveParentDistinctChildRepeatedBroadenedInteractionWeight
    positiveParentDistinctChildRepeatedInteractionWeight
  calc
    (∑ k, ∑ q,
      if IsPositiveOrderedTriple m ![q, k, k] ∧ q ≠ k then
        harmonicOrderedNormalizedInteractionWeight m ![q, k, k] *
          normalizedFiniteTimeResonanceKernel
            (orderedThreeWaveMismatch m decayInteractionSign ![q, k, k]) T
      else 0) <=
        ∑ k, ∑ q,
          (if IsPositiveOrderedTriple m ![q, k, k] ∧ q ≠ k then
            harmonicOrderedNormalizedInteractionWeight m ![q, k, k]
          else 0) * (T / (2 * Real.pi)) := by
      apply Finset.sum_le_sum
      intro k _hk
      apply Finset.sum_le_sum
      intro q _hq
      by_cases hkeep : IsPositiveOrderedTriple m ![q, k, k] ∧ q ≠ k
      · rw [if_pos hkeep, if_pos hkeep]
        exact mul_le_mul_of_nonneg_left
          (normalizedFiniteTimeResonanceKernel_le_height _ hT)
          (harmonicOrderedNormalizedInteractionWeight_nonneg m _)
      · simp [hkeep]
    _ = (∑ k, ∑ q,
          if IsPositiveOrderedTriple m ![q, k, k] ∧ q ≠ k then
            harmonicOrderedNormalizedInteractionWeight m ![q, k, k]
          else 0) * (T / (2 * Real.pi)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.sum_mul]

/-- At kinetic time, the exact deterministic residual is controlled by the
actual mode-averaged parent-distinct collision-network weight.  No IPR,
delocalization, RPA, or random-mass decay hypothesis enters this inequality. -/
theorem physicalCoupling_sq_mul_parentDistinct_at_kineticTime_le_meanInteractionWeight
    {N : Nat} [NeZero N] (kappa g tau : Real)
    (m : Lattice.PositiveMassConfig N)
    (htau : 0 < tau) (hg : g ≠ 0) :
    (kappa * g) ^ 2 *
        (positiveParentDistinctChildRepeatedBroadenedInteractionWeight
          m (tau / g ^ 2) / (N : Real)) <=
      kappa ^ 2 * (tau / (2 * Real.pi) *
        harmonicMeanParentDistinctChildRepeatedInteractionWeight m) := by
  have htime : 0 < tau / g ^ 2 := div_pos htau (sq_pos_of_ne_zero hg)
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hbound :
      positiveParentDistinctChildRepeatedBroadenedInteractionWeight
            m (tau / g ^ 2) / (N : Real) <=
        ((tau / g ^ 2) / (2 * Real.pi)) *
          harmonicMeanParentDistinctChildRepeatedInteractionWeight m := by
    calc
      positiveParentDistinctChildRepeatedBroadenedInteractionWeight
            m (tau / g ^ 2) / (N : Real) <=
          (positiveParentDistinctChildRepeatedInteractionWeight m *
            ((tau / g ^ 2) / (2 * Real.pi))) / (N : Real) :=
        div_le_div_of_nonneg_right
          (positiveParentDistinctChildRepeatedBroadenedInteractionWeight_le_static_height
            m htime) hN.le
      _ = ((tau / g ^ 2) / (2 * Real.pi)) *
          harmonicMeanParentDistinctChildRepeatedInteractionWeight m := by
        unfold harmonicMeanParentDistinctChildRepeatedInteractionWeight
        ring
  have hgsq : 0 <= g ^ 2 := sq_nonneg g
  have hkappa : 0 <= kappa ^ 2 := sq_nonneg kappa
  calc
    (kappa * g) ^ 2 *
          (positiveParentDistinctChildRepeatedBroadenedInteractionWeight
            m (tau / g ^ 2) / (N : Real)) =
        kappa ^ 2 * (g ^ 2 *
          (positiveParentDistinctChildRepeatedBroadenedInteractionWeight
            m (tau / g ^ 2) / (N : Real))) := by ring
    _ <= kappa ^ 2 * (g ^ 2 *
        (((tau / g ^ 2) / (2 * Real.pi)) *
          harmonicMeanParentDistinctChildRepeatedInteractionWeight m)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbound hgsq) hkappa
    _ = kappa ^ 2 * (tau / (2 * Real.pi) *
        harmonicMeanParentDistinctChildRepeatedInteractionWeight m) := by
      field_simp [hg]

/-- One repeated child-pair vertex is bounded by the frequency ceiling times
its root/off-diagonal repeated-cubic coefficient. -/
theorem harmonicParentDistinctRepeatedWeight_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (ceiling : Real) (hceiling : 0 <= ceiling)
    (hfrequency : forall k,
      orderedModeFrequency (harmonicHermitian m) k <= ceiling)
    (k q : OrderedModeIndex N) :
    harmonicOrderedNormalizedInteractionWeight m ![q, k, k] <=
      (ceiling / 2) ^ 3 *
        repeatedCubicCoefficient (harmonicNormalizedEdgeFrame m) k q ^ 2 := by
  rw [harmonicOrderedNormalizedInteractionWeight_repeated_one_two_eq,
    harmonicOrderedNormalizedInteractionWeight_repeated_zero_one_eq]
  have hk0 := harmonicActiveNormalizedCoefficient_nonneg m k
  have hq0 := harmonicActiveNormalizedCoefficient_nonneg m q
  have hkb := harmonicActiveNormalizedCoefficient_le_half_ceiling
    m ceiling hfrequency k
  have hqb := harmonicActiveNormalizedCoefficient_le_half_ceiling
    m ceiling hfrequency q
  have hhalf : 0 <= ceiling / 2 := div_nonneg hceiling (by norm_num)
  have hcoefficient :
      harmonicActiveNormalizedCoefficient m k ^ 2 *
          harmonicActiveNormalizedCoefficient m q <=
        (ceiling / 2) ^ 3 := by
    calc
      harmonicActiveNormalizedCoefficient m k ^ 2 *
          harmonicActiveNormalizedCoefficient m q <=
          (ceiling / 2) ^ 2 * (ceiling / 2) := by
        exact mul_le_mul
          (pow_le_pow_left₀ hk0 hkb 2) hqb hq0 (sq_nonneg _)
      _ = (ceiling / 2) ^ 3 := by ring
  exact mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg _)

/-- Exact aggregate replacement for the uniform IPR hypothesis. -/
theorem positiveParentDistinctChildRepeatedInteractionWeight_div_volume_le_meanOffDiagonal
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (ceiling : Real) (hceiling : 0 <= ceiling)
    (hfrequency : forall k,
      orderedModeFrequency (harmonicHermitian m) k <= ceiling) :
    positiveParentDistinctChildRepeatedInteractionWeight m / (N : Real) <=
      (ceiling / 2) ^ 3 *
        harmonicMeanOffDiagonalRepeatedCubicMass m := by
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hstatic : positiveParentDistinctChildRepeatedInteractionWeight m <=
      (ceiling / 2) ^ 3 *
        offDiagonalRepeatedCubicMass (harmonicNormalizedEdgeFrame m) := by
    classical
    unfold positiveParentDistinctChildRepeatedInteractionWeight
      offDiagonalRepeatedCubicMass rootOffDiagonalRepeatedCubicMass
    calc
      (∑ k, ∑ q,
        if IsPositiveOrderedTriple m ![q, k, k] ∧ q ≠ k then
          harmonicOrderedNormalizedInteractionWeight m ![q, k, k]
        else 0) <=
          ∑ k, ∑ q,
            if q ≠ k then
              (ceiling / 2) ^ 3 *
                repeatedCubicCoefficient
                  (harmonicNormalizedEdgeFrame m) k q ^ 2
            else 0 := by
        apply Finset.sum_le_sum
        intro k _hk
        apply Finset.sum_le_sum
        intro q _hq
        by_cases hpositive : IsPositiveOrderedTriple m ![q, k, k]
        · by_cases hdistinct : q ≠ k
          · rw [if_pos ⟨hpositive, hdistinct⟩, if_pos hdistinct]
            exact harmonicParentDistinctRepeatedWeight_le
              m ceiling hceiling hfrequency k q
          · simp [hpositive, hdistinct]
        · by_cases hdistinct : q ≠ k
          · rw [if_neg (fun h => hpositive h.1), if_pos hdistinct]
            exact mul_nonneg
              (pow_nonneg (div_nonneg hceiling (by norm_num)) 3)
              (sq_nonneg _)
          · simp [hpositive, hdistinct]
      _ = (ceiling / 2) ^ 3 *
          ∑ k, ∑ q,
            if q ≠ k then
              repeatedCubicCoefficient
                (harmonicNormalizedEdgeFrame m) k q ^ 2
            else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _hq
        split_ifs <;> ring
  unfold harmonicMeanOffDiagonalRepeatedCubicMass
    meanOffDiagonalRepeatedCubicMass
  calc
    positiveParentDistinctChildRepeatedInteractionWeight m / (N : Real) <=
        ((ceiling / 2) ^ 3 *
          offDiagonalRepeatedCubicMass (harmonicNormalizedEdgeFrame m)) /
            (N : Real) := div_le_div_of_nonneg_right hstatic hN.le
    _ = (ceiling / 2) ^ 3 *
        (offDiagonalRepeatedCubicMass (harmonicNormalizedEdgeFrame m) /
          (Fintype.card (OrderedModeIndex N) : Real)) := by
      simp [Lattice.Site]
      ring

/-- The actual mode-averaged collision-network weight is controlled by the
off-diagonal cubic aggregate; the latter is only an upper bound, not an
asserted random-mass asymptotic. -/
theorem harmonicMeanParentDistinctChildRepeatedInteractionWeight_le_meanOffDiagonal
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (ceiling : Real) (hceiling : 0 <= ceiling)
    (hfrequency : forall k,
      orderedModeFrequency (harmonicHermitian m) k <= ceiling) :
    harmonicMeanParentDistinctChildRepeatedInteractionWeight m <=
      (ceiling / 2) ^ 3 *
        harmonicMeanOffDiagonalRepeatedCubicMass m := by
  unfold harmonicMeanParentDistinctChildRepeatedInteractionWeight
  exact
    positiveParentDistinctChildRepeatedInteractionWeight_div_volume_le_meanOffDiagonal
      m ceiling hceiling hfrequency

/-- Broadened parent-distinct bound using only the root-averaged
off-diagonal repeated-cubic mass. -/
theorem positiveParentDistinctChildRepeatedBroadened_div_volume_le_meanOffDiagonal
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (ceiling : Real) (hceiling : 0 <= ceiling)
    (hfrequency : forall k,
      orderedModeFrequency (harmonicHermitian m) k <= ceiling)
    {T : Real} (hT : 0 < T) :
    positiveParentDistinctChildRepeatedBroadenedInteractionWeight m T /
        (N : Real) <=
      (T / (2 * Real.pi)) * ((ceiling / 2) ^ 3 *
        harmonicMeanOffDiagonalRepeatedCubicMass m) := by
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hheight : 0 <= T / (2 * Real.pi) :=
    div_nonneg hT.le (mul_nonneg zero_le_two Real.pi_pos.le)
  calc
    positiveParentDistinctChildRepeatedBroadenedInteractionWeight m T /
          (N : Real) <=
        (positiveParentDistinctChildRepeatedInteractionWeight m *
          (T / (2 * Real.pi))) / (N : Real) :=
      div_le_div_of_nonneg_right
        (positiveParentDistinctChildRepeatedBroadenedInteractionWeight_le_static_height
          m hT) hN.le
    _ = (T / (2 * Real.pi)) *
        (positiveParentDistinctChildRepeatedInteractionWeight m /
          (N : Real)) := by ring
    _ <= (T / (2 * Real.pi)) * ((ceiling / 2) ^ 3 *
        harmonicMeanOffDiagonalRepeatedCubicMass m) :=
      mul_le_mul_of_nonneg_left
        (positiveParentDistinctChildRepeatedInteractionWeight_div_volume_le_meanOffDiagonal
          m ceiling hceiling hfrequency) hheight

/-- The aggregate off-diagonal criterion is bounded by the mean IPR, still
without a uniform modewise hypothesis. -/
theorem harmonicMeanOffDiagonalRepeatedCubicMass_le_meanIPR
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    harmonicMeanOffDiagonalRepeatedCubicMass m <=
      harmonicMeanInverseParticipationRatio m := by
  exact meanOffDiagonalRepeatedCubicMass_le_meanIPR
    (harmonicNormalizedEdgeFrame m)
    (by simp [HarmonicOrderedModeIndex])
    (harmonicNormalizedEdgeFrame_orthonormal_unconditional m)

/-- Kinetic-time closure under the weaker mean-IPR condition. -/
theorem physicalCoupling_sq_mul_parentDistinct_at_kineticTime_le_of_meanIPR
    {N : Nat} [NeZero N] (kappa g tau : Real)
    (m : Lattice.PositiveMassConfig N)
    (ceiling : Real) (hceiling : 0 <= ceiling)
    (hfrequency : forall k,
      orderedModeFrequency (harmonicHermitian m) k <= ceiling)
    (htau : 0 < tau) (hg : g ≠ 0) :
    (kappa * g) ^ 2 *
        (positiveParentDistinctChildRepeatedBroadenedInteractionWeight
          m (tau / g ^ 2) / (N : Real)) <=
      kappa ^ 2 * (tau / (2 * Real.pi) * ((ceiling / 2) ^ 3 *
        harmonicMeanInverseParticipationRatio m)) := by
  have htime : 0 < tau / g ^ 2 := div_pos htau (sq_pos_of_ne_zero hg)
  have hoff :=
    positiveParentDistinctChildRepeatedBroadened_div_volume_le_meanOffDiagonal
      m ceiling hceiling hfrequency htime
  have hmean := harmonicMeanOffDiagonalRepeatedCubicMass_le_meanIPR m
  have hbound :
      positiveParentDistinctChildRepeatedBroadenedInteractionWeight
            m (tau / g ^ 2) / (N : Real) <=
        ((tau / g ^ 2) / (2 * Real.pi)) *
          ((ceiling / 2) ^ 3 *
            harmonicMeanInverseParticipationRatio m) := by
    calc
      _ <= ((tau / g ^ 2) / (2 * Real.pi)) *
          ((ceiling / 2) ^ 3 *
            harmonicMeanOffDiagonalRepeatedCubicMass m) := hoff
      _ <= ((tau / g ^ 2) / (2 * Real.pi)) *
          ((ceiling / 2) ^ 3 *
            harmonicMeanInverseParticipationRatio m) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmean
            (pow_nonneg (div_nonneg hceiling (by norm_num)) 3))
          (div_nonneg htime.le (mul_nonneg zero_le_two Real.pi_pos.le))
  have hgsq : 0 <= g ^ 2 := sq_nonneg g
  have hkappa : 0 <= kappa ^ 2 := sq_nonneg kappa
  calc
    (kappa * g) ^ 2 *
          (positiveParentDistinctChildRepeatedBroadenedInteractionWeight
            m (tau / g ^ 2) / (N : Real)) =
        kappa ^ 2 * (g ^ 2 *
          (positiveParentDistinctChildRepeatedBroadenedInteractionWeight
            m (tau / g ^ 2) / (N : Real))) := by ring
    _ <= kappa ^ 2 * (g ^ 2 *
        (((tau / g ^ 2) / (2 * Real.pi)) *
          ((ceiling / 2) ^ 3 *
            harmonicMeanInverseParticipationRatio m))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbound hgsq) hkappa
    _ = kappa ^ 2 * (tau / (2 * Real.pi) * ((ceiling / 2) ^ 3 *
        harmonicMeanInverseParticipationRatio m)) := by
      field_simp [hg]

/-! ## Canonical iid sequence with a transparent averaged collision condition -/

/-- Canonical averaged parent-distinct collision-network weight.  No decay
of this quantity is asserted for the iid mass ensemble. -/
def canonicalParentDistinctChildRepeatedMeanInteractionWeight
    (n : Nat) (omega : RandomEnsemble.SampleSpace) : Real :=
  harmonicMeanParentDistinctChildRepeatedInteractionWeight
    (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
      (N := n + 2) omega)

theorem canonicalParentDistinctChildRepeatedMeanInteractionWeight_nonneg
    (n : Nat) (omega : RandomEnsemble.SampleSpace) :
    0 <= canonicalParentDistinctChildRepeatedMeanInteractionWeight n omega := by
  exact harmonicMeanParentDistinctChildRepeatedInteractionWeight_nonneg _

/-- Canonical kinetic-time bound in terms of the actual mode-averaged
collision-network weight, with no whole-spectrum delocalization premise. -/
theorem canonical_physicalCoupling_sq_mul_parentDistinct_at_kineticTime_le_meanInteractionWeight
    (n : Nat) (omega : RandomEnsemble.SampleSpace)
    (kappa g tau : Real) (htau : 0 < tau) (hg : g ≠ 0) :
    (kappa * g) ^ 2 *
        canonicalParentDistinctChildRepeatedCollisionBudget
          n omega (tau / g ^ 2) <=
      kappa ^ 2 * (tau / (2 * Real.pi) *
        canonicalParentDistinctChildRepeatedMeanInteractionWeight n omega) := by
  simpa [canonicalParentDistinctChildRepeatedCollisionBudget,
    canonicalParentDistinctChildRepeatedMeanInteractionWeight] using
    (physicalCoupling_sq_mul_parentDistinct_at_kineticTime_le_meanInteractionWeight
      kappa g tau
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
        (N := n + 2) omega) htau hg)

/-- A vanishing actual averaged collision-network weight is sufficient for
the parent-distinct sector to vanish at kinetic time.  This premise is
explicit and is not advertised as a consequence of random mass or
orthogonality. -/
theorem canonical_parentDistinct_at_kineticTime_tendsto_zero_of_meanInteractionWeight
    (size : Nat -> Nat) (omega : RandomEnsemble.SampleSpace)
    (kappa tau : Real) (htau : 0 < tau)
    (g : Nat -> Real) (hg0 : forall n, g n ≠ 0)
    (hweight : Tendsto (fun n =>
      canonicalParentDistinctChildRepeatedMeanInteractionWeight
        (size n) omega) atTop (nhds 0)) :
    Tendsto (fun n =>
      (kappa * g n) ^ 2 *
        canonicalParentDistinctChildRepeatedCollisionBudget
          (size n) omega (tau / (g n) ^ 2)) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n =>
      mul_nonneg (sq_nonneg _) <|
        canonicalParentDistinctChildRepeatedCollisionBudget_nonneg
          (size n) omega _
  · exact Eventually.of_forall fun n =>
      canonical_physicalCoupling_sq_mul_parentDistinct_at_kineticTime_le_meanInteractionWeight
        (size n) omega kappa (g n) tau htau (hg0 n)
  · simpa using
      (tendsto_const_nhds.mul (tendsto_const_nhds.mul hweight))

/-! ## Orthogonality obstruction -/

/-- A rational two-mode orthonormal frame with nonzero off-diagonal repeated
cubic mass. -/
def rationalRotationFrame (k j : Fin 2) : Real :=
  if k = 0 then
    if j = 0 then 3 / 5 else 4 / 5
  else if j = 0 then 4 / 5 else -(3 / 5)

theorem rationalRotationFrame_orthonormal (k q : Fin 2) :
    (∑ j, rationalRotationFrame k j * rationalRotationFrame q j) =
      if k = q then 1 else 0 := by
  fin_cases k <;> fin_cases q <;>
    norm_num [rationalRotationFrame, Fin.sum_univ_two]

/-- The off-diagonal root average is a fixed positive number even though the
frame is exactly orthonormal. -/
theorem meanOffDiagonalRepeatedCubicMass_rationalRotationFrame :
    meanOffDiagonalRepeatedCubicMass rationalRotationFrame = 144 / 625 := by
  norm_num [meanOffDiagonalRepeatedCubicMass,
    offDiagonalRepeatedCubicMass, rootOffDiagonalRepeatedCubicMass,
    repeatedCubicCoefficient, rationalRotationFrame, Fin.sum_univ_two]

theorem meanOffDiagonalRepeatedCubicMass_rationalRotationFrame_pos :
    0 < meanOffDiagonalRepeatedCubicMass rationalRotationFrame := by
  rw [meanOffDiagonalRepeatedCubicMass_rationalRotationFrame]
  norm_num

/-- Consequently no theorem using only square-frame orthonormality can force
the parent-distinct aggregate to vanish identically. -/
theorem exists_orthonormalFrame_with_positive_meanOffDiagonalRepeatedMass :
    ∃ u : Fin 2 -> Fin 2 -> Real,
      (∀ k q, (∑ j, u k j * u q j) = if k = q then 1 else 0) ∧
      0 < meanOffDiagonalRepeatedCubicMass u := by
  exact ⟨rationalRotationFrame, rationalRotationFrame_orthonormal,
    meanOffDiagonalRepeatedCubicMass_rationalRotationFrame_pos⟩

/-- Block-diagonal replication of the rational frame.  It is localized in
two-dimensional cells and exists at every positive block count. -/
def replicatedRationalRotationFrame (blocks : Nat)
    (k j : Fin blocks × Fin 2) : Real :=
  if k.1 = j.1 then rationalRotationFrame k.2 j.2 else 0

theorem replicatedRationalRotationFrame_orthonormal
    (blocks : Nat) (k q : Fin blocks × Fin 2) :
    (∑ j, replicatedRationalRotationFrame blocks k j *
      replicatedRationalRotationFrame blocks q j) =
      if k = q then 1 else 0 := by
  rcases k with ⟨kb, ki⟩
  rcases q with ⟨qb, qi⟩
  by_cases hb : kb = qb
  · subst qb
    simp only [replicatedRationalRotationFrame, Fintype.sum_prod_type]
    simp [Prod.ext_iff]
    simpa [Fin.sum_univ_two] using rationalRotationFrame_orthonormal ki qi
  · simp [replicatedRationalRotationFrame, Fintype.sum_prod_type, hb,
      Prod.ext_iff]

theorem repeatedCubicCoefficient_replicatedRationalRotationFrame
    (blocks : Nat) (k q : Fin blocks × Fin 2) :
    repeatedCubicCoefficient (replicatedRationalRotationFrame blocks) k q =
      if k.1 = q.1 then repeatedCubicCoefficient rationalRotationFrame k.2 q.2
      else 0 := by
  rcases k with ⟨kb, ki⟩
  rcases q with ⟨qb, qi⟩
  by_cases hb : kb = qb
  · subst qb
    simp [repeatedCubicCoefficient, replicatedRationalRotationFrame,
      Fintype.sum_prod_type]
  · simp [repeatedCubicCoefficient, replicatedRationalRotationFrame,
      Fintype.sum_prod_type, hb]

theorem rootOffDiagonalRepeatedCubicMass_replicatedRationalRotationFrame
    (blocks : Nat) (k : Fin blocks × Fin 2) :
    rootOffDiagonalRepeatedCubicMass
        (replicatedRationalRotationFrame blocks) k =
      rootOffDiagonalRepeatedCubicMass rationalRotationFrame k.2 := by
  rcases k with ⟨kb, ki⟩
  unfold rootOffDiagonalRepeatedCubicMass
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single kb]
  · simp [repeatedCubicCoefficient_replicatedRationalRotationFrame,
      Prod.ext_iff]
  · intro b _hb hbne
    have hne : kb ≠ b := Ne.symm hbne
    simp [repeatedCubicCoefficient_replicatedRationalRotationFrame, hne]
  · simp

/-- Sharp volume obstruction: at every even dimension `2 * blocks`, an
exactly orthonormal localized frame has the same positive root-averaged
off-diagonal cubic mass.  Hence square-frame orthogonality, even after natural
root averaging, cannot imply any `1 / N` decay. -/
theorem meanOffDiagonalRepeatedCubicMass_replicatedRationalRotationFrame
    (blocks : Nat) [NeZero blocks] :
    meanOffDiagonalRepeatedCubicMass
        (replicatedRationalRotationFrame blocks) = 144 / 625 := by
  have hb : (blocks : Real) ≠ 0 := by
    exact_mod_cast NeZero.ne blocks
  unfold meanOffDiagonalRepeatedCubicMass offDiagonalRepeatedCubicMass
  simp_rw [rootOffDiagonalRepeatedCubicMass_replicatedRationalRotationFrame]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp [hb]
  norm_num [rootOffDiagonalRepeatedCubicMass, repeatedCubicCoefficient,
    rationalRotationFrame, Fin.sum_univ_two]
  ring

end

end ArchonPhysics.CanonicalIIDCoerciveParentDistinctAggregateIPRBound
