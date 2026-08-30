import ArchonPhysics.CanonicalIIDCoerciveActualExpectationCompleted
import ArchonPhysics.PhyslibFPUTActualClusterSourceSlotClosure

/-!
# Canonical iid coercive cluster expectation closure

This module instantiates the abstract block-factorization hierarchy used by
`PhyslibFPUTActualClusterSourceSlotClosure` on the continuous canonical iid
law.  The actual Bochner block moments differentiate to the actual full
alpha--beta insertion moments, so every two-cluster factorization defect has
an exact derivative and an exact finite-time integral formula.

The shell envelopes provide deterministic global bounds for both the defect
and its source.  These are domination / exceptional-event costs only.  No
smallness, decay, RPA, Markov closure, or kinetic conclusion is asserted.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveClusterExpectationClosure

open scoped BigOperators Matrix Topology Interval ENNReal

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationCompleted
open ArchonPhysics.CanonicalIIDCoerciveContinuousMomentFrontier
open ArchonPhysics.CanonicalIIDCoerciveExpectationHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.CanonicalIIDCoerciveSignedModalBlockHierarchy
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTActualClusterSourceSlotClosure
open ArchonPhysics.PhyslibFPUTHigherOrderClusterFactorizationPropagation
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory
open Set

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Canonical continuous-law factorization defect for two finite ordered
blocks. -/
def canonicalCoerciveClusterFactorizationDefect
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (time : Real) : Complex :=
  blockFactorizationDefect
    (canonicalSignedBlockBochnerIntegral (N := N)
      kappa beta g hbeta a entry) left right time

/-- Exact canonical continuous-law source of the two-block factorization
defect. -/
def canonicalCoerciveClusterFactorizationDefectSource
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (time : Real) : Complex :=
  blockFactorizationDefectSource
    (canonicalSignedBlockBochnerIntegral (N := N)
      kappa beta g hbeta a entry)
    (canonicalSignedBlockInsertionBochnerIntegral (N := N)
      kappa beta g hbeta a entry) left right time

/-- A deterministic global cost for the block factorization defect. -/
def canonicalClusterFactorizationDefectEnvelope
    (A : Real) (left right : Finset I) : Real :=
  canonicalSignedBlockEnvelope A (left ∪ right) +
    canonicalSignedBlockEnvelope A left *
      canonicalSignedBlockEnvelope A right

/-- A deterministic global cost for the full alpha--beta source of the block
factorization defect. -/
def canonicalClusterFactorizationDefectSourceEnvelope
    (A S : Real) (left right : Finset I) : Real :=
  canonicalSignedBlockInsertionEnvelope A S (left ∪ right) +
    (canonicalSignedBlockInsertionEnvelope A S left *
        canonicalSignedBlockEnvelope A right +
      canonicalSignedBlockEnvelope A left *
        canonicalSignedBlockInsertionEnvelope A S right)

theorem hasDerivAt_canonicalCoerciveClusterFactorizationDefect
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (time : Real) :
    HasDerivAt
      (canonicalCoerciveClusterFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right)
      (canonicalCoerciveClusterFactorizationDefectSource (N := N)
        kappa beta g hbeta a entry left right time) time := by
  apply hasDerivAt_blockFactorizationDefect
  intro block
  exact hasDerivAt_canonicalSignedBlockBochnerIntegral_actual
    hN ha0 ha1 kappa beta g hbeta entry hpositive block time

theorem norm_canonicalSignedBlockBochnerIntegral_le_envelope
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (time : Real) :
    ‖canonicalSignedBlockBochnerIntegral (N := N)
        kappa beta g hbeta a entry block time‖ ≤
      canonicalSignedBlockEnvelope
        (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta) block := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  have h := norm_integral_le_of_norm_le_const
    (μ := canonicalIIDMassPhaseEnsemble.probability)
    (f := fun omega : CanonicalSample =>
      canonicalSignedBlockObservable (N := N)
          kappa beta g hbeta a entry block (omega, time))
    (C := canonicalSignedBlockEnvelope
      (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta) block)
    (by
      filter_upwards [canonicalSignedBlockBounds_ae_allTime
        hN ha0 ha1 kappa beta g hbeta entry hpositive]
          with omega hbound
      exact (hbound time block).1)
  rw [Measure.real, canonicalIIDMassPhaseEnsemble.probability_univ] at h
  norm_num at h
  simpa [canonicalSignedBlockBochnerIntegral] using h

theorem norm_canonicalSignedBlockInsertionBochnerIntegral_le_envelope
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (time : Real) :
    ‖canonicalSignedBlockInsertionBochnerIntegral (N := N)
        kappa beta g hbeta a entry block time‖ ≤
      canonicalSignedBlockInsertionEnvelope
        (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta)
        (canonicalSignedSourceEnvelope N kappa beta g hbeta) block := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  have h := norm_integral_le_of_norm_le_const
    (μ := canonicalIIDMassPhaseEnsemble.probability)
    (f := fun omega : CanonicalSample =>
      canonicalSignedBlockInsertion (N := N)
          kappa beta g hbeta a entry block (omega, time))
    (C := canonicalSignedBlockInsertionEnvelope
      (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta)
      (canonicalSignedSourceEnvelope N kappa beta g hbeta) block)
    (by
      filter_upwards [canonicalSignedBlockBounds_ae_allTime
        hN ha0 ha1 kappa beta g hbeta entry hpositive]
          with omega hbound
      exact (hbound time block).2)
  rw [Measure.real, canonicalIIDMassPhaseEnsemble.probability_univ] at h
  norm_num at h
  simpa [canonicalSignedBlockInsertionBochnerIntegral] using h

theorem norm_canonicalCoerciveClusterFactorizationDefect_le_envelope
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (time : Real) :
    ‖canonicalCoerciveClusterFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right time‖ ≤
      canonicalClusterFactorizationDefectEnvelope
        (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta)
        left right := by
  unfold canonicalCoerciveClusterFactorizationDefect
    blockFactorizationDefect canonicalClusterFactorizationDefectEnvelope
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · exact norm_canonicalSignedBlockBochnerIntegral_le_envelope
      hN ha0 ha1 kappa beta g hbeta entry hpositive (left ∪ right) time
  · rw [norm_mul]
    exact mul_le_mul
      (norm_canonicalSignedBlockBochnerIntegral_le_envelope
        hN ha0 ha1 kappa beta g hbeta entry hpositive left time)
      (norm_canonicalSignedBlockBochnerIntegral_le_envelope
        hN ha0 ha1 kappa beta g hbeta entry hpositive right time)
      (norm_nonneg _) (by
        unfold canonicalSignedBlockEnvelope
        exact pow_nonneg (by
          linarith [canonicalSignedAmplitudeEnvelope_nonneg
            (N := N) kappa beta g hbeta]) _)

theorem norm_canonicalCoerciveClusterFactorizationDefectSource_le_envelope
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (time : Real) :
    ‖canonicalCoerciveClusterFactorizationDefectSource (N := N)
        kappa beta g hbeta a entry left right time‖ ≤
      canonicalClusterFactorizationDefectSourceEnvelope
        (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta)
        (canonicalSignedSourceEnvelope N kappa beta g hbeta)
        left right := by
  unfold canonicalCoerciveClusterFactorizationDefectSource
    blockFactorizationDefectSource
    canonicalClusterFactorizationDefectSourceEnvelope
  have hA := canonicalSignedAmplitudeEnvelope_nonneg
    (N := N) kappa beta g hbeta
  have hS := canonicalSignedSourceEnvelope_nonneg
    (N := N) kappa beta g hbeta
  have hblock (block : Finset I) : 0 ≤ canonicalSignedBlockEnvelope
      (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta) block := by
    unfold canonicalSignedBlockEnvelope
    exact pow_nonneg (by linarith) _
  have hinsertion (block : Finset I) : 0 ≤ canonicalSignedBlockInsertionEnvelope
      (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta)
      (canonicalSignedSourceEnvelope N kappa beta g hbeta) block := by
    unfold canonicalSignedBlockInsertionEnvelope
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hblock block)) hS
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · exact norm_canonicalSignedBlockInsertionBochnerIntegral_le_envelope
      hN ha0 ha1 kappa beta g hbeta entry hpositive (left ∪ right) time
  · apply (norm_add_le _ _).trans
    apply add_le_add
    · rw [norm_mul]
      exact mul_le_mul
        (norm_canonicalSignedBlockInsertionBochnerIntegral_le_envelope
          hN ha0 ha1 kappa beta g hbeta entry hpositive left time)
        (norm_canonicalSignedBlockBochnerIntegral_le_envelope
          hN ha0 ha1 kappa beta g hbeta entry hpositive right time)
        (norm_nonneg _) (hinsertion left)
    · rw [norm_mul]
      exact mul_le_mul
        (norm_canonicalSignedBlockBochnerIntegral_le_envelope
          hN ha0 ha1 kappa beta g hbeta entry hpositive left time)
        (norm_canonicalSignedBlockInsertionBochnerIntegral_le_envelope
          hN ha0 ha1 kappa beta g hbeta entry hpositive right time)
        (norm_nonneg _) (hblock left)

theorem stronglyMeasurable_canonicalSignedBlockBochnerIntegral
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) :
    StronglyMeasurable
      (canonicalSignedBlockBochnerIntegral (N := N)
        kappa beta g hbeta a entry block) := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  exact (measurable_canonicalSignedBlockObservable (N := N)
      kappa beta g hbeta a entry block).stronglyMeasurable.integral_prod_left'

theorem stronglyMeasurable_canonicalSignedBlockInsertionBochnerIntegral
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) :
    StronglyMeasurable
      (canonicalSignedBlockInsertionBochnerIntegral (N := N)
        kappa beta g hbeta a entry block) := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  exact (measurable_canonicalSignedBlockInsertion (N := N)
      kappa beta g hbeta a entry block).stronglyMeasurable.integral_prod_left'

theorem stronglyMeasurable_canonicalCoerciveClusterFactorizationDefectSource
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (left right : Finset I) :
    StronglyMeasurable
      (canonicalCoerciveClusterFactorizationDefectSource (N := N)
        kappa beta g hbeta a entry left right) := by
  unfold canonicalCoerciveClusterFactorizationDefectSource
    blockFactorizationDefectSource
  exact (stronglyMeasurable_canonicalSignedBlockInsertionBochnerIntegral
      kappa beta g hbeta a entry (left ∪ right)).sub
    (((stronglyMeasurable_canonicalSignedBlockInsertionBochnerIntegral
        kappa beta g hbeta a entry left).mul
      (stronglyMeasurable_canonicalSignedBlockBochnerIntegral
        kappa beta g hbeta a entry right)).add
    ((stronglyMeasurable_canonicalSignedBlockBochnerIntegral
        kappa beta g hbeta a entry left).mul
      (stronglyMeasurable_canonicalSignedBlockInsertionBochnerIntegral
        kappa beta g hbeta a entry right)))

theorem intervalIntegrable_canonicalCoerciveClusterFactorizationDefectSource
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (time : Real) :
    IntervalIntegrable
      (canonicalCoerciveClusterFactorizationDefectSource (N := N)
        kappa beta g hbeta a entry left right) volume 0 time := by
  rw [intervalIntegrable_iff']
  have hvolume : volume (uIcc 0 time) < ∞ := by
    rw [Real.volume_interval]
    exact ENNReal.ofReal_lt_top
  apply IntegrableOn.of_bound hvolume
    ((stronglyMeasurable_canonicalCoerciveClusterFactorizationDefectSource
      kappa beta g hbeta a entry left right).aestronglyMeasurable.restrict)
    (canonicalClusterFactorizationDefectSourceEnvelope
      (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta)
      (canonicalSignedSourceEnvelope N kappa beta g hbeta) left right)
  filter_upwards with s
  exact norm_canonicalCoerciveClusterFactorizationDefectSource_le_envelope
    hN ha0 ha1 kappa beta g hbeta entry hpositive left right s

/-- Exact FTC representation of the continuous canonical factorization
defect.  This is an identity, not a decay estimate. -/
theorem canonicalCoerciveClusterFactorizationDefect_eq_initial_add_integral
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (time : Real) :
    canonicalCoerciveClusterFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right time =
      canonicalCoerciveClusterFactorizationDefect (N := N)
          kappa beta g hbeta a entry left right 0 +
        ∫ s in 0..time,
          canonicalCoerciveClusterFactorizationDefectSource (N := N)
            kappa beta g hbeta a entry left right s := by
  let F := canonicalCoerciveClusterFactorizationDefect (N := N)
    kappa beta g hbeta a entry left right
  let F' := canonicalCoerciveClusterFactorizationDefectSource (N := N)
    kappa beta g hbeta a entry left right
  have hderiv : ∀ s, HasDerivAt F (F' s) s := fun s =>
    hasDerivAt_canonicalCoerciveClusterFactorizationDefect
      hN ha0 ha1 kappa beta g hbeta entry hpositive left right s
  have hderivEq : deriv F = F' := by
    funext s
    exact (hderiv s).deriv
  have hint : IntervalIntegrable F' volume 0 time :=
    intervalIntegrable_canonicalCoerciveClusterFactorizationDefectSource
      hN ha0 ha1 kappa beta g hbeta entry hpositive left right time
  have hintDeriv : IntervalIntegrable (deriv F) volume 0 time := by
    rw [hderivEq]
    exact hint
  have hFTC := intervalIntegral.integral_deriv_eq_sub
    (f := F) (a := 0) (b := time)
    (fun s _hs => (hderiv s).differentiableAt) hintDeriv
  rw [hderivEq] at hFTC
  change F time = F 0 + ∫ s in 0..time, F' s
  calc
    F time = F 0 + (F time - F 0) := by ring
    _ = F 0 + ∫ s in 0..time, F' s := by rw [hFTC]

end

end ArchonPhysics.CanonicalIIDCoerciveClusterExpectationClosure
