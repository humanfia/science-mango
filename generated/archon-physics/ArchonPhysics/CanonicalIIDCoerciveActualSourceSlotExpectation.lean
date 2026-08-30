import ArchonPhysics.CanonicalIIDCoerciveSourceSlotExpectationClosure

/-!
# Actual canonical iid quadratic/quartic source-slot expectations

This endpoint specializes the measurable source-slot closure to the two
actual force channels of the coercive alpha--beta Hamiltonian.  For every
fixed finite ordered cluster and every non-translation slot, the quadratic
and quartic slot observables and the corresponding mixed two-block
observables are Bochner integrable.  Their expectation factorization defects
have deterministic global costs depending only on the displayed finite
volume and shell parameters, never on the random sample.

Together with
`CanonicalIIDCoerciveClusterExpectationClosure`, this gives the concrete
continuous-law analogue of the source-slot resolution in
`PhyslibFPUTActualClusterSourceSlotClosure` and the potential split in
`PhyslibFPUTActualSourceSlotPotentialSplit`: the block defect has its exact
Hamiltonian derivative/FTC formula, while every resolved quadratic/quartic
one-slot expectation is legal and explicitly dominated.

The costs below are not decay estimates.  No RPA, independence, Markov,
nonresonance, or recollision suppression is asserted; all exceptional and
resonant sectors remain in the exact defects.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualSourceSlotExpectation

open scoped BigOperators Matrix Topology

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationCompleted
open ArchonPhysics.CanonicalIIDCoerciveClusterExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveContinuousMomentFrontier
open ArchonPhysics.CanonicalIIDCoercivePotentialChannelExpectation
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.CanonicalIIDCoerciveSourceSlotExpectationClosure
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Mixed expectation with the source slot on the left cluster. -/
def canonicalLeftPotentialSourceSlotMixedMoment
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a sourceKappa sourceBeta sourceG : Real)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (slot : I) (time : Real) : Complex :=
  ∫ omega,
      canonicalPotentialSourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a
          sourceKappa sourceBeta sourceG entry left slot (omega, time) *
        canonicalSignedBlockObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a entry right (omega, time)
    ∂canonicalIIDMassPhaseEnsemble.probability

/-- Mixed expectation with the source slot on the right cluster. -/
def canonicalRightPotentialSourceSlotMixedMoment
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a sourceKappa sourceBeta sourceG : Real)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (slot : I) (time : Real) : Complex :=
  ∫ omega,
      canonicalSignedBlockObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a entry left (omega, time) *
        canonicalPotentialSourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a
          sourceKappa sourceBeta sourceG entry right slot (omega, time)
    ∂canonicalIIDMassPhaseEnsemble.probability

/-- Quadratic left source-slot defect on the full alpha--beta flow. -/
def canonicalLeftQuadraticSourceSlotFactorizationDefect
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (slot : I) (time : Real) : Complex :=
  canonicalLeftPotentialSourceSlotFactorizationDefect (N := N)
    kappa beta g hbeta a kappa 0 g entry left right slot time

/-- Quartic left source-slot defect on the full alpha--beta flow. -/
def canonicalLeftQuarticSourceSlotFactorizationDefect
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (slot : I) (time : Real) : Complex :=
  canonicalLeftPotentialSourceSlotFactorizationDefect (N := N)
    kappa beta g hbeta a 0 beta g entry left right slot time

/-- Quadratic right source-slot defect on the full alpha--beta flow. -/
def canonicalRightQuadraticSourceSlotFactorizationDefect
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (slot : I) (time : Real) : Complex :=
  canonicalRightPotentialSourceSlotFactorizationDefect (N := N)
    kappa beta g hbeta a kappa 0 g entry left right slot time

/-- Quartic right source-slot defect on the full alpha--beta flow. -/
def canonicalRightQuarticSourceSlotFactorizationDefect
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (slot : I) (time : Real) : Complex :=
  canonicalRightPotentialSourceSlotFactorizationDefect (N := N)
    kappa beta g hbeta a 0 beta g entry left right slot time

theorem canonicalPotentialSourceSlotEnvelope_nonneg
    {A S : Real} (hA : 0 ≤ A) (hS : 0 ≤ S)
    (block : Finset I) (slot : I) :
    0 ≤ canonicalPotentialSourceSlotEnvelope A S block slot := by
  unfold canonicalPotentialSourceSlotEnvelope canonicalSignedBlockEnvelope
  exact mul_nonneg (pow_nonneg (by linarith) _) hS

theorem norm_canonicalPotentialSourceSlotBochnerIntegral_le_envelope
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (sourceKappa sourceBeta sourceG : Real)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (time : Real) :
    ‖canonicalPotentialSourceSlotBochnerIntegral (N := N)
        flowKappa flowBeta flowG hflowBeta a
        sourceKappa sourceBeta sourceG entry block slot time‖ ≤
      canonicalPotentialSourceSlotEnvelope
        (canonicalSignedAmplitudeEnvelope N
          flowKappa flowBeta flowG hflowBeta)
        (canonicalSignedPotentialChannelSourceEnvelope N
          sourceKappa sourceBeta sourceG
          (canonicalWeightedCoordinateEnvelope N
            flowKappa flowBeta flowG hflowBeta)) block slot := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  have h := norm_integral_le_of_norm_le_const
    (μ := canonicalIIDMassPhaseEnsemble.probability)
    (f := fun omega : CanonicalSample =>
      canonicalPotentialSourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
        sourceKappa sourceBeta sourceG entry block slot (omega, time))
    (C := canonicalPotentialSourceSlotEnvelope
      (canonicalSignedAmplitudeEnvelope N
        flowKappa flowBeta flowG hflowBeta)
      (canonicalSignedPotentialChannelSourceEnvelope N
        sourceKappa sourceBeta sourceG
        (canonicalWeightedCoordinateEnvelope N
          flowKappa flowBeta flowG hflowBeta)) block slot)
    (by
      filter_upwards [canonicalPotentialSourceSlotBounds_ae_allTime
        hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
          sourceKappa sourceBeta sourceG entry hpositive block slot]
          with omega hbound
      exact hbound time)
  rw [Measure.real, canonicalIIDMassPhaseEnsemble.probability_univ] at h
  norm_num at h
  simpa [canonicalPotentialSourceSlotBochnerIntegral] using h

theorem norm_canonicalLeftPotentialSourceSlotMixedMoment_le_envelope
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (sourceKappa sourceBeta sourceG : Real)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    ‖canonicalLeftPotentialSourceSlotMixedMoment (N := N)
        flowKappa flowBeta flowG hflowBeta a
        sourceKappa sourceBeta sourceG entry left right slot time‖ ≤
      canonicalPotentialSourceSlotEnvelope
          (canonicalSignedAmplitudeEnvelope N
            flowKappa flowBeta flowG hflowBeta)
          (canonicalSignedPotentialChannelSourceEnvelope N
            sourceKappa sourceBeta sourceG
            (canonicalWeightedCoordinateEnvelope N
              flowKappa flowBeta flowG hflowBeta)) left slot *
        canonicalSignedBlockEnvelope
          (canonicalSignedAmplitudeEnvelope N
            flowKappa flowBeta flowG hflowBeta) right := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  have h := norm_integral_le_of_norm_le_const
    (μ := canonicalIIDMassPhaseEnsemble.probability)
    (f := fun omega : CanonicalSample =>
      canonicalPotentialSourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a
          sourceKappa sourceBeta sourceG entry left slot (omega, time) *
        canonicalSignedBlockObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a entry right (omega, time))
    (C := canonicalPotentialSourceSlotEnvelope
        (canonicalSignedAmplitudeEnvelope N
          flowKappa flowBeta flowG hflowBeta)
        (canonicalSignedPotentialChannelSourceEnvelope N
          sourceKappa sourceBeta sourceG
          (canonicalWeightedCoordinateEnvelope N
            flowKappa flowBeta flowG hflowBeta)) left slot *
      canonicalSignedBlockEnvelope
        (canonicalSignedAmplitudeEnvelope N
          flowKappa flowBeta flowG hflowBeta) right)
    (by
      filter_upwards [canonicalPotentialSourceSlotBounds_ae_allTime
          hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
            sourceKappa sourceBeta sourceG entry hpositive left slot,
        canonicalSignedBlockBounds_ae_allTime
          hN ha0 ha1 flowKappa flowBeta flowG hflowBeta entry hpositive]
          with omega hslot hblock
      rw [norm_mul]
      exact mul_le_mul (hslot time) (hblock time right).1
        (norm_nonneg _)
        (canonicalPotentialSourceSlotEnvelope_nonneg
          (canonicalSignedAmplitudeEnvelope_nonneg
            (N := N) flowKappa flowBeta flowG hflowBeta)
          (canonicalSignedPotentialChannelSourceEnvelope_nonneg
            sourceKappa sourceBeta sourceG
            (canonicalWeightedCoordinateEnvelope N
              flowKappa flowBeta flowG hflowBeta)
            (canonicalWeightedCoordinateEnvelope_nonneg
              flowKappa flowBeta flowG hflowBeta)) left slot))
  rw [Measure.real, canonicalIIDMassPhaseEnsemble.probability_univ] at h
  norm_num at h
  simpa [canonicalLeftPotentialSourceSlotMixedMoment] using h

theorem norm_canonicalRightPotentialSourceSlotMixedMoment_le_envelope
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (sourceKappa sourceBeta sourceG : Real)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    ‖canonicalRightPotentialSourceSlotMixedMoment (N := N)
        flowKappa flowBeta flowG hflowBeta a
        sourceKappa sourceBeta sourceG entry left right slot time‖ ≤
      canonicalSignedBlockEnvelope
          (canonicalSignedAmplitudeEnvelope N
            flowKappa flowBeta flowG hflowBeta) left *
        canonicalPotentialSourceSlotEnvelope
          (canonicalSignedAmplitudeEnvelope N
            flowKappa flowBeta flowG hflowBeta)
          (canonicalSignedPotentialChannelSourceEnvelope N
            sourceKappa sourceBeta sourceG
            (canonicalWeightedCoordinateEnvelope N
              flowKappa flowBeta flowG hflowBeta)) right slot := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  have h := norm_integral_le_of_norm_le_const
    (μ := canonicalIIDMassPhaseEnsemble.probability)
    (f := fun omega : CanonicalSample =>
      canonicalSignedBlockObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a entry left (omega, time) *
        canonicalPotentialSourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a
          sourceKappa sourceBeta sourceG entry right slot (omega, time))
    (C := canonicalSignedBlockEnvelope
        (canonicalSignedAmplitudeEnvelope N
          flowKappa flowBeta flowG hflowBeta) left *
      canonicalPotentialSourceSlotEnvelope
        (canonicalSignedAmplitudeEnvelope N
          flowKappa flowBeta flowG hflowBeta)
        (canonicalSignedPotentialChannelSourceEnvelope N
          sourceKappa sourceBeta sourceG
          (canonicalWeightedCoordinateEnvelope N
            flowKappa flowBeta flowG hflowBeta)) right slot)
    (by
      filter_upwards [canonicalSignedBlockBounds_ae_allTime
          hN ha0 ha1 flowKappa flowBeta flowG hflowBeta entry hpositive,
        canonicalPotentialSourceSlotBounds_ae_allTime
          hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
            sourceKappa sourceBeta sourceG entry hpositive right slot]
          with omega hblock hslot
      rw [norm_mul]
      exact mul_le_mul (hblock time left).1 (hslot time)
        (norm_nonneg _)
        (by
          unfold canonicalSignedBlockEnvelope
          exact pow_nonneg (by
            linarith [canonicalSignedAmplitudeEnvelope_nonneg
              (N := N) flowKappa flowBeta flowG hflowBeta]) _))
  rw [Measure.real, canonicalIIDMassPhaseEnsemble.probability_univ] at h
  norm_num at h
  simpa [canonicalRightPotentialSourceSlotMixedMoment] using h

theorem norm_canonicalLeftPotentialSourceSlotFactorizationDefect_le_cost
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (sourceKappa sourceBeta sourceG : Real)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    ‖canonicalLeftPotentialSourceSlotFactorizationDefect (N := N)
        flowKappa flowBeta flowG hflowBeta a
        sourceKappa sourceBeta sourceG entry left right slot time‖ ≤
      canonicalLeftSourceSlotDefectCost
        (canonicalSignedAmplitudeEnvelope N
          flowKappa flowBeta flowG hflowBeta)
        (canonicalSignedPotentialChannelSourceEnvelope N
          sourceKappa sourceBeta sourceG
          (canonicalWeightedCoordinateEnvelope N
            flowKappa flowBeta flowG hflowBeta)) left right slot := by
  let A := canonicalSignedAmplitudeEnvelope N
    flowKappa flowBeta flowG hflowBeta
  let S := canonicalSignedPotentialChannelSourceEnvelope N
    sourceKappa sourceBeta sourceG
    (canonicalWeightedCoordinateEnvelope N
      flowKappa flowBeta flowG hflowBeta)
  have hmixed := norm_canonicalLeftPotentialSourceSlotMixedMoment_le_envelope
    hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      sourceKappa sourceBeta sourceG entry hpositive left right slot time
  have hslot := norm_canonicalPotentialSourceSlotBochnerIntegral_le_envelope
    hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      sourceKappa sourceBeta sourceG entry hpositive left slot time
  have hblock := norm_canonicalSignedBlockBochnerIntegral_le_envelope
    hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive right time
  unfold canonicalLeftPotentialSourceSlotMixedMoment at hmixed
  unfold canonicalLeftPotentialSourceSlotFactorizationDefect
    canonicalLeftSourceSlotDefectCost
  apply (norm_sub_le _ _).trans
  calc
    ‖∫ omega,
          canonicalPotentialSourceSlotObservable (N := N)
              flowKappa flowBeta flowG hflowBeta a
              sourceKappa sourceBeta sourceG entry left slot (omega, time) *
            canonicalSignedBlockObservable (N := N)
              flowKappa flowBeta flowG hflowBeta a entry right (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability‖ +
        ‖canonicalPotentialSourceSlotBochnerIntegral (N := N)
            flowKappa flowBeta flowG hflowBeta a
            sourceKappa sourceBeta sourceG entry left slot time *
          canonicalSignedBlockBochnerIntegral (N := N)
            flowKappa flowBeta flowG hflowBeta a entry right time‖
        ≤ canonicalPotentialSourceSlotEnvelope A S left slot *
            canonicalSignedBlockEnvelope A right +
          canonicalPotentialSourceSlotEnvelope A S left slot *
            canonicalSignedBlockEnvelope A right := by
      apply add_le_add hmixed
      rw [norm_mul]
      exact mul_le_mul hslot hblock (norm_nonneg _)
        (canonicalPotentialSourceSlotEnvelope_nonneg
          (canonicalSignedAmplitudeEnvelope_nonneg
            (N := N) flowKappa flowBeta flowG hflowBeta)
          (canonicalSignedPotentialChannelSourceEnvelope_nonneg
            sourceKappa sourceBeta sourceG
            (canonicalWeightedCoordinateEnvelope N
              flowKappa flowBeta flowG hflowBeta)
            (canonicalWeightedCoordinateEnvelope_nonneg
              flowKappa flowBeta flowG hflowBeta)) left slot)
    _ = 2 * canonicalPotentialSourceSlotEnvelope A S left slot *
          canonicalSignedBlockEnvelope A right := by ring

theorem norm_canonicalRightPotentialSourceSlotFactorizationDefect_le_cost
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (sourceKappa sourceBeta sourceG : Real)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    ‖canonicalRightPotentialSourceSlotFactorizationDefect (N := N)
        flowKappa flowBeta flowG hflowBeta a
        sourceKappa sourceBeta sourceG entry left right slot time‖ ≤
      canonicalRightSourceSlotDefectCost
        (canonicalSignedAmplitudeEnvelope N
          flowKappa flowBeta flowG hflowBeta)
        (canonicalSignedPotentialChannelSourceEnvelope N
          sourceKappa sourceBeta sourceG
          (canonicalWeightedCoordinateEnvelope N
            flowKappa flowBeta flowG hflowBeta)) left right slot := by
  let A := canonicalSignedAmplitudeEnvelope N
    flowKappa flowBeta flowG hflowBeta
  let S := canonicalSignedPotentialChannelSourceEnvelope N
    sourceKappa sourceBeta sourceG
    (canonicalWeightedCoordinateEnvelope N
      flowKappa flowBeta flowG hflowBeta)
  have hmixed := norm_canonicalRightPotentialSourceSlotMixedMoment_le_envelope
    hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      sourceKappa sourceBeta sourceG entry hpositive left right slot time
  have hblock := norm_canonicalSignedBlockBochnerIntegral_le_envelope
    hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive left time
  have hslot := norm_canonicalPotentialSourceSlotBochnerIntegral_le_envelope
    hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      sourceKappa sourceBeta sourceG entry hpositive right slot time
  unfold canonicalRightPotentialSourceSlotMixedMoment at hmixed
  unfold canonicalRightPotentialSourceSlotFactorizationDefect
    canonicalRightSourceSlotDefectCost
  apply (norm_sub_le _ _).trans
  calc
    ‖∫ omega,
          canonicalSignedBlockObservable (N := N)
              flowKappa flowBeta flowG hflowBeta a entry left (omega, time) *
            canonicalPotentialSourceSlotObservable (N := N)
              flowKappa flowBeta flowG hflowBeta a
              sourceKappa sourceBeta sourceG entry right slot (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability‖ +
        ‖canonicalSignedBlockBochnerIntegral (N := N)
            flowKappa flowBeta flowG hflowBeta a entry left time *
          canonicalPotentialSourceSlotBochnerIntegral (N := N)
            flowKappa flowBeta flowG hflowBeta a
            sourceKappa sourceBeta sourceG entry right slot time‖
        ≤ canonicalSignedBlockEnvelope A left *
            canonicalPotentialSourceSlotEnvelope A S right slot +
          canonicalSignedBlockEnvelope A left *
            canonicalPotentialSourceSlotEnvelope A S right slot := by
      apply add_le_add hmixed
      rw [norm_mul]
      exact mul_le_mul hblock hslot (norm_nonneg _) (by
        unfold canonicalSignedBlockEnvelope
        exact pow_nonneg (by
          linarith [canonicalSignedAmplitudeEnvelope_nonneg
            (N := N) flowKappa flowBeta flowG hflowBeta]) _)
    _ = 2 * canonicalSignedBlockEnvelope A left *
          canonicalPotentialSourceSlotEnvelope A S right slot := by ring

/-! ## Explicit quadratic/quartic integrability endpoints -/

theorem integrable_canonicalQuadraticSourceSlotObservable_fixedTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticSourceSlotObservable (N := N)
        kappa beta g hbeta a entry block slot (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  exact integrable_canonicalPotentialSourceSlotObservable_fixedTime
    hN ha0 ha1 kappa beta g hbeta kappa 0 g
      entry hpositive block slot time

theorem integrable_canonicalQuarticSourceSlotObservable_fixedTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuarticSourceSlotObservable (N := N)
        kappa beta g hbeta a entry block slot (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  exact integrable_canonicalPotentialSourceSlotObservable_fixedTime
    hN ha0 ha1 kappa beta g hbeta 0 beta g
      entry hpositive block slot time

theorem integrable_canonicalLeftQuadraticSlotProduct_fixedTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticSourceSlotObservable (N := N)
          kappa beta g hbeta a entry left slot (omega, time) *
        canonicalSignedBlockObservable (N := N)
          kappa beta g hbeta a entry right (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  exact integrable_canonicalPotentialLeftSlotProduct_fixedTime
    hN ha0 ha1 kappa beta g hbeta kappa 0 g
      entry hpositive left right slot time

theorem integrable_canonicalLeftQuarticSlotProduct_fixedTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuarticSourceSlotObservable (N := N)
          kappa beta g hbeta a entry left slot (omega, time) *
        canonicalSignedBlockObservable (N := N)
          kappa beta g hbeta a entry right (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  exact integrable_canonicalPotentialLeftSlotProduct_fixedTime
    hN ha0 ha1 kappa beta g hbeta 0 beta g
      entry hpositive left right slot time

theorem integrable_canonicalRightQuadraticSlotProduct_fixedTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalSignedBlockObservable (N := N)
          kappa beta g hbeta a entry left (omega, time) *
        canonicalQuadraticSourceSlotObservable (N := N)
          kappa beta g hbeta a entry right slot (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  exact integrable_canonicalPotentialRightSlotProduct_fixedTime
    hN ha0 ha1 kappa beta g hbeta kappa 0 g
      entry hpositive left right slot time

theorem integrable_canonicalRightQuarticSlotProduct_fixedTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalSignedBlockObservable (N := N)
          kappa beta g hbeta a entry left (omega, time) *
        canonicalQuarticSourceSlotObservable (N := N)
          kappa beta g hbeta a entry right slot (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  exact integrable_canonicalPotentialRightSlotProduct_fixedTime
    hN ha0 ha1 kappa beta g hbeta 0 beta g
      entry hpositive left right slot time

/-! ## Explicit deterministic costs for the four actual channels -/

theorem norm_canonicalLeftQuadraticSourceSlotFactorizationDefect_le_cost
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    ‖canonicalLeftQuadraticSourceSlotFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right slot time‖ ≤
      canonicalLeftSourceSlotDefectCost
        (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta)
        (canonicalSignedPotentialChannelSourceEnvelope N kappa 0 g
          (canonicalWeightedCoordinateEnvelope N kappa beta g hbeta))
        left right slot := by
  exact norm_canonicalLeftPotentialSourceSlotFactorizationDefect_le_cost
    hN ha0 ha1 kappa beta g hbeta kappa 0 g
      entry hpositive left right slot time

theorem norm_canonicalLeftQuarticSourceSlotFactorizationDefect_le_cost
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    ‖canonicalLeftQuarticSourceSlotFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right slot time‖ ≤
      canonicalLeftSourceSlotDefectCost
        (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta)
        (canonicalSignedPotentialChannelSourceEnvelope N 0 beta g
          (canonicalWeightedCoordinateEnvelope N kappa beta g hbeta))
        left right slot := by
  exact norm_canonicalLeftPotentialSourceSlotFactorizationDefect_le_cost
    hN ha0 ha1 kappa beta g hbeta 0 beta g
      entry hpositive left right slot time

theorem norm_canonicalRightQuadraticSourceSlotFactorizationDefect_le_cost
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    ‖canonicalRightQuadraticSourceSlotFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right slot time‖ ≤
      canonicalRightSourceSlotDefectCost
        (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta)
        (canonicalSignedPotentialChannelSourceEnvelope N kappa 0 g
          (canonicalWeightedCoordinateEnvelope N kappa beta g hbeta))
        left right slot := by
  exact norm_canonicalRightPotentialSourceSlotFactorizationDefect_le_cost
    hN ha0 ha1 kappa beta g hbeta kappa 0 g
      entry hpositive left right slot time

theorem norm_canonicalRightQuarticSourceSlotFactorizationDefect_le_cost
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    ‖canonicalRightQuarticSourceSlotFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right slot time‖ ≤
      canonicalRightSourceSlotDefectCost
        (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta)
        (canonicalSignedPotentialChannelSourceEnvelope N 0 beta g
          (canonicalWeightedCoordinateEnvelope N kappa beta g hbeta))
        left right slot := by
  exact norm_canonicalRightPotentialSourceSlotFactorizationDefect_le_cost
    hN ha0 ha1 kappa beta g hbeta 0 beta g
      entry hpositive left right slot time

end

end ArchonPhysics.CanonicalIIDCoerciveActualSourceSlotExpectation
