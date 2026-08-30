import ArchonPhysics.CanonicalIIDCoerciveActualDuhamelHistoryBochnerGardenBridge
import ArchonPhysics.RandomMassOrderedPhyslibAmplitudeIntertwining

/-!
# Individual actual Duhamel histories: exact annealed integrability reduction

This module separates the remaining random-mass measurability problem from
the already measurable canonical amplitude legs.  The latter are rewritten
exactly into the ordered signed Physlib frame.  It then proves that only
three of the four quadratic history slots and one of the two quartic history
slots need independent annealed integrability proofs: the two literal
remainders follow from the integrable whole source-slot identities.  Finally,
any individually integrable history slot remains integrable after multiplying
by either neighboring canonical block.

No individual history is inferred merely from integrability of a finite sum.
The closure of a remainder always assumes every other summand separately.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualDuhamelHistoryTermIntegrabilityReduction

open scoped BigOperators
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualDuhamelHistoryBochnerGardenBridge
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationCompleted
open ArchonPhysics.CanonicalIIDCoerciveActualPointwiseDuhamelHistoryExpansion
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTActualDuhamelSourceHistoryExpansion
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.RandomMassOrderedPhyslibAmplitudeIntertwining
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The canonical momentum component, reparameterized as a Physlib path. -/
def canonicalPhyslibMomentumPath
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (omega : CanonicalSample) :
    Time -> HilbertConfiguration N :=
  fun time => canonicalFlowMomentum (N := N)
    flowKappa flowBeta flowG hflowBeta a (omega, Time.toRealCLE time)

@[simp] theorem realReparametrize_canonicalPhyslibMomentumPath
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (omega : CanonicalSample) :
    realReparametrize
        (canonicalPhyslibMomentumPath (N := N)
          flowKappa flowBeta flowG hflowBeta a omega) =
      fun time => canonicalFlowMomentum (N := N)
        flowKappa flowBeta flowG hflowBeta a (omega, time) := by
  funext time
  rfl

/-- The measurable canonical amplitude is definitionally the ordered signed
amplitude along the two reparameterized Physlib paths. -/
theorem canonicalInteractionAmplitude_eq_orderedSignedAlongPhyslibPath
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (omega : CanonicalSample)
    (k : OrderedModeIndex N) (time : Real) :
    canonicalInteractionAmplitude (N := N)
        flowKappa flowBeta flowG hflowBeta a k (omega, time) =
      orderedSignedInteractionAmplitudeAlongPhyslibPath
        (canonicalMass (N := N) omega) k
        (canonicalPhyslibMomentumPath (N := N)
          flowKappa flowBeta flowG hflowBeta a omega)
        (canonicalPhyslibPositionPath (N := N)
          flowKappa flowBeta flowG hflowBeta a omega) time := by
  rfl

/-- Every input-amplitude block outside the displayed source leg has the
exact orientation-product rewrite requested by the Physlib adapter. -/
theorem canonicalSignedBlockObservable_eq_orientation_mul_reindexedPhyslibBlock
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (time : Real) :
    canonicalSignedBlockObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a entry block (omega, time) =
      orderedBlockOrientation (canonicalMass (N := N) omega) entry block *
        ∏ i ∈ block,
          phaseSignActComplex (entry i).1
            (reindexedPhyslibInteractionAmplitude
              (canonicalMass (N := N) omega) (entry i).2
              (canonicalPhyslibMomentumPath (N := N)
                flowKappa flowBeta flowG hflowBeta a omega)
              (canonicalPhyslibPositionPath (N := N)
                flowKappa flowBeta flowG hflowBeta a omega) time) := by
  rw [show canonicalSignedBlockObservable (N := N)
      flowKappa flowBeta flowG hflowBeta a entry block (omega, time) =
      ∏ i ∈ block, phaseSignActComplex (entry i).1
        (orderedSignedInteractionAmplitudeAlongPhyslibPath
          (canonicalMass (N := N) omega) (entry i).2
          (canonicalPhyslibMomentumPath (N := N)
            flowKappa flowBeta flowG hflowBeta a omega)
          (canonicalPhyslibPositionPath (N := N)
            flowKappa flowBeta flowG hflowBeta a omega) time) by
    unfold canonicalSignedBlockObservable canonicalSignedInteractionAmplitude
    simp_rw [canonicalInteractionAmplitude_eq_orderedSignedAlongPhyslibPath]]
  exact orderedSignedInteractionBlock_eq_orientation_mul_physlibBlock
    (canonicalMass (N := N) omega) hsimple entry block
    (canonicalPhyslibMomentumPath (N := N)
      flowKappa flowBeta flowG hflowBeta a omega)
    (canonicalPhyslibPositionPath (N := N)
      flowKappa flowBeta flowG hflowBeta a omega) time

/-- The same rewrite preserves the norm because the orientation product has
unit norm on the simple-spectrum event. -/
theorem norm_canonicalSignedBlockObservable_eq_reindexedPhyslibBlock
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (time : Real) :
    ‖canonicalSignedBlockObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a entry block (omega, time)‖ =
      ‖∏ i ∈ block,
          phaseSignActComplex (entry i).1
            (reindexedPhyslibInteractionAmplitude
              (canonicalMass (N := N) omega) (entry i).2
              (canonicalPhyslibMomentumPath (N := N)
                flowKappa flowBeta flowG hflowBeta a omega)
              (canonicalPhyslibPositionPath (N := N)
                flowKappa flowBeta flowG hflowBeta a omega) time)‖ := by
  rw [canonicalSignedBlockObservable_eq_orientation_mul_reindexedPhyslibBlock
    flowKappa flowBeta flowG hflowBeta a omega hsimple entry block time,
    norm_mul, norm_orderedBlockOrientation
      (canonicalMass (N := N) omega) hsimple entry block, one_mul]

/-- Multiplication on the right by any genuine canonical block preserves
integrability of a single history slot. -/
theorem integrable_mul_canonicalSignedBlockObservable_fixedTime
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (time : Real)
    (historySlot : CanonicalSample -> Complex)
    (hhistory : Integrable historySlot
      canonicalIIDMassPhaseEnsemble.probability) :
    Integrable (fun omega => historySlot omega *
      canonicalSignedBlockObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a entry block (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  let A := canonicalSignedAmplitudeEnvelope N
    flowKappa flowBeta flowG hflowBeta
  let C := canonicalSignedBlockEnvelope A block
  have hC : 0 <= C := by
    unfold C canonicalSignedBlockEnvelope A
    exact pow_nonneg (by
      linarith [canonicalSignedAmplitudeEnvelope_nonneg
        (N := N) flowKappa flowBeta flowG hflowBeta]) _
  have hmeas : AEStronglyMeasurable (fun omega : CanonicalSample =>
      canonicalSignedBlockObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a entry block (omega, time))
      canonicalIIDMassPhaseEnsemble.probability :=
    (measurable_canonicalSignedBlockObservable_fixedTime (N := N)
      flowKappa flowBeta flowG hflowBeta a entry block time).aestronglyMeasurable
  refine ⟨hhistory.aestronglyMeasurable.mul hmeas, ?_⟩
  have hscaled : Integrable (fun omega =>
      historySlot omega * (C : Complex))
      canonicalIIDMassPhaseEnsemble.probability :=
    hhistory.mul_const (C : Complex)
  refine hscaled.hasFiniteIntegral.mono ?_
  filter_upwards [canonicalSignedBlockBounds_ae_allTime
    hN ha0 ha1 flowKappa flowBeta flowG hflowBeta entry hpositive]
      with omega hbound
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hC]
  exact mul_le_mul_of_nonneg_left (hbound time block).1 (norm_nonneg _)

/-- Multiplication on the left by any genuine canonical block likewise
preserves integrability of a single history slot. -/
theorem integrable_canonicalSignedBlockObservable_mul_fixedTime
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (time : Real)
    (historySlot : CanonicalSample -> Complex)
    (hhistory : Integrable historySlot
      canonicalIIDMassPhaseEnsemble.probability) :
    Integrable (fun omega =>
      canonicalSignedBlockObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a entry block (omega, time) *
        historySlot omega)
      canonicalIIDMassPhaseEnsemble.probability := by
  simpa [mul_comm] using
    (integrable_mul_canonicalSignedBlockObservable_fixedTime (N := N)
      hN ha0 ha1 flowKappa flowBeta flowG hflowBeta entry hpositive
      block time historySlot hhistory)

/-- Assuming the free, extracted second-Picard, and defect-square quadratic
slots are individually integrable, the literal linear-history remainder is
forced to be integrable by the exact four-term identity. -/
theorem integrable_canonicalQuadraticLinearHistoryRemainder_fixedTime
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (time : Real)
    (hfree : Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase entry block slot
        .freeFirstPicard (omega, time))
      canonicalIIDMassPhaseEnsemble.probability)
    (hsecond : Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase entry block slot
        .quadraticSecondPicard (omega, time))
      canonicalIIDMassPhaseEnsemble.probability)
    (hdefect : Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase entry block slot
        .defectSquare (omega, time))
      canonicalIIDMassPhaseEnsemble.probability) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase entry block slot
        .linearHistoryRemainder (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  have hsum := integrable_canonicalQuadraticDuhamelHistorySourceSlotSum_fixedTime
    (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta radius phase
    entry hpositive block slot time
  have hsub := ((hsum.sub hfree).sub hsecond).sub hdefect
  refine hsub.congr ?_
  filter_upwards with omega
  simp [canonicalQuadraticDuhamelHistorySourceSlotSum,
    actualQuadraticSourceHistories]

/-- Once the free cubic slot is integrable, the literal actual-minus-free
cubic remainder is integrable by the exact two-term identity. -/
theorem integrable_canonicalQuarticHistoryRemainder_fixedTime
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (time : Real)
    (hfree : Integrable (fun omega : CanonicalSample =>
      canonicalQuarticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase entry block slot
        .freeCubicSecondPicard (omega, time))
      canonicalIIDMassPhaseEnsemble.probability) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuarticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase entry block slot
        .cubicHistoryRemainder (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  have hsum := integrable_canonicalQuarticDuhamelHistorySourceSlotSum_fixedTime
    (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta radius phase
    entry hpositive block slot time
  have hsub := hsum.sub hfree
  refine hsub.congr ?_
  filter_upwards with omega
  simp [canonicalQuarticDuhamelHistorySourceSlotSum,
    actualQuarticSourceHistories]

/-- The exact minimal quadratic signature: three primitive histories imply
integrability of every one of the four histories. -/
theorem integrable_canonicalQuadraticHistory_fixedTime_of_threePrimitive
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (time : Real)
    (hfree : Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase entry block slot
        .freeFirstPicard (omega, time))
      canonicalIIDMassPhaseEnsemble.probability)
    (hsecond : Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase entry block slot
        .quadraticSecondPicard (omega, time))
      canonicalIIDMassPhaseEnsemble.probability)
    (hdefect : Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase entry block slot
        .defectSquare (omega, time))
      canonicalIIDMassPhaseEnsemble.probability)
    (history : ActualQuadraticSourceHistory) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase entry block slot
        history (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  cases history with
  | freeFirstPicard => exact hfree
  | quadraticSecondPicard => exact hsecond
  | linearHistoryRemainder =>
      exact integrable_canonicalQuadraticLinearHistoryRemainder_fixedTime
        hN ha0 ha1 flowKappa flowBeta flowG hflowBeta radius phase
        entry hpositive block slot time hfree hsecond hdefect
  | defectSquare => exact hdefect

/-- The exact minimal quartic signature: the free cubic history implies
integrability of both histories. -/
theorem integrable_canonicalQuarticHistory_fixedTime_of_freePrimitive
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (time : Real)
    (hfree : Integrable (fun omega : CanonicalSample =>
      canonicalQuarticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase entry block slot
        .freeCubicSecondPicard (omega, time))
      canonicalIIDMassPhaseEnsemble.probability)
    (history : ActualQuarticSourceHistory) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuarticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase entry block slot
        history (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  cases history with
  | freeCubicSecondPicard => exact hfree
  | cubicHistoryRemainder =>
      exact integrable_canonicalQuarticHistoryRemainder_fixedTime
        hN ha0 ha1 flowKappa flowBeta flowG hflowBeta radius phase
        entry hpositive block slot time hfree

end
end ArchonPhysics.CanonicalIIDCoerciveActualDuhamelHistoryTermIntegrabilityReduction
