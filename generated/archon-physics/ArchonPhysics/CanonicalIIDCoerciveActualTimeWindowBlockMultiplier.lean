import ArchonPhysics.CanonicalIIDCoerciveActualDuhamelHistoryTermIntegrabilityReduction

/-!
# Time-window multiplication by canonical observable blocks

This module lifts a jointly integrable actual source, written with time as
the first product coordinate, through multiplication by any finite canonical
signed-amplitude block.  The block is jointly measurable and has an almost
sure bound uniform in time.  The result is the common adapter needed to pass
from primitive sources to displayed Duhamel history slots on finite windows.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualTimeWindowBlockMultiplier

open Set
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualDuhamelHistoryTermIntegrabilityReduction
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationCompleted
open ArchonPhysics.CanonicalIIDCoerciveActualPointwiseDuhamelHistoryExpansion
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTActualDuhamelSourceHistoryExpansion
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Multiplication by a genuine canonical block preserves joint Bochner
integrability on every finite symmetric time window. -/
theorem integrable_canonicalSignedBlockObservable_mul_source_timeWindow
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (window : Real)
    (source : CanonicalSample × Real -> Complex)
    (hsource : Integrable (fun st : Real × CanonicalSample =>
      source (st.2, st.1))
      ((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability)) :
    Integrable (fun st : Real × CanonicalSample =>
      canonicalSignedBlockObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a entry block (st.2, st.1) *
        source (st.2, st.1))
      ((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability) := by
  let C := canonicalSignedBlockEnvelope
    (canonicalSignedAmplitudeEnvelope N
      flowKappa flowBeta flowG hflowBeta) block
  have hblockMeas : AEStronglyMeasurable
      (fun st : Real × CanonicalSample =>
        canonicalSignedBlockObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a entry block (st.2, st.1))
      ((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability) :=
    ((measurable_canonicalSignedBlockObservable (N := N)
      flowKappa flowBeta flowG hflowBeta a entry block).comp
        (measurable_snd.prodMk measurable_fst)).aestronglyMeasurable
  have hboundBase := canonicalSignedBlockBounds_ae_allTime
    (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive
  have hboundProduct :=
    (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (Icc (-window) window))
      (ν := canonicalIIDMassPhaseEnsemble.probability)).ae hboundBase
  refine hsource.bdd_mul hblockMeas (c := C) ?_
  filter_upwards [hboundProduct] with st hbound
  exact (hbound st.1 block).1

/-- A jointly integrable raw quadratic history source yields a jointly
integrable displayed quadratic history slot on the same time window. -/
theorem integrable_canonicalQuadraticHistorySlot_timeWindow_of_source
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I)
    (history : ActualQuadraticSourceHistory) (window : Real)
    (hsource : Integrable (fun st : Real × CanonicalSample =>
      canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase
        (entry slot) history (st.2, st.1))
      ((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability)) :
    Integrable (fun st : Real × CanonicalSample =>
      canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase
        entry block slot history (st.2, st.1))
      ((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability) := by
  simpa [canonicalQuadraticDuhamelHistorySourceSlotObservable,
    canonicalSignedBlockObservable] using
    (integrable_canonicalSignedBlockObservable_mul_source_timeWindow
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive (block.erase slot) window
      (canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase
        (entry slot) history) hsource)

/-- The analogous adapter for a raw quartic history source. -/
theorem integrable_canonicalQuarticHistorySlot_timeWindow_of_source
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I)
    (history : ActualQuarticSourceHistory) (window : Real)
    (hsource : Integrable (fun st : Real × CanonicalSample =>
      canonicalQuarticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase
        (entry slot) history (st.2, st.1))
      ((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability)) :
    Integrable (fun st : Real × CanonicalSample =>
      canonicalQuarticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase
        entry block slot history (st.2, st.1))
      ((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability) := by
  simpa [canonicalQuarticDuhamelHistorySourceSlotObservable,
    canonicalSignedBlockObservable] using
    (integrable_canonicalSignedBlockObservable_mul_source_timeWindow
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive (block.erase slot) window
      (canonicalQuarticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase
        (entry slot) history) hsource)

end
end ArchonPhysics.CanonicalIIDCoerciveActualTimeWindowBlockMultiplier
