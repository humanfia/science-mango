import ArchonPhysics.CanonicalIIDCoerciveActualDuhamelHistoryTermIntegrabilityReduction

/-!
# Minimal primitive source-history integrability frontier

The canonical amplitude block surrounding a displayed source slot is already
measurable and uniformly bounded.  Consequently the genuinely missing
annealed statement is not a slot-product theorem: it is integrability of the
single oriented source history itself.  This module proves that three such
quadratic source statements and one free-cubic source statement imply every
quadratic/quartic source slot and both left/right mixed products.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualDuhamelPrimitiveSourceIntegrability

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualDuhamelHistoryTermIntegrabilityReduction
open ArchonPhysics.CanonicalIIDCoerciveActualPointwiseDuhamelHistoryExpansion
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTActualDuhamelSourceHistoryExpansion
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A single integrable oriented quadratic source history remains integrable
after insertion into any displayed canonical amplitude block. -/
theorem integrable_canonicalQuadraticDuhamelHistorySourceSlot_of_source
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I)
    (history : ActualQuadraticSourceHistory) (time : Real)
    (hsource : Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase (entry slot)
        history (omega, time))
      canonicalIIDMassPhaseEnsemble.probability) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase entry block slot
        history (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  simpa [canonicalQuadraticDuhamelHistorySourceSlotObservable,
    ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge.canonicalSignedBlockObservable]
    using (integrable_canonicalSignedBlockObservable_mul_fixedTime (N := N)
      hN ha0 ha1 flowKappa flowBeta flowG hflowBeta entry hpositive
      (block.erase slot) time
      (fun omega : CanonicalSample =>
        canonicalQuadraticDuhamelHistorySource (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase (entry slot)
          history (omega, time)) hsource)

/-- The identical source-to-slot adapter for one quartic history. -/
theorem integrable_canonicalQuarticDuhamelHistorySourceSlot_of_source
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I)
    (history : ActualQuarticSourceHistory) (time : Real)
    (hsource : Integrable (fun omega : CanonicalSample =>
      canonicalQuarticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase (entry slot)
        history (omega, time))
      canonicalIIDMassPhaseEnsemble.probability) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuarticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase entry block slot
        history (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  simpa [canonicalQuarticDuhamelHistorySourceSlotObservable,
    ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge.canonicalSignedBlockObservable]
    using (integrable_canonicalSignedBlockObservable_mul_fixedTime (N := N)
      hN ha0 ha1 flowKappa flowBeta flowG hflowBeta entry hpositive
      (block.erase slot) time
      (fun omega : CanonicalSample =>
        canonicalQuarticDuhamelHistorySource (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase (entry slot)
          history (omega, time)) hsource)

/-- Exact minimal quadratic source signature.  Only the free first-Picard,
quadratic second-Picard, and defect-square *sources* require direct proofs;
all four source slots then follow. -/
theorem integrable_canonicalQuadraticHistorySlot_of_threePrimitiveSources
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
      canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase (entry slot)
        .freeFirstPicard (omega, time))
      canonicalIIDMassPhaseEnsemble.probability)
    (hsecond : Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase (entry slot)
        .quadraticSecondPicard (omega, time))
      canonicalIIDMassPhaseEnsemble.probability)
    (hdefect : Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase (entry slot)
        .defectSquare (omega, time))
      canonicalIIDMassPhaseEnsemble.probability)
    (history : ActualQuadraticSourceHistory) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase entry block slot
        history (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  apply integrable_canonicalQuadraticHistory_fixedTime_of_threePrimitive
    hN ha0 ha1 flowKappa flowBeta flowG hflowBeta radius phase
      entry hpositive block slot time
  · exact integrable_canonicalQuadraticDuhamelHistorySourceSlot_of_source
      hN ha0 ha1 flowKappa flowBeta flowG hflowBeta radius phase
        entry hpositive block slot .freeFirstPicard time hfree
  · exact integrable_canonicalQuadraticDuhamelHistorySourceSlot_of_source
      hN ha0 ha1 flowKappa flowBeta flowG hflowBeta radius phase
        entry hpositive block slot .quadraticSecondPicard time hsecond
  · exact integrable_canonicalQuadraticDuhamelHistorySourceSlot_of_source
      hN ha0 ha1 flowKappa flowBeta flowG hflowBeta radius phase
        entry hpositive block slot .defectSquare time hdefect

/-- Exact minimal quartic source signature.  Direct integrability of the
free-cubic source implies both quartic source slots. -/
theorem integrable_canonicalQuarticHistorySlot_of_freePrimitiveSource
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
      canonicalQuarticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase (entry slot)
        .freeCubicSecondPicard (omega, time))
      canonicalIIDMassPhaseEnsemble.probability)
    (history : ActualQuarticSourceHistory) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuarticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase entry block slot
        history (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  apply integrable_canonicalQuarticHistory_fixedTime_of_freePrimitive
    hN ha0 ha1 flowKappa flowBeta flowG hflowBeta radius phase
      entry hpositive block slot time
  exact integrable_canonicalQuarticDuhamelHistorySourceSlot_of_source
    hN ha0 ha1 flowKappa flowBeta flowG hflowBeta radius phase
      entry hpositive block slot .freeCubicSecondPicard time hfree

/-- The three primitive quadratic source statements also give both mixed
left/right products for every quadratic history. -/
theorem integrable_canonicalQuadraticHistory_left_and_right_mixedProducts
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real)
    (hfree : Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase (entry slot)
        .freeFirstPicard (omega, time))
      canonicalIIDMassPhaseEnsemble.probability)
    (hsecond : Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase (entry slot)
        .quadraticSecondPicard (omega, time))
      canonicalIIDMassPhaseEnsemble.probability)
    (hdefect : Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase (entry slot)
        .defectSquare (omega, time))
      canonicalIIDMassPhaseEnsemble.probability)
    (history : ActualQuadraticSourceHistory) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase entry left slot
          history (omega, time) *
        CanonicalIIDCoerciveSignedModalObservableBridge.canonicalSignedBlockObservable
          (N := N) flowKappa flowBeta flowG hflowBeta a entry right
          (omega, time)) canonicalIIDMassPhaseEnsemble.probability ∧
    Integrable (fun omega : CanonicalSample =>
      CanonicalIIDCoerciveSignedModalObservableBridge.canonicalSignedBlockObservable
          (N := N) flowKappa flowBeta flowG hflowBeta a entry left
          (omega, time) *
        canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase entry right slot
          history (omega, time)) canonicalIIDMassPhaseEnsemble.probability := by
  have hleft := integrable_canonicalQuadraticHistorySlot_of_threePrimitiveSources
    hN ha0 ha1 flowKappa flowBeta flowG hflowBeta radius phase entry hpositive
      left slot time hfree hsecond hdefect history
  have hright := integrable_canonicalQuadraticHistorySlot_of_threePrimitiveSources
    hN ha0 ha1 flowKappa flowBeta flowG hflowBeta radius phase entry hpositive
      right slot time hfree hsecond hdefect history
  exact ⟨integrable_mul_canonicalSignedBlockObservable_fixedTime
      hN ha0 ha1 flowKappa flowBeta flowG hflowBeta entry hpositive
        right time _ hleft,
    integrable_canonicalSignedBlockObservable_mul_fixedTime
      hN ha0 ha1 flowKappa flowBeta flowG hflowBeta entry hpositive
        left time _ hright⟩

/-- The free-cubic primitive source statement similarly gives both quartic
mixed products. -/
theorem integrable_canonicalQuarticHistory_left_and_right_mixedProducts
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real)
    (hfree : Integrable (fun omega : CanonicalSample =>
      canonicalQuarticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase (entry slot)
        .freeCubicSecondPicard (omega, time))
      canonicalIIDMassPhaseEnsemble.probability)
    (history : ActualQuarticSourceHistory) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuarticDuhamelHistorySourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase entry left slot
          history (omega, time) *
        CanonicalIIDCoerciveSignedModalObservableBridge.canonicalSignedBlockObservable
          (N := N) flowKappa flowBeta flowG hflowBeta a entry right
          (omega, time)) canonicalIIDMassPhaseEnsemble.probability ∧
    Integrable (fun omega : CanonicalSample =>
      CanonicalIIDCoerciveSignedModalObservableBridge.canonicalSignedBlockObservable
          (N := N) flowKappa flowBeta flowG hflowBeta a entry left
          (omega, time) *
        canonicalQuarticDuhamelHistorySourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase entry right slot
          history (omega, time)) canonicalIIDMassPhaseEnsemble.probability := by
  have hleft := integrable_canonicalQuarticHistorySlot_of_freePrimitiveSource
    hN ha0 ha1 flowKappa flowBeta flowG hflowBeta radius phase entry hpositive
      left slot time hfree history
  have hright := integrable_canonicalQuarticHistorySlot_of_freePrimitiveSource
    hN ha0 ha1 flowKappa flowBeta flowG hflowBeta radius phase entry hpositive
      right slot time hfree history
  exact ⟨integrable_mul_canonicalSignedBlockObservable_fixedTime
      hN ha0 ha1 flowKappa flowBeta flowG hflowBeta entry hpositive
        right time _ hleft,
    integrable_canonicalSignedBlockObservable_mul_fixedTime
      hN ha0 ha1 flowKappa flowBeta flowG hflowBeta entry hpositive
        left time _ hright⟩

end
end ArchonPhysics.CanonicalIIDCoerciveActualDuhamelPrimitiveSourceIntegrability
