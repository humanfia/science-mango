import ArchonPhysics.CanonicalIIDCoerciveActualDefectSquareHistoryIntegrability
import ArchonPhysics.CanonicalIIDCoerciveActualFreeCubicHistoryIntegrability
import ArchonPhysics.CanonicalIIDCoerciveActualDuhamelPrimitiveSourceIntegrability

/-!
# One remaining fixed-time Duhamel primitive

For the canonical oriented free radius and reindexed Haar phase, the free
quadratic, defect-square, and free-cubic primitive histories are now proved
integrable at every fixed real time.  This adapter discharges those three
inputs in the general history reduction.  Thus every quartic history slot is
unconditional, while every quadratic history slot has exactly one remaining
input: integrability of the extracted quadratic second-Picard source itself.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualDuhamelSinglePrimitiveFrontier

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualDefectSquareHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualDuhamelPrimitiveSourceIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualFreeCubicHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualFreeQuadraticHistoryIntegrability
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

/-- Every canonical quadratic history slot is integrable once the single
quadratic second-Picard primitive is integrable. -/
theorem integrable_canonicalQuadraticHistorySlot_of_secondPicardSource
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (C : Real) (hC : 0 <= C)
    (hPoincare : forall (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) ->
        ‖q‖ <= C * ‖Lattice.forwardDifference q‖)
    (flowKappa flowBeta flowG G : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (hG : 0 <= G) (hg : |flowG| <= G)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (time : Real)
    (hsecond : Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        (entry slot) .quadraticSecondPicard (omega, time))
      canonicalIIDMassPhaseEnsemble.probability)
    (history : ActualQuadraticSourceHistory) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot history (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  apply integrable_canonicalQuadraticHistorySlot_of_threePrimitiveSources
    hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      (canonicalOrientedPhyslibFreeRadius (N := N) a)
      (canonicalReindexedPhyslibHaarPhase (N := N))
      entry hpositive block slot time
  · exact integrable_canonicalQuadraticFreeFirstPicardSource_fixedTime
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        (entry slot) (hpositive slot) time
  · exact hsecond
  · exact integrable_canonicalQuadraticDefectSquareSource_fixedTime
      (N := N) hN ha0 ha1 C hC hPoincare
        flowKappa flowBeta flowG G hflowBeta hG hg
        (entry slot) (hpositive slot) time

/-- Both canonical quartic histories are integrable at every fixed real time;
there is no remaining primitive-source hypothesis in this channel. -/
theorem integrable_canonicalQuarticHistorySlot_fixedTime
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (time : Real)
    (history : ActualQuarticSourceHistory) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuarticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot history (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  apply integrable_canonicalQuarticHistorySlot_of_freePrimitiveSource
    hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      (canonicalOrientedPhyslibFreeRadius (N := N) a)
      (canonicalReindexedPhyslibHaarPhase (N := N))
      entry hpositive block slot time
  · exact integrable_canonicalQuarticFreeCubicSource_fixedTime
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        (entry slot) (hpositive slot) time

end
end ArchonPhysics.CanonicalIIDCoerciveActualDuhamelSinglePrimitiveFrontier
