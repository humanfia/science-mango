import ArchonPhysics.CanonicalIIDCoerciveActualDuhamelCanonicalPoincareFrontier
import ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardHistoryIntegrability

/-!
# Unconditional fixed-time closure of every actual Duhamel history slot

All four primitive sources in the actual canonical quadratic/quartic Duhamel
history are now Bochner integrable at every fixed real time and fixed finite
volume:

* the free quadratic first-Picard source;
* the quadratic second-Picard source;
* the actual-minus-free defect-square source;
* the free cubic source.

This module assembles those results.  The finite-lattice Poincare constant is
chosen canonically, and the absolute nonlinear coupling itself supplies the
defect energy envelope.  Hence the final interface exposes no auxiliary
coercivity or source-integrability hypothesis.

This is a fixed-time analytic closure.  It does not assert a kinetic-time
limit, RPA propagation, recollision suppression, or thermalization.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualDuhamelFixedTimeClosure

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualDuhamelCanonicalPoincareFrontier
open ArchonPhysics.CanonicalIIDCoerciveActualDuhamelSinglePrimitiveFrontier
open ArchonPhysics.CanonicalIIDCoerciveActualFreeQuadraticHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualPointwiseDuhamelHistoryExpansion
open ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTActualDuhamelSourceHistoryExpansion
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Every actual canonical quadratic history slot is Bochner integrable at
every fixed real time.  All four primitive-source obligations are discharged
from the Hamiltonian finite-volume construction. -/
theorem integrable_canonicalQuadraticHistorySlot_fixedTime_closed
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (time : Real)
    (history : ActualQuadraticSourceHistory) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot history (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  apply
    integrable_canonicalQuadraticHistorySlot_of_secondPicardSource_autoPoincare
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG |flowG|
        hflowBeta (abs_nonneg flowG) le_rfl
        entry hpositive block slot time
  · exact integrable_canonicalQuadraticSecondPicardSource_fixedTime
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        (entry slot) (hpositive slot) time

/-- Every actual canonical quartic history slot is Bochner integrable at
every fixed real time. -/
theorem integrable_canonicalQuarticHistorySlot_fixedTime_closed
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
  exact integrable_canonicalQuarticHistorySlot_fixedTime
    (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive block slot time history

end
end ArchonPhysics.CanonicalIIDCoerciveActualDuhamelFixedTimeClosure
