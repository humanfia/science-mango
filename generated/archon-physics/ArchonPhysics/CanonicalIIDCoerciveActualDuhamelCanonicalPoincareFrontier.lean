import ArchonPhysics.CanonicalIIDCoerciveActualDuhamelSinglePrimitiveFrontier
import ArchonPhysics.CanonicalRandomMassGlobalFlow

/-!
# Canonical Poincare specialization of the fixed-time Duhamel frontier

The fixed finite periodic lattice already has a mass-uniform Poincare
constant.  This adapter specializes the defect-square estimate to that
canonical constant.  Consequently the user-facing quadratic-history theorem
has only one analytic input left: fixed-time integrability of the quadratic
second-Picard primitive.  No Poincare datum needs to be supplied separately.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualDuhamelCanonicalPoincareFrontier

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualDefectSquareHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualDuhamelSinglePrimitiveFrontier
open ArchonPhysics.CanonicalIIDCoerciveActualPointwiseDuhamelHistoryExpansion
open ArchonPhysics.CanonicalIIDCoerciveActualFreeQuadraticHistoryIntegrability
open ArchonPhysics.CanonicalRandomMassGlobalFlow
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTActualDuhamelSourceHistoryExpansion
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The genuine canonical defect-square source is fixed-time integrable using
the automatically chosen uniform finite-lattice Poincare constant. -/
theorem integrable_canonicalQuadraticDefectSquareSource_fixedTime_autoPoincare
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG G : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (hG : 0 <= G) (hg : |flowG| <= G)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry .defectSquare (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  exact integrable_canonicalQuadraticDefectSquareSource_fixedTime
    (N := N) hN ha0 ha1
      (canonicalUniformPoincareConstant N)
      (canonicalUniformPoincareConstant_pos N).le
      (canonicalUniformPoincareConstant_spec N)
      flowKappa flowBeta flowG G hflowBeta hG hg entry hentry time

/-- Every canonical quadratic history slot is fixed-time integrable once the
quadratic second-Picard primitive is; all finite-volume coercivity data are
now discharged by the canonical lattice construction. -/
theorem integrable_canonicalQuadraticHistorySlot_of_secondPicardSource_autoPoincare
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
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
  exact integrable_canonicalQuadraticHistorySlot_of_secondPicardSource
    (N := N) hN ha0 ha1
      (canonicalUniformPoincareConstant N)
      (canonicalUniformPoincareConstant_pos N).le
      (canonicalUniformPoincareConstant_spec N)
      flowKappa flowBeta flowG G hflowBeta hG hg
      entry hpositive block slot time hsecond history

end
end ArchonPhysics.CanonicalIIDCoerciveActualDuhamelCanonicalPoincareFrontier
