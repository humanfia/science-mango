import ArchonPhysics.ActualThreeSiteQuadraticSecondPicardSourceSlotCharacterBridge

/-!
# Consumer: actual three-site source-slot character split

This consumer exposes the exact endpoint used downstream: the actual
canonical quadratic second-Picard source slot is the sum over one literal
four-element ordinary-history family plus the sum over every remaining raw
character.  The complement is part of the theorem statement, so this result
does not assert that the selected four histories exhaust the source.  The
split allows any observed ordered mode; applying the existing N=3
outer-mismatch small-ball rate additionally requires that the source-slot
mode map to `firstPositivePhysicalModeThree`, and that probability bridge is
not claimed here.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamily
open ArchonPhysics.ActualThreeSiteQuadraticSecondPicardSourceSlotCharacterBridge
open ArchonPhysics.CanonicalIIDCoerciveActualFreeQuadraticHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualPointwiseDuhamelHistoryExpansion
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomMassPositiveLateWindowObservable
open MeasureTheory

noncomputable section

local instance :
    DecidableEq (IteratedQuadraticSecondPicardCharacterTerm 3) :=
  Classical.decEq _

/-- The selected ordinary outer-history subfamily has four distinct raw
character indices. -/
theorem actual_three_site_ordinary_outer_history_finset_card :
    threeSiteOrdinaryOuterHistoryFinset.card = 4 :=
  card_threeSiteOrdinaryOuterHistoryFinset

/-- Consumer-facing almost-sure exact split of the actual source slot into
the four displayed histories and the full raw-character complement. -/
theorem actual_three_site_quadratic_second_picard_source_slot_split_ae
    {I : Type*} [DecidableEq I]
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex 3)
    (block : Finset I) (slot : I) (time : Real) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      canonicalQuadraticDuhamelHistorySourceSlotObservable (N := 3)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := 3) a)
          (canonicalReindexedPhyslibHaarPhase (N := 3))
          entry block slot .quadraticSecondPicard (omega, time) =
        (∑ term ∈ threeSiteOrdinaryOuterHistoryFinset,
          canonicalQuadraticSecondPicardRawCharacterSourceSlotObservable
            (N := 3) flowKappa flowBeta flowG hflowBeta a
            entry block slot term (omega, time)) +
        (∑ term ∈ Finset.univ \ threeSiteOrdinaryOuterHistoryFinset,
          canonicalQuadraticSecondPicardRawCharacterSourceSlotObservable
            (N := 3) flowKappa flowBeta flowG hflowBeta a
            entry block slot term (omega, time)) :=
  threeSiteQuadraticSecondPicardHistorySourceSlot_eq_ordinaryOuter_add_complement_ae
    flowKappa flowBeta flowG hflowBeta a entry block slot time

#print axioms actual_three_site_ordinary_outer_history_finset_card
#print axioms actual_three_site_quadratic_second_picard_source_slot_split_ae

end
end ArchonPhysicsConsumers.Thermalization
