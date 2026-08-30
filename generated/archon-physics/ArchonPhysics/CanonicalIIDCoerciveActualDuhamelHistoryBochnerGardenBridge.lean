import ArchonPhysics.CanonicalIIDCoerciveActualGardenHistoryDecomposition
import ArchonPhysics.CanonicalIIDCoerciveActualPointwiseDuhamelHistoryExpansion

/-!
# Canonical actual histories: garden sectors and aggregate Bochner closure

The actual canonical unit-quadratic and unit-quartic source slots are sent
pointwise into the existing four-sector garden bookkeeping.  At fixed time,
each *whole finite history sum* is also shown Bochner integrable and its
integral is identified with the existing canonical source-slot integral.

No individual oriented Physlib history is claimed measurable or integrable.
Accordingly there is no termwise integral or sectorwise expectation defect
in this module.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualDuhamelHistoryBochnerGardenBridge

open scoped BigOperators
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualGardenHistoryDecomposition
open ArchonPhysics.CanonicalIIDCoerciveActualPointwiseDuhamelHistoryExpansion
open ArchonPhysics.CanonicalIIDCoercivePotentialChannelExpectation
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSourceSlotExpectationClosure
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTActualDuhamelSourceHistoryExpansion
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

def canonicalQuadraticDuhamelHistorySourceSlotSum
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I)
    (st : CanonicalSample × Real) : Complex :=
  ∑ history ∈ actualQuadraticSourceHistories,
    canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
      flowKappa flowBeta flowG hflowBeta a radius phase
      entry block slot history st

def canonicalQuarticDuhamelHistorySourceSlotSum
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I)
    (st : CanonicalSample × Real) : Complex :=
  ∑ history ∈ actualQuarticSourceHistories,
    canonicalQuarticDuhamelHistorySourceSlotObservable (N := N)
      flowKappa flowBeta flowG hflowBeta a radius phase
      entry block slot history st

def canonicalQuadraticDuhamelHistorySectorContribution
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I) (target : GardenHistorySector)
    (st : CanonicalSample × Real) : Complex :=
  finiteHistorySectorContribution actualQuadraticSourceHistories
    actualQuadraticHistorySector
    (fun history =>
      canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase
        entry block slot history st) target

def canonicalQuarticDuhamelHistorySectorContribution
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I) (target : GardenHistorySector)
    (st : CanonicalSample × Real) : Complex :=
  finiteHistorySectorContribution actualQuarticSourceHistories
    actualQuarticHistorySector
    (fun history =>
      canonicalQuarticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase
        entry block slot history st) target

/-- The canonical quadratic history sum is exactly the four exhaustive
garden sectors. -/
theorem canonicalQuadraticDuhamelHistorySourceSlotSum_eq_fourSectors
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I) (st : CanonicalSample × Real) :
    canonicalQuadraticDuhamelHistorySourceSlotSum (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase
        entry block slot st =
      canonicalQuadraticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase
          entry block slot .regularGoodGarden st +
        canonicalQuadraticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase
          entry block slot .badSmallDenominator st +
        canonicalQuadraticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase
          entry block slot .recollisionRepeatedHistory st +
        canonicalQuadraticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase
          entry block slot .truncationRemainder st := by
  unfold canonicalQuadraticDuhamelHistorySourceSlotSum
    canonicalQuadraticDuhamelHistorySectorContribution
  exact finiteHistorySum_eq_fourSectorContributions
    actualQuadraticSourceHistories actualQuadraticHistorySector _

/-- The canonical quartic history sum is exactly the four exhaustive garden
sectors. -/
theorem canonicalQuarticDuhamelHistorySourceSlotSum_eq_fourSectors
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I) (st : CanonicalSample × Real) :
    canonicalQuarticDuhamelHistorySourceSlotSum (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase
        entry block slot st =
      canonicalQuarticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase
          entry block slot .regularGoodGarden st +
        canonicalQuarticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase
          entry block slot .badSmallDenominator st +
        canonicalQuarticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase
          entry block slot .recollisionRepeatedHistory st +
        canonicalQuarticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase
          entry block slot .truncationRemainder st := by
  unfold canonicalQuarticDuhamelHistorySourceSlotSum
    canonicalQuarticDuhamelHistorySectorContribution
  exact finiteHistorySum_eq_fourSectorContributions
    actualQuarticSourceHistories actualQuarticHistorySector _

/-- On a simple spectrum the actual quadratic source slot itself equals the
four canonical history sectors. -/
theorem canonicalPotentialUnitQuadraticSourceSlotObservable_eq_fourSectors
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (time : Real) :
    canonicalPotentialSourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a 1 0 1
        entry block slot (omega, time) =
      canonicalQuadraticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase
          entry block slot .regularGoodGarden (omega, time) +
        canonicalQuadraticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase
          entry block slot .badSmallDenominator (omega, time) +
        canonicalQuadraticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase
          entry block slot .recollisionRepeatedHistory (omega, time) +
        canonicalQuadraticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase
          entry block slot .truncationRemainder (omega, time) := by
  calc
    _ = canonicalQuadraticDuhamelHistorySourceSlotSum (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase
        entry block slot (omega, time) := by
      simpa [canonicalQuadraticDuhamelHistorySourceSlotSum] using
        (canonicalPotentialUnitQuadraticSourceSlotObservable_eq_historySum
          flowKappa flowBeta flowG hflowBeta a radius phase entry block slot
          omega hsimple time)
    _ = _ := canonicalQuadraticDuhamelHistorySourceSlotSum_eq_fourSectors
      flowKappa flowBeta flowG hflowBeta a radius phase
      entry block slot (omega, time)

/-- On a simple spectrum the actual quartic source slot itself equals the
four canonical history sectors. -/
theorem canonicalPotentialUnitQuarticSourceSlotObservable_eq_fourSectors
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (time : Real) :
    canonicalPotentialSourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a 0 1 1
        entry block slot (omega, time) =
      canonicalQuarticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase
          entry block slot .regularGoodGarden (omega, time) +
        canonicalQuarticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase
          entry block slot .badSmallDenominator (omega, time) +
        canonicalQuarticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase
          entry block slot .recollisionRepeatedHistory (omega, time) +
        canonicalQuarticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase
          entry block slot .truncationRemainder (omega, time) := by
  calc
    _ = canonicalQuarticDuhamelHistorySourceSlotSum (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase
        entry block slot (omega, time) := by
      simpa [canonicalQuarticDuhamelHistorySourceSlotSum] using
        (canonicalPotentialUnitQuarticSourceSlotObservable_eq_historySum
          flowKappa flowBeta flowG hflowBeta a radius phase entry block slot
          omega hsimple time)
    _ = _ := canonicalQuarticDuhamelHistorySourceSlotSum_eq_fourSectors
      flowKappa flowBeta flowG hflowBeta a radius phase
      entry block slot (omega, time)

/-- The whole finite quadratic history sum is integrable because it agrees
almost surely with the measurable actual source slot. -/
theorem integrable_canonicalQuadraticDuhamelHistorySourceSlotSum_fixedTime
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySourceSlotSum (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase
        entry block slot (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  refine (integrable_canonicalPotentialSourceSlotObservable_fixedTime
    hN ha0 ha1 flowKappa flowBeta flowG hflowBeta 1 0 1
    entry hpositive block slot time).congr ?_
  filter_upwards [
    canonicalPotentialUnitQuadraticSourceSlotObservable_eq_historySum_ae
      (show 2 <= N by omega) flowKappa flowBeta flowG hflowBeta a
      radius phase entry block slot time] with omega hsum
  simpa [canonicalQuadraticDuhamelHistorySourceSlotSum] using hsum

/-- The whole finite quartic history sum is integrable by the same
almost-sure identification. -/
theorem integrable_canonicalQuarticDuhamelHistorySourceSlotSum_fixedTime
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuarticDuhamelHistorySourceSlotSum (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase
        entry block slot (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  refine (integrable_canonicalPotentialSourceSlotObservable_fixedTime
    hN ha0 ha1 flowKappa flowBeta flowG hflowBeta 0 1 1
    entry hpositive block slot time).congr ?_
  filter_upwards [
    canonicalPotentialUnitQuarticSourceSlotObservable_eq_historySum_ae
      (show 2 <= N by omega) flowKappa flowBeta flowG hflowBeta a
      radius phase entry block slot time] with omega hsum
  simpa [canonicalQuarticDuhamelHistorySourceSlotSum] using hsum

/-- Aggregate quadratic history integration is exactly the existing unit
source-slot Bochner integral. -/
theorem integral_canonicalQuadraticDuhamelHistorySourceSlotSum_eq_sourceSlot
    (hN : 2 <= N)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I) (time : Real) :
    (∫ omega,
      canonicalQuadraticDuhamelHistorySourceSlotSum (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase
        entry block slot (omega, time)
      ∂canonicalIIDMassPhaseEnsemble.probability) =
      canonicalPotentialSourceSlotBochnerIntegral (N := N)
        flowKappa flowBeta flowG hflowBeta a 1 0 1
        entry block slot time := by
  unfold canonicalPotentialSourceSlotBochnerIntegral
  apply integral_congr_ae
  filter_upwards [
    canonicalPotentialUnitQuadraticSourceSlotObservable_eq_historySum_ae
      hN flowKappa flowBeta flowG hflowBeta a radius phase
      entry block slot time] with omega hsum
  simpa [canonicalQuadraticDuhamelHistorySourceSlotSum] using hsum.symm

/-- Aggregate quartic history integration is exactly the existing unit
source-slot Bochner integral. -/
theorem integral_canonicalQuarticDuhamelHistorySourceSlotSum_eq_sourceSlot
    (hN : 2 <= N)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I) (time : Real) :
    (∫ omega,
      canonicalQuarticDuhamelHistorySourceSlotSum (N := N)
        flowKappa flowBeta flowG hflowBeta a radius phase
        entry block slot (omega, time)
      ∂canonicalIIDMassPhaseEnsemble.probability) =
      canonicalPotentialSourceSlotBochnerIntegral (N := N)
        flowKappa flowBeta flowG hflowBeta a 0 1 1
        entry block slot time := by
  unfold canonicalPotentialSourceSlotBochnerIntegral
  apply integral_congr_ae
  filter_upwards [
    canonicalPotentialUnitQuarticSourceSlotObservable_eq_historySum_ae
      hN flowKappa flowBeta flowG hflowBeta a radius phase
      entry block slot time] with omega hsum
  simpa [canonicalQuarticDuhamelHistorySourceSlotSum] using hsum.symm

end

end ArchonPhysics.CanonicalIIDCoerciveActualDuhamelHistoryBochnerGardenBridge
