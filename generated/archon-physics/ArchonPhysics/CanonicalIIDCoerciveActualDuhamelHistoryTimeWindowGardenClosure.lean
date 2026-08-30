import ArchonPhysics.CanonicalIIDCoerciveActualDefectSquareTimeWindowBochner
import ArchonPhysics.CanonicalIIDCoerciveActualDuhamelHistoryBochnerGardenBridge
import ArchonPhysics.CanonicalIIDCoerciveActualFreePrimitiveTimeWindowBochner
import ArchonPhysics.CanonicalIIDCoerciveActualPotentialSourceSlotTimeWindowBochner
import ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardSourceTimeWindowBochner
import ArchonPhysics.CanonicalIIDCoerciveActualTimeWindowBlockMultiplier
import ArchonPhysics.CanonicalRandomMassGlobalFlow
import ArchonPhysics.FiniteSymmetricWindowLocalIntegrability

/-!
# Finite-time-window closure for all actual Duhamel histories and gardens

The four explicit actual primitive sources are jointly Bochner integrable on
every fixed compact time window.  Multiplication by the displayed canonical
block gives the corresponding source slots.  The exact almost-sure
source-slot history reconstruction then isolates the two remaining histories
by subtraction from the complete unit source slot.

Thus every individual quadratic or quartic history slot, every finite history
sum, and every garden-sector contribution is jointly integrable.  Their finite
sums commute term by term with the product integral and satisfy the ordinary
finite-window Fubini theorem.  Nothing here is uniform in the window or on a
kinetic time scale.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualDuhamelHistoryTimeWindowGardenClosure

open scoped BigOperators
open Set
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualDefectSquareTimeWindowBochner
open ArchonPhysics.CanonicalIIDCoerciveActualDuhamelHistoryBochnerGardenBridge
open ArchonPhysics.CanonicalIIDCoerciveActualFreeQuadraticHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualFreePrimitiveTimeWindowBochner
open ArchonPhysics.CanonicalIIDCoerciveActualGardenHistoryDecomposition
open ArchonPhysics.CanonicalIIDCoerciveActualPointwiseDuhamelHistoryExpansion
open ArchonPhysics.CanonicalIIDCoerciveActualPotentialSourceSlotTimeWindowBochner
open ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardSourceTimeWindowBochner
open ArchonPhysics.CanonicalIIDCoerciveActualTimeWindowBlockMultiplier
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSourceSlotExpectationClosure
open ArchonPhysics.CanonicalRandomMassGlobalFlow
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.FiniteSymmetricWindowLocalIntegrability
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTActualDuhamelSourceHistoryExpansion
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Product measure used throughout this strictly finite-window module. -/
abbrev canonicalActualHistoryTimeWindowMeasure (window : Real) :
    Measure (Real × CanonicalSample) :=
  (volume.restrict (Icc (-window) window)).prod
    canonicalIIDMassPhaseEnsemble.probability

/-- The free quadratic primitive remains jointly integrable after insertion
into an arbitrary displayed source slot. -/
theorem integrable_canonicalQuadraticFreeFirstPicardHistorySlot_timeWindow
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (window : Real) :
    Integrable (fun st : Real × CanonicalSample =>
      canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot .freeFirstPicard (st.2, st.1))
      (canonicalActualHistoryTimeWindowMeasure window) := by
  exact integrable_canonicalQuadraticHistorySlot_timeWindow_of_source
    (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      (canonicalOrientedPhyslibFreeRadius (N := N) a)
      (canonicalReindexedPhyslibHaarPhase (N := N))
      entry hpositive block slot .freeFirstPicard window
      (integrable_canonicalQuadraticFreeFirstPicardSource_timeWindow
        (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        (entry slot) (hpositive slot) window)

/-- The quadratic second-Picard primitive has the same displayed-slot
finite-window closure. -/
theorem integrable_canonicalQuadraticSecondPicardHistorySlot_timeWindow
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (window : Real) :
    Integrable (fun st : Real × CanonicalSample =>
      canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot .quadraticSecondPicard (st.2, st.1))
      (canonicalActualHistoryTimeWindowMeasure window) := by
  exact integrable_canonicalQuadraticHistorySlot_timeWindow_of_source
    (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      (canonicalOrientedPhyslibFreeRadius (N := N) a)
      (canonicalReindexedPhyslibHaarPhase (N := N))
      entry hpositive block slot .quadraticSecondPicard window
      (integrable_canonicalQuadraticSecondPicardDuhamelSource_timeWindow
        (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        (entry slot) (hpositive slot) window)

/-- The defect-square primitive is jointly integrable after insertion into a
displayed slot.  The finite-lattice Poincare constant and the coupling
envelope \`|flowG|\` are discharged canonically. -/
theorem integrable_canonicalQuadraticDefectSquareHistorySlot_timeWindow
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (window : Real) :
    Integrable (fun st : Real × CanonicalSample =>
      canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot .defectSquare (st.2, st.1))
      (canonicalActualHistoryTimeWindowMeasure window) := by
  apply integrable_canonicalQuadraticHistorySlot_timeWindow_of_source
    (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      (canonicalOrientedPhyslibFreeRadius (N := N) a)
      (canonicalReindexedPhyslibHaarPhase (N := N))
      entry hpositive block slot .defectSquare window
  exact integrable_canonicalQuadraticDefectSquareSource_timeWindow
    (N := N) hN ha0 ha1
      (canonicalUniformPoincareConstant N)
      (canonicalUniformPoincareConstant_pos N).le
      (canonicalUniformPoincareConstant_spec N)
      flowKappa flowBeta flowG |flowG| hflowBeta
      (abs_nonneg flowG) le_rfl (entry slot) (hpositive slot) window

/-- The free-cubic quartic primitive remains jointly integrable in every
displayed source slot. -/
theorem integrable_canonicalQuarticFreeCubicHistorySlot_timeWindow
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (window : Real) :
    Integrable (fun st : Real × CanonicalSample =>
      canonicalQuarticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot .freeCubicSecondPicard (st.2, st.1))
      (canonicalActualHistoryTimeWindowMeasure window) := by
  exact integrable_canonicalQuarticHistorySlot_timeWindow_of_source
    (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      (canonicalOrientedPhyslibFreeRadius (N := N) a)
      (canonicalReindexedPhyslibHaarPhase (N := N))
      entry hpositive block slot .freeCubicSecondPicard window
      (integrable_canonicalQuarticFreeCubicSource_timeWindow
        (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        (entry slot) (hpositive slot) window)

/-- Subtracting the three explicit quadratic slots from the complete unit
quadratic source slot isolates the actual linear-history remainder. -/
theorem integrable_canonicalQuadraticLinearHistoryRemainderSlot_timeWindow
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (window : Real) :
    Integrable (fun st : Real × CanonicalSample =>
      canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot .linearHistoryRemainder (st.2, st.1))
      (canonicalActualHistoryTimeWindowMeasure window) := by
  have hcomplete :=
    integrable_canonicalPotentialUnitQuadraticSourceSlot_timeWindow
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive block slot window
  have hfree :=
    integrable_canonicalQuadraticFreeFirstPicardHistorySlot_timeWindow
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive block slot window
  have hsecond :=
    integrable_canonicalQuadraticSecondPicardHistorySlot_timeWindow
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive block slot window
  have hdefect :=
    integrable_canonicalQuadraticDefectSquareHistorySlot_timeWindow
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive block slot window
  refine (((hcomplete.sub hfree).sub hsecond).sub hdefect).congr ?_
  have hsimpleBase :=
    RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae (N := N)
      canonicalIIDMassPhaseEnsemble (by omega)
  have hsimpleAE :=
    (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (Icc (-window) window))
      (ν := canonicalIIDMassPhaseEnsemble.probability)).ae hsimpleBase
  filter_upwards [hsimpleAE] with st hsimple
  have hsimple' : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) st.2)) := by
    simpa [harmonicHermitianSample, harmonicHermitian, canonicalMass]
      using hsimple
  have hsum :=
    canonicalPotentialUnitQuadraticSourceSlotObservable_eq_historySum
      flowKappa flowBeta flowG hflowBeta a
      (canonicalOrientedPhyslibFreeRadius (N := N) a)
      (canonicalReindexedPhyslibHaarPhase (N := N))
      entry block slot st.2 hsimple' st.1
  simp [actualQuadraticSourceHistories] at hsum
  simp only [Pi.sub_apply]
  linear_combination hsum

/-- Subtracting the free-cubic slot from the complete unit-quartic slot
isolates the actual cubic-history remainder. -/
theorem integrable_canonicalQuarticCubicHistoryRemainderSlot_timeWindow
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (window : Real) :
    Integrable (fun st : Real × CanonicalSample =>
      canonicalQuarticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot .cubicHistoryRemainder (st.2, st.1))
      (canonicalActualHistoryTimeWindowMeasure window) := by
  have hcomplete :=
    integrable_canonicalPotentialUnitQuarticSourceSlot_timeWindow
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive block slot window
  have hfree :=
    integrable_canonicalQuarticFreeCubicHistorySlot_timeWindow
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive block slot window
  refine (hcomplete.sub hfree).congr ?_
  have hsimpleBase :=
    RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae (N := N)
      canonicalIIDMassPhaseEnsemble (by omega)
  have hsimpleAE :=
    (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (Icc (-window) window))
      (ν := canonicalIIDMassPhaseEnsemble.probability)).ae hsimpleBase
  filter_upwards [hsimpleAE] with st hsimple
  have hsimple' : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) st.2)) := by
    simpa [harmonicHermitianSample, harmonicHermitian, canonicalMass]
      using hsimple
  have hsum :=
    canonicalPotentialUnitQuarticSourceSlotObservable_eq_historySum
      flowKappa flowBeta flowG hflowBeta a
      (canonicalOrientedPhyslibFreeRadius (N := N) a)
      (canonicalReindexedPhyslibHaarPhase (N := N))
      entry block slot st.2 hsimple' st.1
  simp [actualQuarticSourceHistories] at hsum
  simp only [Pi.sub_apply]
  linear_combination hsum

/-- Every actual quadratic history slot is jointly Bochner integrable on the
fixed compact time window. -/
theorem integrable_canonicalQuadraticHistorySlot_timeWindow_closed
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (window : Real)
    (history : ActualQuadraticSourceHistory) :
    Integrable (fun st : Real × CanonicalSample =>
      canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot history (st.2, st.1))
      (canonicalActualHistoryTimeWindowMeasure window) := by
  cases history with
  | freeFirstPicard =>
      exact integrable_canonicalQuadraticFreeFirstPicardHistorySlot_timeWindow
        (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive block slot window
  | quadraticSecondPicard =>
      exact integrable_canonicalQuadraticSecondPicardHistorySlot_timeWindow
        (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive block slot window
  | linearHistoryRemainder =>
      exact integrable_canonicalQuadraticLinearHistoryRemainderSlot_timeWindow
        (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive block slot window
  | defectSquare =>
      exact integrable_canonicalQuadraticDefectSquareHistorySlot_timeWindow
        (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive block slot window

/-- Every actual quartic history slot is jointly Bochner integrable on the
fixed compact time window. -/
theorem integrable_canonicalQuarticHistorySlot_timeWindow_closed
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (window : Real)
    (history : ActualQuarticSourceHistory) :
    Integrable (fun st : Real × CanonicalSample =>
      canonicalQuarticDuhamelHistorySourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot history (st.2, st.1))
      (canonicalActualHistoryTimeWindowMeasure window) := by
  cases history with
  | freeCubicSecondPicard =>
      exact integrable_canonicalQuarticFreeCubicHistorySlot_timeWindow
        (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive block slot window
  | cubicHistoryRemainder =>
      exact integrable_canonicalQuarticCubicHistoryRemainderSlot_timeWindow
        (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive block slot window
/-- The complete finite quadratic history sum is jointly integrable on the
fixed compact time window. -/
theorem integrable_canonicalQuadraticDuhamelHistorySourceSlotSum_timeWindow_closed
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (window : Real) :
    Integrable (fun st : Real × CanonicalSample =>
      canonicalQuadraticDuhamelHistorySourceSlotSum (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot (st.2, st.1))
      (canonicalActualHistoryTimeWindowMeasure window) := by
  unfold canonicalQuadraticDuhamelHistorySourceSlotSum
  apply integrable_finsetSum
  intro history _hhistory
  exact integrable_canonicalQuadraticHistorySlot_timeWindow_closed
    (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive block slot window history

/-- The complete finite quartic history sum is jointly integrable on the
fixed compact time window. -/
theorem integrable_canonicalQuarticDuhamelHistorySourceSlotSum_timeWindow_closed
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (window : Real) :
    Integrable (fun st : Real × CanonicalSample =>
      canonicalQuarticDuhamelHistorySourceSlotSum (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot (st.2, st.1))
      (canonicalActualHistoryTimeWindowMeasure window) := by
  unfold canonicalQuarticDuhamelHistorySourceSlotSum
  apply integrable_finsetSum
  intro history _hhistory
  exact integrable_canonicalQuarticHistorySlot_timeWindow_closed
    (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive block slot window history

/-- Every quadratic garden-sector contribution is jointly integrable on the
fixed compact time window. -/
theorem integrable_canonicalQuadraticDuhamelHistorySectorContribution_timeWindow_closed
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (target : GardenHistorySector)
    (window : Real) :
    Integrable (fun st : Real × CanonicalSample =>
      canonicalQuadraticDuhamelHistorySectorContribution (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot target (st.2, st.1))
      (canonicalActualHistoryTimeWindowMeasure window) := by
  unfold canonicalQuadraticDuhamelHistorySectorContribution
    finiteHistorySectorContribution
  apply integrable_finsetSum
  intro history _hhistory
  by_cases hsector : actualQuadraticHistorySector history = target
  · simp only [hsector, if_true]
    exact integrable_canonicalQuadraticHistorySlot_timeWindow_closed
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive block slot window history
  · simp only [hsector, if_false]
    exact integrable_zero (Real × CanonicalSample) Complex
      (canonicalActualHistoryTimeWindowMeasure window)

/-- Every quartic garden-sector contribution is jointly integrable on the
fixed compact time window. -/
theorem integrable_canonicalQuarticDuhamelHistorySectorContribution_timeWindow_closed
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (target : GardenHistorySector)
    (window : Real) :
    Integrable (fun st : Real × CanonicalSample =>
      canonicalQuarticDuhamelHistorySectorContribution (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot target (st.2, st.1))
      (canonicalActualHistoryTimeWindowMeasure window) := by
  unfold canonicalQuarticDuhamelHistorySectorContribution
    finiteHistorySectorContribution
  apply integrable_finsetSum
  intro history _hhistory
  by_cases hsector : actualQuarticHistorySector history = target
  · simp only [hsector, if_true]
    exact integrable_canonicalQuarticHistorySlot_timeWindow_closed
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive block slot window history
  · simp only [hsector, if_false]
    exact integrable_zero (Real × CanonicalSample) Complex
      (canonicalActualHistoryTimeWindowMeasure window)

/-- The quadratic history sum commutes term by term with its product-measure
Bochner integral. -/
theorem integral_canonicalQuadraticDuhamelHistorySourceSlotSum_timeWindow_eq_sum
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (window : Real) :
    (∫ st : Real × CanonicalSample,
      canonicalQuadraticDuhamelHistorySourceSlotSum (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot (st.2, st.1)
      ∂(canonicalActualHistoryTimeWindowMeasure window)) =
      ∑ history ∈ actualQuadraticSourceHistories,
        ∫ st : Real × CanonicalSample,
          canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
            flowKappa flowBeta flowG hflowBeta a
            (canonicalOrientedPhyslibFreeRadius (N := N) a)
            (canonicalReindexedPhyslibHaarPhase (N := N))
            entry block slot history (st.2, st.1)
          ∂(canonicalActualHistoryTimeWindowMeasure window) := by
  unfold canonicalQuadraticDuhamelHistorySourceSlotSum
  exact integral_finsetSum actualQuadraticSourceHistories
    (fun history _hhistory =>
      integrable_canonicalQuadraticHistorySlot_timeWindow_closed
        (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive block slot window history)

/-- The quartic history sum commutes term by term with its product-measure
Bochner integral. -/
theorem integral_canonicalQuarticDuhamelHistorySourceSlotSum_timeWindow_eq_sum
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (window : Real) :
    (∫ st : Real × CanonicalSample,
      canonicalQuarticDuhamelHistorySourceSlotSum (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot (st.2, st.1)
      ∂(canonicalActualHistoryTimeWindowMeasure window)) =
      ∑ history ∈ actualQuarticSourceHistories,
        ∫ st : Real × CanonicalSample,
          canonicalQuarticDuhamelHistorySourceSlotObservable (N := N)
            flowKappa flowBeta flowG hflowBeta a
            (canonicalOrientedPhyslibFreeRadius (N := N) a)
            (canonicalReindexedPhyslibHaarPhase (N := N))
            entry block slot history (st.2, st.1)
          ∂(canonicalActualHistoryTimeWindowMeasure window) := by
  unfold canonicalQuarticDuhamelHistorySourceSlotSum
  exact integral_finsetSum actualQuarticSourceHistories
    (fun history _hhistory =>
      integrable_canonicalQuarticHistorySlot_timeWindow_closed
        (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive block slot window history)

/-- Each quadratic sector product integral is its finite filtered termwise
history integral. -/
theorem integral_canonicalQuadraticDuhamelHistorySectorContribution_timeWindow_eq_sum
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (target : GardenHistorySector)
    (window : Real) :
    (∫ st : Real × CanonicalSample,
      canonicalQuadraticDuhamelHistorySectorContribution (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot target (st.2, st.1)
      ∂(canonicalActualHistoryTimeWindowMeasure window)) =
      ∑ history ∈ actualQuadraticSourceHistories,
        if actualQuadraticHistorySector history = target then
          ∫ st : Real × CanonicalSample,
            canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
              flowKappa flowBeta flowG hflowBeta a
              (canonicalOrientedPhyslibFreeRadius (N := N) a)
              (canonicalReindexedPhyslibHaarPhase (N := N))
              entry block slot history (st.2, st.1)
            ∂(canonicalActualHistoryTimeWindowMeasure window)
        else 0 := by
  unfold canonicalQuadraticDuhamelHistorySectorContribution
    finiteHistorySectorContribution
  rw [integral_finsetSum actualQuadraticSourceHistories]
  · apply Finset.sum_congr rfl
    intro history _hhistory
    by_cases hsector : actualQuadraticHistorySector history = target
    · simp [hsector]
    · simp [hsector]
  · intro history _hhistory
    by_cases hsector : actualQuadraticHistorySector history = target
    · simp only [hsector, if_true]
      exact integrable_canonicalQuadraticHistorySlot_timeWindow_closed
        (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive block slot window history
    · simp only [hsector, if_false]
      exact integrable_zero (Real × CanonicalSample) Complex
        (canonicalActualHistoryTimeWindowMeasure window)

/-- Each quartic sector product integral is its finite filtered termwise
history integral. -/
theorem integral_canonicalQuarticDuhamelHistorySectorContribution_timeWindow_eq_sum
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (target : GardenHistorySector)
    (window : Real) :
    (∫ st : Real × CanonicalSample,
      canonicalQuarticDuhamelHistorySectorContribution (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot target (st.2, st.1)
      ∂(canonicalActualHistoryTimeWindowMeasure window)) =
      ∑ history ∈ actualQuarticSourceHistories,
        if actualQuarticHistorySector history = target then
          ∫ st : Real × CanonicalSample,
            canonicalQuarticDuhamelHistorySourceSlotObservable (N := N)
              flowKappa flowBeta flowG hflowBeta a
              (canonicalOrientedPhyslibFreeRadius (N := N) a)
              (canonicalReindexedPhyslibHaarPhase (N := N))
              entry block slot history (st.2, st.1)
            ∂(canonicalActualHistoryTimeWindowMeasure window)
        else 0 := by
  unfold canonicalQuarticDuhamelHistorySectorContribution
    finiteHistorySectorContribution
  rw [integral_finsetSum actualQuarticSourceHistories]
  · apply Finset.sum_congr rfl
    intro history _hhistory
    by_cases hsector : actualQuarticHistorySector history = target
    · simp [hsector]
    · simp [hsector]
  · intro history _hhistory
    by_cases hsector : actualQuarticHistorySector history = target
    · simp only [hsector, if_true]
      exact integrable_canonicalQuarticHistorySlot_timeWindow_closed
        (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive block slot window history
    · simp only [hsector, if_false]
      exact integrable_zero (Real × CanonicalSample) Complex
        (canonicalActualHistoryTimeWindowMeasure window)

/-- The complete unit-quadratic source slot equals the full history sum almost
everywhere on the time-window product space. -/
theorem canonicalPotentialUnitQuadraticSourceSlot_eq_historySum_timeWindow_ae
    (hN : 2 <= N)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I) (window : Real) :
    ∀ᵐ st ∂(canonicalActualHistoryTimeWindowMeasure window),
      canonicalPotentialSourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a 1 0 1
          entry block slot (st.2, st.1) =
        canonicalQuadraticDuhamelHistorySourceSlotSum (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry block slot (st.2, st.1) := by
  have hsimpleBase :=
    RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae (N := N)
      canonicalIIDMassPhaseEnsemble hN
  have hsimpleAE :=
    (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (Icc (-window) window))
      (ν := canonicalIIDMassPhaseEnsemble.probability)).ae hsimpleBase
  filter_upwards [hsimpleAE] with st hsimple
  have hsimple' : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) st.2)) := by
    simpa [harmonicHermitianSample, harmonicHermitian, canonicalMass]
      using hsimple
  simpa [canonicalQuadraticDuhamelHistorySourceSlotSum] using
    (canonicalPotentialUnitQuadraticSourceSlotObservable_eq_historySum
      flowKappa flowBeta flowG hflowBeta a
      (canonicalOrientedPhyslibFreeRadius (N := N) a)
      (canonicalReindexedPhyslibHaarPhase (N := N))
      entry block slot st.2 hsimple' st.1)

/-- The complete unit-quartic source slot equals the full history sum almost
everywhere on the time-window product space. -/
theorem canonicalPotentialUnitQuarticSourceSlot_eq_historySum_timeWindow_ae
    (hN : 2 <= N)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I) (window : Real) :
    ∀ᵐ st ∂(canonicalActualHistoryTimeWindowMeasure window),
      canonicalPotentialSourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a 0 1 1
          entry block slot (st.2, st.1) =
        canonicalQuarticDuhamelHistorySourceSlotSum (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry block slot (st.2, st.1) := by
  have hsimpleBase :=
    RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae (N := N)
      canonicalIIDMassPhaseEnsemble hN
  have hsimpleAE :=
    (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (Icc (-window) window))
      (ν := canonicalIIDMassPhaseEnsemble.probability)).ae hsimpleBase
  filter_upwards [hsimpleAE] with st hsimple
  have hsimple' : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) st.2)) := by
    simpa [harmonicHermitianSample, harmonicHermitian, canonicalMass]
      using hsimple
  simpa [canonicalQuarticDuhamelHistorySourceSlotSum] using
    (canonicalPotentialUnitQuarticSourceSlotObservable_eq_historySum
      flowKappa flowBeta flowG hflowBeta a
      (canonicalOrientedPhyslibFreeRadius (N := N) a)
      (canonicalReindexedPhyslibHaarPhase (N := N))
      entry block slot st.2 hsimple' st.1)

/-- Almost every canonical sample has an integrable time section of the full
quadratic history sum on the prescribed window. -/
theorem ae_integrable_time_canonicalQuadraticDuhamelHistorySourceSlotSum
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (window : Real) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      Integrable (fun time : Real =>
        canonicalQuadraticDuhamelHistorySourceSlotSum (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry block slot (omega, time))
        (volume.restrict (Icc (-window) window)) := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  exact
    (integrable_canonicalQuadraticDuhamelHistorySourceSlotSum_timeWindow_closed
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive block slot window).prod_left_ae

/-- Almost every canonical sample has an integrable time section of the full
quartic history sum on the prescribed window. -/
theorem ae_integrable_time_canonicalQuarticDuhamelHistorySourceSlotSum
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (window : Real) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      Integrable (fun time : Real =>
        canonicalQuarticDuhamelHistorySourceSlotSum (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry block slot (omega, time))
        (volume.restrict (Icc (-window) window)) := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  exact
    (integrable_canonicalQuarticDuhamelHistorySourceSlotSum_timeWindow_closed
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive block slot window).prod_left_ae

/-- Almost every sample has an integrable time section of every quadratic
garden-sector contribution. -/
theorem ae_integrable_time_canonicalQuadraticDuhamelHistorySectorContribution
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (target : GardenHistorySector)
    (window : Real) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      Integrable (fun time : Real =>
        canonicalQuadraticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry block slot target (omega, time))
        (volume.restrict (Icc (-window) window)) := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  exact
    (integrable_canonicalQuadraticDuhamelHistorySectorContribution_timeWindow_closed
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive block slot target window).prod_left_ae

/-- Almost every sample has an integrable time section of every quartic
garden-sector contribution. -/
theorem ae_integrable_time_canonicalQuarticDuhamelHistorySectorContribution
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (target : GardenHistorySector)
    (window : Real) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      Integrable (fun time : Real =>
        canonicalQuarticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry block slot target (omega, time))
        (volume.restrict (Icc (-window) window)) := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  exact
    (integrable_canonicalQuarticDuhamelHistorySectorContribution_timeWindow_closed
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive block slot target window).prod_left_ae

/-- Fubini for the complete quadratic history sum on the fixed window. -/
theorem integral_canonicalQuadraticDuhamelHistorySourceSlotSum_timeWindow_eq_iterated
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (window : Real) :
    (∫ st : Real × CanonicalSample,
      canonicalQuadraticDuhamelHistorySourceSlotSum (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot (st.2, st.1)
      ∂(canonicalActualHistoryTimeWindowMeasure window)) =
      ∫ omega : CanonicalSample,
        ∫ time : Real,
          canonicalQuadraticDuhamelHistorySourceSlotSum (N := N)
            flowKappa flowBeta flowG hflowBeta a
            (canonicalOrientedPhyslibFreeRadius (N := N) a)
            (canonicalReindexedPhyslibHaarPhase (N := N))
            entry block slot (omega, time)
          ∂(volume.restrict (Icc (-window) window))
        ∂canonicalIIDMassPhaseEnsemble.probability := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  exact integral_prod_symm _
    (integrable_canonicalQuadraticDuhamelHistorySourceSlotSum_timeWindow_closed
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive block slot window)

/-- Fubini for the complete quartic history sum on the fixed window. -/
theorem integral_canonicalQuarticDuhamelHistorySourceSlotSum_timeWindow_eq_iterated
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (window : Real) :
    (∫ st : Real × CanonicalSample,
      canonicalQuarticDuhamelHistorySourceSlotSum (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot (st.2, st.1)
      ∂(canonicalActualHistoryTimeWindowMeasure window)) =
      ∫ omega : CanonicalSample,
        ∫ time : Real,
          canonicalQuarticDuhamelHistorySourceSlotSum (N := N)
            flowKappa flowBeta flowG hflowBeta a
            (canonicalOrientedPhyslibFreeRadius (N := N) a)
            (canonicalReindexedPhyslibHaarPhase (N := N))
            entry block slot (omega, time)
          ∂(volume.restrict (Icc (-window) window))
        ∂canonicalIIDMassPhaseEnsemble.probability := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  exact integral_prod_symm _
    (integrable_canonicalQuarticDuhamelHistorySourceSlotSum_timeWindow_closed
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive block slot window)

/-- Fubini for every quadratic garden sector on the fixed window. -/
theorem integral_canonicalQuadraticDuhamelHistorySectorContribution_timeWindow_eq_iterated
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (target : GardenHistorySector)
    (window : Real) :
    (∫ st : Real × CanonicalSample,
      canonicalQuadraticDuhamelHistorySectorContribution (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot target (st.2, st.1)
      ∂(canonicalActualHistoryTimeWindowMeasure window)) =
      ∫ omega : CanonicalSample,
        ∫ time : Real,
          canonicalQuadraticDuhamelHistorySectorContribution (N := N)
            flowKappa flowBeta flowG hflowBeta a
            (canonicalOrientedPhyslibFreeRadius (N := N) a)
            (canonicalReindexedPhyslibHaarPhase (N := N))
            entry block slot target (omega, time)
          ∂(volume.restrict (Icc (-window) window))
        ∂canonicalIIDMassPhaseEnsemble.probability := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  exact integral_prod_symm _
    (integrable_canonicalQuadraticDuhamelHistorySectorContribution_timeWindow_closed
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive block slot target window)

/-- Fubini for every quartic garden sector on the fixed window. -/
theorem integral_canonicalQuarticDuhamelHistorySectorContribution_timeWindow_eq_iterated
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (target : GardenHistorySector)
    (window : Real) :
    (∫ st : Real × CanonicalSample,
      canonicalQuarticDuhamelHistorySectorContribution (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot target (st.2, st.1)
      ∂(canonicalActualHistoryTimeWindowMeasure window)) =
      ∫ omega : CanonicalSample,
        ∫ time : Real,
          canonicalQuarticDuhamelHistorySectorContribution (N := N)
            flowKappa flowBeta flowG hflowBeta a
            (canonicalOrientedPhyslibFreeRadius (N := N) a)
            (canonicalReindexedPhyslibHaarPhase (N := N))
            entry block slot target (omega, time)
          ∂(volume.restrict (Icc (-window) window))
        ∂canonicalIIDMassPhaseEnsemble.probability := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  exact integral_prod_symm _
    (integrable_canonicalQuarticDuhamelHistorySectorContribution_timeWindow_closed
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive block slot target window)

/-- The finite-window quadratic statements simultaneously imply that almost
every complete time section is locally integrable on the real line.  This is
not a global-in-time integral bound. -/
theorem ae_locallyIntegrable_time_canonicalQuadraticDuhamelHistorySourceSlotSum
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      LocallyIntegrable (fun time : Real =>
        canonicalQuadraticDuhamelHistorySourceSlotSum (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry block slot (omega, time)) volume := by
  apply ae_locallyIntegrable_of_ae_integrable_symmetric_natWindows
  intro n
  exact ae_integrable_time_canonicalQuadraticDuhamelHistorySourceSlotSum
    (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
    entry hpositive block slot (n : Real)

/-- Almost every complete quartic-history time section is locally integrable
on the real line. -/
theorem ae_locallyIntegrable_time_canonicalQuarticDuhamelHistorySourceSlotSum
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      LocallyIntegrable (fun time : Real =>
        canonicalQuarticDuhamelHistorySourceSlotSum (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry block slot (omega, time)) volume := by
  apply ae_locallyIntegrable_of_ae_integrable_symmetric_natWindows
  intro n
  exact ae_integrable_time_canonicalQuarticDuhamelHistorySourceSlotSum
    (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
    entry hpositive block slot (n : Real)

/-- Almost every quadratic sector time section is locally integrable on the
real line. -/
theorem ae_locallyIntegrable_time_canonicalQuadraticDuhamelHistorySectorContribution
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (target : GardenHistorySector) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      LocallyIntegrable (fun time : Real =>
        canonicalQuadraticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry block slot target (omega, time)) volume := by
  apply ae_locallyIntegrable_of_ae_integrable_symmetric_natWindows
  intro n
  exact ae_integrable_time_canonicalQuadraticDuhamelHistorySectorContribution
    (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
    entry hpositive block slot target (n : Real)

/-- Almost every quartic sector time section is locally integrable on the
real line. -/
theorem ae_locallyIntegrable_time_canonicalQuarticDuhamelHistorySectorContribution
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (target : GardenHistorySector) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      LocallyIntegrable (fun time : Real =>
        canonicalQuarticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry block slot target (omega, time)) volume := by
  apply ae_locallyIntegrable_of_ae_integrable_symmetric_natWindows
  intro n
  exact ae_integrable_time_canonicalQuarticDuhamelHistorySectorContribution
    (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
    entry hpositive block slot target (n : Real)


end
end ArchonPhysics.CanonicalIIDCoerciveActualDuhamelHistoryTimeWindowGardenClosure
