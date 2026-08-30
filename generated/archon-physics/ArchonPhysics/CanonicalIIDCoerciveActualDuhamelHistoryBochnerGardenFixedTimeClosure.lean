import ArchonPhysics.CanonicalIIDCoerciveActualDuhamelFixedTimeClosure
import ArchonPhysics.CanonicalIIDCoerciveActualDuhamelHistoryBochnerGardenBridge

/-!
# Closed fixed-time Bochner calculus for actual Duhamel garden histories

The canonical fixed-mass/Haar reference now makes every individual quadratic
and quartic source history integrable.  This module uses that closure to
justify sectorwise integrability and exchange of each finite history sum with
the annealed Bochner integral.  It is purely finite-time and finite-volume.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualDuhamelHistoryBochnerGardenFixedTimeClosure

open scoped BigOperators
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualDuhamelFixedTimeClosure
open ArchonPhysics.CanonicalIIDCoerciveActualDuhamelHistoryBochnerGardenBridge
open ArchonPhysics.CanonicalIIDCoerciveActualDuhamelHistoryTermIntegrabilityReduction
open ArchonPhysics.CanonicalIIDCoerciveActualFreeQuadraticHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualGardenHistoryDecomposition
open ArchonPhysics.CanonicalIIDCoerciveActualPointwiseDuhamelHistoryExpansion
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.CanonicalIIDCoerciveSourceSlotExpectationClosure
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTActualDuhamelSourceHistoryExpansion
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Four-way finite additivity of the Bochner integral, stated pointwise so
it matches the garden-sector normal form directly. -/
theorem integral_add_four_complex
    {S : Type*} [MeasurableSpace S] (mu : Measure S)
    (f g h r : S -> Complex)
    (hf : Integrable f mu) (hg : Integrable g mu)
    (hh : Integrable h mu) (hr : Integrable r mu) :
    (∫ x, f x + g x + h x + r x ∂mu) =
      (∫ x, f x ∂mu) + (∫ x, g x ∂mu) +
        (∫ x, h x ∂mu) + ∫ x, r x ∂mu := by
  have hfg :
      (∫ x, f x + g x ∂mu) =
        (∫ x, f x ∂mu) + ∫ x, g x ∂mu := by
    simpa only [Pi.add_apply] using integral_add hf hg
  have hfgh :
      (∫ x, f x + g x + h x ∂mu) =
        (∫ x, f x + g x ∂mu) + ∫ x, h x ∂mu := by
    simpa only [Pi.add_apply] using integral_add (hf.add hg) hh
  have hfghr :
      (∫ x, f x + g x + h x + r x ∂mu) =
        (∫ x, f x + g x + h x ∂mu) + ∫ x, r x ∂mu := by
    simpa only [Pi.add_apply] using integral_add ((hf.add hg).add hh) hr
  rw [hfghr, hfgh, hfg]

/-- Every quadratic garden sector is integrable after specializing to the
actual canonical oriented radius and Haar phase. -/
theorem integrable_canonicalQuadraticDuhamelHistorySectorContribution_fixedTime_closed
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (target : GardenHistorySector)
    (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySectorContribution (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot target (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  unfold canonicalQuadraticDuhamelHistorySectorContribution
    finiteHistorySectorContribution
  apply integrable_finsetSum
  intro history _hhistory
  by_cases hsector : actualQuadraticHistorySector history = target
  · simp only [hsector, if_true]
    exact integrable_canonicalQuadraticHistorySlot_fixedTime_closed
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive block slot time history
  · simp only [hsector, if_false]
    exact integrable_zero CanonicalSample Complex
      canonicalIIDMassPhaseEnsemble.probability

/-- Every quartic garden sector is integrable under the same model-native
specialization. -/
theorem integrable_canonicalQuarticDuhamelHistorySectorContribution_fixedTime_closed
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (target : GardenHistorySector)
    (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuarticDuhamelHistorySectorContribution (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot target (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  unfold canonicalQuarticDuhamelHistorySectorContribution
    finiteHistorySectorContribution
  apply integrable_finsetSum
  intro history _hhistory
  by_cases hsector : actualQuarticHistorySector history = target
  · simp only [hsector, if_true]
    exact integrable_canonicalQuarticHistorySlot_fixedTime_closed
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive block slot time history
  · simp only [hsector, if_false]
    exact integrable_zero CanonicalSample Complex
      canonicalIIDMassPhaseEnsemble.probability

/-- The complete quadratic finite history sum may be integrated term by
term, with no primitive-source or envelope hypothesis. -/
theorem integral_canonicalQuadraticDuhamelHistorySourceSlotSum_eq_sum_integrals_closed
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (time : Real) :
    (∫ omega,
      canonicalQuadraticDuhamelHistorySourceSlotSum (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot (omega, time)
      ∂canonicalIIDMassPhaseEnsemble.probability) =
      ∑ history ∈ actualQuadraticSourceHistories,
        ∫ omega,
          canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
            flowKappa flowBeta flowG hflowBeta a
            (canonicalOrientedPhyslibFreeRadius (N := N) a)
            (canonicalReindexedPhyslibHaarPhase (N := N))
            entry block slot history (omega, time)
          ∂canonicalIIDMassPhaseEnsemble.probability := by
  unfold canonicalQuadraticDuhamelHistorySourceSlotSum
  exact integral_finsetSum actualQuadraticSourceHistories
    (fun history _hhistory =>
      integrable_canonicalQuadraticHistorySlot_fixedTime_closed
        (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
          entry hpositive block slot time history)

/-- The complete quartic finite history sum also commutes with its Bochner
integral term by term. -/
theorem integral_canonicalQuarticDuhamelHistorySourceSlotSum_eq_sum_integrals_closed
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (time : Real) :
    (∫ omega,
      canonicalQuarticDuhamelHistorySourceSlotSum (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot (omega, time)
      ∂canonicalIIDMassPhaseEnsemble.probability) =
      ∑ history ∈ actualQuarticSourceHistories,
        ∫ omega,
          canonicalQuarticDuhamelHistorySourceSlotObservable (N := N)
            flowKappa flowBeta flowG hflowBeta a
            (canonicalOrientedPhyslibFreeRadius (N := N) a)
            (canonicalReindexedPhyslibHaarPhase (N := N))
            entry block slot history (omega, time)
          ∂canonicalIIDMassPhaseEnsemble.probability := by
  unfold canonicalQuarticDuhamelHistorySourceSlotSum
  exact integral_finsetSum actualQuarticSourceHistories
    (fun history _hhistory =>
      integrable_canonicalQuarticHistorySlot_fixedTime_closed
        (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
          entry hpositive block slot time history)

/-- Each quadratic sector integral is the finite filtered sum of the
individual history integrals belonging to that sector. -/
theorem integral_canonicalQuadraticDuhamelHistorySectorContribution_eq_sum_integrals_closed
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (target : GardenHistorySector)
    (time : Real) :
    (∫ omega,
      canonicalQuadraticDuhamelHistorySectorContribution (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot target (omega, time)
      ∂canonicalIIDMassPhaseEnsemble.probability) =
      ∑ history ∈ actualQuadraticSourceHistories,
        if actualQuadraticHistorySector history = target then
          ∫ omega,
            canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
              flowKappa flowBeta flowG hflowBeta a
              (canonicalOrientedPhyslibFreeRadius (N := N) a)
              (canonicalReindexedPhyslibHaarPhase (N := N))
              entry block slot history (omega, time)
            ∂canonicalIIDMassPhaseEnsemble.probability
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
      exact integrable_canonicalQuadraticHistorySlot_fixedTime_closed
        (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
          entry hpositive block slot time history
    · simp only [hsector, if_false]
      exact integrable_zero CanonicalSample Complex
        canonicalIIDMassPhaseEnsemble.probability

/-- The corresponding filtered termwise identity for every quartic sector. -/
theorem integral_canonicalQuarticDuhamelHistorySectorContribution_eq_sum_integrals_closed
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (target : GardenHistorySector)
    (time : Real) :
    (∫ omega,
      canonicalQuarticDuhamelHistorySectorContribution (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot target (omega, time)
      ∂canonicalIIDMassPhaseEnsemble.probability) =
      ∑ history ∈ actualQuarticSourceHistories,
        if actualQuarticHistorySector history = target then
          ∫ omega,
            canonicalQuarticDuhamelHistorySourceSlotObservable (N := N)
              flowKappa flowBeta flowG hflowBeta a
              (canonicalOrientedPhyslibFreeRadius (N := N) a)
              (canonicalReindexedPhyslibHaarPhase (N := N))
              entry block slot history (omega, time)
            ∂canonicalIIDMassPhaseEnsemble.probability
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
      exact integrable_canonicalQuarticHistorySlot_fixedTime_closed
        (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
          entry hpositive block slot time history
    · simp only [hsector, if_false]
      exact integrable_zero CanonicalSample Complex
        canonicalIIDMassPhaseEnsemble.probability

/-- The actual unit-quadratic source-slot Bochner integral is the sum of all
four individual canonical history integrals. -/
theorem canonicalPotentialUnitQuadraticSourceSlotBochnerIntegral_eq_sum_historyIntegrals_closed
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (time : Real) :
    canonicalPotentialSourceSlotBochnerIntegral (N := N)
        flowKappa flowBeta flowG hflowBeta a 1 0 1
        entry block slot time =
      ∑ history ∈ actualQuadraticSourceHistories,
        ∫ omega,
          canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
            flowKappa flowBeta flowG hflowBeta a
            (canonicalOrientedPhyslibFreeRadius (N := N) a)
            (canonicalReindexedPhyslibHaarPhase (N := N))
            entry block slot history (omega, time)
          ∂canonicalIIDMassPhaseEnsemble.probability := by
  calc
    _ = ∫ omega,
        canonicalQuadraticDuhamelHistorySourceSlotSum (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry block slot (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability :=
      (integral_canonicalQuadraticDuhamelHistorySourceSlotSum_eq_sourceSlot
        (N := N) (by omega) flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot time).symm
    _ = _ :=
      integral_canonicalQuadraticDuhamelHistorySourceSlotSum_eq_sum_integrals_closed
        (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
          entry hpositive block slot time

/-- The actual unit-quartic source-slot integral is likewise the sum of its
two individual history integrals. -/
theorem canonicalPotentialUnitQuarticSourceSlotBochnerIntegral_eq_sum_historyIntegrals_closed
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (time : Real) :
    canonicalPotentialSourceSlotBochnerIntegral (N := N)
        flowKappa flowBeta flowG hflowBeta a 0 1 1
        entry block slot time =
      ∑ history ∈ actualQuarticSourceHistories,
        ∫ omega,
          canonicalQuarticDuhamelHistorySourceSlotObservable (N := N)
            flowKappa flowBeta flowG hflowBeta a
            (canonicalOrientedPhyslibFreeRadius (N := N) a)
            (canonicalReindexedPhyslibHaarPhase (N := N))
            entry block slot history (omega, time)
          ∂canonicalIIDMassPhaseEnsemble.probability := by
  calc
    _ = ∫ omega,
        canonicalQuarticDuhamelHistorySourceSlotSum (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry block slot (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability :=
      (integral_canonicalQuarticDuhamelHistorySourceSlotSum_eq_sourceSlot
        (N := N) (by omega) flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot time).symm
    _ = _ :=
      integral_canonicalQuarticDuhamelHistorySourceSlotSum_eq_sum_integrals_closed
        (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
          entry hpositive block slot time

/-- The actual unit-quadratic source-slot integral is exactly the sum of the
four integrable garden-sector Bochner integrals. -/
theorem canonicalPotentialUnitQuadraticSourceSlotBochnerIntegral_eq_fourSectorIntegrals_closed
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (time : Real) :
    canonicalPotentialSourceSlotBochnerIntegral (N := N)
        flowKappa flowBeta flowG hflowBeta a 1 0 1
        entry block slot time =
      (∫ omega,
        canonicalQuadraticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry block slot .regularGoodGarden (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability) +
      (∫ omega,
        canonicalQuadraticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry block slot .badSmallDenominator (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability) +
      (∫ omega,
        canonicalQuadraticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry block slot .recollisionRepeatedHistory (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability) +
      (∫ omega,
        canonicalQuadraticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry block slot .truncationRemainder (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability) := by
  have hgood :=
    integrable_canonicalQuadraticDuhamelHistorySectorContribution_fixedTime_closed
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive block slot .regularGoodGarden time
  have hbad :=
    integrable_canonicalQuadraticDuhamelHistorySectorContribution_fixedTime_closed
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive block slot .badSmallDenominator time
  have hrec :=
    integrable_canonicalQuadraticDuhamelHistorySectorContribution_fixedTime_closed
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive block slot .recollisionRepeatedHistory time
  have htrunc :=
    integrable_canonicalQuadraticDuhamelHistorySectorContribution_fixedTime_closed
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive block slot .truncationRemainder time
  calc
    _ = ∫ omega,
        canonicalQuadraticDuhamelHistorySourceSlotSum (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry block slot (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability :=
      (integral_canonicalQuadraticDuhamelHistorySourceSlotSum_eq_sourceSlot
        (N := N) (by omega) flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot time).symm
    _ = ∫ omega,
        (canonicalQuadraticDuhamelHistorySectorContribution (N := N)
            flowKappa flowBeta flowG hflowBeta a
            (canonicalOrientedPhyslibFreeRadius (N := N) a)
            (canonicalReindexedPhyslibHaarPhase (N := N))
            entry block slot .regularGoodGarden (omega, time) +
          canonicalQuadraticDuhamelHistorySectorContribution (N := N)
            flowKappa flowBeta flowG hflowBeta a
            (canonicalOrientedPhyslibFreeRadius (N := N) a)
            (canonicalReindexedPhyslibHaarPhase (N := N))
            entry block slot .badSmallDenominator (omega, time) +
          canonicalQuadraticDuhamelHistorySectorContribution (N := N)
            flowKappa flowBeta flowG hflowBeta a
            (canonicalOrientedPhyslibFreeRadius (N := N) a)
            (canonicalReindexedPhyslibHaarPhase (N := N))
            entry block slot .recollisionRepeatedHistory (omega, time) +
          canonicalQuadraticDuhamelHistorySectorContribution (N := N)
            flowKappa flowBeta flowG hflowBeta a
            (canonicalOrientedPhyslibFreeRadius (N := N) a)
            (canonicalReindexedPhyslibHaarPhase (N := N))
            entry block slot .truncationRemainder (omega, time))
        ∂canonicalIIDMassPhaseEnsemble.probability := by
      apply integral_congr_ae
      filter_upwards with omega
      exact canonicalQuadraticDuhamelHistorySourceSlotSum_eq_fourSectors
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot (omega, time)
    _ = _ :=
      integral_add_four_complex canonicalIIDMassPhaseEnsemble.probability
        _ _ _ _ hgood hbad hrec htrunc

/-- The actual unit-quartic source-slot integral has the identical four-sector
Bochner decomposition (empty sectors contribute zero automatically). -/
theorem canonicalPotentialUnitQuarticSourceSlotBochnerIntegral_eq_fourSectorIntegrals_closed
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (time : Real) :
    canonicalPotentialSourceSlotBochnerIntegral (N := N)
        flowKappa flowBeta flowG hflowBeta a 0 1 1
        entry block slot time =
      (∫ omega,
        canonicalQuarticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry block slot .regularGoodGarden (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability) +
      (∫ omega,
        canonicalQuarticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry block slot .badSmallDenominator (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability) +
      (∫ omega,
        canonicalQuarticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry block slot .recollisionRepeatedHistory (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability) +
      (∫ omega,
        canonicalQuarticDuhamelHistorySectorContribution (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry block slot .truncationRemainder (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability) := by
  have hgood :=
    integrable_canonicalQuarticDuhamelHistorySectorContribution_fixedTime_closed
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive block slot .regularGoodGarden time
  have hbad :=
    integrable_canonicalQuarticDuhamelHistorySectorContribution_fixedTime_closed
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive block slot .badSmallDenominator time
  have hrec :=
    integrable_canonicalQuarticDuhamelHistorySectorContribution_fixedTime_closed
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive block slot .recollisionRepeatedHistory time
  have htrunc :=
    integrable_canonicalQuarticDuhamelHistorySectorContribution_fixedTime_closed
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive block slot .truncationRemainder time
  calc
    _ = ∫ omega,
        canonicalQuarticDuhamelHistorySourceSlotSum (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry block slot (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability :=
      (integral_canonicalQuarticDuhamelHistorySourceSlotSum_eq_sourceSlot
        (N := N) (by omega) flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot time).symm
    _ = ∫ omega,
        (canonicalQuarticDuhamelHistorySectorContribution (N := N)
            flowKappa flowBeta flowG hflowBeta a
            (canonicalOrientedPhyslibFreeRadius (N := N) a)
            (canonicalReindexedPhyslibHaarPhase (N := N))
            entry block slot .regularGoodGarden (omega, time) +
          canonicalQuarticDuhamelHistorySectorContribution (N := N)
            flowKappa flowBeta flowG hflowBeta a
            (canonicalOrientedPhyslibFreeRadius (N := N) a)
            (canonicalReindexedPhyslibHaarPhase (N := N))
            entry block slot .badSmallDenominator (omega, time) +
          canonicalQuarticDuhamelHistorySectorContribution (N := N)
            flowKappa flowBeta flowG hflowBeta a
            (canonicalOrientedPhyslibFreeRadius (N := N) a)
            (canonicalReindexedPhyslibHaarPhase (N := N))
            entry block slot .recollisionRepeatedHistory (omega, time) +
          canonicalQuarticDuhamelHistorySectorContribution (N := N)
            flowKappa flowBeta flowG hflowBeta a
            (canonicalOrientedPhyslibFreeRadius (N := N) a)
            (canonicalReindexedPhyslibHaarPhase (N := N))
            entry block slot .truncationRemainder (omega, time))
        ∂canonicalIIDMassPhaseEnsemble.probability := by
      apply integral_congr_ae
      filter_upwards with omega
      exact canonicalQuarticDuhamelHistorySourceSlotSum_eq_fourSectors
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry block slot (omega, time)
    _ = _ :=
      integral_add_four_complex canonicalIIDMassPhaseEnsemble.probability
        _ _ _ _ hgood hbad hrec htrunc

/-- Every closed quadratic history slot may be multiplied on either side by
another genuine canonical amplitude block, without primitive hypotheses. -/
theorem integrable_canonicalQuadraticHistory_left_and_right_mixedProducts_fixedTime_closed
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real)
    (history : ActualQuadraticSourceHistory) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry left slot history (omega, time) *
        canonicalSignedBlockObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a entry right (omega, time))
      canonicalIIDMassPhaseEnsemble.probability ∧
    Integrable (fun omega : CanonicalSample =>
      canonicalSignedBlockObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a entry left (omega, time) *
        canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry right slot history (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  have hleft := integrable_canonicalQuadraticHistorySlot_fixedTime_closed
    (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive left slot time history
  have hright := integrable_canonicalQuadraticHistorySlot_fixedTime_closed
    (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive right slot time history
  exact ⟨integrable_mul_canonicalSignedBlockObservable_fixedTime
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive right time _ hleft,
    integrable_canonicalSignedBlockObservable_mul_fixedTime
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive left time _ hright⟩

/-- The same unconditional left/right mixed-product closure holds for every
quartic history. -/
theorem integrable_canonicalQuarticHistory_left_and_right_mixedProducts_fixedTime_closed
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real)
    (history : ActualQuarticSourceHistory) :
    Integrable (fun omega : CanonicalSample =>
      canonicalQuarticDuhamelHistorySourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry left slot history (omega, time) *
        canonicalSignedBlockObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a entry right (omega, time))
      canonicalIIDMassPhaseEnsemble.probability ∧
    Integrable (fun omega : CanonicalSample =>
      canonicalSignedBlockObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a entry left (omega, time) *
        canonicalQuarticDuhamelHistorySourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a
          (canonicalOrientedPhyslibFreeRadius (N := N) a)
          (canonicalReindexedPhyslibHaarPhase (N := N))
          entry right slot history (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  have hleft := integrable_canonicalQuarticHistorySlot_fixedTime_closed
    (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive left slot time history
  have hright := integrable_canonicalQuarticHistorySlot_fixedTime_closed
    (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      entry hpositive right slot time history
  exact ⟨integrable_mul_canonicalSignedBlockObservable_fixedTime
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive right time _ hleft,
    integrable_canonicalSignedBlockObservable_mul_fixedTime
      (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hpositive left time _ hright⟩

end
end ArchonPhysics.CanonicalIIDCoerciveActualDuhamelHistoryBochnerGardenFixedTimeClosure
