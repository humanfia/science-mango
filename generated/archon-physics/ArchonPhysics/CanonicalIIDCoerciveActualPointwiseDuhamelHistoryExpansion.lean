import ArchonPhysics.CanonicalIIDCoerciveSourceSlotExpectationClosure
import ArchonPhysics.PhyslibFPUTActualDuhamelSourceHistoryExpansion
import ArchonPhysics.RandomMassOrderedPhyslibBasisIntertwining

/-!
# Pointwise canonical actual-source Duhamel histories

On the simple-spectrum event, the canonical signed ordered source is the
reindexed Physlib source multiplied by its explicit real orientation sign.
This module transports the exact finite second-Picard history expansion
through that intertwining and through one displayed canonical source slot.

Thus the unit quadratic channel is exactly a sum of four histories and the
unit quartic channel is exactly a sum of two histories, pointwise and almost
surely under the canonical iid law.  No RPA, Markov, gap, recollision bound,
kinetic limit, individual-history measurability, or termwise Bochner
integration is asserted.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualPointwiseDuhamelHistoryExpansion

open scoped BigOperators
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoercivePotentialChannelExpectation
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSourceSlotExpectationClosure
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhyslibFPUTActualDuhamelSourceHistoryExpansion
open ArchonPhysics.PhyslibFPUTActualSourceSlotPotentialSplit
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTCoercivePositiveTimeCumulantHierarchy
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.RandomMassOrderedPhyslibBasisIntertwining
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [DecidableEq I]

/-- The actual canonical position trajectory in Physlib's nonnegative-time
parameter. -/
def canonicalPhyslibPositionPath
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (omega : CanonicalSample) :
    Time -> HilbertConfiguration N :=
  fun time => canonicalFlowPosition (N := N)
    flowKappa flowBeta flowG hflowBeta a (omega, Time.toRealCLE time)

@[simp] theorem realReparametrize_canonicalPhyslibPositionPath
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (omega : CanonicalSample) :
    realReparametrize
        (canonicalPhyslibPositionPath (N := N)
          flowKappa flowBeta flowG hflowBeta a omega) =
      fun time => canonicalFlowPosition (N := N)
        flowKappa flowBeta flowG hflowBeta a (omega, time) := by
  funext time
  rfl

/-- The actual ordered unit-quadratic source is the orientation sign times
the reindexed Physlib source. -/
theorem canonicalOrderedUnitQuadraticRotatedSource_eq_orientation_mul_physlib
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (k : OrderedModeIndex N) (time : Real) :
    canonicalOrderedPotentialChannelRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a 1 0 1 k (omega, time) =
      (orderedPhyslibOrientation (canonicalMass (N := N) omega) k : Complex) *
        physlibQuadraticRotatedSource (canonicalMass (N := N) omega) 1 1
          (orderedPhyslibModeIndex k)
          (canonicalPhyslibPositionPath (N := N)
            flowKappa flowBeta flowG hflowBeta a omega) time := by
  unfold canonicalOrderedPotentialChannelRotatedSource
  simpa [physlibQuadraticRotatedSource] using
    (orderedSignedRotatedSource_eq_orientation_mul_physlibModeRotatedSource
      (canonicalMass (N := N) omega) hsimple 1 0 1 k
      (canonicalPhyslibPositionPath (N := N)
        flowKappa flowBeta flowG hflowBeta a omega) time)

/-- The actual ordered unit-quartic source is the orientation sign times the
reindexed Physlib source. -/
theorem canonicalOrderedUnitQuarticRotatedSource_eq_orientation_mul_physlib
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (k : OrderedModeIndex N) (time : Real) :
    canonicalOrderedPotentialChannelRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a 0 1 1 k (omega, time) =
      (orderedPhyslibOrientation (canonicalMass (N := N) omega) k : Complex) *
        physlibCubicRotatedSource (canonicalMass (N := N) omega) 1 1
          (orderedPhyslibModeIndex k)
          (canonicalPhyslibPositionPath (N := N)
            flowKappa flowBeta flowG hflowBeta a omega) time := by
  unfold canonicalOrderedPotentialChannelRotatedSource
  simpa [physlibCubicRotatedSource] using
    (orderedSignedRotatedSource_eq_orientation_mul_physlibModeRotatedSource
      (canonicalMass (N := N) omega) hsimple 0 1 1 k
      (canonicalPhyslibPositionPath (N := N)
        flowKappa flowBeta flowG hflowBeta a omega) time)

/-- One orientation-corrected signed quadratic history on the canonical
trajectory.  The inner history is the already verified finite-ensemble
Physlib history, used here without any finiteness requirement on samples. -/
def canonicalQuadraticDuhamelHistorySource
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : PhaseSign × OrderedModeIndex N)
    (history : ActualQuadraticSourceHistory)
    (st : CanonicalSample × Real) : Complex :=
  (orderedPhyslibOrientation
      (canonicalMass (N := N) st.1) entry.2 : Complex) *
    actualFiniteQuadraticHistorySource
      (fun omega => canonicalMass (N := N) omega)
      (fun _ : Unit => (entry.1, orderedPhyslibModeIndex entry.2))
      (fun omega => canonicalPhyslibPositionPath (N := N)
        flowKappa flowBeta flowG hflowBeta a omega)
      radius phase history st.1 () st.2

/-- One orientation-corrected signed quartic history on the canonical
trajectory. -/
def canonicalQuarticDuhamelHistorySource
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : PhaseSign × OrderedModeIndex N)
    (history : ActualQuarticSourceHistory)
    (st : CanonicalSample × Real) : Complex :=
  (orderedPhyslibOrientation
      (canonicalMass (N := N) st.1) entry.2 : Complex) *
    actualFiniteQuarticHistorySource
      (fun omega => canonicalMass (N := N) omega)
      (fun _ : Unit => (entry.1, orderedPhyslibModeIndex entry.2))
      (fun omega => canonicalPhyslibPositionPath (N := N)
        flowKappa flowBeta flowG hflowBeta a omega)
      radius phase history st.1 () st.2

/-- Exact pointwise four-history reconstruction of the signed canonical
unit-quadratic source. -/
theorem canonicalSignedUnitQuadraticSource_eq_historySum
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : PhaseSign × OrderedModeIndex N)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (time : Real) :
    canonicalSignedPotentialChannelRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a 1 0 1 entry (omega, time) =
      ∑ history ∈ actualQuadraticSourceHistories,
        canonicalQuadraticDuhamelHistorySource (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase entry history
          (omega, time) := by
  have hfinite := congrFun (congrFun (congrFun
    (actualFiniteQuadraticUnitSource_eq_historySum
      (I := Unit) (Omega := Unit)
      (fun _ => canonicalMass (N := N) omega)
      (fun _ => (entry.1, orderedPhyslibModeIndex entry.2))
      (fun _ => canonicalPhyslibPositionPath (N := N)
        flowKappa flowBeta flowG hflowBeta a omega)
      (fun _ => radius omega) (fun _ => phase omega)) ()) ()) time
  unfold canonicalSignedPotentialChannelRotatedSource
  rw [canonicalOrderedUnitQuadraticRotatedSource_eq_orientation_mul_physlib
    flowKappa flowBeta flowG hflowBeta a omega hsimple entry.2 time]
  have horiented := congrArg
    (fun z : Complex =>
      (orderedPhyslibOrientation
        (canonicalMass (N := N) omega) entry.2 : Complex) * z) hfinite
  rw [Finset.mul_sum] at horiented
  cases hsign : entry.1 <;>
    simpa [canonicalQuadraticDuhamelHistorySource,
      actualFiniteQuadraticHistorySource,
      actualFiniteCubicEnsembleSource,
      signedPhyslibCubicLeadingQuadraticSource,
      physlibCubicLeadingQuadraticSource,
      physlibQuadraticRotatedSource, hsign,
      phaseSignActComplex] using horiented

/-- Exact pointwise two-history reconstruction of the signed canonical
unit-quartic source. -/
theorem canonicalSignedUnitQuarticSource_eq_historySum
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : PhaseSign × OrderedModeIndex N)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (time : Real) :
    canonicalSignedPotentialChannelRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a 0 1 1 entry (omega, time) =
      ∑ history ∈ actualQuarticSourceHistories,
        canonicalQuarticDuhamelHistorySource (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase entry history
          (omega, time) := by
  have hfinite := congrFun (congrFun (congrFun
    (actualFiniteQuarticUnitSource_eq_historySum
      (I := Unit) (Omega := Unit)
      (fun _ => canonicalMass (N := N) omega)
      (fun _ => (entry.1, orderedPhyslibModeIndex entry.2))
      (fun _ => canonicalPhyslibPositionPath (N := N)
        flowKappa flowBeta flowG hflowBeta a omega)
      (fun _ => radius omega) (fun _ => phase omega)) ()) ()) time
  unfold canonicalSignedPotentialChannelRotatedSource
  rw [canonicalOrderedUnitQuarticRotatedSource_eq_orientation_mul_physlib
    flowKappa flowBeta flowG hflowBeta a omega hsimple entry.2 time]
  have horiented := congrArg
    (fun z : Complex =>
      (orderedPhyslibOrientation
        (canonicalMass (N := N) omega) entry.2 : Complex) * z) hfinite
  rw [Finset.mul_sum] at horiented
  cases hsign : entry.1 <;>
    simpa [canonicalQuarticDuhamelHistorySource,
      actualFiniteQuarticHistorySource,
      actualFiniteQuarticEnsembleSource,
      signedPhyslibQuarticForceRotatedSource,
      physlibQuarticForceRotatedSource, hsign,
      phaseSignActComplex] using horiented

/-- One displayed canonical source slot with a quadratic history inserted. -/
def canonicalQuadraticDuhamelHistorySourceSlotObservable
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I)
    (history : ActualQuadraticSourceHistory)
    (st : CanonicalSample × Real) : Complex :=
  (∏ j ∈ block.erase slot,
    canonicalSignedInteractionAmplitude (N := N)
      flowKappa flowBeta flowG hflowBeta a (entry j) st) *
    canonicalQuadraticDuhamelHistorySource (N := N)
      flowKappa flowBeta flowG hflowBeta a radius phase
      (entry slot) history st

/-- One displayed canonical source slot with a quartic history inserted. -/
def canonicalQuarticDuhamelHistorySourceSlotObservable
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I)
    (history : ActualQuarticSourceHistory)
    (st : CanonicalSample × Real) : Complex :=
  (∏ j ∈ block.erase slot,
    canonicalSignedInteractionAmplitude (N := N)
      flowKappa flowBeta flowG hflowBeta a (entry j) st) *
    canonicalQuarticDuhamelHistorySource (N := N)
      flowKappa flowBeta flowG hflowBeta a radius phase
      (entry slot) history st

/-- Exact pointwise unit-quadratic source-slot reconstruction. -/
theorem canonicalPotentialUnitQuadraticSourceSlotObservable_eq_historySum
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (time : Real) :
    canonicalPotentialSourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a 1 0 1
        entry block slot (omega, time) =
      ∑ history ∈ actualQuadraticSourceHistories,
        canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase
          entry block slot history (omega, time) := by
  unfold canonicalPotentialSourceSlotObservable
    canonicalQuadraticDuhamelHistorySourceSlotObservable
  rw [canonicalSignedUnitQuadraticSource_eq_historySum
    flowKappa flowBeta flowG hflowBeta a radius phase
    (entry slot) omega hsimple time]
  rw [Finset.mul_sum]

/-- Exact pointwise unit-quartic source-slot reconstruction. -/
theorem canonicalPotentialUnitQuarticSourceSlotObservable_eq_historySum
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (time : Real) :
    canonicalPotentialSourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a 0 1 1
        entry block slot (omega, time) =
      ∑ history ∈ actualQuarticSourceHistories,
        canonicalQuarticDuhamelHistorySourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a radius phase
          entry block slot history (omega, time) := by
  unfold canonicalPotentialSourceSlotObservable
    canonicalQuarticDuhamelHistorySourceSlotObservable
  rw [canonicalSignedUnitQuarticSource_eq_historySum
    flowKappa flowBeta flowG hflowBeta a radius phase
    (entry slot) omega hsimple time]
  rw [Finset.mul_sum]

/-- The quadratic source-slot history reconstruction holds almost surely for
the canonical iid ensemble. -/
theorem canonicalPotentialUnitQuadraticSourceSlotObservable_eq_historySum_ae
    (hN : 2 <= N)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I) (time : Real) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      canonicalPotentialSourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a 1 0 1
          entry block slot (omega, time) =
        ∑ history ∈ actualQuadraticSourceHistories,
          canonicalQuadraticDuhamelHistorySourceSlotObservable (N := N)
            flowKappa flowBeta flowG hflowBeta a radius phase
            entry block slot history (omega, time) := by
  filter_upwards [RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae
    (N := N) canonicalIIDMassPhaseEnsemble hN] with omega hsimpleSample
  have hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)) := by
    simpa [harmonicHermitianSample, harmonicHermitian, canonicalMass]
      using hsimpleSample
  exact canonicalPotentialUnitQuadraticSourceSlotObservable_eq_historySum
    flowKappa flowBeta flowG hflowBeta a radius phase entry block slot
    omega hsimple time

/-- The quartic source-slot history reconstruction holds almost surely for
the canonical iid ensemble. -/
theorem canonicalPotentialUnitQuarticSourceSlotObservable_eq_historySum_ae
    (hN : 2 <= N)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a : Real)
    (radius : CanonicalSample -> Lattice.Site N -> Real)
    (phase : CanonicalSample -> UnitAddTorus (Lattice.Site N))
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I) (time : Real) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      canonicalPotentialSourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a 0 1 1
          entry block slot (omega, time) =
        ∑ history ∈ actualQuarticSourceHistories,
          canonicalQuarticDuhamelHistorySourceSlotObservable (N := N)
            flowKappa flowBeta flowG hflowBeta a radius phase
            entry block slot history (omega, time) := by
  filter_upwards [RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae
    (N := N) canonicalIIDMassPhaseEnsemble hN] with omega hsimpleSample
  have hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)) := by
    simpa [harmonicHermitianSample, harmonicHermitian, canonicalMass]
      using hsimpleSample
  exact canonicalPotentialUnitQuarticSourceSlotObservable_eq_historySum
    flowKappa flowBeta flowG hflowBeta a radius phase entry block slot
    omega hsimple time

end

end ArchonPhysics.CanonicalIIDCoerciveActualPointwiseDuhamelHistoryExpansion
