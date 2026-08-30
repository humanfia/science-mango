import ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow
import ArchonPhysics.GlobalRandomMassModalObservable
import ArchonPhysics.PhyslibFPUTCoercivePositiveTimeCumulantHierarchy
import ArchonPhysics.RandomMassMeasurableOrderedEigenframe

/-!
# Measurable signed modal hierarchy on the canonical iid coercive flow

The normal-mode basis used by `PhyslibHamiltonDuhamel` is selected
noncomputably for each fixed mass realization; its complex amplitudes are
therefore not, by themselves, random variables.  This module closes that
specific measurability gap with the globally measurable first-positive-pivot
eigenframe from `RandomMassMeasurableOrderedEigenframe`.

For every fixed ordered mode we define its mass-weighted position and
momentum coordinates along the *actual canonical iid mass--Haar flow*, form
the usual positive-frequency complex amplitude, and remove the free phase.
The resulting signed paths and every finite block monomial are jointly
measurable in sample and time.

On the almost-sure simple-spectrum locus, the selected signed vector is a
unit eigenvector.  Hence every genuine coercive Hamilton orbit obeys the
exact forced-oscillator equation in this measurable frame, and every finite
block differentiates by inserting the full nonlinear source in one slot.
The canonical global-flow theorem supplies precisely such a genuine orbit
almost surely, for all real times at once.

This is the concrete observable/derivative bridge needed before passing to a
continuous expectation.  It does **not** exchange a time derivative with the
canonical probability integral: that final step still requires a uniform
integrable bound for the full signed source (including the inverse positive
frequency).  No dominated hypothesis is hidden here, and no RPA, Markov,
closure, decay, or kinetic conclusion is asserted.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy

open scoped BigOperators Matrix

open ArchonPhysics
open ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ComplexModeAmplitude
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.GlobalRandomMassModalObservable
open ArchonPhysics.InteractionPictureDuhamel
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedEigenframe
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.ParametricLocalHamiltonianFlow
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.RandomMassMeasurableHarmonicEnergy
open ArchonPhysics.RandomMassMeasurableOrderedEigenframe
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassReducedPhaseInitialData
open ArchonPhysics.ReducedGlobalTrajectoryPhyslibAdapter
open ArchonPhysics.ReducedModeTransform
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]

abbrev CanonicalSample := RandomEnsemble.SampleSpace

/-- The positive mass realization carried by the canonical iid sample. -/
def canonicalMass (omega : CanonicalSample) : Lattice.PositiveMassConfig N :=
  canonicalIIDMassPhaseEnsemble.restrictPositiveMass omega

/-- Position coordinate of the one canonical mass--phase trajectory. -/
def canonicalFlowPosition
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (st : CanonicalSample × Real) : HilbertConfiguration N :=
  (canonicalRandomMassPhaseTrajectory (N := N)
    canonicalIIDMassPhaseEnsemble kappa beta g hbeta a st).2.1

/-- Canonical momentum coordinate of the same trajectory. -/
def canonicalFlowMomentum
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (st : CanonicalSample × Real) : HilbertConfiguration N :=
  (canonicalRandomMassPhaseTrajectory (N := N)
    canonicalIIDMassPhaseEnsemble kappa beta g hbeta a st).2.2

theorem measurable_canonicalFlowPosition
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) :
    Measurable (canonicalFlowPosition (N := N) kappa beta g hbeta a) := by
  exact (measurable_canonicalRandomMassPhaseTrajectory
    (N := N) canonicalIIDMassPhaseEnsemble kappa beta g hbeta a).snd.fst

theorem measurable_canonicalFlowMomentum
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) :
    Measurable (canonicalFlowMomentum (N := N) kappa beta g hbeta a) := by
  exact (measurable_canonicalRandomMassPhaseTrajectory
    (N := N) canonicalIIDMassPhaseEnsemble kappa beta g hbeta a).snd.snd

/-- Measurable first-positive-pivot position coordinate of an ordered mode. -/
def canonicalOrderedModalPosition
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (k : OrderedModeIndex N)
    (st : CanonicalSample × Real) : Real :=
  orderedEigenvectorSample canonicalIIDMassPhaseEnsemble k st.1 ⬝ᵥ
    massWeightedPositionSample
      (fun st : CanonicalSample × Real ↦ canonicalMass (N := N) st.1)
      (canonicalFlowPosition (N := N) kappa beta g hbeta a) st

/-- Measurable first-positive-pivot momentum coordinate of an ordered mode. -/
def canonicalOrderedModalMomentum
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (k : OrderedModeIndex N)
    (st : CanonicalSample × Real) : Real :=
  orderedEigenvectorSample canonicalIIDMassPhaseEnsemble k st.1 ⬝ᵥ
    massWeightedMomentumSample
      (fun st : CanonicalSample × Real ↦ canonicalMass (N := N) st.1)
      (canonicalFlowMomentum (N := N) kappa beta g hbeta a) st

/-- Ordered physical frequency, totalized on every sample. -/
def canonicalOrderedFrequency (k : OrderedModeIndex N)
    (omega : CanonicalSample) : Real :=
  orderedModeFrequency (harmonicHermitian (canonicalMass (N := N) omega)) k

/-- The measurable complex interaction-picture amplitude in the signed
ordered frame. -/
def canonicalInteractionAmplitude
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (k : OrderedModeIndex N)
    (st : CanonicalSample × Real) : Complex :=
  phaseRenormalize (canonicalOrderedFrequency (N := N) k st.1 * st.2)
    (complexModeAmplitude (canonicalOrderedFrequency (N := N) k st.1)
      (canonicalOrderedModalPosition (N := N) kappa beta g hbeta a k st)
      (canonicalOrderedModalMomentum (N := N) kappa beta g hbeta a k st))

/-- Phase/conjugate branch of the measurable canonical amplitude. -/
def canonicalSignedInteractionAmplitude
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : PhaseSign × OrderedModeIndex N)
    (st : CanonicalSample × Real) : Complex :=
  phaseSignActComplex entry.1
    (canonicalInteractionAmplitude (N := N)
      kappa beta g hbeta a entry.2 st)

end

end ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
