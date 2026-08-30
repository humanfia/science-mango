import ArchonPhysics.CanonicalIIDCoerciveActualExpectationCompleted
import ArchonPhysics.FreeFPUTInitialHaarDisjointClusterFactorization

/-!
# Exact initial Haar block moments of the canonical coercive flow

This module identifies the actual continuous-law signed modal observable at
time zero.  Conditional on the random masses, each nontranslation ordered
mode is its mass-dependent real radius times its prescribed Haar phase.
Consequently every finite signed block is a mass-only radial coefficient
times one finite Fourier character, and its canonical expectation is the
mass-radial expectation multiplied by the exact all-mode Haar selector.

An important limitation is explicit.  Disjoint *index* blocks, or even
disjoint phase-mode supports, need not be independent under the annealed
canonical law: all ordered frequencies depend on the same random mass
configuration.  Thus two charge-balanced disjoint blocks can retain a mass
covariance.  We prove exact zero factorization defect when at least one of
two phase-separated block charges is nonzero, and an exact covariance formula
in the balanced--balanced sector.  No positive-time RPA, decay, or propagation
of chaos is asserted.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveInitialHaarBlockMoment

open scoped BigOperators Matrix

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationCompleted
open ArchonPhysics.CanonicalIIDCoerciveContinuousMomentFrontier
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow
open ArchonPhysics.FiniteEnsemblePhaseMoments
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTInitialHaarDisjointClusterFactorization
open ArchonPhysics.GlobalRandomMassModalObservable
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedEigenframe
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedPositiveInitialEnergyProfile
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhaseEnergyModeCoordinates
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.RandomMassMeasurableOrderedEigenframe
open ArchonPhysics.RandomMassMeasurableHarmonicEnergy
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassReducedPhaseInitialData
open ArchonPhysics.SignedEigenframeModeAssembly
open MeasureTheory ProbabilityTheory UnitAddTorus

noncomputable section

variable {N : Nat} [NeZero N]

@[simp] theorem canonicalFlowPosition_zero
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : CanonicalSample) :
    canonicalFlowPosition (N := N) kappa beta g hbeta a (omega, 0) =
      initialPhysicalPosition canonicalIIDMassPhaseEnsemble a omega := by
  unfold canonicalFlowPosition
  rw [canonicalRandomMassPhaseTrajectory_zero]
  rfl

@[simp] theorem canonicalFlowMomentum_zero
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : CanonicalSample) :
    canonicalFlowMomentum (N := N) kappa beta g hbeta a (omega, 0) =
      initialPhysicalMomentum canonicalIIDMassPhaseEnsemble a omega := by
  unfold canonicalFlowMomentum
  rw [canonicalRandomMassPhaseTrajectory_zero]
  rfl

theorem canonicalOrderedModalPosition_zero_of_simple
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (k : OrderedModeIndex N) :
    canonicalOrderedModalPosition (N := N)
        kappa beta g hbeta a k (omega, 0) =
      initialModePositionCoefficient canonicalIIDMassPhaseEnsemble a omega k := by
  unfold canonicalOrderedModalPosition massWeightedPositionSample
  rw [canonicalFlowPosition_zero]
  simp only [canonicalMass]
  rw [sqrtMassTransform_initialPhysicalPosition]
  change signedOrderedEigenvector
      (harmonicHermitian (canonicalMass (N := N) omega)) k ⬝ᵥ
        signedFrameReconstruction
          (harmonicHermitian (canonicalMass (N := N) omega))
          (initialModePositionCoefficient canonicalIIDMassPhaseEnsemble a omega) = _
  exact signedOrderedEigenvector_dot_reconstruction _ hsimple _ k

theorem canonicalOrderedModalMomentum_zero_of_simple
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (k : OrderedModeIndex N) :
    canonicalOrderedModalMomentum (N := N)
        kappa beta g hbeta a k (omega, 0) =
      initialModeMomentumCoefficient canonicalIIDMassPhaseEnsemble a omega k := by
  unfold canonicalOrderedModalMomentum massWeightedMomentumSample
  rw [canonicalFlowMomentum_zero]
  simp only [canonicalMass]
  rw [inverseSqrtMassTransform_initialPhysicalMomentum]
  change signedOrderedEigenvector
      (harmonicHermitian (canonicalMass (N := N) omega)) k ⬝ᵥ
        signedFrameReconstruction
          (harmonicHermitian (canonicalMass (N := N) omega))
          (initialModeMomentumCoefficient canonicalIIDMassPhaseEnsemble a omega) = _
  exact signedOrderedEigenvector_dot_reconstruction _ hsimple _ k

/-- The mass-dependent initial radius of one ordered mode. -/
def canonicalInitialOrderedRadius
    (a : Real) (k : OrderedModeIndex N) (omega : CanonicalSample) : Real :=
  Real.sqrt (orderedTargetEnergy N a k /
    canonicalOrderedFrequency (N := N) k omega)

theorem canonicalInteractionAmplitude_zero_of_simple
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (k : OrderedModeIndex N)
    (hk : k ≠ lastOrderedIndex (ι := Lattice.Site N)) :
    canonicalInteractionAmplitude (N := N)
        kappa beta g hbeta a k (omega, 0) =
      (canonicalInitialOrderedRadius (N := N) a k omega : Complex) *
        unitPhase (orderedPhaseSample canonicalIIDMassPhaseEnsemble omega k) := by
  have hfrequency : 0 < canonicalOrderedFrequency (N := N) k omega := by
    exact (orderedModeFrequency_pos_iff_ne_last
      (canonicalMass (N := N) omega) hsimple k).2 hk
  have htarget : 0 ≤ orderedTargetEnergy N a k :=
    orderedPositiveInitialEnergyProfile_nonneg hN ha0 ha1 _
  unfold canonicalInteractionAmplitude
  rw [canonicalOrderedModalPosition_zero_of_simple
      kappa beta g hbeta a omega hsimple k,
    canonicalOrderedModalMomentum_zero_of_simple
      kappa beta g hbeta a omega hsimple k]
  simp only [mul_zero]
  simp [phaseRenormalize, phaseFactor]
  simpa [canonicalInitialOrderedRadius, canonicalOrderedFrequency,
    orderedFrequencySample, initialModePositionCoefficient,
    initialModeMomentumCoefficient, harmonicHermitianSample,
    harmonicHermitian, canonicalMass] using
    (complexModeAmplitude_phaseCoordinates
      (orderedPhaseSample canonicalIIDMassPhaseEnsemble omega k)
      htarget hfrequency)

end

end ArchonPhysics.CanonicalIIDCoerciveInitialHaarBlockMoment
