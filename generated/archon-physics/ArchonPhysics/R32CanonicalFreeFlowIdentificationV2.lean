import ArchonPhysics.CanonicalIIDCoerciveSignedModalBlockHierarchy
import ArchonPhysics.GlobalReducedParametricFlowAdapter
import ArchonPhysics.OrderedTranslationLastMode
import ArchonPhysics.R32FrozenFreeModalInvarianceV3
import ArchonPhysics.RandomMassReducedPhaseInitialData
import ArchonPhysics.TranslationZeroModeEnergy

/-!
# R32: identification of the explicit free phases with the canonical `g = 0` flow

`R32FrozenFreeModalInvarianceV3` constructs the explicit frozen free
orbit by advancing the canonical Haar phases with
`physicalFreePhaseEvolution`.  This file identifies its ordered modal energy
with the physical ordered modal energy read from the actual canonical global
Hamiltonian flow at coupling zero.

For a positive ordered mode, the signed interaction-picture amplitude of the
canonical zero-coupling flow has derivative zero.  Its norm therefore stays
constant, and the complex-amplitude energy identity gives conservation of
that individual physical mode.  The translation mode is handled by the
existing reduced zero-momentum theorem.  Thus no abstract free field or
extra dynamics hypothesis is introduced: both sides use the repository's
canonical initial sample and canonical global flow.
-/

open scoped Matrix

namespace ArchonPhysics.R32CanonicalFreeFlowIdentificationV2

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveSignedModalBlockHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ComplexModeAmplitude
open ArchonPhysics.GlobalRandomMassModalObservable
open ArchonPhysics.GlobalReducedParametricFlowAdapter
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedEigenframe
open ArchonPhysics.MeasurableOrderedHarmonicEnergy
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.RandomMassMeasurableHarmonicEnergy
open ArchonPhysics.RandomMassMeasurableOrderedEigenframe
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPhaseLateWindowObservable
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassReducedPhaseInitialData
open ArchonPhysics.R32FrozenEnergyDilution
open ArchonPhysics.R32FrozenFreeModalInvarianceV3
open ArchonPhysics.SpectralBandEnergyObservable
open ArchonPhysics.TranslationZeroModeEnergy
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]

/-! ## Signed-coordinate energy identities -/

/-- On a simple spectrum, the basis-free projector energy is the square of
the coordinate in the canonical signed ordered eigenvector. -/
theorem orderedModeEnergy_eq_sq_signedOrderedCoordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (mode : Fin (Fintype.card ι)) (x : ι -> Real) :
    orderedModeEnergy A mode x =
      (signedOrderedEigenvector A mode ⬝ᵥ x) ^ 2 := by
  unfold orderedModeEnergy orderedModeProjectedState coordinateEnergy
  rw [← signedOrderedEigenvector_outerProduct A hsimple mode,
    Matrix.vecMulVec_mulVec, smul_dotProduct, dotProduct_smul,
    signedOrderedEigenvector_dot_self A hsimple mode]
  simp only [op_smul_eq_smul, smul_eq_mul, mul_one, pow_two]

/-- Consequently, the basis-free ordered harmonic energy is the ordinary
scalar harmonic energy of the two signed modal coordinates. -/
theorem orderedHarmonicModeEnergy_eq_signedModalEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (mode : Fin (Fintype.card ι)) (position momentum : ι -> Real) :
    orderedHarmonicModeEnergy A mode position momentum =
      HarmonicModes.modalEnergy (orderedEigenvalue A mode)
        (signedOrderedEigenvector A mode ⬝ᵥ position)
        (signedOrderedEigenvector A mode ⬝ᵥ momentum) := by
  unfold orderedHarmonicModeEnergy HarmonicModes.modalEnergy
  rw [orderedModeEnergy_eq_sq_signedOrderedCoordinate A hsimple mode momentum,
    orderedModeEnergy_eq_sq_signedOrderedCoordinate A hsimple mode position]

/-! ## The zero-coupling interaction amplitude -/

/-- At `g = 0`, the mass-weighted nonlinear residual force is identically
zero. -/
@[simp] theorem transformedNonlinearForce_zeroCoupling
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (q : HilbertConfiguration N) :
    transformedNonlinearForce m kappa beta 0 q = 0 := by
  simp [transformedNonlinearForce, nonlinearPotentialGradient,
    nonlinearPotentialDerivative]

/-- Hence the complete rotated source of every canonical ordered mode is
zero along the canonical `g = 0` global flow. -/
@[simp] theorem canonicalOrderedRotatedSource_zeroCoupling
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (sample : CanonicalSample) (mode : OrderedModeIndex N)
    (time : Real) :
    canonicalOrderedRotatedSource (N := N)
      kappa beta 0 hbeta a mode (sample, time) = 0 := by
  simp [canonicalOrderedRotatedSource, orderedSignedRotatedSource,
    orderedSignedNonlinearForce, orderedSignedCoordinate,
    ForcedComplexModeDuhamel.forcedModeSource]

/-- A positive canonical mode at zero coupling has a constant
interaction-picture amplitude.  The derivative comes from the actual
canonical global/reduced Hamiltonian-flow identification. -/
theorem canonicalInteractionAmplitude_zeroCoupling_eq_initial
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (sample : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) sample)))
    (mode : OrderedModeIndex N)
    (hfrequency : 0 < orderedModeFrequency
      (harmonicHermitian (canonicalMass (N := N) sample)) mode)
    (time : Real) :
    canonicalInteractionAmplitude (N := N)
        kappa beta 0 hbeta a mode (sample, time) =
      canonicalInteractionAmplitude (N := N)
        kappa beta 0 hbeta a mode (sample, 0) := by
  let amplitude : Real -> Complex := fun s =>
    canonicalInteractionAmplitude (N := N)
      kappa beta 0 hbeta a mode (sample, s)
  have hderiv : forall s, HasDerivAt amplitude 0 s := by
    intro s
    simpa [amplitude] using
      (hasDerivAt_canonicalInteractionAmplitude_of_simple
        hN ha0 ha1 kappa beta 0 hbeta sample hsimple
        mode hfrequency s)
  exact is_const_of_deriv_eq_zero
    (fun s => (hderiv s).differentiableAt)
    (fun s => (hderiv s).deriv) time 0

/-! ## Physical modal energy of the canonical free global flow -/

/-- On a positive mode, the physical projector energy read from the
canonical global flow is frequency times the squared norm of its canonical
interaction-picture amplitude. -/
theorem canonicalFreeFlowModeEnergy_eq_frequency_mul_normSq
    (kappa beta : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (sample : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) sample)))
    (mode : OrderedModeIndex N)
    (hfrequency : 0 < orderedModeFrequency
      (harmonicHermitian (canonicalMass (N := N) sample)) mode)
    (time : Real) :
    sampledPhysicalOrderedModeEnergyAlongFlow
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
        (canonicalPhaseInitialSample (N := N) kappa beta 0 a)
        (canonicalRandomMassPhaseGlobalFlow N kappa beta 0 hbeta)
        (sample, time) mode =
      orderedModeFrequency
          (harmonicHermitian (canonicalMass (N := N) sample)) mode *
        Complex.normSq
          (canonicalInteractionAmplitude (N := N)
            kappa beta 0 hbeta a mode (sample, time)) := by
  change orderedHarmonicModeEnergy
      (harmonicHermitian (canonicalMass (N := N) sample)) mode
      (sqrtMassTransform (canonicalMass (N := N) sample)
        (canonicalFlowPosition (N := N)
          kappa beta 0 hbeta a (sample, time)))
      (inverseSqrtMassTransform (canonicalMass (N := N) sample)
        (canonicalFlowMomentum (N := N)
          kappa beta 0 hbeta a (sample, time))) = _
  rw [orderedHarmonicModeEnergy_eq_signedModalEnergy _ hsimple]
  have hfrequencySq :
      orderedModeFrequency
          (harmonicHermitian (canonicalMass (N := N) sample)) mode ^ 2 =
        orderedEigenvalue
          (harmonicHermitian (canonicalMass (N := N) sample)) mode := by
    apply Real.sq_sqrt
    simpa [harmonicOrderedEigenvalue, harmonicHermitianSample,
      harmonicHermitian] using
      (harmonicOrderedEigenvalue_nonneg
        (fun _ : Unit => canonicalMass (N := N) sample) () mode)
  rw [← hfrequencySq]
  rw [← frequency_mul_normSq_eq_modalEnergy hfrequency]
  simp [canonicalInteractionAmplitude, canonicalOrderedFrequency,
    canonicalOrderedModalPosition, canonicalOrderedModalMomentum,
    orderedEigenvectorSample, massWeightedPositionSample,
    massWeightedMomentumSample, canonicalMass, harmonicHermitianSample,
    harmonicHermitian]

/-- At time zero the canonical `g = 0` global-flow energy is exactly the
frozen quarter-contrast target profile. -/
theorem canonicalFreeFlowModeEnergy_zero_eq_frozenTwoBandEnergy
    (hN : 3 <= N) (kappa beta : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (sample : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) sample)))
    (mode : OrderedModeIndex N) :
    sampledPhysicalOrderedModeEnergyAlongFlow
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
        (canonicalPhaseInitialSample (N := N) kappa beta 0 (1 / 4))
        (canonicalRandomMassPhaseGlobalFlow N kappa beta 0 hbeta)
        (sample, 0) mode = frozenTwoBandEnergy N mode := by
  unfold sampledPhysicalOrderedModeEnergyAlongFlow sampledFlowPosition
    sampledFlowMomentum harmonicOrderedPhysicalModeEnergy
    massWeightedPositionSample massWeightedMomentumSample
  change orderedHarmonicModeEnergy
      (harmonicHermitianSample
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N)) sample)
      mode
      (sqrtMassTransform
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) sample)
        ((canonicalRandomMassPhaseGlobalFlow N kappa beta 0 hbeta
          (canonicalPhaseInitialSample
            (N := N) kappa beta 0 (1 / 4) sample, 0)).2.1))
      (inverseSqrtMassTransform
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) sample)
        ((canonicalRandomMassPhaseGlobalFlow N kappa beta 0 hbeta
          (canonicalPhaseInitialSample
            (N := N) kappa beta 0 (1 / 4) sample, 0)).2.2)) =
        frozenTwoBandEnergy N mode
  rw [canonicalRandomMassPhaseGlobalFlow_zero]
  change harmonicOrderedPhysicalModeEnergy
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
      (initialPhysicalPosition canonicalIIDMassPhaseEnsemble (1 / 4))
      (initialPhysicalMomentum canonicalIIDMassPhaseEnsemble (1 / 4))
      sample mode = frozenTwoBandEnergy N mode
  simpa [frozenTwoBandEnergy] using
    (harmonicOrderedPhysicalModeEnergy_initial_eq_target
      canonicalIIDMassPhaseEnsemble hN
      (a := (1 / 4 : Real)) (by norm_num) (by norm_num)
      sample hsimple mode)

/-- The reduced zero-momentum constraint makes the translation-mode energy
of the canonical zero-coupling global flow vanish at every real time. -/
theorem canonicalFreeFlowTranslationModeEnergy_eq_zero
    (hN : 3 <= N) (kappa beta : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (sample : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) sample)))
    (time : Real) :
    sampledPhysicalOrderedModeEnergyAlongFlow
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
        (canonicalPhaseInitialSample (N := N) kappa beta 0 (1 / 4))
        (canonicalRandomMassPhaseGlobalFlow N kappa beta 0 hbeta)
        (sample, time)
        (lastOrderedIndex (ι := Lattice.Site N)) = 0 := by
  obtain ⟨z, _hz0, _hz, hmatch, _henergy⟩ :=
    canonicalRandomMassPhaseTrajectory_matches_reduced_of_simple
      canonicalIIDMassPhaseEnsemble hN
      (a := (1 / 4 : Real)) (by norm_num) (by norm_num)
      kappa beta 0 hbeta sample hsimple
  have hzero := orderedZeroMode_physicalHarmonicEnergy_eq_zero
    (canonicalMass (N := N) sample) hsimple
    (lastOrderedIndex (ι := Lattice.Site N))
    (harmonic_lastOrderedEigenvalue_eq_zero
      (canonicalMass (N := N) sample))
    (z time).1 (z time).2
  unfold sampledPhysicalOrderedModeEnergyAlongFlow
    harmonicOrderedPhysicalModeEnergy massWeightedPositionSample
    massWeightedMomentumSample sampledFlowPosition sampledFlowMomentum
  change orderedHarmonicModeEnergy
      (harmonicHermitian (canonicalMass (N := N) sample))
      (lastOrderedIndex (ι := Lattice.Site N))
      (sqrtMassTransform (canonicalMass (N := N) sample)
        ((canonicalRandomMassPhaseTrajectory (N := N)
          canonicalIIDMassPhaseEnsemble kappa beta 0 hbeta (1 / 4)
          (sample, time)).2.1))
      (inverseSqrtMassTransform (canonicalMass (N := N) sample)
        ((canonicalRandomMassPhaseTrajectory (N := N)
          canonicalIIDMassPhaseEnsemble kappa beta 0 hbeta (1 / 4)
          (sample, time)).2.2)) = 0
  rw [hmatch time]
  simpa [embedReducedPoint] using hzero

/-- On every simple realization, the actual canonical Hamiltonian global
flow at `g = 0` has the frozen physical energy in every ordered mode and at
every real time. -/
theorem canonicalFreeFlowModeEnergy_eq_frozenTwoBandEnergy
    (hN : 3 <= N) (kappa beta : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (sample : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) sample)))
    (time : Real) (mode : OrderedModeIndex N) :
    sampledPhysicalOrderedModeEnergyAlongFlow
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
        (canonicalPhaseInitialSample (N := N) kappa beta 0 (1 / 4))
        (canonicalRandomMassPhaseGlobalFlow N kappa beta 0 hbeta)
        (sample, time) mode = frozenTwoBandEnergy N mode := by
  by_cases hlast : mode = lastOrderedIndex (ι := Lattice.Site N)
  · subst mode
    rw [canonicalFreeFlowTranslationModeEnergy_eq_zero
      hN kappa beta hbeta sample hsimple time]
    exact (orderedTargetEnergy_last (N := N) (1 / 4)).symm
  · have hfrequency : 0 < orderedModeFrequency
        (harmonicHermitian (canonicalMass (N := N) sample)) mode :=
      (orderedModeFrequency_pos_iff_ne_last
        (canonicalMass (N := N) sample) hsimple mode).2 hlast
    calc
      sampledPhysicalOrderedModeEnergyAlongFlow
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
          (canonicalPhaseInitialSample (N := N) kappa beta 0 (1 / 4))
          (canonicalRandomMassPhaseGlobalFlow N kappa beta 0 hbeta)
          (sample, time) mode =
        orderedModeFrequency
            (harmonicHermitian (canonicalMass (N := N) sample)) mode *
          Complex.normSq
            (canonicalInteractionAmplitude (N := N)
              kappa beta 0 hbeta (1 / 4) mode (sample, time)) :=
        canonicalFreeFlowModeEnergy_eq_frequency_mul_normSq
          kappa beta hbeta (1 / 4) sample hsimple mode hfrequency time
      _ = orderedModeFrequency
            (harmonicHermitian (canonicalMass (N := N) sample)) mode *
          Complex.normSq
            (canonicalInteractionAmplitude (N := N)
              kappa beta 0 hbeta (1 / 4) mode (sample, 0)) := by
        rw [canonicalInteractionAmplitude_zeroCoupling_eq_initial
          hN (a := (1 / 4 : Real)) (by norm_num) (by norm_num)
          kappa beta hbeta sample hsimple mode hfrequency time]
      _ = sampledPhysicalOrderedModeEnergyAlongFlow
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
          (canonicalPhaseInitialSample (N := N) kappa beta 0 (1 / 4))
          (canonicalRandomMassPhaseGlobalFlow N kappa beta 0 hbeta)
          (sample, 0) mode :=
        (canonicalFreeFlowModeEnergy_eq_frequency_mul_normSq
          kappa beta hbeta (1 / 4) sample hsimple mode hfrequency 0).symm
      _ = frozenTwoBandEnergy N mode :=
        canonicalFreeFlowModeEnergy_zero_eq_frozenTwoBandEnergy
          hN kappa beta hbeta sample hsimple mode

/-! ## Identification with the explicit `physicalFreePhaseEvolution` orbit -/

/-- Pointwise identification: the physical ordered modal energy of the
actual canonical `g = 0` global flow is exactly the modal energy of the
explicit frozen Haar phase evolution. -/
theorem canonicalFreeFlowModeEnergy_eq_explicit
    (hN : 3 <= N) (kappa beta : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (sample : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) sample)))
    (time : Real) (mode : OrderedModeIndex N) :
    sampledPhysicalOrderedModeEnergyAlongFlow
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
        (canonicalPhaseInitialSample (N := N) kappa beta 0 (1 / 4))
        (canonicalRandomMassPhaseGlobalFlow N kappa beta 0 hbeta)
        (sample, time) mode =
      canonicalFrozenFreeModalEnergy sample time mode := by
  have hexplicit := canonicalFrozenFreeModalEnergy_eq_frozenTwoBandEnergy
    hN sample
      (by simpa [canonicalMass, harmonicHermitianSample, harmonicHermitian]
        using hsimple)
      time mode
  exact (canonicalFreeFlowModeEnergy_eq_frozenTwoBandEnergy
    hN kappa beta hbeta sample hsimple time mode).trans hexplicit.symm

/-- Almost surely, one sample set works simultaneously for every real time
and every ordered mode: the canonical Hamiltonian `g = 0` flow, the explicit
`physicalFreePhaseEvolution` orbit, and the frozen two-band profile all
agree in physical modal energy. -/
theorem canonicalFreeFlowModeEnergy_eq_explicit_ae_allTime
    (hN : 3 <= N) (kappa beta : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta) :
    ∀ᵐ sample ∂canonicalIIDMassPhaseEnsemble.probability,
      forall time : Real, forall mode : OrderedModeIndex N,
        sampledPhysicalOrderedModeEnergyAlongFlow
            (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
            (canonicalPhaseInitialSample (N := N)
              kappa beta 0 (1 / 4))
            (canonicalRandomMassPhaseGlobalFlow N kappa beta 0 hbeta)
            (sample, time) mode =
              canonicalFrozenFreeModalEnergy sample time mode ∧
          canonicalFrozenFreeModalEnergy sample time mode =
            frozenTwoBandEnergy N mode := by
  filter_upwards [
    RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae
      (N := N) canonicalIIDMassPhaseEnsemble (show 2 <= N by omega)]
      with sample hsimpleSample
  have hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) sample)) := by
    simpa [canonicalMass, harmonicHermitianSample, harmonicHermitian] using
      hsimpleSample
  intro time mode
  refine ⟨canonicalFreeFlowModeEnergy_eq_explicit
    hN kappa beta hbeta sample hsimple time mode, ?_⟩
  exact canonicalFrozenFreeModalEnergy_eq_frozenTwoBandEnergy
    hN sample hsimpleSample time mode

#print axioms canonicalInteractionAmplitude_zeroCoupling_eq_initial
#print axioms canonicalFreeFlowModeEnergy_eq_explicit
#print axioms canonicalFreeFlowModeEnergy_eq_explicit_ae_allTime

end

end ArchonPhysics.R32CanonicalFreeFlowIdentificationV2
