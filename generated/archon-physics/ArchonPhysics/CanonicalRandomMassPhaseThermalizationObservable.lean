import ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow
import ArchonPhysics.RandomMassPhaseLateWindowObservable

/-!
# Canonical frozen random-mass thermalization observables

This module closes the deterministic/measurable end of the frozen random-mass,
random-phase construction.  The late-window distance and its two rational
hitting diagnostics use the single sample-independent
`canonicalRandomMassPhaseGlobalFlow`; no abstract flow parameter remains.

On every simple-spectrum realization the canonical ambient orbit is identified
for all real times with a genuine untruncated reduced Hamiltonian trajectory.
Consequently the complete late-window `l1` diagnostic is exactly the same
quantity computed from the physical ordered modal energies of that reduced
trajectory.  No finiteness of either hitting time, kinetic limit, or `g⁻²`
scaling is asserted.
-/

namespace ArchonPhysics.CanonicalRandomMassPhaseThermalizationObservable

open ArchonPhysics
open ArchonPhysics.CanonicalRandomMassGlobalFlow
open ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.GlobalRandomMassModalObservable
open ArchonPhysics.GlobalReducedParametricFlowAdapter
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.ParametricLocalHamiltonianFlow
open ArchonPhysics.RandomMassPhaseLateWindowObservable
open ArchonPhysics.RandomMassPositiveLateWindowObservable
open ArchonPhysics.RandomMassReducedPhaseInitialData
open MeasureTheory

noncomputable section

/-- The canonical late-window positive-mode `l1` distance.  All samples use
the same globally defined cutoff flow. -/
def canonicalFrozenLateWindowL1Distance
    {N : Nat} [NeZero N]
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a mu T : Real) : RandomEnsemble.SampleSpace → Real :=
  sampledPositiveLateWindowL1Distance
    (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
    (canonicalPhaseInitialSample (N := N) kappa beta g a)
    (canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta) mu T

/-- Positive-rational strict-threshold hitting time of the canonical frozen
late-window distance.  The value may be infinite. -/
def canonicalFrozenRationalStrictHittingTime
    {N : Nat} [NeZero N]
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a mu delta : Real) : RandomEnsemble.SampleSpace → ENNReal :=
  sampledPositiveLateWindowRationalStrictHittingTime
    (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
    (canonicalPhaseInitialSample (N := N) kappa beta g a)
    (canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta) mu delta

/-- Fixed-duration rational-persistence hitting time of the canonical frozen
late-window distance.  The value may be infinite. -/
def canonicalFrozenRationalPersistentHittingTime
    {N : Nat} [NeZero N]
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a mu delta duration : Real) :
    RandomEnsemble.SampleSpace → ENNReal :=
  sampledPositiveLateWindowRationalPersistentHittingTime
    (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
    (canonicalPhaseInitialSample (N := N) kappa beta g a)
    (canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta)
    mu delta duration

theorem measurable_canonicalFrozenLateWindowL1Distance
    {N : Nat} [NeZero N]
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a mu T : Real) :
    Measurable (canonicalFrozenLateWindowL1Distance
      (N := N) kappa beta g hbeta a mu T) := by
  exact measurable_canonicalPhaseInitialLateWindowL1Distance
    kappa beta g a
    (canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta)
    (measurable_canonicalRandomMassPhaseGlobalFlow kappa beta g hbeta) mu T

theorem measurable_canonicalFrozenRationalStrictHittingTime
    {N : Nat} [NeZero N]
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a mu delta : Real) :
    Measurable (canonicalFrozenRationalStrictHittingTime
      (N := N) kappa beta g hbeta a mu delta) := by
  exact measurable_canonicalPhaseInitialRationalStrictHittingTime
    kappa beta g a
    (canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta)
    (measurable_canonicalRandomMassPhaseGlobalFlow kappa beta g hbeta)
    mu delta

theorem measurable_canonicalFrozenRationalPersistentHittingTime
    {N : Nat} [NeZero N]
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a mu delta duration : Real) :
    Measurable (canonicalFrozenRationalPersistentHittingTime
      (N := N) kappa beta g hbeta a mu delta duration) := by
  exact measurable_canonicalPhaseInitialRationalPersistentHittingTime
    kappa beta g a
    (canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta)
    (measurable_canonicalRandomMassPhaseGlobalFlow kappa beta g hbeta)
    mu delta duration

/-- Positive ordered physical modal-energy profile of a genuine reduced path.
It uses exactly the realization-dependent mask appearing in the sampled
observable. -/
def reducedTrajectoryPositiveEnergyProfile
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (z : Real → ReducedPhaseSpace m) (t : Real)
    (k : OrderedModeIndex N) : Real :=
  if k ∈ positiveModeIndices (harmonicHermitian m) then
    reducedPhysicalOrderedModeEnergy m (z t) k
  else 0

/-- The late-window `l1` diagnostic computed directly from a genuine reduced
physical trajectory. -/
def reducedTrajectoryPositiveLateWindowL1Distance
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (z : Real → ReducedPhaseSpace m) (mu T : Real) : Real :=
  l1Distance
    (normalizedWeights
      (lateWindowAverage (reducedTrajectoryPositiveEnergyProfile m z) mu T))
    (fun k ↦
      if k ∈ positiveModeIndices (harmonicHermitian m) then
        ((N - 1 : Nat) : Real)⁻¹
      else 0)

variable {S : Type*} [MeasurableSpace S]

omit [MeasurableSpace S] in
/-- Pointwise fidelity of one ordered physical mode.  Unlike the fixed-mass
adapter in `GlobalRandomMassModalObservable`, the mass family may vary away
from the selected sample. -/
theorem sampledPhysicalOrderedModeEnergyAlongFlow_eq_reduced_at
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (kappa beta g : Real) (s : S)
    (z : Real → ReducedPhaseSpace (massSample s))
    (hmatch : ∀ t, flow (initial s, t) =
      embedReducedPoint (massSample s) kappa beta g (z t))
    (t : Real) (k : OrderedModeIndex N) :
    sampledPhysicalOrderedModeEnergyAlongFlow
        massSample initial flow (s, t) k =
      reducedPhysicalOrderedModeEnergy (massSample s) (z t) k := by
  simp [sampledPhysicalOrderedModeEnergyAlongFlow,
    RandomMassMeasurableHarmonicEnergy.harmonicOrderedPhysicalModeEnergy,
    RandomMassMeasurableHarmonicEnergy.massWeightedPositionSample,
    RandomMassMeasurableHarmonicEnergy.massWeightedMomentumSample,
    sampledFlowPosition, sampledFlowMomentum, reducedPhysicalOrderedModeEnergy,
    harmonicHermitianSample, hmatch, embedReducedPoint]

omit [MeasurableSpace S] in
/-- All combinators in the sampled late-window diagnostic are extensional in
the physical modal-energy path.  Hence an all-time ambient/reduced match gives
equality with the genuine reduced-path diagnostic. -/
theorem sampledPositiveLateWindowL1Distance_eq_reduced_of_match
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (kappa beta g : Real) (s : S)
    (z : Real → ReducedPhaseSpace (massSample s))
    (hmatch : ∀ t, flow (initial s, t) =
      embedReducedPoint (massSample s) kappa beta g (z t))
    (mu T : Real) :
    sampledPositiveLateWindowL1Distance
        massSample initial flow mu T s =
      reducedTrajectoryPositiveLateWindowL1Distance
        (massSample s) z mu T := by
  have hprofile :
      (fun t k ↦ sampledPositivePhysicalOrderedEnergyProfileAlongFlow
        massSample initial flow (s, t) k) =
      reducedTrajectoryPositiveEnergyProfile (massSample s) z := by
    funext t k
    change
      (if k ∈ positiveModeIndices (harmonicHermitian (massSample s)) then
        sampledPhysicalOrderedModeEnergyAlongFlow
          massSample initial flow (s, t) k else 0) =
      (if k ∈ positiveModeIndices (harmonicHermitian (massSample s)) then
        reducedPhysicalOrderedModeEnergy (massSample s) (z t) k else 0)
    by_cases hk : k ∈ positiveModeIndices (harmonicHermitian (massSample s))
    · simp only [if_pos hk]
      exact sampledPhysicalOrderedModeEnergyAlongFlow_eq_reduced_at
        massSample initial flow kappa beta g s z hmatch t k
    · simp [hk]
  unfold sampledPositiveLateWindowL1Distance
    sampledPositiveLateWindowNormalizedWeights
    sampledPositiveLateWindowAverage sampledPositiveUniformWeights
    reducedTrajectoryPositiveLateWindowL1Distance
  rw [hprofile]
  rfl

/-- On a simple realization, the canonical frozen observable is literally
computed along a genuine untruncated reduced Hamiltonian trajectory. -/
theorem canonicalFrozenLateWindowL1Distance_matches_reduced_of_simple
    {N : Nat} [NeZero N]
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
          (N := N) omega)))
    (mu T : Real) :
    ∃ z : Real → ReducedPhaseSpace
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega),
      z 0 = reducedInitialStateOfSimple
        canonicalIIDMassPhaseEnsemble a omega hsimple ∧
      (∀ t, HasDerivAt z
        (reducedVectorField
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega) kappa beta g (z t)) t) ∧
      (∀ t, canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta
          (canonicalPhaseInitialSample (N := N) kappa beta g a omega, t) =
        embedReducedPoint
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega) kappa beta g (z t)) ∧
      (∀ t k, sampledPhysicalOrderedModeEnergyAlongFlow
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
          (canonicalPhaseInitialSample (N := N) kappa beta g a)
          (canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta)
          (omega, t) k =
        reducedPhysicalOrderedModeEnergy
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega) (z t) k) ∧
      canonicalFrozenLateWindowL1Distance
          (N := N) kappa beta g hbeta a mu T omega =
        reducedTrajectoryPositiveLateWindowL1Distance
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega) z mu T := by
  obtain ⟨z, hz0, hz, htrajectory, _henergy⟩ :=
    canonicalRandomMassPhaseTrajectory_matches_reduced_of_simple
      canonicalIIDMassPhaseEnsemble hN ha0 ha1
      kappa beta g hbeta omega hsimple
  have hmatch : ∀ t,
      canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta
          (canonicalPhaseInitialSample (N := N) kappa beta g a omega, t) =
        embedReducedPoint
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega) kappa beta g (z t) := by
    intro t
    simpa [canonicalRandomMassPhaseTrajectory,
      canonicalIIDRandomMassTrajectory, canonicalRandomMassTrajectory,
      canonicalPhaseInitialSample, canonicalRandomMassPhaseGlobalFlow,
      canonicalIIDRandomMassGlobalFlow, canonicalIIDUniformEnergyShell] using
      htrajectory t
  have hmode : ∀ t k, sampledPhysicalOrderedModeEnergyAlongFlow
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
      (canonicalPhaseInitialSample (N := N) kappa beta g a)
      (canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta)
      (omega, t) k =
    reducedPhysicalOrderedModeEnergy
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
        (N := N) omega) (z t) k := by
    intro t k
    exact sampledPhysicalOrderedModeEnergyAlongFlow_eq_reduced_at
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
      (canonicalPhaseInitialSample (N := N) kappa beta g a)
      (canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta)
      kappa beta g omega z hmatch t k
  refine ⟨z, hz0, hz, hmatch, hmode, ?_⟩
  exact sampledPositiveLateWindowL1Distance_eq_reduced_of_match
    (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
    (canonicalPhaseInitialSample (N := N) kappa beta g a)
    (canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta)
    kappa beta g omega z hmatch mu T

/-- Almost surely, the measurable canonical frozen late-window diagnostic is
the physical diagnostic of one genuine untruncated reduced trajectory. -/
theorem canonicalFrozenLateWindowL1Distance_matches_reduced_ae
    {N : Nat} [NeZero N]
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu T : Real) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      ∃ hsimple : SimpleOrderedSpectrum
          (harmonicHermitian
            (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
              (N := N) omega)),
        ∃ z : Real → ReducedPhaseSpace
            (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
              (N := N) omega),
          z 0 = reducedInitialStateOfSimple
            canonicalIIDMassPhaseEnsemble a omega hsimple ∧
          (∀ t, HasDerivAt z
            (reducedVectorField
              (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
                (N := N) omega) kappa beta g (z t)) t) ∧
          (∀ t, canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta
              (canonicalPhaseInitialSample (N := N) kappa beta g a omega, t) =
            embedReducedPoint
              (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
                (N := N) omega) kappa beta g (z t)) ∧
          (∀ t k, sampledPhysicalOrderedModeEnergyAlongFlow
              (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
              (canonicalPhaseInitialSample (N := N) kappa beta g a)
              (canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta)
              (omega, t) k =
            reducedPhysicalOrderedModeEnergy
              (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
                (N := N) omega) (z t) k) ∧
          canonicalFrozenLateWindowL1Distance
              (N := N) kappa beta g hbeta a mu T omega =
            reducedTrajectoryPositiveLateWindowL1Distance
              (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
                (N := N) omega) z mu T := by
  have hsimpleAE :=
    RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae
      (N := N) canonicalIIDMassPhaseEnsemble (show 2 ≤ N by omega)
  filter_upwards [hsimpleAE] with omega hsimpleSample
  have hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
          (N := N) omega)) := by
    simpa [harmonicHermitianSample, harmonicHermitian] using hsimpleSample
  exact ⟨hsimple,
    canonicalFrozenLateWindowL1Distance_matches_reduced_of_simple
      hN ha0 ha1 kappa beta g hbeta omega hsimple mu T⟩

end

end ArchonPhysics.CanonicalRandomMassPhaseThermalizationObservable
