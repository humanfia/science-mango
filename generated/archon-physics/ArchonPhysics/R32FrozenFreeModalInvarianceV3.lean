import ArchonPhysics.CanonicalRandomMicroscopicCertificate
import ArchonPhysics.FreeFPUTTensorPhaseExpansion
import ArchonPhysics.LateWindowTailAverage
import ArchonPhysics.OrderedTranslationLastMode
import ArchonPhysics.R32LateWindowNormalizationStability

/-!
# R32: exact invariance of the canonical frozen profile under the free flow

This Add-only corrected version records the exact `g = 0` baseline for the
canonical random-mass initial state.  Almost surely its physical ordered
harmonic energies are the frozen quarter-contrast two-band profile.  The
explicit harmonic evolution is implemented by `physicalFreePhaseEvolution`;
along that orbit every ordered modal energy is constant for every real time,
including the zero-frequency translation mode.  Consequently the total
energy is always one and every positive late-window normalized profile is
exactly the original frozen profile.

No nonlinear flow comparison, perturbative estimate, or kinetic approximation
is used here.
-/

namespace ArchonPhysics.R32FrozenFreeModalInvarianceV3

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.CanonicalRandomMicroscopicCertificate
open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.FiniteHarmonicHaarPhasePropagation
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.LateWindowTailAverage
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhaseEnergyModeCoordinates
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPositiveLateWindowObservable
open ArchonPhysics.R32FrozenEnergyDilution
open ArchonPhysics.R32LateWindowNormalizationStability
open MeasureTheory

noncomputable section

/-! ## Canonical initial physical energies -/

/-- The physical ordered harmonic energy of the canonical frozen-quarter
initial position and momentum. -/
def canonicalFrozenInitialModeEnergy
    {N : Nat} [NeZero N]
    (sample : RandomEnsemble.SampleSpace) (mode : OrderedModeIndex N) : Real :=
  RandomMassMeasurableHarmonicEnergy.harmonicOrderedPhysicalModeEnergy
    (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
    (initialPhysicalPosition canonicalIIDMassPhaseEnsemble (1 / 4))
    (initialPhysicalMomentum canonicalIIDMassPhaseEnsemble (1 / 4))
    sample mode

/-- Almost surely, every canonical initial physical modal energy is exactly
the frozen two-band energy. -/
theorem canonicalFrozenInitialModeEnergy_eq_frozenTwoBandEnergy_ae
    {N : Nat} [NeZero N] (hN : 3 <= N) :
    ∀ᵐ sample ∂canonicalIIDMassPhaseEnsemble.probability,
      ∀ mode : OrderedModeIndex N,
        canonicalFrozenInitialModeEnergy sample mode =
          frozenTwoBandEnergy N mode := by
  have hprofile := initialProfileIsExact_ae hN
    (a := (1 / 4 : Real)) (by norm_num) (by norm_num)
  filter_upwards [hprofile] with sample hsample
  intro mode
  simpa [canonicalFrozenInitialModeEnergy, frozenTwoBandEnergy] using
    hsample.1 mode

/-- The canonical initial physical harmonic energy has total one almost
surely. -/
theorem totalWeight_canonicalFrozenInitialModeEnergy_eq_one_ae
    {N : Nat} [NeZero N] (hN : 3 <= N) :
    ∀ᵐ sample ∂canonicalIIDMassPhaseEnsemble.probability,
      totalWeight (canonicalFrozenInitialModeEnergy (N := N) sample) = 1 := by
  have hprofile := initialProfileIsExact_ae hN
    (a := (1 / 4 : Real)) (by norm_num) (by norm_num)
  filter_upwards [hprofile] with sample hsample
  simpa [totalWeight, canonicalFrozenInitialModeEnergy] using hsample.2

/-! ## Explicit `g = 0` harmonic evolution -/

/-- The canonical ordered Haar phase vector advanced by the physical free
harmonic phase flow.  This is the explicit `g = 0` orbit in modal phase
coordinates. -/
def canonicalFrozenFreePhase
    {N : Nat} [NeZero N]
    (sample : RandomEnsemble.SampleSpace) (time : Real) :
    UnitAddTorus (OrderedModeIndex N) :=
  physicalFreePhaseEvolution
    (orderedFrequencySample canonicalIIDMassPhaseEnsemble sample) time
    (fun mode => orderedPhaseSample canonicalIIDMassPhaseEnsemble sample mode)

/-- Position coefficient of one ordered mode along the explicit free orbit. -/
def canonicalFrozenFreeModePosition
    {N : Nat} [NeZero N]
    (sample : RandomEnsemble.SampleSpace) (time : Real)
    (mode : OrderedModeIndex N) : Real :=
  phaseCoordinate (frozenTwoBandEnergy N mode)
    (orderedFrequencySample canonicalIIDMassPhaseEnsemble sample mode)
    (canonicalFrozenFreePhase sample time mode)

/-- Momentum coefficient of one ordered mode along the explicit free orbit. -/
def canonicalFrozenFreeModeMomentum
    {N : Nat} [NeZero N]
    (sample : RandomEnsemble.SampleSpace) (time : Real)
    (mode : OrderedModeIndex N) : Real :=
  phaseMomentum (frozenTwoBandEnergy N mode)
    (canonicalFrozenFreePhase sample time mode)

/-- Ordered harmonic modal energy along the explicit free orbit. -/
def canonicalFrozenFreeModalEnergy
    {N : Nat} [NeZero N]
    (sample : RandomEnsemble.SampleSpace) (time : Real)
    (mode : OrderedModeIndex N) : Real :=
  HarmonicModes.modalEnergy
    ((orderedFrequencySample canonicalIIDMassPhaseEnsemble sample mode) ^ 2)
    (canonicalFrozenFreeModePosition sample time mode)
    (canonicalFrozenFreeModeMomentum sample time mode)

/-- On a simple mass realization, the explicit free energy of every mode is
the prescribed frozen energy at every real time.  The translation mode is
handled separately at its exact zero frequency. -/
theorem canonicalFrozenFreeModalEnergy_eq_frozenTwoBandEnergy
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (sample : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitianSample
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N)) sample))
    (time : Real) (mode : OrderedModeIndex N) :
    canonicalFrozenFreeModalEnergy sample time mode =
      frozenTwoBandEnergy N mode := by
  by_cases hlast : mode = lastOrderedIndex (ι := Lattice.Site N)
  · subst mode
    have heigenzero :
        orderedEigenvalue
            (harmonicHermitianSample
              (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
              sample)
            (lastOrderedIndex (ι := Lattice.Site N)) = 0 := by
      simpa [harmonicHermitianSample, harmonicHermitian] using
        harmonic_lastOrderedEigenvalue_eq_zero
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) sample)
    have hzero : orderedFrequencySample canonicalIIDMassPhaseEnsemble sample
        (lastOrderedIndex (ι := Lattice.Site N)) = 0 := by
      simp [orderedFrequencySample, orderedModeFrequency, heigenzero]
    simp [canonicalFrozenFreeModalEnergy,
      canonicalFrozenFreeModePosition, canonicalFrozenFreeModeMomentum,
      hzero, frozenTwoBandEnergy, HarmonicModes.modalEnergy,
      phaseCoordinate, phaseMomentum]
  · have hfrequency :
        0 < orderedFrequencySample canonicalIIDMassPhaseEnsemble sample mode := by
      have hpos := (orderedModeFrequency_pos_iff_ne_last
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) sample)
        hsimple mode).2 hlast
      simpa [orderedFrequencySample, harmonicHermitianSample,
        harmonicHermitian] using hpos
    exact modalEnergy_phaseCoordinates
      (canonicalFrozenFreePhase sample time mode)
      (frozenTwoBandEnergy_nonneg hN mode) hfrequency

/-- Every free modal energy is independent of time. -/
theorem canonicalFrozenFreeModalEnergy_invariant
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (sample : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitianSample
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N)) sample))
    (s t : Real) (mode : OrderedModeIndex N) :
    canonicalFrozenFreeModalEnergy sample t mode =
      canonicalFrozenFreeModalEnergy sample s mode := by
  rw [canonicalFrozenFreeModalEnergy_eq_frozenTwoBandEnergy
      hN sample hsimple t mode,
    canonicalFrozenFreeModalEnergy_eq_frozenTwoBandEnergy
      hN sample hsimple s mode]

/-- Almost surely, the canonical explicit free orbit has the exact frozen
energy in every mode simultaneously for all real times. -/
theorem canonicalFrozenFreeModalEnergy_eq_frozenTwoBandEnergy_ae
    {N : Nat} [NeZero N] (hN : 3 <= N) :
    ∀ᵐ sample ∂canonicalIIDMassPhaseEnsemble.probability,
      ∀ time : Real, ∀ mode : OrderedModeIndex N,
        canonicalFrozenFreeModalEnergy sample time mode =
          frozenTwoBandEnergy N mode := by
  have hsimpleAE :=
    RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae
      (N := N) canonicalIIDMassPhaseEnsemble (show 2 <= N by omega)
  filter_upwards [hsimpleAE] with sample hsimple
  intro time mode
  exact canonicalFrozenFreeModalEnergy_eq_frozenTwoBandEnergy
    hN sample hsimple time mode

/-- Almost surely, the explicit free energy agrees both with the canonical
initial physical energy and with the deterministic frozen profile. -/
theorem canonicalFrozenInitial_and_freeModalEnergy_agree_ae
    {N : Nat} [NeZero N] (hN : 3 <= N) :
    ∀ᵐ sample ∂canonicalIIDMassPhaseEnsemble.probability,
      ∀ time : Real, ∀ mode : OrderedModeIndex N,
        canonicalFrozenFreeModalEnergy sample time mode =
            canonicalFrozenInitialModeEnergy sample mode ∧
          canonicalFrozenInitialModeEnergy sample mode =
            frozenTwoBandEnergy N mode := by
  filter_upwards
    [canonicalFrozenInitialModeEnergy_eq_frozenTwoBandEnergy_ae hN,
      canonicalFrozenFreeModalEnergy_eq_frozenTwoBandEnergy_ae hN]
      with sample hinitial hfree
  intro time mode
  exact ⟨(hfree time mode).trans (hinitial mode).symm, hinitial mode⟩

/-! ## Total energy and late-window profile -/

/-- The total explicit free harmonic modal energy is one at every time. -/
theorem totalWeight_canonicalFrozenFreeModalEnergy_eq_one
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (sample : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitianSample
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N)) sample))
    (time : Real) :
    totalWeight
        (canonicalFrozenFreeModalEnergy (N := N) sample time) = 1 := by
  calc
    totalWeight (canonicalFrozenFreeModalEnergy (N := N) sample time) =
        ∑ mode : OrderedModeIndex N, frozenTwoBandEnergy N mode := by
      unfold totalWeight
      apply Finset.sum_congr rfl
      intro mode _hmode
      exact canonicalFrozenFreeModalEnergy_eq_frozenTwoBandEnergy
        hN sample hsimple time mode
    _ = 1 := sum_frozenTwoBandEnergy_eq_one hN

/-- Every positive late-window average of the explicit free orbit is exactly
the frozen profile. -/
theorem lateWindowAverage_canonicalFrozenFreeModalEnergy_eq
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (sample : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitianSample
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N)) sample))
    (mu T : Real) (hmu : mu < 1) (hT : 0 < T) :
    lateWindowAverage
        (canonicalFrozenFreeModalEnergy (N := N) sample) mu T =
      frozenTwoBandEnergy N := by
  have hprofile : canonicalFrozenFreeModalEnergy (N := N) sample =
      fun _time : Real => frozenTwoBandEnergy N := by
    funext time mode
    exact canonicalFrozenFreeModalEnergy_eq_frozenTwoBandEnergy
      hN sample hsimple time mode
  rw [hprofile]
  exact lateWindowAverage_const (frozenTwoBandEnergy N) mu T hmu hT

/-- The late-window total energy is still exactly one. -/
theorem totalWeight_lateWindowAverage_canonicalFrozenFreeModalEnergy_eq_one
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (sample : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitianSample
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N)) sample))
    (mu T : Real) (hmu : mu < 1) (hT : 0 < T) :
    totalWeight
      (lateWindowAverage
        (canonicalFrozenFreeModalEnergy (N := N) sample) mu T) = 1 := by
  rw [lateWindowAverage_canonicalFrozenFreeModalEnergy_eq
    hN sample hsimple mu T hmu hT]
  exact sum_frozenTwoBandEnergy_eq_one hN

/-- Normalizing a positive late-window profile changes nothing: the result is
the original frozen two-band profile exactly. -/
theorem normalizedWeights_lateWindowAverage_canonicalFrozenFreeModalEnergy
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (sample : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitianSample
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N)) sample))
    (mu T : Real) (hmu : mu < 1) (hT : 0 < T) :
    normalizedWeights
        (lateWindowAverage
          (canonicalFrozenFreeModalEnergy (N := N) sample) mu T) =
      frozenTwoBandEnergy N := by
  rw [lateWindowAverage_canonicalFrozenFreeModalEnergy_eq
    hN sample hsimple mu T hmu hT]
  exact normalizedWeights_frozenTwoBandEnergy hN

/-- Almost-sure all-window version of the exact normalized-profile identity. -/
theorem normalizedWeights_lateWindowAverage_canonicalFrozenFreeModalEnergy_ae
    {N : Nat} [NeZero N] (hN : 3 <= N) :
    ∀ᵐ sample ∂canonicalIIDMassPhaseEnsemble.probability,
      ∀ mu T : Real, mu < 1 -> 0 < T ->
        normalizedWeights
            (lateWindowAverage
              (canonicalFrozenFreeModalEnergy (N := N) sample) mu T) =
          frozenTwoBandEnergy N := by
  have hsimpleAE :=
    RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae
      (N := N) canonicalIIDMassPhaseEnsemble (show 2 <= N by omega)
  filter_upwards [hsimpleAE] with sample hsimple
  intro mu T hmu hT
  exact normalizedWeights_lateWindowAverage_canonicalFrozenFreeModalEnergy
    hN sample hsimple mu T hmu hT

#print axioms canonicalFrozenInitialModeEnergy_eq_frozenTwoBandEnergy_ae
#print axioms canonicalFrozenFreeModalEnergy_invariant
#print axioms totalWeight_canonicalFrozenFreeModalEnergy_eq_one
#print axioms normalizedWeights_lateWindowAverage_canonicalFrozenFreeModalEnergy
#print axioms normalizedWeights_lateWindowAverage_canonicalFrozenFreeModalEnergy_ae

end

end ArchonPhysics.R32FrozenFreeModalInvarianceV3
