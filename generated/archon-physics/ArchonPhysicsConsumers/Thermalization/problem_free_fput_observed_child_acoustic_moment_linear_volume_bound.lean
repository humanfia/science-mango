import ArchonPhysics.FreeFPUTObservedChildAcousticMomentLinearVolumeBound
import ArchonPhysics.TruncatedGaussianMassPhaseEnsemble

/-!
# Consumer: frozen-Gaussian linear-volume acoustic moment

Every frozen sample of the conditioned Gaussian mass ensemble lies in the
deterministic support `[4/5, 6/5]`.  This consumer applies the clean-cycle
spectral comparison to expose the positive-frequency floor, the `O(N)`
observed-child acoustic moment, and the resulting q-level inverse-time bound.
-/

namespace ArchonPhysicsConsumers.Thermalization.FreeFPUTObservedChildAcousticMomentLinearVolumeBound

open ArchonPhysics
open ArchonPhysics.FreeFPUTObservedChildAcousticMomentLinearVolumeBound
open ArchonPhysics.FreeFPUTQLevelCorrectionResonanceIntegration
open ArchonPhysics.FreeFPUTQLevelOffResonantVolumeBound
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.TruncatedGaussianMassLaw

noncomputable section

/-- Frozen finite-volume mass configuration of one Gaussian sample. -/
def gaussianFrozenMass
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (sample : Omega) :
    Lattice.PositiveMassConfig N :=
  ensemble.restrictPositiveMass sample

private theorem gaussianFrozenMass_lower
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (sample : Omega) :
    ∀ i : Lattice.Site N, (4 / 5 : Real) ≤
      (gaussianFrozenMass (N := N) ensemble sample).mass i := by
  intro i
  simpa [gaussianFrozenMass, RandomEnsemble.massLower] using
    (ensemble.mass_mem_support i.val sample).1

private theorem gaussianFrozenMass_upper
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (sample : Omega) :
    ∀ i : Lattice.Site N,
      (gaussianFrozenMass (N := N) ensemble sample).mass i ≤ (6 / 5 : Real) := by
  intro i
  simpa [gaussianFrozenMass, RandomEnsemble.massUpper] using
    (ensemble.mass_mem_support i.val sample).2

/-- Every positive frozen-Gaussian squared frequency is at least
`(40/3)/N²`. -/
theorem gaussianSample_modeFrequencySq_ge_fortyThirds_div_volume_sq
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (sample : Omega)
    (mode : Lattice.Site N)
    (hfrequency : 0 < modeFrequency
      (gaussianFrozenMass (N := N) ensemble sample) mode) :
    (40 / 3 : Real) / (N : Real) ^ 2 ≤
      modeFrequencySq (gaussianFrozenMass (N := N) ensemble sample) mode :=
  frozenSupport_modeFrequencySq_ge_fortyThirds_div_volume_sq
    (gaussianFrozenMass (N := N) ensemble sample)
    (gaussianFrozenMass_lower (N := N) ensemble sample)
    (gaussianFrozenMass_upper (N := N) ensemble sample) mode hfrequency

/-- The full frozen-Gaussian observed-child inverse-frequency moment is at
most the volume. -/
theorem gaussianSample_observedChildAcousticInverseMoment_le_volume
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (sample : Omega)
    (observed : Lattice.Site N) :
    observedChildAcousticInverseMoment
        (gaussianFrozenMass (N := N) ensemble sample) observed ≤ (N : Real) :=
  observedChildAcousticInverseMoment_le_volume
    (gaussianFrozenMass (N := N) ensemble sample)
    (gaussianFrozenMass_lower (N := N) ensemble sample)
    (gaussianFrozenMass_upper (N := N) ensemble sample) observed

/-- Frozen-Gaussian static q-level correction with the `O(N)` acoustic term
made explicit. -/
theorem gaussianSample_qLevelOffResonantCorrectionStaticMass_le_linear_volume
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (sample : Omega)
    (kappa : Real) (energy : Lattice.Site N → Real)
    (observed : Lattice.Site N) (energyBound ceiling : Real)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (gaussianFrozenMass (N := N) ensemble sample)))
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    (hObserved :
      0 < modeFrequency
        (gaussianFrozenMass (N := N) ensemble sample) observed)
    (hCeiling : 0 ≤ ceiling)
    (hFrequency : ∀ mode,
      orderedModeFrequency
        (harmonicHermitian
          (gaussianFrozenMass (N := N) ensemble sample)) mode ≤
          ceiling) :
    qLevelOffResonantCorrectionStaticMass
        (gaussianFrozenMass (N := N) ensemble sample) kappa energy observed ≤
      16 * kappa ^ 2 * energyBound ^ 2 * (N : Real) +
        12 * (kappa ^ 2 * energyBound ^ 2 /
          modeFrequency
            (gaussianFrozenMass (N := N) ensemble sample) observed ^ 2) *
            ceiling +
        8 * kappa ^ 2 * energyBound ^ 2 /
          modeFrequency
            (gaussianFrozenMass (N := N) ensemble sample) observed :=
  qLevelOffResonantCorrectionStaticMass_le_linear_volume
    (gaussianFrozenMass (N := N) ensemble sample) kappa energy observed
    energyBound ceiling hsimple hEnergyBoundNonneg hEnergy hEnergyBound
    hObserved hCeiling hFrequency
    (gaussianFrozenMass_lower (N := N) ensemble sample)
    (gaussianFrozenMass_upper (N := N) ensemble sample)

/-- Frozen-Gaussian inverse-time endpoint with the linear-volume acoustic
term substituted. -/
theorem gaussianSample_abs_qLevelOffResonantCorrectionSum_le_linear_volume
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (sample : Omega)
    (kappa : Real) (energy : Lattice.Site N → Real)
    (observed : Lattice.Site N) (energyBound ceiling : Real)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (gaussianFrozenMass (N := N) ensemble sample)))
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    (hObserved :
      0 < modeFrequency
        (gaussianFrozenMass (N := N) ensemble sample) observed)
    (hCeiling : 0 ≤ ceiling)
    (hFrequency : ∀ mode,
      orderedModeFrequency
        (harmonicHermitian
          (gaussianFrozenMass (N := N) ensemble sample)) mode ≤
          ceiling)
    {time : Real} (hTime : 0 < time) :
    |qLevelOffResonantCorrectionSum
        (gaussianFrozenMass (N := N) ensemble sample) kappa time energy
          observed| ≤
      (16 * kappa ^ 2 * energyBound ^ 2 * (N : Real) +
        12 * (kappa ^ 2 * energyBound ^ 2 /
          modeFrequency
            (gaussianFrozenMass (N := N) ensemble sample) observed ^ 2) *
            ceiling +
        8 * kappa ^ 2 * energyBound ^ 2 /
          modeFrequency
            (gaussianFrozenMass (N := N) ensemble sample) observed) /
        time :=
  abs_qLevelOffResonantCorrectionSum_le_linear_volume_over_time
    (gaussianFrozenMass (N := N) ensemble sample) kappa energy observed
    energyBound ceiling hsimple hEnergyBoundNonneg hEnergy hEnergyBound
    hObserved hCeiling hFrequency
    (gaussianFrozenMass_lower (N := N) ensemble sample)
    (gaussianFrozenMass_upper (N := N) ensemble sample) hTime

#print axioms gaussianSample_modeFrequencySq_ge_fortyThirds_div_volume_sq
#print axioms gaussianSample_observedChildAcousticInverseMoment_le_volume
#print axioms
  gaussianSample_qLevelOffResonantCorrectionStaticMass_le_linear_volume
#print axioms
  gaussianSample_abs_qLevelOffResonantCorrectionSum_le_linear_volume

end

end ArchonPhysicsConsumers.Thermalization.FreeFPUTObservedChildAcousticMomentLinearVolumeBound
