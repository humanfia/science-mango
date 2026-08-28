import ArchonPhysics.PhyslibFPUTGaussianQLevelOffResonantVolumeConsumer

/-!
# Consumer: true volume scale of q-level off-resonant corrections

This conventional consumer exposes the deterministic `1 / time` endpoint,
its frozen-Gaussian leading-output specialization with the weighted acoustic
moment visible, and the fully explicit finite-volume version obtained from
the unconditional acoustic floor.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTQLevelCorrectionResonanceIntegration
open ArchonPhysics.FreeFPUTQLevelOffResonantVolumeBound
open ArchonPhysics.GaussianIIDMassPhaseEnsemble
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhyslibFPUTGaussianQLevelOffResonantVolumeConsumer
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.TruncatedGaussianMassLaw
open Filter MeasureTheory

noncomputable section

/-- Deterministic consumer endpoint with no acoustic-gap assumption. -/
theorem problem_abs_qLevelOffResonantCorrectionSum_le_trueVolume_over_time
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (energyBound ceiling : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    (hObserved : 0 < modeFrequency m observed)
    (hCeiling : 0 ≤ ceiling)
    (hFrequency : ∀ mode,
      orderedModeFrequency (harmonicHermitian m) mode ≤ ceiling)
    {time : Real} (hTime : 0 < time) :
    |qLevelOffResonantCorrectionSum m kappa time energy observed| ≤
      (16 * kappa ^ 2 * energyBound ^ 2 *
          observedChildAcousticInverseMoment m observed +
        12 * (kappa ^ 2 * energyBound ^ 2 /
          modeFrequency m observed ^ 2) * ceiling +
        8 * kappa ^ 2 * energyBound ^ 2 /
          modeFrequency m observed) / time :=
  abs_qLevelOffResonantCorrectionSum_le_acousticMoment_add_uniform_over_time
    m kappa energy observed energyBound ceiling hsimple
    hEnergyBoundNonneg hEnergy hEnergyBound hObserved hCeiling hFrequency hTime

/-- Frozen-Gaussian leading-output consumer endpoint. -/
theorem problem_gaussian_ae_abs_leading_qLevelOffResonantCorrectionSum_le
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (kappa : Real) (energy : Lattice.Site N → Real)
    (energyBound : Real)
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    {time : Real} (hTime : 0 < time) :
    ∀ᵐ sample ∂ensemble.probability,
      let m := ensemble.restrictPositiveMass (N := N) sample
      let q :=
        ArchonPhysics.PhyslibFPUTGaussianCrossOrbitLinearVolumeConsumer.leadingOrderedModeIndex N
      let observed := orderedIndexEquiv q
      |qLevelOffResonantCorrectionSum m kappa time energy observed| ≤
        (16 * kappa ^ 2 * energyBound ^ 2 *
            observedChildAcousticInverseMoment m observed +
          12 * (kappa ^ 2 * energyBound ^ 2 /
            modeFrequency m observed ^ 2) * Real.sqrt 5 +
          8 * kappa ^ 2 * energyBound ^ 2 /
            modeFrequency m observed) / time :=
  gaussian_ae_abs_leading_qLevelOffResonantCorrectionSum_le
    ensemble hN kappa energy energyBound hEnergyBoundNonneg
      hEnergy hEnergyBound hTime

/-- Frozen-Gaussian endpoint with the acoustic moment replaced by its coarse
but unconditional `O(N^(3/2))` finite-volume envelope. -/
theorem problem_gaussian_ae_abs_leading_qLevelOffResonantCorrectionSum_le_explicit
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (kappa : Real) (energy : Lattice.Site N → Real)
    (energyBound : Real)
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    {time : Real} (hTime : 0 < time) :
    ∀ᵐ sample ∂ensemble.probability,
      let m := ensemble.restrictPositiveMass (N := N) sample
      let q :=
        ArchonPhysics.PhyslibFPUTGaussianCrossOrbitLinearVolumeConsumer.leadingOrderedModeIndex N
      let observed := orderedIndexEquiv q
      |qLevelOffResonantCorrectionSum m kappa time energy observed| ≤
        (16 * kappa ^ 2 * energyBound ^ 2 *
            Real.sqrt
              (4 * RandomEnsemble.massUpper * (N : Real) ^ 3) +
          12 * (kappa ^ 2 * energyBound ^ 2 /
            modeFrequency m observed ^ 2) * Real.sqrt 5 +
          8 * kappa ^ 2 * energyBound ^ 2 /
            modeFrequency m observed) / time :=
  gaussian_ae_abs_leading_qLevelOffResonantCorrectionSum_le_explicit
    ensemble hN kappa energy energyBound hEnergyBoundNonneg
      hEnergy hEnergyBound hTime

#print axioms
  problem_abs_qLevelOffResonantCorrectionSum_le_trueVolume_over_time
#print axioms
  problem_gaussian_ae_abs_leading_qLevelOffResonantCorrectionSum_le
#print axioms
  problem_gaussian_ae_abs_leading_qLevelOffResonantCorrectionSum_le_explicit

end

end ArchonPhysicsConsumers.Thermalization
