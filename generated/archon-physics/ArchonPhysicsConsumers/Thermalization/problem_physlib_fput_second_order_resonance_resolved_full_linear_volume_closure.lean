import ArchonPhysics.PhyslibFPUTSecondOrderResonanceResolvedFullLinearVolumeClosure

/-!
# Consumer: full resonance-resolved linear-volume closure

This consumer exposes the deterministic frozen-support endpoint and its
frozen Gaussian leading-mode almost-everywhere specialization.  The q-level
off-resonant and cross-orbit pieces are explicit `O(N/T)` bounds.  The
counterrotating static mass remains displayed and is not claimed uniform in
volume.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctCounterrotatingSignedFluxDecay
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTQLevelCorrectionResonanceIntegration
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.GaussianIIDMassPhaseEnsemble
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhyslibFPUTGaussianCrossOrbitLinearVolumeConsumer
open ArchonPhysics.PhyslibFPUTSecondOrderQLevelUnifiedClosure
open ArchonPhysics.PhyslibFPUTSecondOrderResonanceResolvedFullLinearVolumeClosure
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound
open ArchonPhysics.PhyslibFPUTSecondOrderUnifiedDegenerateClosure
open ArchonPhysics.RandomMassPositiveCollisionData
open Filter MeasureTheory

noncomputable section

/-- Named deterministic endpoint with explicit linear-volume q-level and
cross-orbit contributions. -/
theorem problem_abs_ordered_resonanceResolvedResidual_le_fullLinearVolumeBound
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (q : OrderedModeIndex N) (energy : Lattice.Site N → Real)
    (energyBound ceiling : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    (hCeiling : 0 ≤ ceiling)
    (hFrequencyCeiling : ∀ mode,
      orderedModeFrequency (harmonicHermitian m) mode ≤ ceiling)
    (hmassLower : ∀ i, (4 / 5 : Real) ≤ m.mass i)
    (hmassUpper : ∀ i, m.mass i ≤ (6 / 5 : Real))
    {time : Real} (htime : 0 < time)
    (hFrequency : 0 < orderedModeFrequency (harmonicHermitian m) q) :
    |normalizedSecondOrderHaarBroadening
          m kappa beta energy (orderedIndexEquiv q) time -
        qLevelResolvedSecondOrderSignedFluxMain
          m kappa time energy (orderedIndexEquiv q) -
        allEqualOrbitGainSum
          m kappa time energy (orderedIndexEquiv q) -
        qLevelPotentiallyResonantCorrectionSum
          m kappa time energy (orderedIndexEquiv q)| ≤
      (16 * kappa ^ 2 * energyBound ^ 2 * (N : Real) +
        12 * (kappa ^ 2 * energyBound ^ 2 /
          orderedModeFrequency (harmonicHermitian m) q ^ 2) * ceiling +
        8 * kappa ^ 2 * energyBound ^ 2 /
          orderedModeFrequency (harmonicHermitian m) q) / time +
        allDistinctCounterrotatingStaticFluxMass
          m kappa energy (orderedIndexEquiv q) *
          ((2 / orderedModeFrequency (harmonicHermitian m) q) ^ 2 / time) +
        2 * (N : Real) * kappa ^ 2 * energyBound ^ 2 /
          (orderedModeFrequency (harmonicHermitian m) q * time) :=
  abs_ordered_resonanceResolvedResidual_le_fullLinearVolumeBound
    m kappa beta q energy energyBound ceiling hsimple hEnergyBoundNonneg
    hEnergy hEnergyBound hCeiling hFrequencyCeiling hmassLower hmassUpper
    htime hFrequency

/-- Named frozen-Gaussian leading-output specialization. -/
theorem problem_gaussian_ae_abs_leading_resonanceResolvedResidual_le_fullLinearVolumeBound
    {Omega : Type*} [MeasurableSpace Omega]
    {parameters : TruncatedGaussianMassLaw.Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (kappa beta : Real) (energy : Lattice.Site N → Real)
    (energyBound : Real)
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    {time : Real} (htime : 0 < time) :
    ∀ᵐ sample ∂ensemble.probability,
      let m := ensemble.restrictPositiveMass (N := N) sample
      let q := leadingOrderedModeIndex N
      |normalizedSecondOrderHaarBroadening
            m kappa beta energy (orderedIndexEquiv q) time -
          qLevelResolvedSecondOrderSignedFluxMain
            m kappa time energy (orderedIndexEquiv q) -
          allEqualOrbitGainSum
            m kappa time energy (orderedIndexEquiv q) -
          qLevelPotentiallyResonantCorrectionSum
            m kappa time energy (orderedIndexEquiv q)| ≤
        (16 * kappa ^ 2 * energyBound ^ 2 * (N : Real) +
          12 * (kappa ^ 2 * energyBound ^ 2 /
            Real.sqrt (5 / 3 : Real) ^ 2) * Real.sqrt 5 +
          8 * kappa ^ 2 * energyBound ^ 2 /
            Real.sqrt (5 / 3 : Real)) / time +
          allDistinctCounterrotatingStaticFluxMass
            m kappa energy (orderedIndexEquiv q) *
            ((2 / Real.sqrt (5 / 3 : Real)) ^ 2 / time) +
          2 * (N : Real) * kappa ^ 2 * energyBound ^ 2 /
            (Real.sqrt (5 / 3 : Real) * time) :=
  gaussian_ae_abs_leading_resonanceResolvedResidual_le_fullLinearVolumeBound
    ensemble hN kappa beta energy energyBound hEnergyBoundNonneg
    hEnergy hEnergyBound htime

#print axioms
  problem_abs_ordered_resonanceResolvedResidual_le_fullLinearVolumeBound
#print axioms
  problem_gaussian_ae_abs_leading_resonanceResolvedResidual_le_fullLinearVolumeBound

end

end ArchonPhysicsConsumers.Thermalization
