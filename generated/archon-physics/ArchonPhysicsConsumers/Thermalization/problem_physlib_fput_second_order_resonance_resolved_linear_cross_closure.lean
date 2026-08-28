import ArchonPhysics.PhyslibFPUTSecondOrderResonanceResolvedLinearCrossClosure

/-!
# Consumer: resonance-resolved second order with linear cross volume

This consumer exposes the deterministic ordered-mode endpoint and its frozen
Gaussian leading-mode almost-everywhere specialization.  Potentially resonant
corrections stay in the main expression; the off-resonant and counterrotating
static masses are not asserted to be uniform in volume.
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
open ArchonPhysics.PhyslibFPUTSecondOrderResonanceResolvedLinearCrossClosure
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound
open ArchonPhysics.PhyslibFPUTSecondOrderUnifiedDegenerateClosure
open ArchonPhysics.RandomMassPositiveCollisionData
open Filter MeasureTheory

noncomputable section

/-- Named deterministic endpoint for the full resonance-resolved residual with
the linear-volume cross contribution. -/
theorem problem_abs_ordered_resonanceResolvedResidual_le_linearCrossVolumeBound
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (q : OrderedModeIndex N) (energy : Lattice.Site N → Real)
    (energyBound : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
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
      qLevelOffResonantCorrectionStaticMass
          m kappa energy (orderedIndexEquiv q) / time +
        allDistinctCounterrotatingStaticFluxMass
          m kappa energy (orderedIndexEquiv q) *
          ((2 / orderedModeFrequency (harmonicHermitian m) q) ^ 2 / time) +
        2 * (N : Real) * kappa ^ 2 * energyBound ^ 2 /
          (orderedModeFrequency (harmonicHermitian m) q * time) :=
  abs_ordered_resonanceResolvedResidual_le_linearCrossVolumeBound
    m kappa beta q energy energyBound hsimple hEnergyBoundNonneg
      hEnergy hEnergyBound htime hFrequency

/-- Named frozen-Gaussian leading-mode almost-everywhere endpoint, with both
remaining finite-volume static masses displayed literally. -/
theorem problem_gaussian_ae_abs_leading_resonanceResolvedResidual_le_linearCrossVolumeBound
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
        qLevelOffResonantCorrectionStaticMass
            m kappa energy (orderedIndexEquiv q) / time +
          allDistinctCounterrotatingStaticFluxMass
            m kappa energy (orderedIndexEquiv q) *
            ((2 / orderedModeFrequency (harmonicHermitian m) q) ^ 2 / time) +
          2 * (N : Real) * kappa ^ 2 * energyBound ^ 2 /
            (Real.sqrt (5 / 3 : Real) * time) :=
  gaussian_ae_abs_leading_resonanceResolvedResidual_le_linearCrossVolumeBound
    ensemble hN kappa beta energy energyBound hEnergyBoundNonneg
      hEnergy hEnergyBound htime

#print axioms
  problem_abs_ordered_resonanceResolvedResidual_le_linearCrossVolumeBound
#print axioms
  problem_gaussian_ae_abs_leading_resonanceResolvedResidual_le_linearCrossVolumeBound

end

end ArchonPhysicsConsumers.Thermalization
