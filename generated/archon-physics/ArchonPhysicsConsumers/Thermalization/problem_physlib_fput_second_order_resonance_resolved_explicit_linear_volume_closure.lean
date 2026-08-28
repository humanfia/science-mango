import ArchonPhysics.PhyslibFPUTSecondOrderResonanceResolvedExplicitLinearVolumeClosure

/-!
# Consumer: fully explicit linear-volume resonance closure

This consumer exposes the fixed-output counterrotating `O(N)` estimate and
the resulting deterministic and frozen-Gaussian resonance-resolved residual
bounds.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctCounterrotatingSignedFluxDecay
open ArchonPhysics.FreeFPUTAllDistinctCounterrotatingStaticFluxVolumeBound
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTQLevelCorrectionResonanceIntegration
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.GaussianIIDMassPhaseEnsemble
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhyslibFPUTGaussianCrossOrbitLinearVolumeConsumer
open ArchonPhysics.PhyslibFPUTSecondOrderQLevelUnifiedClosure
open ArchonPhysics.PhyslibFPUTSecondOrderResonanceResolvedExplicitLinearVolumeClosure
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound
open ArchonPhysics.PhyslibFPUTSecondOrderUnifiedDegenerateClosure
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.TruncatedGaussianMassLaw
open Filter MeasureTheory

noncomputable section

/-- Named consumer endpoint for the fixed-output physical all-distinct
counterrotating static mass. -/
theorem problem_allDistinctCounterrotatingStaticFluxMass_le_linear_volume
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (kappa : Real) (energy : Lattice.Site N → Real)
    (observed : Lattice.Site N) (energyCeiling frequencyCeiling : Real)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (henergyCeiling : ∀ mode, energy mode ≤ energyCeiling)
    (hfrequencyCeiling : 0 ≤ frequencyCeiling)
    (hfrequency : ∀ k,
      orderedModeFrequency (harmonicHermitian m) k ≤ frequencyCeiling) :
    allDistinctCounterrotatingStaticFluxMass m kappa energy observed ≤
      ((3 / 2 : Real) * kappa ^ 2 * frequencyCeiling *
        energyCeiling ^ 2) * (N : Real) :=
  allDistinctCounterrotatingStaticFluxMass_le_linear_volume
    m hsimple kappa energy observed energyCeiling frequencyCeiling
      henergy henergyCeiling hfrequencyCeiling hfrequency

/-- Named deterministic endpoint in which every non-main second-order
residual contribution is explicit and linear in the volume. -/
theorem problem_abs_ordered_resonanceResolvedResidual_le_explicitLinearVolumeBound
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
        (((3 / 2 : Real) * kappa ^ 2 * ceiling * energyBound ^ 2) *
          (N : Real)) *
          ((2 / orderedModeFrequency (harmonicHermitian m) q) ^ 2 / time) +
        2 * (N : Real) * kappa ^ 2 * energyBound ^ 2 /
          (orderedModeFrequency (harmonicHermitian m) q * time) :=
  abs_ordered_resonanceResolvedResidual_le_explicitLinearVolumeBound
    m kappa beta q energy energyBound ceiling hsimple hEnergyBoundNonneg
      hEnergy hEnergyBound hCeiling hFrequencyCeiling hmassLower hmassUpper
      htime hFrequency

/-- Named frozen-Gaussian leading-output endpoint. -/
theorem problem_gaussian_ae_abs_leading_resonanceResolvedResidual_le_explicitLinearVolumeBound
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
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
          (((3 / 2 : Real) * kappa ^ 2 * Real.sqrt 5 *
            energyBound ^ 2) * (N : Real)) *
            ((2 / Real.sqrt (5 / 3 : Real)) ^ 2 / time) +
          2 * (N : Real) * kappa ^ 2 * energyBound ^ 2 /
            (Real.sqrt (5 / 3 : Real) * time) :=
  gaussian_ae_abs_leading_resonanceResolvedResidual_le_explicitLinearVolumeBound
    ensemble hN kappa beta energy energyBound hEnergyBoundNonneg
      hEnergy hEnergyBound htime

#print axioms problem_allDistinctCounterrotatingStaticFluxMass_le_linear_volume
#print axioms
  problem_abs_ordered_resonanceResolvedResidual_le_explicitLinearVolumeBound
#print axioms
  problem_gaussian_ae_abs_leading_resonanceResolvedResidual_le_explicitLinearVolumeBound

end

end ArchonPhysicsConsumers.Thermalization
