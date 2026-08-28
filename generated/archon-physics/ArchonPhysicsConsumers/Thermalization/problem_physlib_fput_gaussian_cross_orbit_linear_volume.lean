import ArchonPhysics.PhyslibFPUTGaussianCrossOrbitLinearVolumeConsumer

/-!
# Consumer: linear-volume FPUT cross-orbit decay

This conventional Thermalization consumer exposes the deterministic
`O(N/T)` cross-orbit estimate and its two frozen-Gaussian consequences: an
almost-everywhere `O(1/N)` estimate after `N^2` normalization and almost-sure
convergence of that normalized remainder to zero.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTCrossOrbitLinearVolumeBound
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.GaussianIIDMassPhaseEnsemble
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhyslibFPUTGaussianCrossOrbitLinearVolumeConsumer
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.TruncatedGaussianMassLaw
open Filter MeasureTheory Topology

noncomputable section

/-- Consumer endpoint for the deterministic one-power volume improvement. -/
theorem problem_abs_re_physical_crossOrbit_le_energy_linearVolume
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (q : OrderedModeIndex N) (energy : Lattice.Site N → Real)
    (energyBound : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (henergyBoundNonneg : 0 ≤ energyBound)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (henergyBound : ∀ mode, energy mode ≤ energyBound)
    {time : Real}
    (hfrequency : 0 < orderedModeFrequency (harmonicHermitian m) q)
    (htime : 0 < time) :
    |(freeQuadraticCrossSwapOrbitCoherentRemainder
        (physicalQuadraticCoupling kappa g m (orderedIndexEquiv q))
        m (orderedIndexEquiv q)
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
        time).re| ≤
      2 * (N : Real) * (kappa * g) ^ 2 * energyBound ^ 2 /
        (orderedModeFrequency (harmonicHermitian m) q * time) :=
  abs_re_physical_crossOrbit_le_energy_linearVolume
    kappa g m q energy energyBound hsimple henergyBoundNonneg
      henergy henergyBound hfrequency htime

/-- Consumer endpoint for the frozen-Gaussian almost-everywhere `O(1/N)`
bound on the `N^2`-normalized leading-mode cross remainder. -/
theorem problem_gaussian_ae_normalized_leading_crossOrbit_le_inverseVolume
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (kappa g : Real) (energy : Lattice.Site N → Real)
    (energyBound : Real)
    (henergyBoundNonneg : 0 ≤ energyBound)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (henergyBound : ∀ mode, energy mode ≤ energyBound)
    {time : Real} (htime : 0 < time) :
    ∀ᵐ sample ∂ensemble.probability,
      let m := ensemble.restrictPositiveMass (N := N) sample
      let q := leadingOrderedModeIndex N
      |(freeQuadraticCrossSwapOrbitCoherentRemainder
          (physicalQuadraticCoupling kappa g m (orderedIndexEquiv q))
          m (orderedIndexEquiv q)
          (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
          time).re| / (N : Real) ^ 2 ≤
        2 * (kappa * g) ^ 2 * energyBound ^ 2 /
          ((N : Real) * Real.sqrt (5 / 3 : Real) * time) :=
  gaussian_ae_normalized_leading_crossOrbit_le_inverseVolume
    ensemble hN kappa g energy energyBound henergyBoundNonneg
      henergy henergyBound htime

/-- Consumer endpoint for almost-sure thermodynamic disappearance of the
same normalized cross remainder. -/
theorem problem_gaussianLeadingNormalizedCrossOrbit_tendsto_zero_ae
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    (kappa g : Real)
    (energy : ∀ n : Nat, Lattice.Site (n + 2) → Real)
    (energyBound : Real)
    (henergyBoundNonneg : 0 ≤ energyBound)
    (henergy : ∀ n mode, 0 ≤ energy n mode)
    (henergyBound : ∀ n mode, energy n mode ≤ energyBound)
    {time : Real} (htime : 0 < time) :
    ∀ᵐ sample ∂ensemble.probability,
      Tendsto
        (gaussianLeadingNormalizedCrossOrbit
          ensemble kappa g energy time sample)
        atTop (nhds 0) :=
  gaussianLeadingNormalizedCrossOrbit_tendsto_zero_ae
    ensemble kappa g energy energyBound henergyBoundNonneg
      henergy henergyBound htime

#print axioms problem_abs_re_physical_crossOrbit_le_energy_linearVolume
#print axioms
  problem_gaussian_ae_normalized_leading_crossOrbit_le_inverseVolume
#print axioms problem_gaussianLeadingNormalizedCrossOrbit_tendsto_zero_ae

end

end ArchonPhysicsConsumers.Thermalization
