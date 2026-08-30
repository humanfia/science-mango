import ArchonPhysics.FreeFPUTMesoscopicCrossOrbitKineticScale

/-!
# Consumer: mesoscopic FPUT cross-orbit kinetic scale

This consumer exposes the exact common scale
`g^2 T(N,g) = N / T(N,g) = |g| sqrt N`, the finite hard-mode bound, and
the resulting varying-volume `o(g^2)` cross-orbit theorem.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTCrossOrbitLinearVolumeBound
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTMesoscopicCrossOrbitKineticScale
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassPositiveCollisionData
open Filter Topology

noncomputable section

theorem problem_mesoscopicFPUTBlockTime_commonScale
    {N : Nat} [NeZero N] {g : Real} (hg : g ≠ 0) :
    g ^ 2 * mesoscopicFPUTBlockTime N g =
        |g| * Real.sqrt (N : Real) ∧
      (N : Real) / mesoscopicFPUTBlockTime N g =
        |g| * Real.sqrt (N : Real) :=
  ⟨couplingSq_mul_mesoscopicFPUTBlockTime hg,
    volume_div_mesoscopicFPUTBlockTime hg⟩

theorem problem_normalized_crossOrbit_le_mesoscopicJointScale
    {N : Nat} [NeZero N]
    (kappa g : Real) (hkappa : kappa ≠ 0) (hg : g ≠ 0)
    (m : Lattice.PositiveMassConfig N)
    (q : OrderedModeIndex N) (energy : Lattice.Site N → Real)
    (energyBound : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (henergyBoundNonneg : 0 ≤ energyBound)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (henergyBound : ∀ mode, energy mode ≤ energyBound)
    (hfrequency : 0 < orderedModeFrequency (harmonicHermitian m) q) :
    |(freeQuadraticCrossSwapOrbitCoherentRemainder
        (physicalQuadraticCoupling kappa g m (orderedIndexEquiv q))
        m (orderedIndexEquiv q)
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
        (mesoscopicFPUTBlockTime N g)).re| / (kappa * g) ^ 2 ≤
      (2 * energyBound ^ 2 /
          orderedModeFrequency (harmonicHermitian m) q) *
        (|g| * Real.sqrt (N : Real)) :=
  normalized_crossOrbit_le_mesoscopicJointScale
    kappa g hkappa hg m q energy energyBound hsimple
      henergyBoundNonneg henergy henergyBound hfrequency

theorem problem_normalized_crossOrbit_tendsto_zero_at_mesoscopicScale
    (N : Nat → Nat) [hN : ∀ n, NeZero (N n)]
    (kappa : Real) (hkappa : kappa ≠ 0)
    (g : Nat → Real) (hg : ∀ n, g n ≠ 0)
    (m : ∀ n, Lattice.PositiveMassConfig (N n))
    (q : ∀ n, OrderedModeIndex (N n))
    (energy : ∀ n, Lattice.Site (N n) → Real)
    (energyBound frequencyLower : Real)
    (henergyBoundNonneg : 0 ≤ energyBound)
    (hfrequencyLower : 0 < frequencyLower)
    (hsimple : ∀ n, SimpleOrderedSpectrum (harmonicHermitian (m n)))
    (henergy : ∀ n mode, 0 ≤ energy n mode)
    (henergyBound : ∀ n mode, energy n mode ≤ energyBound)
    (hfrequency : ∀ n, frequencyLower ≤
      orderedModeFrequency (harmonicHermitian (m n)) (q n))
    (hjoint : Tendsto
      (fun n ↦ |g n| * Real.sqrt (N n : Real)) atTop (nhds 0)) :
    Tendsto
      (fun n ↦
        |(freeQuadraticCrossSwapOrbitCoherentRemainder
            (physicalQuadraticCoupling kappa (g n) (m n)
              (orderedIndexEquiv (q n)))
            (m n) (orderedIndexEquiv (q n))
            (phaseEnergyRadius (energy n) (modeFrequency (m n)))
            (modeFrequency (m n))
            (mesoscopicFPUTBlockTime (N n) (g n))).re| /
          (kappa * g n) ^ 2)
      atTop (nhds 0) :=
  normalized_crossOrbit_tendsto_zero_at_mesoscopicScale
    N kappa hkappa g hg m q energy energyBound frequencyLower
      henergyBoundNonneg hfrequencyLower hsimple henergy henergyBound
      hfrequency hjoint

/-- Consumer endpoint for the unconditional all-hard-mode average estimate.
The acoustic cutoff stays explicit, so no uniform spectral gap is assumed. -/
theorem problem_positiveOrderedHardMeanNormalizedCrossOrbitRemainder_le
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (kappa g : Real) (hkappa : kappa ≠ 0) (hg : g ≠ 0)
    (m : Lattice.PositiveMassConfig N)
    (energy : Lattice.Site N → Real) (energyBound cutoff : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (henergyBoundNonneg : 0 ≤ energyBound)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (henergyBound : ∀ mode, energy mode ≤ energyBound)
    (hcutoff : 0 < cutoff) :
    positiveOrderedHardMeanNormalizedCrossOrbitRemainder
        kappa g m energy cutoff ≤
      (2 * energyBound ^ 2 / cutoff) *
        (|g| * Real.sqrt (N : Real)) :=
  positiveOrderedHardMeanNormalizedCrossOrbitRemainder_le
    hN kappa g hkappa hg m energy energyBound cutoff hsimple
      henergyBoundNonneg henergy henergyBound hcutoff

#print axioms
  problem_positiveOrderedHardMeanNormalizedCrossOrbitRemainder_le
#print axioms problem_mesoscopicFPUTBlockTime_commonScale
#print axioms problem_normalized_crossOrbit_le_mesoscopicJointScale
#print axioms
  problem_normalized_crossOrbit_tendsto_zero_at_mesoscopicScale

end

end ArchonPhysicsConsumers.Thermalization
