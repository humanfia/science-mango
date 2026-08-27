import ArchonPhysics.FreeFPUTCrossOrbitCoefficientVolumeBound

/-!
# Consumer gate: explicit volume control of cross-orbit coherence
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTCrossOrbitCoefficientVolumeBound
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTCrossOrbitZeroChargeBridge
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch

noncomputable section

/-- The exceptional zero-charge support grows at most linearly in volume. -/
theorem problem_card_zeroChargeQuadraticPhaseTerms_le
    (N : Nat) [NeZero N] :
    (zeroChargeQuadraticPhaseTerms N).card ≤ 2 * N :=
  card_zeroChargeQuadraticPhaseTerms_le N

theorem problem_card_zeroChargeQuadraticPhaseTerms
    (N : Nat) [NeZero N] :
    (zeroChargeQuadraticPhaseTerms N).card = 2 * N :=
  card_zeroChargeQuadraticPhaseTerms N

/-- Existing coefficient and energy estimates give an explicit `N^2`
finite-volume bound for the unnormalized physical cross term. -/
theorem problem_abs_re_physical_crossOrbit_le_energy_volume
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (energy : Lattice.Site N → Real)
    (energyBound : Real) (henergyBoundNonneg : 0 ≤ energyBound)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (henergyBound : ∀ mode, energy mode ≤ energyBound)
    {time : Real} (hfrequency : 0 < modeFrequency m observed)
    (htime : 0 < time) :
    |(freeQuadraticCrossSwapOrbitCoherentRemainder
        (physicalQuadraticCoupling kappa g m observed) m observed
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
        time).re| ≤
      2 * (N : Real) ^ 2 * (kappa * g) ^ 2 * energyBound ^ 2 /
        (modeFrequency m observed * time) :=
  abs_re_physical_crossOrbit_le_energy_volume
    kappa g m observed energy energyBound henergyBoundNonneg
    henergy henergyBound hfrequency htime

/-- The `N^2`-normalized cross term has a genuinely volume-independent
inverse-time constant when the observed frequency has a uniform floor. -/
theorem problem_normalized_abs_re_physical_crossOrbit_le_energy
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (energy : Lattice.Site N → Real)
    (energyBound frequencyFloor : Real)
    (henergyBoundNonneg : 0 ≤ energyBound)
    (hfrequencyFloor : 0 < frequencyFloor)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (henergyBound : ∀ mode, energy mode ≤ energyBound)
    {time : Real} (hfrequency : frequencyFloor ≤ modeFrequency m observed)
    (htime : 0 < time) :
    |(freeQuadraticCrossSwapOrbitCoherentRemainder
        (physicalQuadraticCoupling kappa g m observed) m observed
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
        time).re| / (N : Real) ^ 2 ≤
      2 * (kappa * g) ^ 2 * energyBound ^ 2 /
        (frequencyFloor * time) :=
  normalized_abs_re_physical_crossOrbit_le_energy
    kappa g m observed energy energyBound frequencyFloor
    henergyBoundNonneg hfrequencyFloor henergy henergyBound hfrequency htime

/-- A transparent unnormalized volume-uniform endpoint: inverse-volume
control of every zero-charge coefficient and a uniform observed-frequency
floor suffice for an `N`-independent inverse-time bound. -/
theorem problem_abs_re_crossOrbit_le_of_inverseVolumeCoefficient
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) {time : Real}
    (uniformCoefficient frequencyFloor : Real)
    (huniformCoefficient : 0 ≤ uniformCoefficient)
    (hfrequencyFloor : 0 < frequencyFloor)
    (hcoefficient : ∀ term : QuadraticPhaseTerm N,
      quadraticPhaseCharge term = 0 →
      ‖freeQuadraticDuhamelCoefficient
        coupling m observed radius term‖ ≤ uniformCoefficient / N)
    (hfrequency : frequencyFloor ≤ frequency observed)
    (htime : 0 < time) :
    |(freeQuadraticCrossSwapOrbitCoherentRemainder
        coupling m observed radius frequency time).re| ≤
      16 * uniformCoefficient ^ 2 / (frequencyFloor ^ 2 * time) :=
  abs_re_crossOrbit_le_of_inverseVolumeCoefficient
    coupling m observed radius frequency uniformCoefficient frequencyFloor
    huniformCoefficient hfrequencyFloor hcoefficient hfrequency htime

#print axioms problem_card_zeroChargeQuadraticPhaseTerms_le
#print axioms problem_card_zeroChargeQuadraticPhaseTerms
#print axioms problem_abs_re_physical_crossOrbit_le_energy_volume
#print axioms problem_normalized_abs_re_physical_crossOrbit_le_energy
#print axioms problem_abs_re_crossOrbit_le_of_inverseVolumeCoefficient

end

end ArchonPhysicsConsumers.Thermalization
