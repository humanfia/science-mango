import ArchonPhysics.HardSoftRayleighJeansL1Gluing

/-!
# Consumer: hard/soft Rayleigh--Jeans L1 gluing

This consumer records that convergence to the independently normalized hard
Rayleigh--Jeans modal-energy target, plus vanishing soft mass and mode
fraction, implies full normalized-energy `L1` equipartition.
-/

namespace ArchonPhysicsConsumers.Thermalization

open Filter
open ArchonPhysics
open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.HardSoftRayleighJeansL1Gluing
open ArchonPhysics.ResonantThreeWaveHardFrequencyRestriction
open ArchonPhysics.ResonantThreeWaveKineticEquilibrium
open ArchonPhysics.SoftSectorL1Control

noncomputable section

example
    (M : Nat → Nat)
    (frequency : ∀ n, Fin (M n) → Real)
    (cutoff : Nat → Real)
    (p : ∀ n, Fin (M n) → Real)
    (hM : ∀ n, 0 < M n)
    (hp : ∀ n i, 0 ≤ p n i)
    (htotal : ∀ n, totalWeight (p n) = 1)
    (hhard : ∀ n,
      (Finset.univ \ softFrequencySector (frequency n) (cutoff n)).Nonempty)
    (hhardMass : ∀ n,
      0 < sectorWeight
        (Finset.univ \ softFrequencySector (frequency n) (cutoff n)) (p n))
    (hsoft : Tendsto
      (fun n ↦ sectorWeight
        (softFrequencySector (frequency n) (cutoff n)) (p n))
      atTop (nhds 0))
    (hfraction : Tendsto
      (fun n ↦ (softFrequencySector (frequency n) (cutoff n)).card /
        (M n : Real)) atTop (nhds 0))
    (hhardRJ : Tendsto
      (fun n ↦ normalizedSectorL1Deficit
        (Finset.univ \ softFrequencySector (frequency n) (cutoff n)) (p n))
      atTop (nhds 0)) :
    Tendsto
      (fun n ↦ l1Distance (p n)
        (uniformWeights : Fin (M n) → Real)) atTop (nhds 0) :=
  tendsto_l1Distance_uniform_of_hardRJ_cutoff
    M frequency cutoff p hM hp htotal hhard hhardMass
      hsoft hfraction hhardRJ

example {Mode : Type} [MeasurableSpace Mode] [Fintype Mode]
    (collision : ResonantThreeWaveMeasure Mode)
    {cutoff temperature : Real} (hcutoff : 0 < cutoff)
    (htemperature : 0 < temperature)
    (hard : Finset Mode) (hhard : hard.Nonempty) :
    normalizedSectorL1Deficit hard
      (fun mode ↦
        (hardFrequencyRestriction collision cutoff).frequency mode *
          rayleighJeansAction temperature
            (hardFrequencyRestriction collision cutoff).frequency mode) = 0 :=
  hardBandRayleighJeans_normalizedSectorL1Deficit_eq_zero
    collision hcutoff htemperature hard hhard

set_option linter.hashCommand false in
#check l1Distance_uniform_le_hardNormalized_add_two_soft

set_option linter.hashCommand false in
#check tendsto_l1Distance_uniform_of_hardRJ_cutoff

set_option linter.hashCommand false in
#check hardBandRayleighJeans_normalizedSectorL1Deficit_eq_zero

set_option linter.hashCommand false in
#print axioms tendsto_l1Distance_uniform_of_hardRJ_cutoff

set_option linter.hashCommand false in
#print axioms hardBandRayleighJeans_normalizedSectorL1Deficit_eq_zero

end

end ArchonPhysicsConsumers.Thermalization
