import ArchonPhysics.HardBandRayleighJeansF3Core

/-!
# Consumer: non-vacuous hard-band Rayleigh--Jeans F3 core

This consumer exposes the positive-cutoff `L-infinity`, concrete-distance,
and normalized-energy `L1` interfaces.  It deliberately does not assert
relaxation of a nonstationary exact collision trajectory.
-/

namespace ArchonPhysicsConsumers.Thermalization
open MeasureTheory

open ArchonPhysics
open ArchonPhysics.CanonicalOnShellRayleighJeansDistanceF2
open ArchonPhysics.HardBandRayleighJeansF3Core
open ArchonPhysics.HardSoftRayleighJeansL1Gluing
open ArchonPhysics.ResonantThreeWaveHardFrequencyRestriction
open ArchonPhysics.ResonantThreeWaveHardFrequencyRayleighJeansEquilibrium
open ArchonPhysics.ResonantThreeWaveKineticEquilibrium
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open scoped ENNReal MeasureTheory

noncomputable section

variable {Mode : Type} [MeasurableSpace Mode]

example [Fintype Mode]
    (collision : ResonantThreeWaveMeasure Mode)
    {cutoff temperature : Real} (hcutoff : 0 < cutoff)
    (htemperature : 0 < temperature)
    (hard : Finset Mode) (hhard : hard.Nonempty) :
    MemLp
        (rayleighJeansAction temperature
          (hardFrequencyRestriction collision cutoff).frequency)
        ∞ (collisionReferenceMeasure
          (hardFrequencyRestriction collision cutoff)) ∧
      (∀ mode, ‖rayleighJeansAction temperature
          (hardFrequencyRestriction collision cutoff).frequency mode‖ ≤
        ‖temperature‖ / cutoff) ∧
      hardBandRayleighJeansClass collision cutoff temperature hcutoff ∈
        rayleighJeansEquilibriumSet
          (hardFrequencyRestriction collision cutoff) ∧
      rayleighJeansDistance (hardFrequencyRestriction collision cutoff)
          (hardBandRayleighJeansClass
            collision cutoff temperature hcutoff) = 0 ∧
      normalizedSectorL1Deficit hard
        (fun mode ↦
          (hardFrequencyRestriction collision cutoff).frequency mode *
            rayleighJeansAction temperature
              (hardFrequencyRestriction collision cutoff).frequency mode) = 0 :=
  hardBandRayleighJeans_f3_core_certificate
    collision hcutoff htemperature hard hhard

set_option linter.hashCommand false in
#check @norm_hardBandRayleighJeansAction_le

set_option linter.hashCommand false in
#check @hardBandRayleighJeansAction_memLp_top

set_option linter.hashCommand false in
#check @hardBandRayleighJeansClass_mem_equilibriumSet

set_option linter.hashCommand false in
#check @hardBand_rayleighJeansEquilibriumSet_nonempty

set_option linter.hashCommand false in
#check @hardBandRayleighJeansDistance_eq_zero

set_option linter.hashCommand false in
#check @hardBandRayleighJeans_f3_core_certificate

set_option linter.hashCommand false in
#check @tendsto_l1Distance_uniform_of_hardRJ_cutoff

set_option linter.hashCommand false in
#print axioms norm_hardBandRayleighJeansAction_le

set_option linter.hashCommand false in
#print axioms hardBandRayleighJeansAction_memLp_top

set_option linter.hashCommand false in
#print axioms hardBandRayleighJeansClass_mem_equilibriumSet

set_option linter.hashCommand false in
#print axioms hardBand_rayleighJeansEquilibriumSet_nonempty

set_option linter.hashCommand false in
#print axioms hardBandRayleighJeansDistance_eq_zero

set_option linter.hashCommand false in
#print axioms hardBandRayleighJeans_f3_core_certificate

set_option linter.hashCommand false in
#print axioms tendsto_l1Distance_uniform_of_hardRJ_cutoff

end

end ArchonPhysicsConsumers.Thermalization
