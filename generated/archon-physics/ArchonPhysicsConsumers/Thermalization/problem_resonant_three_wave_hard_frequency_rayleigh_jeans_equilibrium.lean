import ArchonPhysics.ResonantThreeWaveHardFrequencyRayleighJeansEquilibrium

/-!
# Consumer: hard-frequency Rayleigh--Jeans equilibrium

This consumer instantiates the canonical `L-infinity` equilibrium only after
restricting the collision law to a positive hard-frequency band.
-/

namespace ArchonPhysicsConsumers.Thermalization

open MeasureTheory
open ArchonPhysics
open ArchonPhysics.ResonantThreeWaveHardFrequencyRestriction
open ArchonPhysics.ResonantThreeWaveHardFrequencyRayleighJeansEquilibrium
open ArchonPhysics.ResonantThreeWaveKineticEntropy
open ArchonPhysics.ResonantThreeWaveKineticEquilibrium
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

example (collision : ResonantThreeWaveMeasure Mode)
    {cutoff temperature : Real} (hcutoff : 0 < cutoff)
    (htemperature : 0 < temperature) :
    collisionMap (hardFrequencyRestriction collision cutoff)
        (hardBandRayleighJeansClass collision cutoff temperature hcutoff) = 0 ∧
      continuumLogEntropyProduction
        (hardFrequencyRestriction collision cutoff)
        (rayleighJeansAction temperature
          (hardFrequencyRestriction collision cutoff).frequency) = 0 :=
  hardBandRayleighJeansClass_equilibrium_certificate
    collision hcutoff htemperature

example (collision : ResonantThreeWaveMeasure Mode) (g : Real)
    {cutoff temperature : Real} (hcutoff : 0 < cutoff)
    (htemperature : 0 < temperature) :
    let equilibrium :=
      hardBandRayleighJeansClass collision cutoff temperature hcutoff
    (∀ t : Real, (fun _ : Real ↦ equilibrium) t = equilibrium) ∧
      ∀ t : Real, HasDerivAt (fun _ : Real ↦ equilibrium)
        (rnCollisionVectorField
          (hardFrequencyRestriction collision cutoff) g equilibrium) t :=
  hardBandRayleighJeansClass_global_stationary
    collision g hcutoff htemperature

set_option linter.hashCommand false in
#check hardBandRayleighJeansClass

set_option linter.hashCommand false in
#check collisionMap_hardBandRayleighJeansClass_eq_zero

set_option linter.hashCommand false in
#check hardBandRayleighJeansClass_global_stationary

set_option linter.hashCommand false in
#check hardBandRayleighJeansClass_entropyProduction_eq_zero

set_option linter.hashCommand false in
#print axioms hardBandRayleighJeansClass_equilibrium_certificate

set_option linter.hashCommand false in
#print axioms hardBandRayleighJeansClass_global_stationary

end

end ArchonPhysicsConsumers.Thermalization
