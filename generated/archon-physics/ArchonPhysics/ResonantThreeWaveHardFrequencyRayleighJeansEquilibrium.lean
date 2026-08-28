import ArchonPhysics.ResonantThreeWaveHardFrequencyRestriction
import ArchonPhysics.ResonantThreeWaveKineticLInfinityEquilibrium

/-!
# Rayleigh--Jeans equilibrium on a hard-frequency subsystem

A positive hard cutoff supplies exactly the global frequency floor needed to
place the Rayleigh--Jeans action in canonical `L-infinity`.  This module is a
thin specialization of the existing quotient equilibrium theory to the
genuine restricted collision measure.

No statement is made that the acoustic full-spectrum profile `T / omega`
belongs to `L-infinity`: every result below is explicitly about
`hardFrequencyRestriction collision cutoff`.
-/

namespace ArchonPhysics.ResonantThreeWaveHardFrequencyRayleighJeansEquilibrium

open MeasureTheory
open ArchonPhysics.ResonantThreeWaveHardFrequencyRestriction
open ArchonPhysics.ResonantThreeWaveKineticEntropy
open ArchonPhysics.ResonantThreeWaveKineticEquilibrium
open ArchonPhysics.ResonantThreeWaveKineticLInfinityEquilibrium
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- The Rayleigh--Jeans state of the collision law restricted to frequencies
above a strictly positive cutoff. -/
def hardBandRayleighJeansClass
    (collision : ResonantThreeWaveMeasure Mode)
    (cutoff temperature : Real) (hcutoff : 0 < cutoff) :
    CanonicalLInfinity (hardFrequencyRestriction collision cutoff) :=
  rayleighJeansClass (hardFrequencyRestriction collision cutoff)
    temperature cutoff hcutoff
    (cutoff_le_hardFrequencyRestriction_frequency collision cutoff)

/-- The canonical collision map of the hard subsystem vanishes at its
Rayleigh--Jeans class. -/
theorem collisionMap_hardBandRayleighJeansClass_eq_zero
    (collision : ResonantThreeWaveMeasure Mode)
    {cutoff temperature : Real} (hcutoff : 0 < cutoff)
    (htemperature : 0 < temperature) :
    collisionMap (hardFrequencyRestriction collision cutoff)
      (hardBandRayleighJeansClass collision cutoff temperature hcutoff) = 0 := by
  exact collisionMap_rayleighJeansClass_eq_zero
    (hardFrequencyRestriction collision cutoff) temperature htemperature
    cutoff hcutoff
    (cutoff_le_hardFrequencyRestriction_frequency collision cutoff)

/-- The constant hard-band Rayleigh--Jeans curve is a global stationary
solution for every coupling. -/
theorem hardBandRayleighJeansClass_global_stationary
    (collision : ResonantThreeWaveMeasure Mode) (g : Real)
    {cutoff temperature : Real} (hcutoff : 0 < cutoff)
    (htemperature : 0 < temperature) :
    let equilibrium :=
      hardBandRayleighJeansClass collision cutoff temperature hcutoff
    (∀ t : Real, (fun _ : Real ↦ equilibrium) t = equilibrium) ∧
      ∀ t : Real, HasDerivAt (fun _ : Real ↦ equilibrium)
        (rnCollisionVectorField
          (hardFrequencyRestriction collision cutoff) g equilibrium) t := by
  exact rayleighJeansClass_global_stationary
    (hardFrequencyRestriction collision cutoff) g temperature htemperature
    cutoff hcutoff
    (cutoff_le_hardFrequencyRestriction_frequency collision cutoff)

/-- The explicit Rayleigh--Jeans representative has zero logarithmic entropy
production against the hard collision measure. -/
theorem hardBandRayleighJeansClass_entropyProduction_eq_zero
    (collision : ResonantThreeWaveMeasure Mode)
    {cutoff temperature : Real} (hcutoff : 0 < cutoff)
    (htemperature : 0 < temperature) :
    continuumLogEntropyProduction
      (hardFrequencyRestriction collision cutoff)
      (rayleighJeansAction temperature
        (hardFrequencyRestriction collision cutoff).frequency) = 0 := by
  exact rayleighJeansClass_entropyProduction_eq_zero
    (hardFrequencyRestriction collision cutoff) temperature htemperature
    cutoff hcutoff
    (cutoff_le_hardFrequencyRestriction_frequency collision cutoff)

/-- A single consumer-facing certificate collecting collision stationarity
and zero entropy production on the hard subsystem. -/
theorem hardBandRayleighJeansClass_equilibrium_certificate
    (collision : ResonantThreeWaveMeasure Mode)
    {cutoff temperature : Real} (hcutoff : 0 < cutoff)
    (htemperature : 0 < temperature) :
    collisionMap (hardFrequencyRestriction collision cutoff)
        (hardBandRayleighJeansClass collision cutoff temperature hcutoff) = 0 ∧
      continuumLogEntropyProduction
        (hardFrequencyRestriction collision cutoff)
        (rayleighJeansAction temperature
          (hardFrequencyRestriction collision cutoff).frequency) = 0 := by
  exact ⟨collisionMap_hardBandRayleighJeansClass_eq_zero
      collision hcutoff htemperature,
    hardBandRayleighJeansClass_entropyProduction_eq_zero
      collision hcutoff htemperature⟩

end

end ArchonPhysics.ResonantThreeWaveHardFrequencyRayleighJeansEquilibrium
