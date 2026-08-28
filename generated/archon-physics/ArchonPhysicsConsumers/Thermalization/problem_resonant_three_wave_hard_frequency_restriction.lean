import ArchonPhysics.ResonantThreeWaveHardFrequencyRestriction

namespace ArchonPhysicsConsumers.Thermalization

open Filter MeasureTheory
open ArchonPhysics
open ArchonPhysics.ResonantThreeWaveHardFrequencyRestriction
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym

example {Mode : Type*} [MeasurableSpace Mode]
    (collision : ResonantThreeWaveMeasure Mode) (cutoff : Real) :
    (hardFrequencyRestriction collision cutoff).frequency =ᵐ[
        collisionReferenceMeasure (hardFrequencyRestriction collision cutoff)]
      collision.frequency := by
  exact hardFrequencyRestriction_frequency_eq_original_ae_reference
    collision cutoff

#print axioms hardFrequencyRestriction_frequency_eq_original_ae_reference

end ArchonPhysicsConsumers.Thermalization
