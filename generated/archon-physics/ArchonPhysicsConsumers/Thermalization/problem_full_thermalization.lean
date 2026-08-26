import ArchonPhysics.FullThermalization

/-!
# Consumer: full conditional nonzero-mode thermalization

This target locks both the inverse-square window and energy-density endpoints.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics

/-- Kernel-lock the exact full conditional certificate endpoint. -/
theorem problem_full_thermalization :
    (@fullNonzeroModeThermalizationLaw) =
      @fullNonzeroModeThermalizationLaw := rfl

/-- Kernel-lock the energy-density form of the same endpoint. -/
theorem problem_full_thermalization_energy_density :
    (@fullNonzeroModeEnergyDensityThermalizationLaw) =
      @fullNonzeroModeEnergyDensityThermalizationLaw := rfl

end ArchonPhysicsConsumers.Thermalization

open ArchonPhysics

#print axioms fullNonzeroModeThermalizationLaw
#print axioms fullNonzeroModeEnergyDensityThermalizationLaw
