import ArchonPhysics.AlphaFPUTEffectiveKineticScaling

/-!
# Consumer: alpha-FPUT effective kinetic exponents

These identities expose the four-wave and finite-volume six-wave scaling
targets without asserting the still-separate microscopic kinetic limit.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.AlphaFPUTEffectiveKineticScaling

theorem problem_alpha_fput_four_wave_energy_density_scale
    {energyDensity : Real} (henergy : 0 ≤ energyDensity) (alpha : Real) :
    effectiveFourWaveKineticTime
        (alphaFPUTWeakParameter alpha energyDensity) =
      1 / (alpha ^ 4 * energyDensity ^ 2) :=
  effectiveFourWaveKineticTime_weakParameter henergy alpha

theorem problem_alpha_fput_six_wave_energy_density_scale
    {energyDensity : Real} (henergy : 0 ≤ energyDensity) (alpha : Real) :
    effectiveSixWaveKineticTime
        (alphaFPUTWeakParameter alpha energyDensity) =
      1 / (alpha ^ 8 * energyDensity ^ 4) :=
  effectiveSixWaveKineticTime_weakParameter henergy alpha

#print axioms problem_alpha_fput_four_wave_energy_density_scale
#print axioms problem_alpha_fput_six_wave_energy_density_scale

end ArchonPhysicsConsumers.Thermalization
