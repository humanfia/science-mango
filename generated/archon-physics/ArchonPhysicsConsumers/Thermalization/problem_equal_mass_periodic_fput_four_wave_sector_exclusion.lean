import ArchonPhysics.EqualMassPeriodicFPUTFourWaveSectorExclusion

/-!
# Consumer: nonzero one-to-three FPUT sector exclusion
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave
open ArchonPhysics.EqualMassPeriodicFPUTFourWaveSectorExclusion
open ArchonPhysics.Lattice

theorem problem_equal_mass_three_to_one_has_zero_input
    {N : Nat} [NeZero N] {output a b c : Site N}
    (hmomentum : output = a + b + c)
    (hfrequency : periodicSineFrequency N output =
      periodicSineFrequency N a + periodicSineFrequency N b +
        periodicSineFrequency N c) :
    a = 0 ∨ b = 0 ∨ c = 0 :=
  threeToOne_resonance_has_zero_input hmomentum hfrequency

theorem problem_equal_mass_one_plus_three_minus_has_zero_mode
    {N : Nat} [NeZero N] (modes : Fin 4 → Site N)
    (hmomentum : FourierMomentumBalanced onePlusThreeMinusSign modes)
    (hfrequency : periodicSinePhaseMismatch onePlusThreeMinusSign modes = 0) :
    ∃ r, modes r = 0 :=
  onePlusThreeMinus_resonance_has_zero_mode modes hmomentum hfrequency

#print axioms problem_equal_mass_three_to_one_has_zero_input
#print axioms problem_equal_mass_one_plus_three_minus_has_zero_mode

end ArchonPhysicsConsumers.Thermalization
