import ArchonPhysics.SixWaveCollisionAlgebra

/-!
# Consumer: resonant six-wave FPUT collision algebra

This consumer exposes the invariant and detailed-balance layer needed after
the equal-mass alpha-FPUT normal-form reduction reaches its first connected
`3 <-> 3` resonant channel.  The Hamiltonian-to-kinetic convergence remains a
separate theorem obligation.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.SixWaveCollisionAlgebra

theorem problem_six_wave_action_conservation
    (rate n₁ n₂ n₃ n₄ n₅ n₆ : Real) :
    sixWaveLinearObservableSlope
      1 1 1 1 1 1 rate n₁ n₂ n₃ n₄ n₅ n₆ = 0 :=
  sixWaveActionSlope_eq_zero rate n₁ n₂ n₃ n₄ n₅ n₆

theorem problem_six_wave_energy_conservation
    (ω₁ ω₂ ω₃ ω₄ ω₅ ω₆ rate n₁ n₂ n₃ n₄ n₅ n₆ : Real)
    (hω : ω₁ + ω₂ + ω₃ = ω₄ + ω₅ + ω₆) :
    sixWaveLinearObservableSlope
      ω₁ ω₂ ω₃ ω₄ ω₅ ω₆ rate n₁ n₂ n₃ n₄ n₅ n₆ = 0 :=
  sixWaveEnergySlope_eq_zero_of_resonance
    ω₁ ω₂ ω₃ ω₄ ω₅ ω₆ rate n₁ n₂ n₃ n₄ n₅ n₆ hω

theorem problem_six_wave_rayleigh_jeans_stationary
    (chemical inverseTemperature : Real)
    (ω₁ ω₂ ω₃ ω₄ ω₅ ω₆ : Real)
    (hω : ω₁ + ω₂ + ω₃ = ω₄ + ω₅ + ω₆) :
    sixWaveCollisionFlux
      (rayleighJeansAction chemical inverseTemperature ω₁)
      (rayleighJeansAction chemical inverseTemperature ω₂)
      (rayleighJeansAction chemical inverseTemperature ω₃)
      (rayleighJeansAction chemical inverseTemperature ω₄)
      (rayleighJeansAction chemical inverseTemperature ω₅)
      (rayleighJeansAction chemical inverseTemperature ω₆) = 0 :=
  sixWaveCollisionFlux_rayleighJeans_eq_zero
    chemical inverseTemperature ω₁ ω₂ ω₃ ω₄ ω₅ ω₆ hω

#print axioms problem_six_wave_action_conservation
#print axioms problem_six_wave_energy_conservation
#print axioms problem_six_wave_rayleigh_jeans_stationary

end ArchonPhysicsConsumers.Thermalization
