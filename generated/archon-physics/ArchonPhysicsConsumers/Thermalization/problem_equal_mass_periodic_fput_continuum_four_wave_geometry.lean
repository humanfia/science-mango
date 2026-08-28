import ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry

/-!
# Consumer: continuum equal-mass FPUT four-wave geometry
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry

theorem problem_direct_continuum_four_wave_shell_is_pairing
    {k₀ k₁ k₂ : Real}
    (hk₀0 : 0 < k₀) (hk₀2pi : k₀ < 2 * Real.pi)
    (hk₁0 : 0 < k₁) (hk₁2pi : k₁ < 2 * Real.pi)
    (hk₂0 : 0 < k₂) (hk₂2pi : k₂ < 2 * Real.pi) :
    directReducedFourWaveMismatch k₀ k₁ k₂ = 0 ↔
      k₂ = k₀ ∨ k₂ = k₁ :=
  directReducedFourWaveMismatch_eq_zero_iff_pairing
    hk₀0 hk₀2pi hk₁0 hk₁2pi hk₂0 hk₂2pi

theorem problem_umklapp_continuum_four_wave_equation
    (k₀ k₁ k₂ : Real) :
    umklappReducedFourWaveMismatch k₀ k₁ k₂ =
      4 * (Real.sin ((k₀ + k₁) / 4) *
          Real.cos ((k₀ - k₁) / 4) -
        Real.cos ((k₀ + k₁) / 4) *
          Real.sin ((2 * k₂ - k₀ - k₁) / 4)) :=
  umklappReducedFourWaveMismatch_factor k₀ k₁ k₂

#print axioms problem_direct_continuum_four_wave_shell_is_pairing
#print axioms problem_umklapp_continuum_four_wave_equation

end ArchonPhysicsConsumers.Thermalization
