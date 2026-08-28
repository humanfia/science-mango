import ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge

/-!
# Consumer: discrete/continuum equal-mass FPUT shell bridge
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell
open ArchonPhysics.Lattice

theorem problem_finite_fput_grid_frequency_is_continuum_frequency
    (N : Nat) [NeZero N] (k : Site N) :
    continuumAcousticFrequency (gridWaveNumber N k) =
      ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave.periodicSineFrequency
        N k :=
  continuumAcousticFrequency_gridWaveNumber N k

theorem problem_finite_fput_four_wave_shell_is_direct_or_umklapp
    {N : Nat} [NeZero N] (k₀ k₁ k₂ : Site N) :
    reducedTwoToTwoMismatch k₀ k₁ k₂ =
        directReducedFourWaveMismatch
          (gridWaveNumber N k₀) (gridWaveNumber N k₁)
            (gridWaveNumber N k₂) ∨
      reducedTwoToTwoMismatch k₀ k₁ k₂ =
        umklappReducedFourWaveMismatch
          (gridWaveNumber N k₀) (gridWaveNumber N k₁)
            (gridWaveNumber N k₂) :=
  reducedTwoToTwoMismatch_eq_direct_or_umklapp k₀ k₁ k₂

#print axioms problem_finite_fput_grid_frequency_is_continuum_frequency
#print axioms problem_finite_fput_four_wave_shell_is_direct_or_umklapp

end ArchonPhysicsConsumers.Thermalization
