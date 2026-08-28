import ArchonPhysics.EqualMassPeriodicFPUTDirectNearResonanceLocalization

/-!
# Consumer: direct-branch near-resonance localization
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTDirectNearResonanceLocalization

theorem problem_direct_fput_near_resonance_localizes_to_pairings
    {k₀ k₁ k₂ s rho Delta : Real}
    (hs : s ≤ |Real.sin ((k₀ + k₁) / 4)|)
    (hs0 : 0 ≤ s) (hrho : 0 ≤ rho)
    (hnear : |directReducedFourWaveMismatch k₀ k₁ k₂| ≤ Delta)
    (hthreshold : Delta < 8 * s * rho ^ 2) :
    |Real.sin ((k₂ - k₀) / 4)| < rho ∨
      |Real.sin ((k₂ - k₁) / 4)| < rho :=
  directNearResonance_localizes_to_pairing_sine
    hs hs0 hrho hnear hthreshold

#print axioms problem_direct_fput_near_resonance_localizes_to_pairings

end ArchonPhysicsConsumers.Thermalization
