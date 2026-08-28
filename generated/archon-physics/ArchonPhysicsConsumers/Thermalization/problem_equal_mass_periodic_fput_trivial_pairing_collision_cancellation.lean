import ArchonPhysics.EqualMassPeriodicFPUTTrivialPairingCollisionCancellation

/-!
# Consumer: trivial FPUT pairing collision cancellation
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.EqualMassPeriodicFPUTTrivialPairingCollisionCancellation
open ArchonPhysics.Lattice

theorem problem_trivial_fput_pairing_has_zero_collision_flux
    {N : Nat} (action : Site N → Real) (k₀ k₁ : Site N) :
    reducedTwoToTwoCollisionFlux action k₀ k₁ k₀ = 0 ∧
      reducedTwoToTwoCollisionFlux action k₀ k₁ k₁ = 0 :=
  ⟨reducedTwoToTwoCollisionFlux_pairing_left action k₀ k₁,
    reducedTwoToTwoCollisionFlux_pairing_right action k₀ k₁⟩

#print axioms problem_trivial_fput_pairing_has_zero_collision_flux

end ArchonPhysicsConsumers.Thermalization
