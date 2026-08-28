import ArchonPhysics.EqualMassPeriodicFPUTDirectSectorClosure

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.Lattice
open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell
open ArchonPhysics.EqualMassPeriodicFPUTTrivialPairingCollisionCancellation
open ArchonPhysics.EqualMassPeriodicFPUTDirectSectorClosure

noncomputable section

theorem finite_direct_exactResonance_is_pairing_consumer
    {N : Nat} [NeZero N] (k₀ k₁ k₂ : Site N)
    (hdirect : FiniteDirectTwoToTwoBranch k₀ k₁ k₂) :
    reducedTwoToTwoMismatch k₀ k₁ k₂ = 0 ↔
      k₂ = k₀ ∨ k₂ = k₁ :=
  finite_direct_zeroMismatch_iff_pairing k₀ k₁ k₂ hdirect

theorem finite_direct_exactResonance_zeroFlux_consumer
    {N : Nat} [NeZero N] (action : Site N → Real)
    (k₀ k₁ k₂ : Site N)
    (hdirect : FiniteDirectTwoToTwoBranch k₀ k₁ k₂)
    (hzero : reducedTwoToTwoMismatch k₀ k₁ k₂ = 0) :
    reducedTwoToTwoCollisionFlux action k₀ k₁ k₂ = 0 :=
  reducedTwoToTwoCollisionFlux_eq_zero_of_direct_of_zeroMismatch
    action k₀ k₁ k₂ hdirect hzero

theorem finite_exactResonance_zeroFlux_or_Umklapp_consumer
    {N : Nat} [NeZero N] (action : Site N → Real)
    (k₀ k₁ k₂ : Site N)
    (hzero : reducedTwoToTwoMismatch k₀ k₁ k₂ = 0) :
    reducedTwoToTwoCollisionFlux action k₀ k₁ k₂ = 0 ∨
      reducedTwoToTwoMismatch k₀ k₁ k₂ =
        umklappReducedFourWaveMismatch
          (gridWaveNumber N k₀) (gridWaveNumber N k₁)
            (gridWaveNumber N k₂) :=
  zeroMismatch_zeroFlux_or_eq_umklapp action k₀ k₁ k₂ hzero

#print axioms finite_direct_exactResonance_is_pairing_consumer
#print axioms finite_direct_exactResonance_zeroFlux_consumer
#print axioms finite_exactResonance_zeroFlux_or_Umklapp_consumer

end

end ArchonPhysicsConsumers.Thermalization
