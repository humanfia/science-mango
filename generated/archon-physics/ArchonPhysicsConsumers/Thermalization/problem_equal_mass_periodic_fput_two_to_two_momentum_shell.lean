import ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell
open ArchonPhysics.Lattice

noncomputable section

def twoToTwoMomentumShell_freePairEquiv_consumer
    {N : Nat} (k₀ : Site N) :
    (Site N × Site N) ≃ TwoToTwoMomentumShell N k₀ :=
  freePairEquivTwoToTwoMomentumShell k₀

theorem twoToTwoMomentumShell_exactCard_consumer
    (N : Nat) [NeZero N] (k₀ : Site N) :
    Fintype.card (TwoToTwoMomentumShell N k₀) = N ^ 2 :=
  card_twoToTwoMomentumShell N k₀

theorem twoToTwoMomentumShell_reducedMismatch_consumer
    {N : Nat} [NeZero N] (k₀ : Site N)
    (shell : TwoToTwoMomentumShell N k₀) :
    twoToTwoShellMismatch k₀ shell =
      reducedTwoToTwoMismatch k₀
        (shellModeOne shell) (shellModeTwo shell) :=
  twoToTwoShellMismatch_eq_reduced k₀ shell

theorem twoToTwoMomentumShell_trivialPairings_consumer
    {N : Nat} [NeZero N] (k₀ k₁ : Site N) :
    reducedTwoToTwoMismatch k₀ k₁ k₀ = 0 ∧
      reducedTwoToTwoMismatch k₀ k₁ k₁ = 0 :=
  ⟨reducedTwoToTwoMismatch_pairing_left k₀ k₁,
    reducedTwoToTwoMismatch_pairing_right k₀ k₁⟩

#print axioms twoToTwoMomentumShell_freePairEquiv_consumer
#print axioms twoToTwoMomentumShell_exactCard_consumer
#print axioms twoToTwoMomentumShell_reducedMismatch_consumer
#print axioms twoToTwoMomentumShell_trivialPairings_consumer

end

end ArchonPhysicsConsumers.Thermalization
