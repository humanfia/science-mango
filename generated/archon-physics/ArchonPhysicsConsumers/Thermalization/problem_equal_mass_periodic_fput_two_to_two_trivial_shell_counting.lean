import ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoTrivialShellCounting

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoTrivialShellCounting
open ArchonPhysics.Lattice

noncomputable section

theorem twoToTwo_trivialPairingLocus_exactCard_consumer
    {N : Nat} [NeZero N] (k₀ : Site N) :
    (trivialPairingParameterLocus k₀).card = 2 * N - 1 :=
  card_trivialPairingParameterLocus k₀

theorem twoToTwo_trivialPairingLocus_zeroMismatch_consumer
    {N : Nat} [NeZero N] (k₀ : Site N) (free : Site N × Site N)
    (hfree : free ∈ trivialPairingParameterLocus k₀) :
    reducedTwoToTwoMismatch k₀ free.1 free.2 = 0 :=
  reducedTwoToTwoMismatch_eq_zero_of_mem_trivialPairingParameterLocus
    k₀ free hfree

theorem twoToTwo_trivialNontrivialPartition_consumer
    {N : Nat} [NeZero N] (k₀ : Site N) :
    (nontrivialPairingParameterLocus k₀).card +
        (trivialPairingParameterLocus k₀).card = N ^ 2 :=
  card_nontrivial_add_card_trivialPairingParameterLocus k₀

theorem twoToTwo_nearResonantNontrivial_sliceReduction_consumer
    {N B : Nat} [NeZero N] (k₀ : Site N) (Δ : Real)
    (hslice : ∀ k₁ : Site N,
      (firstCoordinateSlice (nearResonantNontrivialPairs k₀ Δ) k₁).card ≤ B) :
    (nearResonantNontrivialPairs k₀ Δ).card ≤ N * B :=
  card_nearResonantNontrivialPairs_le_volume_mul k₀ Δ hslice

#print axioms twoToTwo_trivialPairingLocus_exactCard_consumer
#print axioms twoToTwo_trivialPairingLocus_zeroMismatch_consumer
#print axioms twoToTwo_trivialNontrivialPartition_consumer
#print axioms twoToTwo_nearResonantNontrivial_sliceReduction_consumer

end

end ArchonPhysicsConsumers.Thermalization
