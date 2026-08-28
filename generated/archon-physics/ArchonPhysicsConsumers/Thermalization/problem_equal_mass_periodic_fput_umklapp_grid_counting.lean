import ArchonPhysics.EqualMassPeriodicFPUTUmklappGridCounting

namespace ArchonPhysicsConsumers.Thermalization

open Set
open ArchonPhysics
open ArchonPhysics.Lattice
open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoTrivialShellCounting
open ArchonPhysics.EqualMassPeriodicFPUTUmklappTransversality
open ArchonPhysics.EqualMassPeriodicFPUTUmklappGridCounting

noncomputable section

theorem FourierGrid_interval_card_bound_consumer
    {N B : Nat} [NeZero N] (modes : Finset (Site N))
    {a D : Real}
    (hinterval : ∀ k ∈ modes, gridWaveNumber N k ∈ Icc a (a + D))
    (hwidth : D ≤ 2 * Real.pi * (B : Real) / (N : Real)) :
    modes.card ≤ B + 1 :=
  card_gridModes_le_add_one_of_mem_interval modes hinterval hwidth

theorem conditional_Umklapp_total_nearResonant_count_consumer
    {N B : Nat} [NeZero N] (k₀ : Site N)
    {a b : Site N → Real} {γ Δ : Real}
    (hγ : 0 < γ) (hΔ : 0 ≤ Δ)
    (htransverse : ∀ k₁ : Site N,
      UmklappK₂FixedSignTransverseOn
        (gridWaveNumber N k₀) (gridWaveNumber N k₁)
          (a k₁) (b k₁) γ)
    (hinterval : ∀ (k₁ : Site N) k₂,
      k₂ ∈ secondCoordinateSlice
          (nearResonantNontrivialPairs k₀ Δ) k₁ →
        gridWaveNumber N k₂ ∈ Icc (a k₁) (b k₁))
    (humklapp : ∀ (k₁ : Site N) k₂,
      k₂ ∈ secondCoordinateSlice
          (nearResonantNontrivialPairs k₀ Δ) k₁ →
        reducedTwoToTwoMismatch k₀ k₁ k₂ =
          umklappReducedFourWaveMismatch
            (gridWaveNumber N k₀) (gridWaveNumber N k₁)
              (gridWaveNumber N k₂))
    (hwidth : 2 * Δ / γ ≤
      2 * Real.pi * (B : Real) / (N : Real)) :
    (nearResonantNontrivialPairs k₀ Δ).card ≤ N * (B + 1) :=
  card_nearResonantNontrivialPairs_le_volume_mul_add_one
    k₀ hγ hΔ htransverse hinterval humklapp hwidth

#print axioms FourierGrid_interval_card_bound_consumer
#print axioms conditional_Umklapp_total_nearResonant_count_consumer

end

end ArchonPhysicsConsumers.Thermalization
