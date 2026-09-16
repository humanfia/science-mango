import FrozenTarget_0359946abd256b16
theorem M8.DiscoveryResources.fold_charges : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (A : Finset (ZMod N)), M8.DiscoveryResources.memberCharge A ≤ 4*N*(N+1) ∧ M8.DiscoveryResources.spanCharge A ≤ 16*N*(N+1)^2
  intro N inst A
  have hcard : A.card ≤ N := by
    simpa only [ZMod.card] using Finset.card_le_univ A
  constructor
  · calc
      M8.DiscoveryResources.memberCharge A = A.card * (4 * (N + 1)) := by
        simp [M8.DiscoveryResources.memberCharge]
      _ ≤ N * (4 * (N + 1)) := Nat.mul_le_mul_right _ hcard
      _ = 4 * N * (N + 1) := by ring
  · calc
      M8.DiscoveryResources.spanCharge A = A.card * (16 * (N + 1)^2) := by
        simp [M8.DiscoveryResources.spanCharge]
      _ ≤ N * (16 * (N + 1)^2) := Nat.mul_le_mul_right _ hcard
      _ = 16 * N * (N + 1)^2 := by ring
