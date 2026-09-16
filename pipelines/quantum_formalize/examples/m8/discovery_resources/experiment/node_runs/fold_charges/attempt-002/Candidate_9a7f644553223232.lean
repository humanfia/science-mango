import FrozenTarget_9a7f644553223232
theorem M8.DiscoveryResources.fold_charges : QuantumHarnessFrozenTarget := by
  intro N inst A
  have hcard : A.card ≤ N := by
    simpa only [ZMod.card] using Finset.card_le_univ A
  constructor
  · simpa only [M8.DiscoveryResources.memberCharge, Finset.sum_const,
      smul_eq_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_le_mul_right (4 * (N + 1)) hcard
  · simpa only [M8.DiscoveryResources.spanCharge, Finset.sum_const,
      smul_eq_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_le_mul_right (16 * (N + 1) ^ 2) hcard
