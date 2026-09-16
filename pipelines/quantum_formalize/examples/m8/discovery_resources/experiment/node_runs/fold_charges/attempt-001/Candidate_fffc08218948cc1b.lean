import FrozenTarget_fffc08218948cc1b
theorem M8.DiscoveryResources.fold_charges : QuantumHarnessFrozenTarget := by
  intro N inst A
  have hcard : A.card ≤ N := by
    simpa only [ZMod.card] using (Finset.card_le_univ A)
  constructor
  · simpa [M8.DiscoveryResources.memberCharge, mul_comm, mul_left_comm, mul_assoc] using
      (Nat.mul_le_mul_right (4 * (N + 1)) hcard)
  · simpa [M8.DiscoveryResources.spanCharge, mul_comm, mul_left_comm, mul_assoc] using
      (Nat.mul_le_mul_right (16 * (N + 1) ^ 2) hcard)
