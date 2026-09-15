import FrozenTarget_3cff81c5981caae3
theorem M5.source_below_birth_bound : QuantumHarnessFrozenTarget := by
  change ∀ (w T E N : ℕ), N < M5.packingCutoff w T + E → E ≤ 2 ^ (w * T) → N < M5.birthBound w T
  intro w T E N hN hE
  have h := Nat.lt_of_lt_of_le hN (Nat.add_le_add_left hE (M5.packingCutoff w T))
  unfold M5.birthBound
  omega
