import FrozenTarget_2243bb56c6870ba5
theorem M8.Cutoff.indexed_storage_envelope : QuantumHarnessFrozenTarget := by
  change ∀ (N R : ℕ), R ≤ M8.Cutoff.limit N → N ^ 2 * 2 ^ R ≤ (N + 1) ^ 3
  intro N R hR
  calc
    N ^ 2 * 2 ^ R ≤ N ^ 2 * (N + 1) :=
      Nat.mul_le_mul_left _ (M8.Cutoff.state_bound N R hR)
    _ ≤ (N + 1) ^ 3 := by nlinarith
