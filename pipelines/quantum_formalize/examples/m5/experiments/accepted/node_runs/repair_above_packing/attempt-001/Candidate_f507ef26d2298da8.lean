import FrozenTarget_f507ef26d2298da8
theorem M5.repair_above_packing : QuantumHarnessFrozenTarget := by
  change ∀ (w T e k : ℕ), 0 < T → w ≤ k → w * T ≤ e + k * T
  intro w T e k hT hwk
  exact Nat.le_trans (Nat.mul_le_mul_right T hwk) (Nat.le_add_left (k * T) e)
