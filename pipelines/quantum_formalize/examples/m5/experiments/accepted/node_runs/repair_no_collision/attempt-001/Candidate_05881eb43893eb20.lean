import FrozenTarget_05881eb43893eb20
theorem M5.repair_no_collision : QuantumHarnessFrozenTarget := by
  change ∀ (w T r j e k : ℕ), r < T → j < w → w ≤ k → M5.packedExponent T r j ≠ e + k * T
  intro w T r j e k hr hj hwk
  have hT : 0 < T := Nat.lt_of_le_of_lt (Nat.zero_le r) hr
  exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (M5.packed_range w T r j hr hj) (M5.repair_above_packing w T e k hT hwk))
