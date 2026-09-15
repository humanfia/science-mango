import FrozenTarget_05e52296b168886f
theorem M5.Packing.packed_value_mod : QuantumHarnessFrozenTarget := by
  change ∀ (w T : ℕ) (r : Fin w → Fin T) (i : Fin w), M5.Packing.packedValue r i % T = (r i).val
  intro w T r i
  simp [M5.Packing.packedValue, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt (r i).isLt]
