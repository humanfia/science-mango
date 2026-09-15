import FrozenTarget_8e3c2514f72a8f8c
theorem M5.packed_residue : QuantumHarnessFrozenTarget := by
  change ∀ (T r j : ℕ), r < T → M5.packedExponent T r j % T = r
  intro T r j hr
  simp [M5.packedExponent, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hr]
