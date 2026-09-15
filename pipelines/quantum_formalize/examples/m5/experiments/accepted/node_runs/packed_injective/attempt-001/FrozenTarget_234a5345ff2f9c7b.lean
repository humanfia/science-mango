import M5Foundation

theorem M5.packed_residue : ∀ (T r j : ℕ), r < T → M5.packedExponent T r j % T = r := by
  change ∀ (T r j : ℕ), r < T → M5.packedExponent T r j % T = r
  intro T r j hr
  simp [M5.packedExponent, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hr]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (T r s j k : ℕ), r < T → s < T → M5.packedExponent T r j = M5.packedExponent T s k → r = s ∧ j = k
