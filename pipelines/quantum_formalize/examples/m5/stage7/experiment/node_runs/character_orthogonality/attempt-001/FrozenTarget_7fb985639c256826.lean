import M5Character

theorem M5.Character.bit_orthogonality : ∀ b : ZMod 2, (∑ a : ZMod 2, M5.Character.bitSign a b) = if b = 0 then 2 else 0 := by
  change ∀ b : ZMod 2, (∑ a : ZMod 2, M5.Character.bitSign a b) = if b = 0 then 2 else 0
  decide
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (D : ℕ) (z : M5.Character.BinaryVector D), (∑ lam : M5.Character.BinaryVector D, M5.Character.value lam z) = if z = 0 then (2 : ℤ) ^ D else 0
