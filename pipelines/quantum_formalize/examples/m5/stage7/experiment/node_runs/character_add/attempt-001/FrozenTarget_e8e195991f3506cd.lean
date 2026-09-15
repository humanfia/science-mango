import M5Character

theorem M5.Character.bit_add : ∀ a b c : ZMod 2, M5.Character.bitSign a (b + c) = M5.Character.bitSign a b * M5.Character.bitSign a c := by
  change ∀ a b c : ZMod 2, M5.Character.bitSign a (b + c) = M5.Character.bitSign a b * M5.Character.bitSign a c
  decide
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (D : ℕ) (lam z u : M5.Character.BinaryVector D), M5.Character.value lam (z + u) = M5.Character.value lam z * M5.Character.value lam u
