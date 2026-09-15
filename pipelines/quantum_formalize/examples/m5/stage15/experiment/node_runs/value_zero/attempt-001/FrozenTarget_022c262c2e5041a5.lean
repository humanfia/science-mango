import M5TupleCharacter


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (D : ℕ) (lam : M5.Character.BinaryVector D), M5.Character.value lam 0 = 1
