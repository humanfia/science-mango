import M5TupleCharacter


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (D n k : ℕ) (f : Fin n → M5.Character.BinaryVector D) (z : M5.Character.BinaryVector D), (∑ lam : M5.Character.BinaryVector D, M5.Character.value lam z * ∑ t : Fin k → Fin n, M5.Character.value lam (M5.TupleCharacter.vectorSum f t)) = (2 : ℤ) ^ D * (M5.TupleCharacter.count k f z : ℤ)
