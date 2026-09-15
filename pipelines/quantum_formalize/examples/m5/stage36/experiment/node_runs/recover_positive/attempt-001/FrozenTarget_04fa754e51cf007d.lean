import M5BinaryRecovery


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (∀ q : List Bool, q.length < p.length + n → c q = c (q ++ [false]) + c (q ++ [true])) → 0 < c p → 0 < c (M5.BinaryRecovery.recover c p n)
