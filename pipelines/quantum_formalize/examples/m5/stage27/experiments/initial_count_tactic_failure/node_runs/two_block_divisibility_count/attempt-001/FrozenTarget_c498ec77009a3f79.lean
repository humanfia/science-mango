import M5OrderCount


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (P : M5.BinaryPolynomial) (W : Finset ℕ) (k : ℕ), P.Monic → 0 ∉ W → M5.OrderCount.nOne P W k ^ 2 = M5.OrderCount.twoBlockIndicatorSum P W k
