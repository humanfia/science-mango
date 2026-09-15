import M5SignatureCongruence


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (D a a' : M5.BinaryPolynomial) (T : ℕ), D ∣ M5.cyclicModulus T → AdjoinRoot.mk (M5.cyclicModulus T) a = AdjoinRoot.mk (M5.cyclicModulus T) a' → (D ∣ a ↔ D ∣ a')
