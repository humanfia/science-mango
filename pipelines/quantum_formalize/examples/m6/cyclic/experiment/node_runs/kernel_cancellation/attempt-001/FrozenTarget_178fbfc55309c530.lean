import M6Cyclic


def QuantumHarnessFrozenTarget : Prop :=
  ∀ F K h : M6.Cyclic.BinaryPolynomial, F ≠ 0 → (F*K ∣ F*h ↔ K ∣ h)
