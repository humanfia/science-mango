import M5QuotientCharacter


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (z : AdjoinRoot P), M5.QuotientCharacter.coordinates P hP z = 0 ↔ z = 0
