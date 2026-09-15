import M5QuotientCharacter


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (lam : M5.Character.BinaryVector P.natDegree) (z u : AdjoinRoot P), M5.QuotientCharacter.value P hP lam (z + u) = M5.QuotientCharacter.value P hP lam z * M5.QuotientCharacter.value P hP lam u
