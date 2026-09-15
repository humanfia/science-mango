import M5ArithmeticSubset


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (lam : M5.Character.BinaryVector P.natDegree) (z : AdjoinRoot P), M5.QuotientCharacter.value P hP lam z = 1 ∨ M5.QuotientCharacter.value P hP lam z = -1
