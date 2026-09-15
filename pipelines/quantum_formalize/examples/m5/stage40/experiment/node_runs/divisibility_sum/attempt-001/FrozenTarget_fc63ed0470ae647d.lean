import M5TupleCompletion


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (P Z : M5.BinaryPolynomial) (T d k : ℕ) (t : Fin k → Fin (T / d)), (P ∣ Z + M5.ArithmeticTuple.tuplePolynomial T d k t ↔ AdjoinRoot.mk P (M5.ArithmeticTuple.tuplePolynomial T d k t) = AdjoinRoot.mk P Z)
