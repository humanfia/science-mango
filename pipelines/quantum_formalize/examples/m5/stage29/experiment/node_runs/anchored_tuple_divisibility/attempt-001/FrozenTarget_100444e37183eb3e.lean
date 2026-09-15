import M5AnchoredTupleCount


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (P : M5.BinaryPolynomial) (T d k : ℕ) (t : Fin k → Fin (T / d)), (P ∣ 1 + M5.ArithmeticTuple.tuplePolynomial T d k t ↔ AdjoinRoot.mk P (M5.ArithmeticTuple.tuplePolynomial T d k t) = 1)
