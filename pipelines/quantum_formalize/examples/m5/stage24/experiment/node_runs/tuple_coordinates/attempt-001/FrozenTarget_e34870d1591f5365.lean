import M5ArithmeticTuple


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (T d k : ℕ) (t : Fin k → Fin (T / d)), M5.QuotientCharacter.coordinates P hP (AdjoinRoot.mk P (M5.ArithmeticTuple.tuplePolynomial T d k t)) = M5.TupleCharacter.vectorSum (fun j : Fin (T / d) => M5.QuotientCharacter.coordinates P hP (AdjoinRoot.mk P ((Polynomial.X : M5.BinaryPolynomial) ^ (d * j.val)))) t
