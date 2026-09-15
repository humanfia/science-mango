import M5ResidueTailBridge


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (T k : ℕ) (hT : 0 < T) (r : Fin k → Fin T), M5.SupportPolynomial.ofResidueTuple (M5.ResidueTailBridge.anchored hT r) = 1 + ∑ i : Fin k, (Polynomial.X : M5.BinaryPolynomial) ^ (r i).val
