import M5Translation


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (S : Finset (ZMod N)) (c : ZMod N), AdjoinRoot.mk (M5.cyclicModulus N) (M5.Translation.supportPolynomial (M5.Translation.shift S c)) = AdjoinRoot.mk (M5.cyclicModulus N) ((Polynomial.X : M5.BinaryPolynomial) ^ c.val) * AdjoinRoot.mk (M5.cyclicModulus N) (M5.Translation.supportPolynomial S)
