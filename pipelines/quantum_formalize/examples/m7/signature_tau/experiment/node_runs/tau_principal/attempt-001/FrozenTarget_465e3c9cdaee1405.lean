import M7SignatureTau


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (F : M6.Cyclic.BinaryPolynomial), M7.SignatureIdeal.principal N (M7.SignatureTau.tau u F) = (M7.SignatureIdeal.principal N F).map (M7.QuotientAuto.substitution u)
