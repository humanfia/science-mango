import M7QuotientAuto


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (p : M6.Cyclic.BinaryPolynomial), M6.Cyclic.image N (p.comp (Polynomial.X ^ (u : ZMod N).val)) = M7.QuotientAuto.substitution u (M6.Cyclic.image N p)
