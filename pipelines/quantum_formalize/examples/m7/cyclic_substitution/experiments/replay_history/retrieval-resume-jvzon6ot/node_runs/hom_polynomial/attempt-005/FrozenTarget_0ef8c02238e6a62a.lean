import M7CyclicSubstitution


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (h : M7.CyclicSubstitution.RootCondition u) (p : M6.Cyclic.BinaryPolynomial), M7.CyclicSubstitution.hom u h (M6.Cyclic.image N p) = p.eval₂ (AdjoinRoot.of (M6.Cyclic.modulus N)) (M7.CyclicSubstitution.point u)
