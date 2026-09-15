import M7SignatureIdeal

theorem M7.SignatureIdeal.modulus_zero : ∀ (N : ℕ) [NeZero N], M6.Cyclic.image N (M6.Cyclic.modulus N) = 0 := by
  intro N inst
  change AdjoinRoot.mk (M6.Cyclic.modulus N) (M6.Cyclic.modulus N) = 0
  exact AdjoinRoot.mk_self
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ a b : M6.Cyclic.BinaryPolynomial, M7.SignatureIdeal.pairIdeal N a b = M7.SignatureIdeal.principal N (M6.Cyclic.signature a b (M6.Cyclic.modulus N))
