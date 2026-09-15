import FrozenTarget_ad066b7d45fcea6b
theorem M7.SignatureIdeal.modulus_zero : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], M6.Cyclic.image N (M6.Cyclic.modulus N) = 0
  intro N hN
  change AdjoinRoot.mk (M6.Cyclic.modulus N) (M6.Cyclic.modulus N) = 0
  exact AdjoinRoot.mk_self (M6.Cyclic.modulus N)
