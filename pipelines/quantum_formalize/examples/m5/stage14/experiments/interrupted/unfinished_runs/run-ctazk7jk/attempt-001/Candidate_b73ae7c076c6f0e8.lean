import FrozenTarget_b73ae7c076c6f0e8
theorem M5.SubsetCharacter.signed_product_coefficient : QuantumHarnessFrozenTarget := by
  change ∀ (D : ℕ) (S : Finset ℕ) (k : ℕ) (f : ℕ → M5.Character.BinaryVector D) (lam : M5.Character.BinaryVector D), (M5.SubsetCharacter.signedProduct S (fun s => M5.Character.value lam (f s))).coeff k = ∑ U ∈ S.powersetCard k, M5.Character.value lam (M5.SubsetCharacter.vectorSum U f)
  intro D S k f lam
  classical
  rw [M5.SubsetCharacter.signed_product_expansion]
  simp [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Finset.powersetCard_eq_filter, Finset.sum_filter, eq_comm]
