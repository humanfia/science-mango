import FrozenTarget_ef4eae138f654721
theorem M5.SubsetCharacter.signed_product_expansion : QuantumHarnessFrozenTarget := by
  change ∀ (D : ℕ) (S : Finset ℕ) (f : ℕ → M5.Character.BinaryVector D) (lam : M5.Character.BinaryVector D), M5.SubsetCharacter.signedProduct S (fun s => M5.Character.value lam (f s)) = ∑ U ∈ S.powerset, Polynomial.C (M5.Character.value lam (M5.SubsetCharacter.vectorSum U f)) * (Polynomial.X : Polynomial ℤ) ^ U.card
  intro D S f lam
  classical
  unfold M5.SubsetCharacter.signedProduct
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro U hU
  rw [M5.SubsetCharacter.character_subset_sum]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, map_prod]
