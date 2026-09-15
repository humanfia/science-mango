import M5SubsetCharacter

theorem M5.SubsetCharacter.value_zero : ∀ (D : ℕ) (lam : M5.Character.BinaryVector D), M5.Character.value lam 0 = 1 := by
  change ∀ (D : ℕ) (lam : M5.Character.BinaryVector D), M5.Character.value lam 0 = 1
  intro D lam
  simp [M5.Character.value, M5.Character.bitSign]

theorem M5.SubsetCharacter.character_subset_sum : ∀ (D : ℕ) (U : Finset ℕ) (f : ℕ → M5.Character.BinaryVector D) (lam : M5.Character.BinaryVector D), M5.Character.value lam (M5.SubsetCharacter.vectorSum U f) = ∏ s ∈ U, M5.Character.value lam (f s) := by
  change ∀ (D : ℕ) (U : Finset ℕ) (f : ℕ → M5.Character.BinaryVector D) (lam : M5.Character.BinaryVector D), M5.Character.value lam (M5.SubsetCharacter.vectorSum U f) = ∏ s ∈ U, M5.Character.value lam (f s)
  intro D U f lam
  classical
  unfold M5.SubsetCharacter.vectorSum
  induction U using Finset.induction_on with
  | empty =>
      simpa using M5.SubsetCharacter.value_zero D lam
  | @insert s U hs ih =>
      rw [Finset.sum_insert hs, Finset.prod_insert hs]
      first
      | rw [M5.Character.character_add, ih]
      | rw [M5.SubsetCharacter.character_add, ih]

theorem M5.SubsetCharacter.signed_product_expansion : ∀ (D : ℕ) (S : Finset ℕ) (f : ℕ → M5.Character.BinaryVector D) (lam : M5.Character.BinaryVector D), M5.SubsetCharacter.signedProduct S (fun s => M5.Character.value lam (f s)) = ∑ U ∈ S.powerset, Polynomial.C (M5.Character.value lam (M5.SubsetCharacter.vectorSum U f)) * (Polynomial.X : Polynomial ℤ) ^ U.card := by
  change ∀ (D : ℕ) (S : Finset ℕ) (f : ℕ → M5.Character.BinaryVector D) (lam : M5.Character.BinaryVector D), M5.SubsetCharacter.signedProduct S (fun s => M5.Character.value lam (f s)) = ∑ U ∈ S.powerset, Polynomial.C (M5.Character.value lam (M5.SubsetCharacter.vectorSum U f)) * (Polynomial.X : Polynomial ℤ) ^ U.card
  intro D S f lam
  classical
  unfold M5.SubsetCharacter.signedProduct
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro U hU
  clear hU
  rw [M5.SubsetCharacter.character_subset_sum]
  induction U using Finset.induction_on with
  | empty => simp
  | @insert s U hs ih =>
      rw [Finset.prod_insert hs, Finset.prod_insert hs, Finset.card_insert_of_notMem hs, ih, map_mul, pow_succ]
      ring

theorem M5.SubsetCharacter.signed_product_coefficient : ∀ (D : ℕ) (S : Finset ℕ) (k : ℕ) (f : ℕ → M5.Character.BinaryVector D) (lam : M5.Character.BinaryVector D), (M5.SubsetCharacter.signedProduct S (fun s => M5.Character.value lam (f s))).coeff k = ∑ U ∈ S.powersetCard k, M5.Character.value lam (M5.SubsetCharacter.vectorSum U f) := by
  change ∀ (D : ℕ) (S : Finset ℕ) (k : ℕ) (f : ℕ → M5.Character.BinaryVector D) (lam : M5.Character.BinaryVector D), (M5.SubsetCharacter.signedProduct S (fun s => M5.Character.value lam (f s))).coeff k = ∑ U ∈ S.powersetCard k, M5.Character.value lam (M5.SubsetCharacter.vectorSum U f)
  intro D S k f lam
  classical
  rw [M5.SubsetCharacter.signed_product_expansion]
  simp [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Finset.powersetCard_eq_filter, Finset.sum_filter, eq_comm]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (D : ℕ) (S : Finset ℕ) (k : ℕ) (f : ℕ → M5.Character.BinaryVector D) (z : M5.Character.BinaryVector D), (∑ lam : M5.Character.BinaryVector D, M5.Character.value lam z * (M5.SubsetCharacter.signedProduct S (fun s => M5.Character.value lam (f s))).coeff k) = (2 : ℤ) ^ D * (M5.SubsetCharacter.count S k f z : ℤ)
