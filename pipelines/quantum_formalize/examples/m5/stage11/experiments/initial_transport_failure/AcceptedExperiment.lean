import M5Binomial

theorem M5.Binomial.negative_coeff : ∀ m j : ℕ, (((1 : Polynomial ℤ) - Polynomial.X) ^ m).coeff j = (-1 : ℤ) ^ j * (m.choose j : ℤ) := by
  change ∀ m j : ℕ, (((1 : Polynomial ℤ) - Polynomial.X) ^ m).coeff j = (-1 : ℤ) ^ j * (m.choose j : ℤ)
  intro m j
  have h : (1 : Polynomial ℤ) - Polynomial.X =
      Polynomial.X * Polynomial.C (-1 : ℤ) + 1 := by
    simp
    <;> ring
  rw [h, add_pow, ← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply, one_pow, mul_one, mul_pow,
    ← Polynomial.C_pow, ← Polynomial.C_eq_natCast, Polynomial.coeff_mul_C]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [Polynomial.coeff_X_pow, hij, hij.symm]
  · intro hj
    have hmj : m < j := by
      simp only [Finset.mem_range] at hj
      omega
    simp [Nat.choose_eq_zero_of_lt hmj]

theorem M5.Binomial.signed_product_split : ∀ (S : Finset ℕ) (f : ℕ → ℤ), (∀ s ∈ S, f s = 1 ∨ f s = -1) → M5.Binomial.signedProduct S f = (1 - Polynomial.X) ^ M5.Binomial.negativeCount S f * (1 + Polynomial.X) ^ (S.card - M5.Binomial.negativeCount S f) := by
  classical
  intro S f hf
  unfold M5.Binomial.signedProduct M5.Binomial.negativeCount
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun s => f s = -1)]
  have hn : (S.filter (fun s => f s = -1)).prod
      (fun s => (1 + Polynomial.C (f s) * Polynomial.X : Polynomial ℤ)) =
      (1 - Polynomial.X : Polynomial ℤ) ^ (S.filter (fun s => f s = -1)).card := by
    calc
      _ = (S.filter (fun s => f s = -1)).prod
          (fun _ => (1 - Polynomial.X : Polynomial ℤ)) := by
        apply Finset.prod_congr rfl
        intro s hs
        have h := (Finset.mem_filter.mp hs).2
        simp [h, sub_eq_add_neg]
      _ = _ := by simp
  have hp : (S.filter (fun s => ¬ f s = -1)).prod
      (fun s => (1 + Polynomial.C (f s) * Polynomial.X : Polynomial ℤ)) =
      (1 + Polynomial.X : Polynomial ℤ) ^ (S.filter (fun s => ¬ f s = -1)).card := by
    calc
      _ = (S.filter (fun s => ¬ f s = -1)).prod
          (fun _ => (1 + Polynomial.X : Polynomial ℤ)) := by
        apply Finset.prod_congr rfl
        intro s hs
        obtain ⟨hs, hneg⟩ := Finset.mem_filter.mp hs
        have hpos : f s = 1 := (hf s hs).resolve_right hneg
        simp [hpos]
      _ = _ := by simp
  rw [hn, hp]
  have hcard := Finset.card_filter_add_card_filter_not (s := S) (fun s => f s = -1)
  have hc : (S.filter (fun s => ¬ f s = -1)).card =
      S.card - (S.filter (fun s => f s = -1)).card := by omega
  rw [hc]

theorem M5.Binomial.binomial_convolution : ∀ m n k : ℕ, (((1 - Polynomial.X : Polynomial ℤ) ^ m) * (1 + Polynomial.X) ^ n).coeff k = ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * (m.choose j : ℤ) * (n.choose (k-j) : ℤ) := by
  change ∀ m n k : ℕ, (((1 - Polynomial.X : Polynomial ℤ) ^ m) * (1 + Polynomial.X) ^ n).coeff k = ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * (m.choose j : ℤ) * (n.choose (k - j) : ℤ)
  intro m n k
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [M5.Binomial.negative_coeff, Polynomial.coeff_one_add_X_pow]

theorem M5.Binomial.signed_coefficient_eval : ∀ (S : Finset ℕ) (f : ℕ → ℤ) (k : ℕ), (∀ s ∈ S, f s = 1 ∨ f s = -1) → (M5.Binomial.signedProduct S f).coeff k = ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ((M5.Binomial.negativeCount S f).choose j : ℤ) * ((S.card - M5.Binomial.negativeCount S f).choose (k-j) : ℤ) := by
  unfold QuantumHarnessFrozenTarget
  intro S f k hf
  rw [M5.Binomial.signed_product_split S f hf]
  exact M5.Binomial.binomial_convolution (M5.Binomial.negativeCount S f) (S.card - M5.Binomial.negativeCount S f) k
#print axioms M5.Binomial.negative_coeff
#print axioms M5.Binomial.binomial_convolution
#print axioms M5.Binomial.signed_product_split
#print axioms M5.Binomial.signed_coefficient_eval
