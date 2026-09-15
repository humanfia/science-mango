import FrozenTarget_a41dce5eba8b27c9
theorem M5.Binomial.signed_product_split : QuantumHarnessFrozenTarget := by
  classical
  intro S f hf
  unfold M5.Binomial.signedProduct M5.Binomial.negativeCount
  rw [← Finset.prod_filter_mul_prod_filter_not (p := fun s => f s = -1)]
  calc
    _ = (1 - Polynomial.X) ^ (S.filter (fun s => f s = -1)).card *
        (1 + Polynomial.X) ^ (S.filter (fun s => ¬ f s = -1)).card := by
      congr 1
      · trans ∏ s ∈ S.filter (fun s => f s = -1), (1 - Polynomial.X : Polynomial ℤ)
        · apply Finset.prod_congr rfl
          intro s hs
          simp [(Finset.mem_filter.mp hs).2, sub_eq_add_neg]
        · simp
      · trans ∏ s ∈ S.filter (fun s => ¬ f s = -1), (1 + Polynomial.X : Polynomial ℤ)
        · apply Finset.prod_congr rfl
          intro s hs
          obtain ⟨hsS, hsneg⟩ := Finset.mem_filter.mp hs
          have hspos : f s = 1 := (hf s hsS).resolve_right hsneg
          simp [hspos]
        · simp
    _ = _ := by rw [Finset.card_filter_not]
