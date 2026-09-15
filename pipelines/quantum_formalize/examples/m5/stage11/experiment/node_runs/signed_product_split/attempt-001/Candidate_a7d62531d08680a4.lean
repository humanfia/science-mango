import FrozenTarget_a7d62531d08680a4
theorem M5.Binomial.signed_product_split : QuantumHarnessFrozenTarget := by
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
