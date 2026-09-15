import FrozenTarget_f5319e318b46adc3
theorem M6.Euclid.remainder_correct : QuantumHarnessFrozenTarget := by
  change ∀ p q : M6.Euclid.BP, (M6.Euclid.remainder p q).value = p % q ∧ (M6.Euclid.remainder p q).cancellations + M6.Euclid.rank (M6.Euclid.remainder p q).value ≤ M6.Euclid.rank p ∧ (q ≠ 0 → M6.Euclid.rank (M6.Euclid.remainder p q).value < M6.Euclid.rank q)
  intro p q
  have h : (M6.Euclid.remainder p q).value = p % q ∧ (M6.Euclid.remainder p q).cancellations + M6.Euclid.rank (M6.Euclid.remainder p q).value ≤ M6.Euclid.rank p := by
    simpa [M6.Euclid.remainder] using
      (M6.Euclid.remainder_aux_correct (M6.Euclid.rank p) p q (le_refl _))
  refine ⟨h.1, h.2, ?_⟩
  intro hq
  rw [h.1]
  apply ((M6.Euclid.rank_order (p % q) q).1).mpr
  exact Polynomial.degree_mod_lt p hq
