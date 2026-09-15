import FrozenTarget_b0be91d2f2b6e3ba
theorem M6.ActualCounts.input_normalization : QuantumHarnessFrozenTarget := by
  classical
  intro N inst a b ha hb
  have hs := M6.ActualCounts.dual_weighted_sum N a b ha hb
    (fun _ => (1 : Polynomial ℤ))
  have hc := congrArg (fun p : Polynomial ℤ => Polynomial.eval (0 : ℤ) p) hs
  simp only [Polynomial.eval_sum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hc
  have hcard : Fintype.card (M6.Physical.Block N) = 2 ^ N := by
    simpa only [Nat.card_eq_fintype_card] using M6.Spaces.input_card N
  rw [hcard] at hc
  exact_mod_cast hc.symm
