import FrozenTarget_41d451f8f56e689b
theorem M5.CompletionBlock.union_divisibility : QuantumHarnessFrozenTarget := by
  change ∀ (P : M5.BinaryPolynomial) (A U : Finset ℕ), Disjoint A U → (P ∣ M5.SupportPolynomial.ofSupport (A ∪ U) ↔ AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport U) = AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport A))
  intro P A U hAU
  have hdouble : M5.SupportPolynomial.ofSupport A + M5.SupportPolynomial.ofSupport A = 0 := by
    ext n
    simp only [Polynomial.coeff_add, Polynomial.coeff_zero]
    have htwo : (2 : ZMod 2) = 0 := by decide
    rw [← two_mul, htwo, zero_mul]
  have hdouble' := congrArg (AdjoinRoot.mk P) hdouble
  rw [map_add, map_zero] at hdouble'
  rw [M5.CompletionBlock.support_union A U hAU, ← AdjoinRoot.mk_eq_zero, map_add]
  constructor
  · intro h
    exact add_left_cancel (h.trans hdouble'.symm)
  · intro h
    rw [h]
    exact hdouble'
