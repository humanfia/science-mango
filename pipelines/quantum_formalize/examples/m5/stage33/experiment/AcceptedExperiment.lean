import M5CompletionBlock

theorem M5.CompletionBlock.support_union : ∀ A U : Finset ℕ, Disjoint A U → M5.SupportPolynomial.ofSupport (A ∪ U) = M5.SupportPolynomial.ofSupport A + M5.SupportPolynomial.ofSupport U := by
  change ∀ A U : Finset ℕ, Disjoint A U → M5.SupportPolynomial.ofSupport (A ∪ U) = M5.SupportPolynomial.ofSupport A + M5.SupportPolynomial.ofSupport U
  intro A U h
  unfold M5.SupportPolynomial.ofSupport
  exact Finset.sum_union h

theorem M5.CompletionBlock.union_divisibility : ∀ (P : M5.BinaryPolynomial) (A U : Finset ℕ), Disjoint A U → (P ∣ M5.SupportPolynomial.ofSupport (A ∪ U) ↔ AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport U) = AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport A)) := by
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

theorem M5.CompletionBlock.completion_count : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (A W : Finset ℕ) (k : ℕ), Disjoint A W → M5.ArithmeticSubset.n P hP W k (AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport A)) = (M5.CompletionBlock.count P A W k : ℤ) := by
  classical
  change ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (A W : Finset ℕ) (k : ℕ), Disjoint A W → M5.ArithmeticSubset.n P hP W k (AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport A)) = (M5.CompletionBlock.count P A W k : ℤ)
  intro P hP A W k hAW
  rw [M5.ArithmeticSubset.n_exact]
  unfold M5.CompletionBlock.count
  apply congrArg (fun S : Finset (Finset ℕ) => (S.card : ℤ))
  apply Finset.filter_congr
  intro U hU
  have hUW : U ⊆ W := (Finset.mem_powersetCard.mp hU).1
  have hAU : Disjoint A U := hAW.mono_right hUW
  exact (M5.CompletionBlock.union_divisibility P A U hAU).symm
#print axioms M5.CompletionBlock.support_union
#print axioms M5.CompletionBlock.union_divisibility
#print axioms M5.CompletionBlock.completion_count
