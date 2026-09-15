import M5CompletionBlock

noncomputable def preflight_support_union : Prop :=
  ∀ A U : Finset ℕ, Disjoint A U → M5.SupportPolynomial.ofSupport (A ∪ U) = M5.SupportPolynomial.ofSupport A + M5.SupportPolynomial.ofSupport U

noncomputable def preflight_union_divisibility : Prop :=
  ∀ (P : M5.BinaryPolynomial) (A U : Finset ℕ), Disjoint A U → (P ∣ M5.SupportPolynomial.ofSupport (A ∪ U) ↔ AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport U) = AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport A))

noncomputable def preflight_completion_count : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (A W : Finset ℕ) (k : ℕ), Disjoint A W → M5.ArithmeticSubset.n P hP W k (AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport A)) = (M5.CompletionBlock.count P A W k : ℤ)
