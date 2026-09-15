import M5AnchoredCount

noncomputable def preflight_anchor_polynomial : Prop :=
  ∀ U : Finset ℕ, 0 ∉ U → M5.SupportPolynomial.ofSupport (insert 0 U) = 1 + M5.SupportPolynomial.ofSupport U

noncomputable def preflight_anchor_divisibility : Prop :=
  ∀ (P : M5.BinaryPolynomial) (U : Finset ℕ), 0 ∉ U → (P ∣ M5.SupportPolynomial.ofSupport (insert 0 U) ↔ AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport U) = 1)

noncomputable def preflight_anchored_single_block_count : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (W : Finset ℕ) (k : ℕ), 0 ∉ W → M5.ArithmeticSubset.n P hP W k 1 = (M5.AnchoredCount.count P W k : ℤ)
