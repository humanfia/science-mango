import M5AnchoredCount

theorem M5.AnchoredCount.anchor_polynomial : ∀ U : Finset ℕ, 0 ∉ U → M5.SupportPolynomial.ofSupport (insert 0 U) = 1 + M5.SupportPolynomial.ofSupport U := by
  change ∀ U : Finset ℕ, 0 ∉ U → M5.SupportPolynomial.ofSupport (insert 0 U) = 1 + M5.SupportPolynomial.ofSupport U
  intro U hU
  simp [M5.SupportPolynomial.ofSupport, Finset.sum_insert, hU]

theorem M5.AnchoredCount.anchor_divisibility : ∀ (P : M5.BinaryPolynomial) (U : Finset ℕ), 0 ∉ U → (P ∣ M5.SupportPolynomial.ofSupport (insert 0 U) ↔ AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport U) = 1) := by
  change ∀ (P : M5.BinaryPolynomial) (U : Finset ℕ), 0 ∉ U → (P ∣ M5.SupportPolynomial.ofSupport (insert 0 U) ↔ AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport U) = 1)
  intro P U hU
  have htwo : (1 : AdjoinRoot P) + 1 = 0 := by
    have h := congrArg (AdjoinRoot.mk P) (CharTwo.add_self_eq_zero (1 : M5.BinaryPolynomial))
    simpa only [map_add, map_one, map_zero] using h
  rw [M5.AnchoredCount.anchor_polynomial U hU, ← AdjoinRoot.mk_eq_zero, map_add, map_one]
  constructor
  · intro h
    exact add_left_cancel (h.trans htwo.symm)
  · intro h
    rw [h]
    exact htwo
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (W : Finset ℕ) (k : ℕ), 0 ∉ W → M5.ArithmeticSubset.n P hP W k 1 = (M5.AnchoredCount.count P W k : ℤ)
