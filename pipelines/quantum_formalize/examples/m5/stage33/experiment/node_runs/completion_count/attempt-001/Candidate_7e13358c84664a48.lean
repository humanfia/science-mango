import FrozenTarget_7e13358c84664a48
theorem M5.CompletionBlock.completion_count : QuantumHarnessFrozenTarget := by
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
