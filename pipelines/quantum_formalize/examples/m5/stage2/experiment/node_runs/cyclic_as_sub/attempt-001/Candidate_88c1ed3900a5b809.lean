import FrozenTarget_88c1ed3900a5b809
theorem M5.Lift.cyclic_as_sub : QuantumHarnessFrozenTarget := by
  change ∀ N : ℕ, M5.cyclicModulus N = (Polynomial.X : M5.BinaryPolynomial) ^ N - 1
  intro N
  simp [M5.cyclicModulus, sub_eq_add_neg, CharTwo.neg_eq]
