import M5Lift

theorem M5.Lift.cyclic_as_sub : ∀ N : ℕ, M5.cyclicModulus N = (Polynomial.X : M5.BinaryPolynomial) ^ N - 1 := by
  change ∀ N : ℕ, M5.cyclicModulus N = (Polynomial.X : M5.BinaryPolynomial) ^ N - 1
  intro N
  simp [M5.cyclicModulus, sub_eq_add_neg, CharTwo.neg_eq]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ T E j : ℕ, M5.cyclicModulus (T + j * E) - M5.cyclicModulus T = (Polynomial.X : M5.BinaryPolynomial) ^ T * M5.cyclicModulus (j * E)
