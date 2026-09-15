import M5TupleCompletion

theorem M5.TupleCompletion.divisibility_sum : ∀ (P Z : M5.BinaryPolynomial) (T d k : ℕ) (t : Fin k → Fin (T / d)), (P ∣ Z + M5.ArithmeticTuple.tuplePolynomial T d k t ↔ AdjoinRoot.mk P (M5.ArithmeticTuple.tuplePolynomial T d k t) = AdjoinRoot.mk P Z) := by
  intro P Z T d k t
  have hneg : -Z = Z := by
    ext n
    simp only [Polynomial.coeff_neg]
    have h : ∀ a : ZMod 2, -a = a := by decide
    exact h (Z.coeff n)
  rw [AdjoinRoot.mk_eq_mk, sub_eq_add_neg, hneg, add_comm]

theorem M5.TupleCompletion.completion_R_count : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (Z : M5.BinaryPolynomial) (T d k : ℕ), M5.ArithmeticTuple.R P hP T d k (AdjoinRoot.mk P Z) = (M5.TupleCompletion.count P Z T d k : ℤ) := by
  intro P hP Z T d k
  classical
  rw [M5.ArithmeticTuple.R_exact]
  simp only [M5.TupleCompletion.count, M5.TupleCompletion.divisibility_sum]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (Z : M5.BinaryPolynomial) (T d k : ℕ), 0 < T → d ∣ T → M5.ArithmeticTuple.R P hP T d k (AdjoinRoot.mk P Z) = (M5.TupleCompletion.restrictedCount P Z T d k : ℤ)
