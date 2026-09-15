import M5TupleCompletion

noncomputable def preflight_divisibility_sum : Prop :=
  ∀ (P Z : M5.BinaryPolynomial) (T d k : ℕ) (t : Fin k → Fin (T / d)), (P ∣ Z + M5.ArithmeticTuple.tuplePolynomial T d k t ↔ AdjoinRoot.mk P (M5.ArithmeticTuple.tuplePolynomial T d k t) = AdjoinRoot.mk P Z)

noncomputable def preflight_completion_R_count : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (Z : M5.BinaryPolynomial) (T d k : ℕ), M5.ArithmeticTuple.R P hP T d k (AdjoinRoot.mk P Z) = (M5.TupleCompletion.count P Z T d k : ℤ)

noncomputable def preflight_restricted_completion_R : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (Z : M5.BinaryPolynomial) (T d k : ℕ), 0 < T → d ∣ T → M5.ArithmeticTuple.R P hP T d k (AdjoinRoot.mk P Z) = (M5.TupleCompletion.restrictedCount P Z T d k : ℤ)
