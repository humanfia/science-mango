import M5ArithmeticTuple

noncomputable def preflight_tuple_coordinates : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (T d k : ℕ) (t : Fin k → Fin (T / d)), M5.QuotientCharacter.coordinates P hP (AdjoinRoot.mk P (M5.ArithmeticTuple.tuplePolynomial T d k t)) = M5.TupleCharacter.vectorSum (fun j : Fin (T / d) => M5.QuotientCharacter.coordinates P hP (AdjoinRoot.mk P ((Polynomial.X : M5.BinaryPolynomial) ^ (d * j.val)))) t

noncomputable def preflight_numerator_exact : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (T d k : ℕ) (z : AdjoinRoot P), M5.ArithmeticTuple.numerator P hP T d k z = (2 : ℤ) ^ P.natDegree * ((Finset.univ.filter (fun t : Fin k → Fin (T / d) => AdjoinRoot.mk P (M5.ArithmeticTuple.tuplePolynomial T d k t) = z)).card : ℤ)

noncomputable def preflight_R_exact : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (T d k : ℕ) (z : AdjoinRoot P), M5.ArithmeticTuple.R P hP T d k z = ((Finset.univ.filter (fun t : Fin k → Fin (T / d) => AdjoinRoot.mk P (M5.ArithmeticTuple.tuplePolynomial T d k t) = z)).card : ℤ)

noncomputable def preflight_R_nonnegative : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (T d k : ℕ) (z : AdjoinRoot P), 0 ≤ M5.ArithmeticTuple.R P hP T d k z
