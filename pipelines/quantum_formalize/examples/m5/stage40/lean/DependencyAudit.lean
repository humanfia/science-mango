import M5TupleCompletion

example : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (T d k : ℕ) (t : Fin k → Fin (T / d)), M5.QuotientCharacter.coordinates P hP (AdjoinRoot.mk P (M5.ArithmeticTuple.tuplePolynomial T d k t)) = M5.TupleCharacter.vectorSum (fun j : Fin (T / d) => M5.QuotientCharacter.coordinates P hP (AdjoinRoot.mk P ((Polynomial.X : M5.BinaryPolynomial) ^ (d * j.val)))) t := @M5.ArithmeticTuple.tuple_coordinates
#print axioms M5.ArithmeticTuple.tuple_coordinates
example : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (T d k : ℕ) (z : AdjoinRoot P), M5.ArithmeticTuple.numerator P hP T d k z = (2 : ℤ) ^ P.natDegree * ((Finset.univ.filter (fun t : Fin k → Fin (T / d) => AdjoinRoot.mk P (M5.ArithmeticTuple.tuplePolynomial T d k t) = z)).card : ℤ) := @M5.ArithmeticTuple.numerator_exact
#print axioms M5.ArithmeticTuple.numerator_exact
example : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (T d k : ℕ) (z : AdjoinRoot P), M5.ArithmeticTuple.R P hP T d k z = ((Finset.univ.filter (fun t : Fin k → Fin (T / d) => AdjoinRoot.mk P (M5.ArithmeticTuple.tuplePolynomial T d k t) = z)).card : ℤ) := @M5.ArithmeticTuple.R_exact
#print axioms M5.ArithmeticTuple.R_exact
example : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (T d k : ℕ) (z : AdjoinRoot P), 0 ≤ M5.ArithmeticTuple.R P hP T d k z := @M5.ArithmeticTuple.R_nonnegative
#print axioms M5.ArithmeticTuple.R_nonnegative
