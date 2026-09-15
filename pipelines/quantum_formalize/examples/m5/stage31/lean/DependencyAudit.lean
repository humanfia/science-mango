import M5ResidueCount

example : ∀ (F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → ∀ p ∈ M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F, p.Monic ∧ Irreducible p := M5.PolynomialIndicator.residual_factors_regular

#print axioms M5.PolynomialIndicator.residual_factors_regular

example : ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → F ∣ a → F ∣ b → M5.PolynomialIndicator.factorExclusionSum a b F N = (if M5.completeSignature a b N = F then 1 else 0) := M5.PolynomialIndicator.conditional_indicator

#print axioms M5.PolynomialIndicator.conditional_indicator

example : ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → M5.PolynomialIndicator.factorExclusionSum a b F N = (if M5.completeSignature a b N = F then 1 else 0) := M5.PolynomialIndicator.exact_signature_indicator

#print axioms M5.PolynomialIndicator.exact_signature_indicator

example : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (T d k : ℕ) (t : Fin k → Fin (T / d)), M5.QuotientCharacter.coordinates P hP (AdjoinRoot.mk P (M5.ArithmeticTuple.tuplePolynomial T d k t)) = M5.TupleCharacter.vectorSum (fun j : Fin (T / d) => M5.QuotientCharacter.coordinates P hP (AdjoinRoot.mk P ((Polynomial.X : M5.BinaryPolynomial) ^ (d * j.val)))) t := M5.ArithmeticTuple.tuple_coordinates

#print axioms M5.ArithmeticTuple.tuple_coordinates

example : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (T d k : ℕ) (z : AdjoinRoot P), M5.ArithmeticTuple.numerator P hP T d k z = (2 : ℤ) ^ P.natDegree * ((Finset.univ.filter (fun t : Fin k → Fin (T / d) => AdjoinRoot.mk P (M5.ArithmeticTuple.tuplePolynomial T d k t) = z)).card : ℤ) := M5.ArithmeticTuple.numerator_exact

#print axioms M5.ArithmeticTuple.numerator_exact

example : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (T d k : ℕ) (z : AdjoinRoot P), M5.ArithmeticTuple.R P hP T d k z = ((Finset.univ.filter (fun t : Fin k → Fin (T / d) => AdjoinRoot.mk P (M5.ArithmeticTuple.tuplePolynomial T d k t) = z)).card : ℤ) := M5.ArithmeticTuple.R_exact

#print axioms M5.ArithmeticTuple.R_exact

example : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (T d k : ℕ) (z : AdjoinRoot P), 0 ≤ M5.ArithmeticTuple.R P hP T d k z := M5.ArithmeticTuple.R_nonnegative

#print axioms M5.ArithmeticTuple.R_nonnegative

example : ∀ (P : M5.BinaryPolynomial) (T d k : ℕ) (t : Fin k → Fin (T / d)), (P ∣ 1 + M5.ArithmeticTuple.tuplePolynomial T d k t ↔ AdjoinRoot.mk P (M5.ArithmeticTuple.tuplePolynomial T d k t) = 1) := M5.AnchoredTupleCount.anchored_tuple_divisibility

#print axioms M5.AnchoredTupleCount.anchored_tuple_divisibility

example : ∀ T d : ℕ, 0 < T → d ∣ T → ∃ e : Fin (T / d) ≃ {r : Fin T // d ∣ r.val}, ∀ j : Fin (T / d), (e j).val.val = d * j.val := M5.AnchoredTupleCount.multiples_equivalence

#print axioms M5.AnchoredTupleCount.multiples_equivalence

example : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (T d k : ℕ), M5.ArithmeticTuple.R P hP T d k 1 = (M5.AnchoredTupleCount.count P T d k : ℤ) := M5.AnchoredTupleCount.anchored_R_count

#print axioms M5.AnchoredTupleCount.anchored_R_count

example : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (T d k : ℕ), 0 < T → d ∣ T → M5.ArithmeticTuple.R P hP T d k 1 = (M5.AnchoredTupleCount.restrictedCount P T d k : ℤ) := M5.AnchoredTupleCount.restricted_R_count

#print axioms M5.AnchoredTupleCount.restricted_R_count
