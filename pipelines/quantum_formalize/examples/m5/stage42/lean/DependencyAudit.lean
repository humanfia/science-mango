import M5ConditionalResidueCount

example : ∀ (T k : ℕ) (F : M5.BinaryPolynomial) (a b : Fin k → Fin T), 0 < T → F.Monic → F ∣ M5.cyclicModulus T → M5.ResidueCount.pairIndicator F a b = (@ite ℤ (M5.ResidueCount.feasible F a b) (Classical.propDecidable _) 1 0) := M5.ResidueCount.pair_indicator_exact

#print axioms M5.ResidueCount.pair_indicator_exact

example : ∀ (P : M5.BinaryPolynomial) (T d k : ℕ), P.Monic → 0 < T → d ∣ T → M5.ResidueCount.ROne P T d k ^ 2 = ∑ a : Fin k → Fin T, ∑ b : Fin k → Fin T, (@ite ℤ (((∀ i : Fin k, d ∣ (a i).val) ∧ P ∣ M5.ResidueCount.tailPolynomial a) ∧ ((∀ i : Fin k, d ∣ (b i).val) ∧ P ∣ M5.ResidueCount.tailPolynomial b)) (Classical.propDecidable _) 1 0) := M5.ResidueCount.two_block_R_count

#print axioms M5.ResidueCount.two_block_R_count

example : ∀ (T w : ℕ) (F : M5.BinaryPolynomial), 0 < T → 0 < w → F.Monic → F ∣ M5.cyclicModulus T → M5.ResidueCount.rawA T w F = ∑ a : Fin (w-1) → Fin T, ∑ b : Fin (w-1) → Fin T, M5.ResidueCount.pairIndicator F a b := M5.ResidueCount.arithmetic_indicator_expansion

#print axioms M5.ResidueCount.arithmetic_indicator_expansion

example : ∀ (T w : ℕ) (F : M5.BinaryPolynomial), 0 < T → 0 < w → F.Monic → F ∣ M5.cyclicModulus T → M5.ResidueCount.rawA T w F = (M5.ResidueCount.validTailPairs T w F).card := M5.ResidueCount.exact_rawA

#print axioms M5.ResidueCount.exact_rawA

example : ∀ (T w : ℕ) (F : M5.BinaryPolynomial), 0 < T → 0 < w → F.Monic → F ∣ M5.cyclicModulus T → (0 ≤ M5.ResidueCount.rawA T w F ∧ (0 < M5.ResidueCount.rawA T w F ↔ ∃ a b : Fin (w-1) → Fin T, M5.ResidueCount.feasible F a b)) := M5.ResidueCount.rawA_nonnegative_and_positive

#print axioms M5.ResidueCount.rawA_nonnegative_and_positive

example : ∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → M5.ResidueCount.A w F = (M5.ResidueCount.validTailPairs (M5.signaturePeriod F) w F).card ∧ 0 ≤ M5.ResidueCount.A w F ∧ (0 < M5.ResidueCount.A w F ↔ ∃ a b : Fin (w-1) → Fin (M5.signaturePeriod F), M5.ResidueCount.feasible F a b) := M5.ResidueCount.period_A_exact

#print axioms M5.ResidueCount.period_A_exact

example : ∀ (P Z : M5.BinaryPolynomial) (T d k : ℕ) (t : Fin k → Fin (T / d)), (P ∣ Z + M5.ArithmeticTuple.tuplePolynomial T d k t ↔ AdjoinRoot.mk P (M5.ArithmeticTuple.tuplePolynomial T d k t) = AdjoinRoot.mk P Z) := M5.TupleCompletion.divisibility_sum

#print axioms M5.TupleCompletion.divisibility_sum

example : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (Z : M5.BinaryPolynomial) (T d k : ℕ), M5.ArithmeticTuple.R P hP T d k (AdjoinRoot.mk P Z) = (M5.TupleCompletion.count P Z T d k : ℤ) := M5.TupleCompletion.completion_R_count

#print axioms M5.TupleCompletion.completion_R_count

example : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (Z : M5.BinaryPolynomial) (T d k : ℕ), 0 < T → d ∣ T → M5.ArithmeticTuple.R P hP T d k (AdjoinRoot.mk P Z) = (M5.TupleCompletion.restrictedCount P Z T d k : ℤ) := M5.TupleCompletion.restricted_completion_R

#print axioms M5.TupleCompletion.restricted_completion_R
