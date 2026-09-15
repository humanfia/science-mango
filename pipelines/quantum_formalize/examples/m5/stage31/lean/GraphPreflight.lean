import M5ResidueCount

noncomputable def M5.Stage31Target.two_block_R_count : Prop :=
  ∀ (P : M5.BinaryPolynomial) (T d k : ℕ), P.Monic → 0 < T → d ∣ T → M5.ResidueCount.ROne P T d k ^ 2 = ∑ a : Fin k → Fin T, ∑ b : Fin k → Fin T, (@ite ℤ (((∀ i : Fin k, d ∣ (a i).val) ∧ P ∣ M5.ResidueCount.tailPolynomial a) ∧ ((∀ i : Fin k, d ∣ (b i).val) ∧ P ∣ M5.ResidueCount.tailPolynomial b)) (Classical.propDecidable _) 1 0)

#check M5.Stage31Target.two_block_R_count

noncomputable def M5.Stage31Target.pair_indicator_exact : Prop :=
  ∀ (T k : ℕ) (F : M5.BinaryPolynomial) (a b : Fin k → Fin T), 0 < T → F.Monic → F ∣ M5.cyclicModulus T → M5.ResidueCount.pairIndicator F a b = (@ite ℤ (M5.ResidueCount.feasible F a b) (Classical.propDecidable _) 1 0)

#check M5.Stage31Target.pair_indicator_exact

noncomputable def M5.Stage31Target.arithmetic_indicator_expansion : Prop :=
  ∀ (T w : ℕ) (F : M5.BinaryPolynomial), 0 < T → 0 < w → F.Monic → F ∣ M5.cyclicModulus T → M5.ResidueCount.rawA T w F = ∑ a : Fin (w-1) → Fin T, ∑ b : Fin (w-1) → Fin T, M5.ResidueCount.pairIndicator F a b

#check M5.Stage31Target.arithmetic_indicator_expansion

noncomputable def M5.Stage31Target.exact_rawA : Prop :=
  ∀ (T w : ℕ) (F : M5.BinaryPolynomial), 0 < T → 0 < w → F.Monic → F ∣ M5.cyclicModulus T → M5.ResidueCount.rawA T w F = (M5.ResidueCount.validTailPairs T w F).card

#check M5.Stage31Target.exact_rawA

noncomputable def M5.Stage31Target.rawA_nonnegative_and_positive : Prop :=
  ∀ (T w : ℕ) (F : M5.BinaryPolynomial), 0 < T → 0 < w → F.Monic → F ∣ M5.cyclicModulus T → (0 ≤ M5.ResidueCount.rawA T w F ∧ (0 < M5.ResidueCount.rawA T w F ↔ ∃ a b : Fin (w-1) → Fin T, M5.ResidueCount.feasible F a b))

#check M5.Stage31Target.rawA_nonnegative_and_positive

noncomputable def M5.Stage31Target.period_A_exact : Prop :=
  ∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → M5.ResidueCount.A w F = (M5.ResidueCount.validTailPairs (M5.signaturePeriod F) w F).card ∧ 0 ≤ M5.ResidueCount.A w F ∧ (0 < M5.ResidueCount.A w F ↔ ∃ a b : Fin (w-1) → Fin (M5.signaturePeriod F), M5.ResidueCount.feasible F a b)

#check M5.Stage31Target.period_A_exact

