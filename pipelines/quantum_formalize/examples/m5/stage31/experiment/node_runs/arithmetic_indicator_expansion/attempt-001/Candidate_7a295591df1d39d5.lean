import FrozenTarget_7a295591df1d39d5
theorem M5.ResidueCount.arithmetic_indicator_expansion : QuantumHarnessFrozenTarget := by
  classical
  intro T w F hT hw hF hFT
  have hprod : ∀ S : Finset M5.BinaryPolynomial,
      (∀ p ∈ S, p.Monic) → (∏ p ∈ S, p).Monic := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert p S hp ih =>
      intro h
      rw [Finset.prod_insert hp]
      exact (h p (Finset.mem_insert_self p S)).mul
        (ih (fun q hq => h q (Finset.mem_insert_of_mem hq)))
  have hcount : ∀ d ∈ T.divisors,
      ∀ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus T) F).powerset,
      M5.ResidueCount.ROne (F * ∏ p ∈ S, p) T d (w - 1) ^ 2 =
        ∑ a : Fin (w - 1) → Fin T, ∑ b : Fin (w - 1) → Fin T,
          (if (((∀ i, d ∣ (a i).val) ∧
            F * ∏ p ∈ S, p ∣ M5.ResidueCount.tailPolynomial a) ∧
            ((∀ i, d ∣ (b i).val) ∧
            F * ∏ p ∈ S, p ∣ M5.ResidueCount.tailPolynomial b)) then (1 : ℤ) else 0) := by
    intro d hd S hS
    apply M5.ResidueCount.two_block_R_count
    · apply hF.mul
      apply hprod
      intro p hp
      exact (M5.PolynomialIndicator.residual_factors_regular F T hT hF hFT p
        ((Finset.mem_powerset.mp hS) hp)).1
    · exact hT
    · exact (Nat.mem_divisors.mp hd).1
  unfold M5.ResidueCount.rawA M5.ResidueCount.pairIndicator
  unfold M5.PolynomialIndicator.factorExclusionSum
  simp (disch := assumption) only [hcount]
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    enter [2, d]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, a, 2, d]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, a]
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro S hS
  simp only [M5.ResidueCount.residueSupport, Finset.mem_image, Finset.mem_univ,
    true_and, forall_exists_index, forall_apply_eq_imp_iff]
  split_ifs <;> simp_all <;> ring
