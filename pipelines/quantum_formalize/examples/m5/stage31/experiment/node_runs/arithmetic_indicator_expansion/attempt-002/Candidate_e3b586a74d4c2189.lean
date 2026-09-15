import FrozenTarget_e3b586a74d4c2189
theorem M5.ResidueCount.arithmetic_indicator_expansion : QuantumHarnessFrozenTarget := by
  classical
  intro T w F hT hw hF hFT
  have hcount (d : ℕ) (hd : d ∈ T.divisors)
      (S : Finset M5.BinaryPolynomial)
      (hS : S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus T) F).powerset) :
      M5.ResidueCount.ROne (F * ∏ p ∈ S, p) T d (w - 1) ^ 2 =
        ∑ a : Fin (w - 1) → Fin T, ∑ b : Fin (w - 1) → Fin T,
          @ite ℤ
            (((∀ i, d ∣ (a i).val) ∧ F * ∏ p ∈ S, p ∣ M5.ResidueCount.tailPolynomial a) ∧
             ((∀ i, d ∣ (b i).val) ∧ F * ∏ p ∈ S, p ∣ M5.ResidueCount.tailPolynomial b))
            (Classical.propDecidable _) 1 0 := by
    apply M5.ResidueCount.two_block_R_count
    · apply hF.mul
      apply Polynomial.monic_prod_of_monic
      intro p hp
      exact (M5.PolynomialIndicator.residual_factors_regular F T hT hF hFT p
        ((Finset.mem_powerset.mp hS) hp)).1
    · exact hT
    · exact (Nat.mem_divisors.mp hd).1
  have hmove {α β γ : Type*} (s : Finset α) (t : Finset β)
      (u : Finset γ) (f : α → β → γ → ℤ) :
      (∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ u, f i j k) =
        ∑ j ∈ t, ∑ k ∈ u, ∑ i ∈ s, f i j k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
  let E := (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus T) F).powerset
  let f := fun (d : ℕ) (S : Finset M5.BinaryPolynomial)
      (a b : Fin (w - 1) → Fin T) =>
    ArithmeticFunction.moebius d * ((-1 : ℤ) ^ S.card *
      @ite ℤ
        (((∀ i, d ∣ (a i).val) ∧ F * ∏ p ∈ S, p ∣ M5.ResidueCount.tailPolynomial a) ∧
         ((∀ i, d ∣ (b i).val) ∧ F * ∏ p ∈ S, p ∣ M5.ResidueCount.tailPolynomial b))
        (Classical.propDecidable _) 1 0)
  change M5.ResidueCount.rawA T w F = _
  calc
    M5.ResidueCount.rawA T w F =
        ∑ d ∈ T.divisors, ∑ S ∈ E,
          ∑ a : Fin (w - 1) → Fin T, ∑ b : Fin (w - 1) → Fin T, f d S a b := by
      unfold M5.ResidueCount.rawA
      dsimp only [E, f]
      simp (disch := assumption) only [hcount, Finset.mul_sum]
    _ = ∑ d ∈ T.divisors, ∑ a : Fin (w - 1) → Fin T,
          ∑ b : Fin (w - 1) → Fin T, ∑ S ∈ E, f d S a b := by
      apply Finset.sum_congr rfl
      intro d hd
      exact hmove E Finset.univ Finset.univ (f d)
    _ = ∑ a : Fin (w - 1) → Fin T, ∑ b : Fin (w - 1) → Fin T,
          ∑ d ∈ T.divisors, ∑ S ∈ E, f d S a b := by
      exact hmove T.divisors Finset.univ Finset.univ
        (fun d a b => ∑ S ∈ E, f d S a b)
    _ = ∑ a : Fin (w - 1) → Fin T, ∑ b : Fin (w - 1) → Fin T,
          M5.ResidueCount.pairIndicator F a b := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      unfold M5.ResidueCount.pairIndicator M5.PolynomialIndicator.factorExclusionSum
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S hS
      apply Finset.sum_congr rfl
      intro d hd
      dsimp only [f]
      by_cases ha' : ∀ i : Fin (w - 1), d ∣ (a i).val
      <;> by_cases hb' : ∀ i : Fin (w - 1), d ∣ (b i).val
      <;> by_cases hPa : F * ∏ p ∈ S, p ∣ M5.ResidueCount.tailPolynomial a
      <;> by_cases hPb : F * ∏ p ∈ S, p ∣ M5.ResidueCount.tailPolynomial b
      <;> simp [ha', hb', hPa, hPb]
