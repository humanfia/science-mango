import FrozenTarget_bf6bc0cecfe3a13e
theorem M5.ConditionalResidueCount.arithmetic_indicator_expansion : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (T w : ℕ) (F : M5.BinaryPolynomial) (p q : List (Fin T)), _
  intro T w F p q hT hw hF hFT
  have hmonic (S : Finset M5.BinaryPolynomial)
      (hS : S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus T) F).powerset) :
      (F * ∏ r ∈ S, r).Monic := by
    apply hF.mul
    apply Polynomial.monic_prod_of_monic
    intro r hr
    exact (M5.PolynomialIndicator.residual_factors_regular F T hT hF hFT r
      ((Finset.mem_powerset.mp hS) hr)).1
  have hcount (d : ℕ)
      (hd : d ∈ (M5.ConditionalResidueCount.selectedGcd T p q).divisors)
      (S : Finset M5.BinaryPolynomial)
      (hS : S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus T) F).powerset) :
      M5.ConditionalResidueCount.RSelected (F * ∏ r ∈ S, r)
        (M5.ConditionalResidueCount.selectedPolynomial p) T d
        (M5.ConditionalResidueCount.remaining w p) *
      M5.ConditionalResidueCount.RSelected (F * ∏ r ∈ S, r)
        (M5.ConditionalResidueCount.selectedPolynomial q) T d
        (M5.ConditionalResidueCount.remaining w q) =
      ∑ a : Fin (M5.ConditionalResidueCount.remaining w p) → Fin T,
        ∑ b : Fin (M5.ConditionalResidueCount.remaining w q) → Fin T,
          M5.ConditionalResidueCount.divisibilityIndicator (F * ∏ r ∈ S, r)
            (M5.ConditionalResidueCount.selectedPolynomial p)
            (M5.ConditionalResidueCount.selectedPolynomial q) d a b := by
    apply M5.ConditionalResidueCount.selected_R_pair_count
    · exact hmonic S hS
    · exact hT
    · exact ((M5.ConditionalResidueCount.prefix_gcd_divisibility T d p q).mp
        (Nat.mem_divisors.mp hd).1).1
  have hfour {α β γ δ : Type*} (s : Finset α) (t : Finset β)
      (u : Finset γ) (v : Finset δ) (f : α → β → γ → δ → ℤ) :
      (∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ u, ∑ l ∈ v, f i j k l) =
        ∑ k ∈ u, ∑ l ∈ v, ∑ i ∈ s, ∑ j ∈ t, f i j k l := by
    calc
      _ = ∑ i ∈ s, ∑ k ∈ u, ∑ j ∈ t, ∑ l ∈ v, f i j k l := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
      _ = ∑ k ∈ u, ∑ i ∈ s, ∑ j ∈ t, ∑ l ∈ v, f i j k l := by
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        calc
          _ = ∑ i ∈ s, ∑ l ∈ v, ∑ j ∈ t, f i j k l := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.sum_comm]
          _ = _ := by rw [Finset.sum_comm]
  unfold M5.ConditionalResidueCount.rawConditionalA
  simp only [mul_assoc]
  simp (disch := assumption) only [hcount]
  unfold M5.ConditionalResidueCount.pairIndicator
  unfold M5.PolynomialIndicator.factorExclusionSum
  dsimp only
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [hfour]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  first
  | (apply Finset.sum_congr rfl
     intro d hd
     apply Finset.sum_congr rfl
     intro S hS
     unfold M5.ConditionalResidueCount.divisibilityIndicator
     split_ifs <;> simp_all only [and_self, and_true, true_and, and_false,
       false_and, not_true_eq_false, not_false_eq_true, ite_true, ite_false,
       mul_zero, zero_mul, mul_one, one_mul] <;> ring)
  | (rw [Finset.sum_comm]
     apply Finset.sum_congr rfl
     intro S hS
     apply Finset.sum_congr rfl
     intro d hd
     unfold M5.ConditionalResidueCount.divisibilityIndicator
     split_ifs <;> simp_all only [and_self, and_true, true_and, and_false,
       false_and, not_true_eq_false, not_false_eq_true, ite_true, ite_false,
       mul_zero, zero_mul, mul_one, one_mul] <;> ring)
