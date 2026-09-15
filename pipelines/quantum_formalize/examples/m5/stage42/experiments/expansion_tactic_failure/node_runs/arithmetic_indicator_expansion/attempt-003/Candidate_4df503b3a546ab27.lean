import FrozenTarget_4df503b3a546ab27
theorem M5.ConditionalResidueCount.arithmetic_indicator_expansion : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (T w : ℕ) (F : M5.BinaryPolynomial) (p q : List (Fin T)), _
  intro T w F p q hT hw hF hFT
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
    · apply hF.mul
      apply Polynomial.monic_prod_of_monic
      intro r hr
      exact (M5.PolynomialIndicator.residual_factors_regular F T hT hF hFT r
        ((Finset.mem_powerset.mp hS) hr)).1
    · exact hT
    · exact ((M5.ConditionalResidueCount.prefix_gcd_divisibility T d p q).mp
        (Nat.mem_divisors.mp hd).1).1
  have shuffle {α β γ δ : Type*}
      (s : Finset α) (t : Finset β) (u : Finset γ) (v : Finset δ)
      (f : α → β → γ → δ → ℤ) :
      (∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ u, ∑ l ∈ v, f i j k l) =
        ∑ k ∈ u, ∑ l ∈ v, ∑ i ∈ s, ∑ j ∈ t, f i j k l := by
    conv_lhs =>
      arg 2
      ext i
      rw [Finset.sum_comm]
      arg 2
      ext k
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_comm]
  unfold M5.ConditionalResidueCount.rawConditionalA
    M5.ConditionalResidueCount.pairIndicator
    M5.PolynomialIndicator.factorExclusionSum
  dsimp only
  simp only [mul_assoc]
  simp (disch := assumption) only [hcount]
  unfold M5.ConditionalResidueCount.divisibilityIndicator
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [shuffle]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro S hS
  by_cases ha' : ∀ i, d ∣ (a i).val
  <;> by_cases hb' : ∀ i, d ∣ (b i).val
  <;> by_cases hA : (F * ∏ r ∈ S, r) ∣
      M5.ConditionalResidueCount.completedPolynomial
        (M5.ConditionalResidueCount.selectedPolynomial p) a
  <;> by_cases hB : (F * ∏ r ∈ S, r) ∣
      M5.ConditionalResidueCount.completedPolynomial
        (M5.ConditionalResidueCount.selectedPolynomial q) b
  <;> simp [ha', hb', hA, hB, mul_assoc]
