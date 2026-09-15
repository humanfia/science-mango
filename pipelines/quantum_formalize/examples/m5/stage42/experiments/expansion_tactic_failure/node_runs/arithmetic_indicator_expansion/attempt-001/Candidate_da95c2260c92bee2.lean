import FrozenTarget_da95c2260c92bee2
theorem M5.ConditionalResidueCount.arithmetic_indicator_expansion : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (T w : ℕ) (F : M5.BinaryPolynomial) (p q : List (Fin T)), _
  intro T w F p q hT hw hF hFT
  have hdT (d : ℕ)
      (hd : d ∈ (M5.ConditionalResidueCount.selectedGcd T p q).divisors) :
      d ∣ T :=
    ((M5.ConditionalResidueCount.prefix_gcd_divisibility T d p q).mp
      (Nat.mem_divisors.mp hd).1).1
  have hmonic (S : Finset M5.BinaryPolynomial)
      (hS : S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus T) F).powerset) :
      (F * ∏ P ∈ S, P).Monic := by
    apply hF.mul
    apply Polynomial.monic_prod_of_monic
    intro P hP
    exact (M5.PolynomialIndicator.residual_factors_regular F T hT hF hFT P
      ((Finset.mem_powerset.mp hS) hP)).1
  have hcount (d : ℕ)
      (hd : d ∈ (M5.ConditionalResidueCount.selectedGcd T p q).divisors)
      (S : Finset M5.BinaryPolynomial)
      (hS : S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus T) F).powerset) :=
    M5.ConditionalResidueCount.selected_R_pair_count
      (F * ∏ P ∈ S, P)
      (M5.ConditionalResidueCount.selectedPolynomial p)
      (M5.ConditionalResidueCount.selectedPolynomial q)
      T d (M5.ConditionalResidueCount.remaining w p)
      (M5.ConditionalResidueCount.remaining w q)
      (hmonic S hS) hT (hdT d hd)
  have move {α β γ : Type*} (s : Finset α) (t : Finset β)
      (u : Finset γ) (f : α → β → γ → ℤ) :
      (∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ u, f i j k) =
        ∑ j ∈ t, ∑ k ∈ u, ∑ i ∈ s, f i j k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
  unfold M5.ConditionalResidueCount.rawConditionalA
  simp only [mul_assoc]
  simp (disch := assumption) only [hcount]
  simp only [Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext d
    rw [move]
  rw [move]
  unfold M5.ConditionalResidueCount.pairIndicator
  unfold M5.PolynomialIndicator.factorExclusionSum
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  first
  | skip
  | rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro S hS
  unfold M5.ConditionalResidueCount.divisibilityIndicator
  by_cases hda : ∀ i, d ∣ (a i).val
  <;> by_cases hdb : ∀ i, d ∣ (b i).val
  <;> by_cases hpa : (F * ∏ P ∈ S, P) ∣
      M5.ConditionalResidueCount.completedPolynomial
        (M5.ConditionalResidueCount.selectedPolynomial p) a
  <;> by_cases hpb : (F * ∏ P ∈ S, P) ∣
      M5.ConditionalResidueCount.completedPolynomial
        (M5.ConditionalResidueCount.selectedPolynomial q) b
  <;> simp [hda, hdb, hpa, hpb, mul_assoc]
