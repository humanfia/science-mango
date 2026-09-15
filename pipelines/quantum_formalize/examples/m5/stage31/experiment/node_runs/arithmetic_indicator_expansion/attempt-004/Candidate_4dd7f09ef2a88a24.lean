import FrozenTarget_4dd7f09ef2a88a24
theorem M5.ResidueCount.arithmetic_indicator_expansion : QuantumHarnessFrozenTarget := by
  classical
  intro T w F hT hw hF hFT
  have hmonic : ∀ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus T) F).powerset,
      (F * ∏ p ∈ S, p).Monic := by
    intro S hS
    apply hF.mul
    apply Polynomial.monic_prod_of_monic
    intro p hp
    exact (M5.PolynomialIndicator.residual_factors_regular F T hT hF hFT p
      ((Finset.mem_powerset.mp hS) hp)).1
  have hR : ∀ d ∈ T.divisors,
      ∀ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus T) F).powerset,
      M5.ResidueCount.ROne (F * ∏ p ∈ S, p) T d (w - 1) ^ 2 =
        ∑ a : Fin (w - 1) → Fin T, ∑ b : Fin (w - 1) → Fin T,
          (if (((∀ i, d ∣ (a i).val) ∧ (F * ∏ p ∈ S, p) ∣ M5.ResidueCount.tailPolynomial a) ∧
            ((∀ i, d ∣ (b i).val) ∧ (F * ∏ p ∈ S, p) ∣ M5.ResidueCount.tailPolynomial b))
          then (1 : ℤ) else 0) := by
    intro d hd S hS
    refine (M5.ResidueCount.two_block_R_count (F * ∏ p ∈ S, p) T d (w - 1)
      (hmonic S hS) hT (Nat.mem_divisors.mp hd).1).trans ?_
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    by_cases h : (((∀ i, d ∣ (a i).val) ∧ (F * ∏ p ∈ S, p) ∣ M5.ResidueCount.tailPolynomial a) ∧
      ((∀ i, d ∣ (b i).val) ∧ (F * ∏ p ∈ S, p) ∣ M5.ResidueCount.tailPolynomial b))
    <;> simp [h]
  have hmove : ∀ {α β γ : Type} (s : Finset α) (t : Finset β) (u : Finset γ)
      (f : α → β → γ → ℤ),
      (∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, f x y z) =
        ∑ y ∈ t, ∑ z ∈ u, ∑ x ∈ s, f x y z := by
    intro α β γ s t u f
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    rw [Finset.sum_comm]
  have hshuffle : ∀ {α β γ δ : Type} (s : Finset α) (t : Finset β)
      (u : Finset γ) (v : Finset δ) (f : α → β → γ → δ → ℤ),
      (∑ x ∈ s, ∑ y ∈ t, ∑ a ∈ u, ∑ b ∈ v, f x y a b) =
        ∑ a ∈ u, ∑ b ∈ v, ∑ x ∈ s, ∑ y ∈ t, f x y a b := by
    intro α β γ δ s t u v f
    calc
      _ = ∑ x ∈ s, ∑ a ∈ u, ∑ b ∈ v, ∑ y ∈ t, f x y a b := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hmove t u v (fun y a b => f x y a b)
      _ = _ := hmove s u v (fun x a b => ∑ y ∈ t, f x y a b)
  unfold M5.ResidueCount.rawA
  simp (disch := assumption) only [hR]
  simp only [Finset.mul_sum]
  rw [hshuffle]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [M5.ResidueCount.pairIndicator, M5.PolynomialIndicator.factorExclusionSum,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hda : ∀ i, d ∣ (a i).val
  <;> by_cases hdb : ∀ i, d ∣ (b i).val
  <;> by_cases hpa : (F * ∏ p ∈ S, p) ∣ M5.ResidueCount.tailPolynomial a
  <;> by_cases hpb : (F * ∏ p ∈ S, p) ∣ M5.ResidueCount.tailPolynomial b
  <;> simp [hda, hdb, hpa, hpb, mul_assoc]
