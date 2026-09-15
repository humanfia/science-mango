import FrozenTarget_2521c2dca2e21cc5
theorem M5.ResidueCount.arithmetic_indicator_expansion : QuantumHarnessFrozenTarget := by
  classical
  intro T w F hT hw hF hFT
  have hmonic (S : Finset M5.BinaryPolynomial)
      (hS : S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus T) F).powerset) :
      (F * ∏ p ∈ S, p).Monic := by
    apply hF.mul
    apply Polynomial.monic_prod_of_monic
    intro p hp
    exact (M5.PolynomialIndicator.residual_factors_regular F T hT hF hFT p
      ((Finset.mem_powerset.mp hS) hp)).1
  have hR (d : ℕ) (hd : d ∈ T.divisors)
      (S : Finset M5.BinaryPolynomial)
      (hS : S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus T) F).powerset) :
      M5.ResidueCount.ROne (F * ∏ p ∈ S, p) T d (w - 1) ^ 2 =
        ∑ a : Fin (w - 1) → Fin T, ∑ b : Fin (w - 1) → Fin T,
          (if (((∀ i, d ∣ (a i).val) ∧ (F * ∏ p ∈ S, p) ∣ M5.ResidueCount.tailPolynomial a) ∧
            ((∀ i, d ∣ (b i).val) ∧ (F * ∏ p ∈ S, p) ∣ M5.ResidueCount.tailPolynomial b))
          then (1 : ℤ) else 0) := by
    exact M5.ResidueCount.two_block_R_count _ T d (w - 1)
      (hmonic S hS) hT (Nat.mem_divisors.mp hd).1
  have hmove : ∀ {α β γ : Type} (s : Finset α) (t : Finset β)
      (u : Finset γ) (f : α → β → γ → ℤ),
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
        exact hmove t u v (f x)
      _ = _ := hmove s u v (fun x a b => ∑ y ∈ t, f x y a b)
  unfold M5.ResidueCount.rawA
  simp (disch := assumption) only [hR]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [hshuffle]
  unfold M5.ResidueCount.pairIndicator M5.PolynomialIndicator.factorExclusionSum
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hda : ∀ i, d ∣ (a i).val
  <;> by_cases hdb : ∀ i, d ∣ (b i).val
  <;> by_cases hpa : (F * ∏ p ∈ S, p) ∣ M5.ResidueCount.tailPolynomial a
  <;> by_cases hpb : (F * ∏ p ∈ S, p) ∣ M5.ResidueCount.tailPolynomial b
  <;> simp_all [M5.ResidueCount.residueSupport, and_assoc, and_left_comm, and_comm, mul_assoc]
