import M5ResidueCount

theorem M5.ResidueCount.pair_indicator_exact : ∀ (T k : ℕ) (F : M5.BinaryPolynomial) (a b : Fin k → Fin T), 0 < T → F.Monic → F ∣ M5.cyclicModulus T → M5.ResidueCount.pairIndicator F a b = (@ite ℤ (M5.ResidueCount.feasible F a b) (Classical.propDecidable _) 1 0) := by
  classical
  intro T k F a b hT hF hFT
  have hc := M5.Connectivity.connected_indicator T
    (M5.ResidueCount.residueSupport a)
    (M5.ResidueCount.residueSupport b) hT
  have hp := M5.PolynomialIndicator.exact_signature_indicator
    (M5.ResidueCount.tailPolynomial a)
    (M5.ResidueCount.tailPolynomial b) F T hT hF hFT
  simp [M5.ResidueCount.residueSupport, M5.Connectivity.supportGcd,
    Finset.gcd_image, Function.comp_def] at hc
  unfold M5.ResidueCount.pairIndicator M5.ResidueCount.feasible
  simp only [hp]
  simp_all [M5.ResidueCount.residueSupport, M5.Connectivity.supportGcd,
    Finset.gcd_image, Function.comp_def, ← Finset.sum_mul, ← Finset.mul_sum,
    ite_mul, mul_ite, and_assoc, and_comm, and_left_comm]
  <;> split_ifs at * <;> simp_all

theorem M5.ResidueCount.two_block_R_count : ∀ (P : M5.BinaryPolynomial) (T d k : ℕ), P.Monic → 0 < T → d ∣ T → M5.ResidueCount.ROne P T d k ^ 2 = ∑ a : Fin k → Fin T, ∑ b : Fin k → Fin T, (@ite ℤ (((∀ i : Fin k, d ∣ (a i).val) ∧ P ∣ M5.ResidueCount.tailPolynomial a) ∧ ((∀ i : Fin k, d ∣ (b i).val) ∧ P ∣ M5.ResidueCount.tailPolynomial b)) (Classical.propDecidable _) 1 0) := by
  classical
  intro P T d k hP hT hd
  simp only [M5.ResidueCount.ROne, dif_pos hP]
  rw [M5.AnchoredTupleCount.restricted_R_count P hP T d k hT hd]
  unfold M5.AnchoredTupleCount.restrictedCount
  simp only [pow_two, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hqa : (∀ i : Fin k, d ∣ (a i).val) ∧ P ∣ 1 + ∑ i : Fin k, (Polynomial.X : M5.BinaryPolynomial) ^ (a i).val
  <;> by_cases hqb : (∀ i : Fin k, d ∣ (b i).val) ∧ P ∣ 1 + ∑ i : Fin k, (Polynomial.X : M5.BinaryPolynomial) ^ (b i).val
  <;> simp [M5.ResidueCount.tailPolynomial, hqa, hqb]

theorem M5.ResidueCount.arithmetic_indicator_expansion : ∀ (T w : ℕ) (F : M5.BinaryPolynomial), 0 < T → 0 < w → F.Monic → F ∣ M5.cyclicModulus T → M5.ResidueCount.rawA T w F = ∑ a : Fin (w-1) → Fin T, ∑ b : Fin (w-1) → Fin T, M5.ResidueCount.pairIndicator F a b := by
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

theorem M5.ResidueCount.exact_rawA : ∀ (T w : ℕ) (F : M5.BinaryPolynomial), 0 < T → 0 < w → F.Monic → F ∣ M5.cyclicModulus T → M5.ResidueCount.rawA T w F = (M5.ResidueCount.validTailPairs T w F).card := by
  classical
  intro T w F hT hw hF hFT
  rw [M5.ResidueCount.arithmetic_indicator_expansion T w F hT hw hF hFT]
  simp_rw [M5.ResidueCount.pair_indicator_exact T (w - 1) F _ _ hT hF hFT]
  simp only [M5.ResidueCount.validTailPairs, Finset.card_eq_sum_ones,
    Nat.cast_sum, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h : M5.ResidueCount.feasible F a b <;> simp [h]

theorem M5.ResidueCount.rawA_nonnegative_and_positive : ∀ (T w : ℕ) (F : M5.BinaryPolynomial), 0 < T → 0 < w → F.Monic → F ∣ M5.cyclicModulus T → (0 ≤ M5.ResidueCount.rawA T w F ∧ (0 < M5.ResidueCount.rawA T w F ↔ ∃ a b : Fin (w-1) → Fin T, M5.ResidueCount.feasible F a b)) := by
  classical
  intro T w F hT hw hF hFT
  rw [M5.ResidueCount.exact_rawA T w F hT hw hF hFT]
  constructor
  · positivity
  · rw [Int.natCast_pos, Finset.card_pos]
    constructor
    · rintro ⟨⟨a, b⟩, hab⟩
      exact ⟨a, b, by simpa [M5.ResidueCount.validTailPairs] using hab⟩
    · rintro ⟨a, b, hab⟩
      exact ⟨(a, b), by simpa [M5.ResidueCount.validTailPairs] using hab⟩
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → M5.ResidueCount.A w F = (M5.ResidueCount.validTailPairs (M5.signaturePeriod F) w F).card ∧ 0 ≤ M5.ResidueCount.A w F ∧ (0 < M5.ResidueCount.A w F ↔ ∃ a b : Fin (w-1) → Fin (M5.signaturePeriod F), M5.ResidueCount.feasible F a b)
