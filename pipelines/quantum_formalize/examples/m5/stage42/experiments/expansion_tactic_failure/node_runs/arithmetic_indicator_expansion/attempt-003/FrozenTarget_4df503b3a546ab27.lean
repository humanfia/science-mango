import M5ConditionalResidueCount

theorem M5.ConditionalResidueCount.prefix_gcd_divisibility : ∀ (T d : ℕ) (p q : List (Fin T)), (d ∣ M5.ConditionalResidueCount.selectedGcd T p q ↔ d ∣ T ∧ (∀ r ∈ p, d ∣ r.val) ∧ (∀ r ∈ q, d ∣ r.val)) := by
  change ∀ (T d : ℕ) (p q : List (Fin T)), _
  intro T d p q
  have hl {α : Type} (f : α → ℕ) (l : List α) (s : ℕ) :
      d ∣ l.foldl (fun g r => Nat.gcd g (f r)) s ↔
        d ∣ s ∧ ∀ r ∈ l, d ∣ f r := by
    induction l generalizing s with
    | nil => simp
    | cons a l ih =>
        simp [List.foldl_cons, ih, Nat.dvd_gcd_iff, and_assoc]
  have hr {α : Type} (f : α → ℕ) (l : List α) (s : ℕ) :
      d ∣ l.foldr (fun r g => Nat.gcd (f r) g) s ↔
        d ∣ s ∧ ∀ r ∈ l, d ∣ f r := by
    induction l with
    | nil => simp
    | cons a l ih =>
        simp [List.foldr_cons, ih, Nat.dvd_gcd_iff, and_assoc,
          and_left_comm, and_comm]
  simp [M5.ConditionalResidueCount.selectedGcd,
    M5.ConditionalResidueCount.prefixGcd, hl, hr,
    Nat.dvd_gcd_iff, and_assoc]

theorem M5.ConditionalResidueCount.selected_R_pair_count : ∀ (P ZA ZB : M5.BinaryPolynomial) (T d k l : ℕ), P.Monic → 0 < T → d ∣ T → M5.ConditionalResidueCount.RSelected P ZA T d k * M5.ConditionalResidueCount.RSelected P ZB T d l = ∑ a : Fin k → Fin T, ∑ b : Fin l → Fin T, M5.ConditionalResidueCount.divisibilityIndicator P ZA ZB d a b := by
  classical
  intro P ZA ZB T d k l hP hT hd
  simp only [M5.ConditionalResidueCount.RSelected, dif_pos hP]
  rw [M5.TupleCompletion.restricted_completion_R P hP ZA T d k hT hd,
    M5.TupleCompletion.restricted_completion_R P hP ZB T d l hT hd]
  unfold M5.TupleCompletion.restrictedCount M5.ConditionalResidueCount.divisibilityIndicator M5.ConditionalResidueCount.completedPolynomial
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hqa : (∀ i : Fin k, d ∣ (a i).val) ∧ P ∣ ZA + ∑ i : Fin k, (Polynomial.X : M5.BinaryPolynomial) ^ (a i).val
  <;> by_cases hqb : (∀ i : Fin l, d ∣ (b i).val) ∧ P ∣ ZB + ∑ i : Fin l, (Polynomial.X : M5.BinaryPolynomial) ^ (b i).val
  <;> simp [hqa, hqb]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (T w : ℕ) (F : M5.BinaryPolynomial) (p q : List (Fin T)), 0 < T → 0 < w → F.Monic → F ∣ M5.cyclicModulus T → M5.ConditionalResidueCount.rawConditionalA T w F p q = ∑ a : Fin (M5.ConditionalResidueCount.remaining w p) → Fin T, ∑ b : Fin (M5.ConditionalResidueCount.remaining w q) → Fin T, M5.ConditionalResidueCount.pairIndicator w F p q a b
