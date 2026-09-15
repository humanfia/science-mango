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

theorem M5.ConditionalResidueCount.arithmetic_indicator_expansion : ∀ (T w : ℕ) (F : M5.BinaryPolynomial) (p q : List (Fin T)), 0 < T → 0 < w → F.Monic → F ∣ M5.cyclicModulus T → M5.ConditionalResidueCount.rawConditionalA T w F p q = ∑ a : Fin (M5.ConditionalResidueCount.remaining w p) → Fin T, ∑ b : Fin (M5.ConditionalResidueCount.remaining w q) → Fin T, M5.ConditionalResidueCount.pairIndicator w F p q a b := by
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
  have shuffle {α β γ δ : Type}
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
  simp (disch := assumption) only [hcount]
  unfold M5.ConditionalResidueCount.divisibilityIndicator
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [shuffle]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  conv_rhs => rw [Finset.sum_comm]
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

theorem M5.ConditionalResidueCount.pair_indicator_exact : ∀ (T w : ℕ) (F : M5.BinaryPolynomial) (p q : List (Fin T)), ∀ (a : Fin (M5.ConditionalResidueCount.remaining w p) → Fin T) (b : Fin (M5.ConditionalResidueCount.remaining w q) → Fin T), 0 < T → F.Monic → F ∣ M5.cyclicModulus T → M5.ConditionalResidueCount.pairIndicator w F p q a b = M5.ConditionalResidueCount.feasibleIndicator w F p q a b := by
  classical
  change ∀ (T w : ℕ) (F : M5.BinaryPolynomial) (p q : List (Fin T)), _
  intro T w F p q a b hT hF hFT
  have hg : 0 < M5.ConditionalResidueCount.selectedGcd T p q :=
    Nat.pos_of_dvd_of_pos
      ((M5.ConditionalResidueCount.prefix_gcd_divisibility T
        (M5.ConditionalResidueCount.selectedGcd T p q) p q).mp (dvd_refl _)).1 hT
  have hc := M5.Connectivity.connected_indicator
    (M5.ConditionalResidueCount.selectedGcd T p q)
    (insert 0 (Finset.univ.image (fun i => (a i).val)))
    (insert 0 (Finset.univ.image (fun i => (b i).val))) hg
  simp [M5.Connectivity.supportGcd, Finset.gcd_image] at hc
  have hp := M5.PolynomialIndicator.exact_signature_indicator
    (M5.ConditionalResidueCount.completedPolynomial
      (M5.ConditionalResidueCount.selectedPolynomial p) a)
    (M5.ConditionalResidueCount.completedPolynomial
      (M5.ConditionalResidueCount.selectedPolynomial q) b)
    F T hT hF hFT
  simp only [M5.ConditionalResidueCount.pairIndicator,
    M5.ConditionalResidueCount.feasibleIndicator,
    M5.ConditionalResidueCount.feasible]
  try dsimp only
  simp_all [M5.Connectivity.supportGcd, Finset.gcd_image,
    mul_ite, ite_mul]
  all_goals split_ifs <;> simp_all
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (T w : ℕ) (F : M5.BinaryPolynomial) (p q : List (Fin T)), 0 < T → 0 < w → F.Monic → F ∣ M5.cyclicModulus T → M5.ConditionalResidueCount.conditionalAAt T w F p q = (M5.ConditionalResidueCount.validCompletions T w F p q).card
