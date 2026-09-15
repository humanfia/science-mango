import M5ConditionalResidueCount

noncomputable def M5.Stage42Target.prefix_gcd_divisibility : Prop :=
  ∀ (T d : ℕ) (p q : List (Fin T)), (d ∣ M5.ConditionalResidueCount.selectedGcd T p q ↔ d ∣ T ∧ (∀ r ∈ p, d ∣ r.val) ∧ (∀ r ∈ q, d ∣ r.val))

#check M5.Stage42Target.prefix_gcd_divisibility

noncomputable def M5.Stage42Target.selected_R_pair_count : Prop :=
  ∀ (P ZA ZB : M5.BinaryPolynomial) (T d k l : ℕ), P.Monic → 0 < T → d ∣ T → M5.ConditionalResidueCount.RSelected P ZA T d k * M5.ConditionalResidueCount.RSelected P ZB T d l = ∑ a : Fin k → Fin T, ∑ b : Fin l → Fin T, M5.ConditionalResidueCount.divisibilityIndicator P ZA ZB d a b

#check M5.Stage42Target.selected_R_pair_count

noncomputable def M5.Stage42Target.pair_indicator_exact : Prop :=
  ∀ (T w : ℕ) (F : M5.BinaryPolynomial) (p q : List (Fin T)), ∀ (a : Fin (M5.ConditionalResidueCount.remaining w p) → Fin T) (b : Fin (M5.ConditionalResidueCount.remaining w q) → Fin T), 0 < T → F.Monic → F ∣ M5.cyclicModulus T → M5.ConditionalResidueCount.pairIndicator w F p q a b = M5.ConditionalResidueCount.feasibleIndicator w F p q a b

#check M5.Stage42Target.pair_indicator_exact

noncomputable def M5.Stage42Target.arithmetic_indicator_expansion : Prop :=
  ∀ (T w : ℕ) (F : M5.BinaryPolynomial) (p q : List (Fin T)), 0 < T → 0 < w → F.Monic → F ∣ M5.cyclicModulus T → M5.ConditionalResidueCount.rawConditionalA T w F p q = ∑ a : Fin (M5.ConditionalResidueCount.remaining w p) → Fin T, ∑ b : Fin (M5.ConditionalResidueCount.remaining w q) → Fin T, M5.ConditionalResidueCount.pairIndicator w F p q a b

#check M5.Stage42Target.arithmetic_indicator_expansion

noncomputable def M5.Stage42Target.exact_conditionalA : Prop :=
  ∀ (T w : ℕ) (F : M5.BinaryPolynomial) (p q : List (Fin T)), 0 < T → 0 < w → F.Monic → F ∣ M5.cyclicModulus T → M5.ConditionalResidueCount.conditionalAAt T w F p q = (M5.ConditionalResidueCount.validCompletions T w F p q).card

#check M5.Stage42Target.exact_conditionalA

noncomputable def M5.Stage42Target.period_conditionalA_exact : Prop :=
  ∀ (w : ℕ) (F : M5.BinaryPolynomial) (p q : List (Fin (M5.signaturePeriod F))), 0 < w → F.Monic → F.coeff 0 = 1 → M5.ConditionalResidueCount.conditionalA w F p q = (M5.ConditionalResidueCount.validCompletions (M5.signaturePeriod F) w F p q).card ∧ 0 ≤ M5.ConditionalResidueCount.conditionalA w F p q ∧ (0 < M5.ConditionalResidueCount.conditionalA w F p q ↔ M5.ConditionalResidueCount.fits w p q ∧ ∃ a : Fin (M5.ConditionalResidueCount.remaining w p) → Fin (M5.signaturePeriod F), ∃ b : Fin (M5.ConditionalResidueCount.remaining w q) → Fin (M5.signaturePeriod F), M5.ConditionalResidueCount.feasible w F p q a b)

#check M5.Stage42Target.period_conditionalA_exact

