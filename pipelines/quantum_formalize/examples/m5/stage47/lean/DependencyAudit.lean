import M5ArithmeticResidueRecovery

import M5ConditionalResidueCountAccepted

import M5ResidueRecoveryAccepted

import M5PrefixPartitionAccepted

example : ∀ (T : ℕ) (f : Fin T → ℤ) (xs : List (Fin T)), (M5.ResidueRecovery.pick f xs).2 ≤ xs.length := M5.ResidueRecovery.pick_bound

#print axioms M5.ResidueRecovery.pick_bound

example : ∀ (T : ℕ) (f : Fin T → ℤ) (xs : List (Fin T)), (∃ a ∈ xs, 0 < f a) → ∃ a ∈ xs, (M5.ResidueRecovery.pick f xs).1 = some a ∧ 0 < f a := M5.ResidueRecovery.pick_positive

#print axioms M5.ResidueRecovery.pick_positive

example : ∀ (T : ℕ) (c : List (Fin T) → ℤ) (p : List (Fin T)) (n : ℕ), (∀ q : List (Fin T), q.length < p.length + n → c q = ∑ a : Fin T, c (q ++ [a])) → 0 < c p → ∃ q : List (Fin T), (M5.ResidueRecovery.recover c p n).1 = some q ∧ q.length = p.length + n ∧ 0 < c q ∧ (M5.ResidueRecovery.recover c p n).2 ≤ n * T := M5.ResidueRecovery.recover_success

#print axioms M5.ResidueRecovery.recover_success

example : ∀ (T : ℕ) (c : List (Fin T) → ℤ) (Valid : List (Fin T) → Prop) (m : ℕ), (∀ q : List (Fin T), q.length < m → c q = ∑ a : Fin T, c (q ++ [a])) → (∀ q : List (Fin T), q.length = m → 0 < c q → Valid q) → 0 < c [] → ∃ q : List (Fin T), (M5.ResidueRecovery.recover c [] m).1 = some q ∧ q.length = m ∧ Valid q ∧ (M5.ResidueRecovery.recover c [] m).2 ≤ m * T := M5.ResidueRecovery.recover_valid

#print axioms M5.ResidueRecovery.recover_valid

example : ∀ (α : Type) (W : Finset (List α)), M5.PrefixPartition.count W [] = (W.card : ℤ) := M5.PrefixPartition.count_empty

#print axioms M5.PrefixPartition.count_empty

example : ∀ (α : Type) [DecidableEq α] (W : Finset (List α)) (m : ℕ) (p : List α), (∀ q ∈ W, q.length = m) → p.length = m → M5.PrefixPartition.count W p = (if p ∈ W then 1 else 0) := M5.PrefixPartition.count_terminal

#print axioms M5.PrefixPartition.count_terminal

example : ∀ (α : Type) (p q : List α) (a : α) (h : p.length < q.length), (p ++ [a]).IsPrefix q ↔ p.IsPrefix q ∧ q.get ⟨p.length, h⟩ = a := M5.PrefixPartition.prefix_next

#print axioms M5.PrefixPartition.prefix_next

example : ∀ (α : Type) [Fintype α] [DecidableEq α] (W : Finset (List α)) (m : ℕ) (p : List α), (∀ q ∈ W, q.length = m) → p.length < m → M5.PrefixPartition.count W p = ∑ a : α, M5.PrefixPartition.count W (p ++ [a]) := M5.PrefixPartition.count_partition

#print axioms M5.PrefixPartition.count_partition

example : ∀ (T d : ℕ) (p q : List (Fin T)), (d ∣ M5.ConditionalResidueCount.selectedGcd T p q ↔ d ∣ T ∧ (∀ r ∈ p, d ∣ r.val) ∧ (∀ r ∈ q, d ∣ r.val)) := M5.ConditionalResidueCount.prefix_gcd_divisibility

#print axioms M5.ConditionalResidueCount.prefix_gcd_divisibility

example : ∀ (P ZA ZB : M5.BinaryPolynomial) (T d k l : ℕ), P.Monic → 0 < T → d ∣ T → M5.ConditionalResidueCount.RSelected P ZA T d k * M5.ConditionalResidueCount.RSelected P ZB T d l = ∑ a : Fin k → Fin T, ∑ b : Fin l → Fin T, M5.ConditionalResidueCount.divisibilityIndicator P ZA ZB d a b := M5.ConditionalResidueCount.selected_R_pair_count

#print axioms M5.ConditionalResidueCount.selected_R_pair_count

example : ∀ (T w : ℕ) (F : M5.BinaryPolynomial) (p q : List (Fin T)), 0 < T → 0 < w → F.Monic → F ∣ M5.cyclicModulus T → M5.ConditionalResidueCount.rawConditionalA T w F p q = ∑ a : Fin (M5.ConditionalResidueCount.remaining w p) → Fin T, ∑ b : Fin (M5.ConditionalResidueCount.remaining w q) → Fin T, M5.ConditionalResidueCount.pairIndicator w F p q a b := M5.ConditionalResidueCount.arithmetic_indicator_expansion

#print axioms M5.ConditionalResidueCount.arithmetic_indicator_expansion

example : ∀ (T w : ℕ) (F : M5.BinaryPolynomial) (p q : List (Fin T)), ∀ (a : Fin (M5.ConditionalResidueCount.remaining w p) → Fin T) (b : Fin (M5.ConditionalResidueCount.remaining w q) → Fin T), 0 < T → F.Monic → F ∣ M5.cyclicModulus T → M5.ConditionalResidueCount.pairIndicator w F p q a b = M5.ConditionalResidueCount.feasibleIndicator w F p q a b := M5.ConditionalResidueCount.pair_indicator_exact

#print axioms M5.ConditionalResidueCount.pair_indicator_exact

example : ∀ (T w : ℕ) (F : M5.BinaryPolynomial) (p q : List (Fin T)), 0 < T → 0 < w → F.Monic → F ∣ M5.cyclicModulus T → M5.ConditionalResidueCount.conditionalAAt T w F p q = (M5.ConditionalResidueCount.validCompletions T w F p q).card := M5.ConditionalResidueCount.exact_conditionalA

#print axioms M5.ConditionalResidueCount.exact_conditionalA

example : ∀ (w : ℕ) (F : M5.BinaryPolynomial) (p q : List (Fin (M5.signaturePeriod F))), 0 < w → F.Monic → F.coeff 0 = 1 → M5.ConditionalResidueCount.conditionalA w F p q = (M5.ConditionalResidueCount.validCompletions (M5.signaturePeriod F) w F p q).card ∧ 0 ≤ M5.ConditionalResidueCount.conditionalA w F p q ∧ (0 < M5.ConditionalResidueCount.conditionalA w F p q ↔ M5.ConditionalResidueCount.fits w p q ∧ ∃ a : Fin (M5.ConditionalResidueCount.remaining w p) → Fin (M5.signaturePeriod F), ∃ b : Fin (M5.ConditionalResidueCount.remaining w q) → Fin (M5.signaturePeriod F), M5.ConditionalResidueCount.feasible w F p q a b) := M5.ConditionalResidueCount.period_conditionalA_exact

#print axioms M5.ConditionalResidueCount.period_conditionalA_exact
