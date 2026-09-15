import M5ArithmeticResidueRecovery

noncomputable def M5.Stage47Target.completion_word_split : Prop :=
  ∀ {α : Type} (k : ℕ) (u : List α) (a : Fin (k - (u.take k).length) → α) (b : Fin (k - (u.drop k).length) → α), u.length ≤ 2*k → (M5.ArithmeticResidueRecovery.completionWord k u a b).length = 2*k ∧ u.IsPrefix (M5.ArithmeticResidueRecovery.completionWord k u a b) ∧ (M5.ArithmeticResidueRecovery.completionWord k u a b).take k = u.take k ++ List.ofFn a ∧ (M5.ArithmeticResidueRecovery.completionWord k u a b).drop k = u.drop k ++ List.ofFn b

#check M5.Stage47Target.completion_word_split

noncomputable def M5.Stage47Target.completion_prefix_card : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (k : ℕ) (u : List α) (Valid : List α → Prop), u.length ≤ 2*k → M5.ArithmeticResidueRecovery.completionCount k u Valid = M5.PrefixPartition.count (M5.ArithmeticResidueRecovery.fullWords (2*k) Valid) u

#check M5.Stage47Target.completion_prefix_card

noncomputable def M5.Stage47Target.prefix_algebra : Prop :=
  ∀ (T k : ℕ) (p : List (Fin T)) (a : Fin k → Fin T), M5.ConditionalResidueCount.selectedPolynomial (p ++ List.ofFn a) = M5.ConditionalResidueCount.completedPolynomial (M5.ConditionalResidueCount.selectedPolynomial p) a ∧ M5.ConditionalResidueCount.prefixGcd (p ++ List.ofFn a) = Nat.gcd (M5.ConditionalResidueCount.prefixGcd p) (Finset.univ.gcd (fun i : Fin k => (a i).val))

#check M5.Stage47Target.prefix_algebra

noncomputable def M5.Stage47Target.completion_feasible : Prop :=
  ∀ (T w : ℕ) (F : M5.BinaryPolynomial) (u : List (Fin T)) (a : Fin ((w-1) - (u.take (w-1)).length) → Fin T) (b : Fin ((w-1) - (u.drop (w-1)).length) → Fin T), u.length ≤ 2*(w-1) → (M5.ConditionalResidueCount.feasible w F (u.take (w-1)) (u.drop (w-1)) a b ↔ M5.ArithmeticResidueRecovery.wordValid w F (M5.ArithmeticResidueRecovery.completionWord (w-1) u a b))

#check M5.Stage47Target.completion_feasible

noncomputable def M5.Stage47Target.oracle_prefix_count : Prop :=
  ∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → ∀ (u : List (Fin (M5.signaturePeriod F))), u.length ≤ 2*(w-1) → M5.ArithmeticResidueRecovery.oracle w F u = M5.PrefixPartition.count (M5.ArithmeticResidueRecovery.fullWords (2*(w-1)) (M5.ArithmeticResidueRecovery.wordValid w F)) u

#check M5.Stage47Target.oracle_prefix_count

noncomputable def M5.Stage47Target.oracle_initial : Prop :=
  ∀ (w : ℕ) (F : M5.BinaryPolynomial), M5.ArithmeticResidueRecovery.oracle w F [] = M5.ResidueCount.A w F

#check M5.Stage47Target.oracle_initial

noncomputable def M5.Stage47Target.oracle_partition_terminal : Prop :=
  ∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → (∀ (u : List (Fin (M5.signaturePeriod F))), u.length < 2*(w-1) → M5.ArithmeticResidueRecovery.oracle w F u = ∑ a : Fin (M5.signaturePeriod F), M5.ArithmeticResidueRecovery.oracle w F (u ++ [a])) ∧ (∀ (u : List (Fin (M5.signaturePeriod F))), u.length = 2*(w-1) → 0 < M5.ArithmeticResidueRecovery.oracle w F u → M5.ArithmeticResidueRecovery.wordValid w F u)

#check M5.Stage47Target.oracle_partition_terminal

noncomputable def M5.Stage47Target.recovery_correct : Prop :=
  ∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → 0 < M5.ResidueCount.A w F → ∃ u : List (Fin (M5.signaturePeriod F)), (M5.ArithmeticResidueRecovery.recover w F).1 = some u ∧ u.length = 2*(w-1) ∧ M5.ArithmeticResidueRecovery.wordValid w F u ∧ (M5.ArithmeticResidueRecovery.recover w F).2 ≤ 2*(w-1)*(M5.signaturePeriod F)

#check M5.Stage47Target.recovery_correct

