import M5ResidueRecovery

noncomputable def preflight_pick_bound : Prop :=
  ∀ (T : ℕ) (f : Fin T → ℤ) (xs : List (Fin T)), (M5.ResidueRecovery.pick f xs).2 ≤ xs.length

noncomputable def preflight_pick_positive : Prop :=
  ∀ (T : ℕ) (f : Fin T → ℤ) (xs : List (Fin T)), (∃ a ∈ xs, 0 < f a) → ∃ a ∈ xs, (M5.ResidueRecovery.pick f xs).1 = some a ∧ 0 < f a

noncomputable def preflight_recover_success : Prop :=
  ∀ (T : ℕ) (c : List (Fin T) → ℤ) (p : List (Fin T)) (n : ℕ), (∀ q : List (Fin T), q.length < p.length + n → c q = ∑ a : Fin T, c (q ++ [a])) → 0 < c p → ∃ q : List (Fin T), (M5.ResidueRecovery.recover c p n).1 = some q ∧ q.length = p.length + n ∧ 0 < c q ∧ (M5.ResidueRecovery.recover c p n).2 ≤ n * T

noncomputable def preflight_recover_valid : Prop :=
  ∀ (T : ℕ) (c : List (Fin T) → ℤ) (Valid : List (Fin T) → Prop) (m : ℕ), (∀ q : List (Fin T), q.length < m → c q = ∑ a : Fin T, c (q ++ [a])) → (∀ q : List (Fin T), q.length = m → 0 < c q → Valid q) → 0 < c [] → ∃ q : List (Fin T), (M5.ResidueRecovery.recover c [] m).1 = some q ∧ q.length = m ∧ Valid q ∧ (M5.ResidueRecovery.recover c [] m).2 ≤ m * T
