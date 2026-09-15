import M5BinaryRecovery

noncomputable def preflight_recover_length : Prop :=
  ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (M5.BinaryRecovery.recover c p n).length = p.length + n

noncomputable def preflight_recover_positive : Prop :=
  ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (∀ q : List Bool, q.length < p.length + n → c q = c (q ++ [false]) + c (q ++ [true])) → 0 < c p → 0 < c (M5.BinaryRecovery.recover c p n)

noncomputable def preflight_recover_valid : Prop :=
  ∀ (c : List Bool → ℤ) (Valid : List Bool → Prop) (m : ℕ), (∀ q : List Bool, q.length < m → c q = c (q ++ [false]) + c (q ++ [true])) → (∀ q : List Bool, q.length = m → 0 < c q → Valid q) → 0 < c [] → (M5.BinaryRecovery.recover c [] m).length = m ∧ Valid (M5.BinaryRecovery.recover c [] m)
