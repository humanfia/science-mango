import M5BirthSearch

noncomputable def preflight_birth_spec : Prop :=
  ∀ (T lower B : ℕ) (C : ℕ → ℤ), (∃ N : ℕ, N ≤ B ∧ lower ≤ N ∧ T ∣ N ∧ 0 < C N) → ∃ b : ℕ, M5.BirthSearch.birth T lower B C = some b ∧ b ≤ B ∧ lower ≤ b ∧ T ∣ b ∧ 0 < C b ∧ ∀ N : ℕ, lower ≤ N → T ∣ N → 0 < C N → b ≤ N

noncomputable def preflight_birth_exact : Prop :=
  ∀ (T lower B : ℕ) (C : ℕ → ℤ) (Valid : ℕ → Prop), (∀ N : ℕ, Valid N → lower ≤ N ∧ T ∣ N) → (∀ N : ℕ, lower ≤ N → T ∣ N → (0 < C N ↔ Valid N)) → (∃ N : ℕ, N ≤ B ∧ Valid N) → ∃ b : ℕ, M5.BirthSearch.birth T lower B C = some b ∧ Valid b ∧ ∀ N : ℕ, Valid N → b ≤ N

noncomputable def preflight_birth_none_iff : Prop :=
  ∀ (T lower B : ℕ) (C : ℕ → ℤ), M5.BirthSearch.birth T lower B C = none ↔ ∀ N : ℕ, N ≤ B → lower ≤ N → T ∣ N → C N ≤ 0
