import M5BirthSearch


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (T lower B : ℕ) (C : ℕ → ℤ), (∃ N : ℕ, N ≤ B ∧ lower ≤ N ∧ T ∣ N ∧ 0 < C N) → ∃ b : ℕ, M5.BirthSearch.birth T lower B C = some b ∧ b ≤ B ∧ lower ≤ b ∧ T ∣ b ∧ 0 < C b ∧ ∀ N : ℕ, lower ≤ N → T ∣ N → 0 < C N → b ≤ N
