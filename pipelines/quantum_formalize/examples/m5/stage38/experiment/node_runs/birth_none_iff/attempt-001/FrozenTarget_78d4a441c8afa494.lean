import M5BirthSearch


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (T lower B : ℕ) (C : ℕ → ℤ), M5.BirthSearch.birth T lower B C = none ↔ ∀ N : ℕ, N ≤ B → lower ≤ N → T ∣ N → C N ≤ 0
