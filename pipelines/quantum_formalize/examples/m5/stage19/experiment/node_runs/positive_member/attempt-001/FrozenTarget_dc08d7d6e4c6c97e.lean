import M5PhysicalBridge


def QuantumHarnessFrozenTarget : Prop :=
  ∀ A : Finset ℕ, 2 ≤ A.card → 0 ∈ A → ∃ a ∈ A, 0 < a
