import M6ActualCounts
import M6ActualCountsDependencies


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (α β : Type) [Fintype α] (L : α → β) (k : ℕ), (∀ a₀ : α, Nat.card {a : α // L a = L a₀} = k) → ∀ w : β → Polynomial ℤ, (∑ a, w (L a)) = Polynomial.C (k : ℤ) * ∑ b ∈ M6.ActualCounts.imageWords L, w b
