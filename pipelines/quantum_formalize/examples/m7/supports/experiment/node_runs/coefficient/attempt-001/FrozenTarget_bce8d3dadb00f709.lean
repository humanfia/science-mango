import M7Supports


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N), ∀ n : ℕ, (M7.Supports.polynomial A).coeff n = if ∃ i ∈ A, i.val = n then 1 else 0
