import M5CRT


def QuantumHarnessFrozenTarget : Prop :=
  ∀ R r w : ℕ, 0 < R → ∃ k : ℕ, w ≤ k ∧ k < w + R ∧ Nat.ModEq R k r
