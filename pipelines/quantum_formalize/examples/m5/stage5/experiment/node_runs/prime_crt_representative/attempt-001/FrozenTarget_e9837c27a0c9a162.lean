import M5CRT


def QuantumHarnessFrozenTarget : Prop :=
  ∀ δ e : ℕ, 0 < δ → ∃ r : ℕ, r < M5.CRT.primeProduct δ ∧ ∀ p ∈ δ.primeFactors, Nat.ModEq p r (M5.CRT.repairResidue e p)
