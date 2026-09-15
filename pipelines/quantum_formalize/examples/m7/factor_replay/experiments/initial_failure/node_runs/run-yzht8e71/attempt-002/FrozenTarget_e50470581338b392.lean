import M7FactorReplay


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (n : ℕ) (p : M7.FactorReplay.BP), p ∈ M7.FactorReplay.pool n ↔ p.natDegree ≤ n
