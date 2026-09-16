import M8Coverage


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], 8 ≤ N → Even N → M8.Coverage.PhysicalTwo (M8.P4Family.recipe N)
