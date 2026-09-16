import M8MixedNonproduct


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M8.MixedNonproduct.Product c ↔ ∀ z ∈ M8.MixedNonproduct.Cycles c, ∀ t ∈ M8.MixedNonproduct.Cycles c, (z.1,t.2) ∈ M8.MixedNonproduct.Cycles c
