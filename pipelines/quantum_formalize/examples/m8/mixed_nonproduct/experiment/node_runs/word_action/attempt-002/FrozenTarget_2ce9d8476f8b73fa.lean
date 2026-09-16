import M8MixedNonproduct


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N), Function.Bijective (M8.MixedNonproduct.wordAction g) ∧ ∀ z : M6.Physical.Word N, M8.MixedNonproduct.wordAction g z ∈ M8.MixedNonproduct.Cycles (M7.Action.act g c) ↔ z ∈ M8.MixedNonproduct.Cycles c
