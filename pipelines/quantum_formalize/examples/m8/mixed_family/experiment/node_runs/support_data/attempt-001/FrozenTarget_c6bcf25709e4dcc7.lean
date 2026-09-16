import M8MixedFamily


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], 7 ≤ N → (M8.MixedFamily.left N).card = 2 ∧ (M8.MixedFamily.right N).card = 2 ∧ (0 : ZMod N) ∈ M8.MixedFamily.left N ∧ (0 : ZMod N) ∈ M8.MixedFamily.right N ∧ (1 : ZMod N) ∈ M8.MixedFamily.left N
