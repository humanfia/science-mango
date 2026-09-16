import M8P4Family


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], 8 ≤ N → (M8.P4Family.support N).card = 4 ∧ (0 : ZMod N) ∈ M8.P4Family.support N ∧ (1 : ZMod N) ∈ M8.P4Family.support N
