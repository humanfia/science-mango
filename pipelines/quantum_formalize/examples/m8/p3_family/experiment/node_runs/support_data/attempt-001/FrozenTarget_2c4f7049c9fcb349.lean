import M8P3Family


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], 3 ≤ N → (M8.P3Family.support N).card = 3 ∧ (0 : ZMod N) ∈ M8.P3Family.support N ∧ (1 : ZMod N) ∈ M8.P3Family.support N
