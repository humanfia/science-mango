import M8AntipodalFamily


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], 8 ≤ N → Even N → (M8.AntipodalFamily.support N).card = 4 ∧ (0 : ZMod N) ∈ M8.AntipodalFamily.support N ∧ (1 : ZMod N) ∈ M8.AntipodalFamily.support N ∧ ((N/2 : ℕ) : ZMod N) ∈ M8.AntipodalFamily.support N
