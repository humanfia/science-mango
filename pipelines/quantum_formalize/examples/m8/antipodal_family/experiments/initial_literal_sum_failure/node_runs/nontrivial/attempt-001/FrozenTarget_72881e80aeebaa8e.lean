import M8AntipodalFamily


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], 8 ≤ N → Even N → (M8.AntipodalFamily.polynomial N).Monic ∧ M8.AntipodalFamily.polynomial N ≠ 1 ∧ M8.AntipodalFamily.polynomial N ≠ 0 ∧ (M8.AntipodalFamily.polynomial N).natDegree = N/2+1
