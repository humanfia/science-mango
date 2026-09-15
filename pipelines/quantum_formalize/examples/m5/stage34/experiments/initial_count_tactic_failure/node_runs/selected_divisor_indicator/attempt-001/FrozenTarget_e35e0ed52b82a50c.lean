import M5ConditionalCount


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) (A B U V : Finset ℕ), 0 < N → M5.ConditionalCount.selectedDivisorSum N A B U V = (if M5.Connectivity.supportGcd N (A ∪ U) (B ∪ V) = 1 then (1 : ℤ) else 0)
