import M5ArithmeticWorkflowReady


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F.coeff 0 = 1 → (0 < M5.OrderCount.C N w F ↔ (∃ S U : Finset ℕ, M5.PhysicalOrder.realizes N w F S U))
