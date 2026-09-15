import M5PhysicalOrder


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (A B : Finset ℕ) (w T : ℕ), 2 ≤ w → 0 < T → 0 ∈ A → 0 ∈ B → (∀ b ∈ B, b < w * T) → 0 < M5.PhysicalOrder.supportPeriod A B ∧ M5.PhysicalOrder.supportPeriod A B ≤ 2 ^ (w * T) ∧ EuclideanDomain.gcd (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B) ∣ M5.cyclicModulus (M5.PhysicalOrder.supportPeriod A B)
