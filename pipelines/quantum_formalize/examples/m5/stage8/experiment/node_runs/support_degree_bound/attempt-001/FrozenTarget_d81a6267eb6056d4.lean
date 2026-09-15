import M5PackingInjective
import M5SupportPolynomial


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (S : Finset ℕ) (K : ℕ), 0 < K → (∀ e ∈ S, e < K) → (M5.SupportPolynomial.ofSupport S).natDegree < K
