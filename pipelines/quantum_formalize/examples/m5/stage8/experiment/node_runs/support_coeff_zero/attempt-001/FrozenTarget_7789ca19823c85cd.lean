import M5PackingInjective
import M5SupportPolynomial


def QuantumHarnessFrozenTarget : Prop :=
  ∀ S : Finset ℕ, (M5.SupportPolynomial.ofSupport S).coeff 0 = if 0 ∈ S then 1 else 0
