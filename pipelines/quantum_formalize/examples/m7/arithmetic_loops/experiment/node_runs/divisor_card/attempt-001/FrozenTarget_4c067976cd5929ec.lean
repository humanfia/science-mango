import M7ArithmeticLoops


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ A B : Finset ℕ, (M5.Connectivity.supportGcd N A B).divisors.card ≤ M7.ArithmeticLoops.divisorCount N
