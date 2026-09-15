import M5IntegerMobius


def QuantumHarnessFrozenTarget : Prop :=
  ∀ n : ℕ, (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) = if n = 1 then (1 : ℤ) else 0
