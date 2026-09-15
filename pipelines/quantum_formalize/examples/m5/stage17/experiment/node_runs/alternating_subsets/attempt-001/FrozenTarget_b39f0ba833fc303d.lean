import M5FiniteExclusion


def QuantumHarnessFrozenTarget : Prop :=
  ∀ S : Finset M5.BinaryPolynomial, (∑ H ∈ S.powerset, (-1 : ℤ)^H.card) = if S = ∅ then 1 else 0
