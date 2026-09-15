import M7Domain


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (A B : M7.Domain.Support N), Nat.gcd N (((M7.Supports.polynomial A).support ∪ (M7.Supports.polynomial B).support).gcd id) = M7.Domain.connectivityGcd A B
