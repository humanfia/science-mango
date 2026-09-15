import M7Domain


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (A : M7.Domain.Support N), M6.Coordinates.coefficients N (M7.Supports.polynomial A) = M7.Supports.indicator A
