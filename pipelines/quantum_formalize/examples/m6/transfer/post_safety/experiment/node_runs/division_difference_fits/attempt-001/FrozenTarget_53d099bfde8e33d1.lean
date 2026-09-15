import M6PostSafety


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (R N : ℕ) (z w : ℤ) (j k : ℕ), z.natAbs ≤ 2^R*8^N → w.natAbs ≤ 2^R*8^N → (z/(2:ℤ)^j - w/(2:ℤ)^k).natAbs < 2^(M6.Transfer.queryCoefficientBits R N - 1)
