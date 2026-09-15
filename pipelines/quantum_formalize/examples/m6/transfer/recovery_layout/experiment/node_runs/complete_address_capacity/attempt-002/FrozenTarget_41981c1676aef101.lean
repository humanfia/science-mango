import M6RecoveryLayout


def QuantumHarnessFrozenTarget : Prop :=
  ∀ R N slots : ℕ, R < N → slots ≤ 512*(N+1)^2 → M6.Transfer.solveStorage R N slots < 2^(M6.Transfer.actualAddressBits R N)
