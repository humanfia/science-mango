import M6RecoveryLayout


def QuantumHarnessFrozenTarget : Prop :=
  ∀ R N : ℕ, M6.Transfer.actualTraceStorage R N + 2*(2*N+1)*M6.Transfer.queryCoefficientBits R N + M6.Transfer.recoveryStackBits R N ≤ M6.Transfer.pairedQueryStorage R N
