import M6RecoveryLayout
#check (∀ R N : ℕ, M6.Transfer.actualTraceStorage R N + 2*(2*N+1)*M6.Transfer.queryCoefficientBits R N + M6.Transfer.recoveryStackBits R N ≤ M6.Transfer.pairedQueryStorage R N)
#check (∀ R N slots : ℕ, R < N → slots ≤ 512*(N+1)^2 → M6.Transfer.solveStorage R N slots < 2^(M6.Transfer.actualAddressBits R N))
