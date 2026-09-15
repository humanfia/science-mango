import M6TransferActualResources
#check (∀ R N : ℕ, R < N → M6.Transfer.actualTraceWork R N ≤ 16384 * N^3 * 4^R)
#check (∀ R N : ℕ, R < N → M6.Transfer.actualTraceStorage R N ≤ 4096 * N^2 * 2^R)
#check (∀ R N : ℕ, R < N → M6.Transfer.actualTraceStorage R N < 2^(M6.Transfer.actualAddressBits R N))
#check (∀ R N : ℕ, 2^R * 8^N < 2^(M6.Transfer.coefficientBits R N - 1))
