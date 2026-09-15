import M6TransferResources
#check (∀ R : ℕ, Fintype.card (M6.Transfer.Memory R) = 2^R)
#check (∀ R N : ℕ, M6.Transfer.traceCoefficientOps R N = 6 * N * (2*N+1) * 4^R)
#check (∀ R N : ℕ, R < N → M6.Transfer.traceWorkModel R N ≤ 4096 * N^3 * 4^R)
#check (∀ R N : ℕ, R < N → M6.Transfer.traceStorageModel R N ≤ 128 * N^2 * 2^R)
#check (∀ R N : ℕ, 2^R * 8^N < 2^(M6.Transfer.coefficientBits R N))
#check (∀ R N : ℕ, 0 < N → M6.Transfer.addressLocations R N ≤ 2^(M6.Transfer.addressBits R N))
