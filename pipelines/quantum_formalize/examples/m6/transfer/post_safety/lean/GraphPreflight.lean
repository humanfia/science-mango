import M6PostSafety
#check (∀ (R N : ℕ) (z w : ℤ) (j k : ℕ), z.natAbs ≤ 2^R*8^N → w.natAbs ≤ 2^R*8^N → (z/(2:ℤ)^j - w/(2:ℤ)^k).natAbs < 2^(M6.Transfer.queryCoefficientBits R N - 1))
#check (∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (P : M6.Pinned.Pins (2*N)) (d : ℕ), ((M6.ActualTransfer.Q N a b P).coeff d).natAbs < 2^(M6.Transfer.queryCoefficientBits (M6.ActualTransfer.span a b) N - 1))
