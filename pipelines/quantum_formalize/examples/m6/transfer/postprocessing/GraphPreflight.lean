import M6Postprocessing
#check (∀ (z : ℤ) (k : ℕ), Int.shiftRight z k = z / (2:ℤ)^k)
#check (∀ (R N : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (d : ℕ), 2*N < d → (M6.Transfer.scalarTracePolynomial W N).coeff d = 0)
#check (∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (P : M6.Pinned.Pins (2*N)) (d : ℕ), M6.ActualTransfer.shiftedCoefficient N a b P d = (M6.ActualTransfer.Q N a b P).coeff d)
#check (∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (P : M6.Pinned.Pins (2*N)), M6.ActualTransfer.shiftedOutput N a b P = M6.ActualTransfer.Q N a b P)
#check (∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (P : M6.Pinned.Pins (2*N)), M6.ActualTransfer.shiftedScan N a b P = M6.Pinned.firstPositive (2*N) (M6.ActualTransfer.Q N a b P))
