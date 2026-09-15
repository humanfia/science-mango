import M6SolveResources
#check (∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (d : ℕ) (v : M6.Pinned.Vector (2*N)) (k : ℕ), M6.ActualTransfer.solve N a b = some (d,v,k) → k ≤ 2*N)
#check (∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → M6.ActualTransfer.actualDistanceWork N a b ≤ 50000*N^3*4^(M6.ActualTransfer.span a b))
#check (∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (d : ℕ) (v : M6.Pinned.Vector (2*N)) (k : ℕ), M6.ActualTransfer.span a b < N → M6.ActualTransfer.solve N a b = some (d,v,k) → M6.ActualTransfer.actualWitnessWork N a b k ≤ 200000*N^4*4^(M6.ActualTransfer.span a b))
