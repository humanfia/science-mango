import M6TransferTrace
#check (∀ (R : ℕ) (K : Type) [CommSemiring K] (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → K) (start finish : M6.Transfer.Memory R) (n : ℕ), M6.Transfer.layers W start n finish = M6.Transfer.matrixProduct (fun i => M6.Transfer.edgeMatrix (W i)) n start finish)
#check (∀ (R : ℕ) (K : Type) [CommSemiring K] (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → K) (N : ℕ), M6.Transfer.arrayTrace W N = Matrix.trace (M6.Transfer.matrixProduct (fun i => M6.Transfer.edgeMatrix (W i)) N))
#check (∀ (S K : Type) [Fintype S] [DecidableEq S] [CommSemiring K] (N : ℕ) [NeZero N] (A : ℕ → Matrix S S K), Matrix.trace (M6.Transfer.matrixProduct A N) = ∑ m : ZMod N → S, ∏ i : ZMod N, A i.val (m i) (m (i+1)))
#check (∀ (R N : ℕ) [NeZero N] (K : Type) [CommSemiring K] (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → K), Matrix.trace (M6.Transfer.matrixProduct (fun i => M6.Transfer.edgeMatrix (W i)) N) = ∑ p : M6.Transfer.ClosedWalk R N, ∏ i : ZMod N, W i.val (p.val.1 i) (M6.Transfer.labels p i))
#check (∀ (R N : ℕ) [NeZero N] (K : Type) [CommSemiring K] (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → K), M6.Transfer.arrayTrace W N = ∑ h : M6.Transfer.Input N, ∏ i : ZMod N, W i.val (M6.Transfer.memoryAt h i) (h i))
#check (∀ (S K : Type) [Fintype S] [DecidableEq S] [CommSemiring K] (A : Matrix S S K) (N : ℕ), M6.Transfer.matrixProduct (fun _ => A) N = A ^ N)
