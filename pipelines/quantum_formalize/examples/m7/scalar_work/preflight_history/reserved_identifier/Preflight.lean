import M7ScalarWork
def target_0 : Prop := ∀ (N D k : ℕ) (W : Finset ℕ), 0 < N → D ≤ N → k ≤ N → W.card ≤ N → M7.ScalarWork.term D W k ≤ 128 * N^4
def target_1 : Prop := ∀ (N w : ℕ) (A B WA WB : Finset ℕ), 0 < N → w ≤ N → M7.PrefixCompleted.Base N A B WA WB → ∀ F : M5.BinaryPolynomial, F.Monic → F ∣ M5.cyclicModulus N → M7.ScalarWork.prefix N w F A B WA WB ≤ 1024 * N^4 * M7.ArithmeticLoops.divisorCount N * 2^(M7.ArithmeticLoops.factorCount N + N)
def target_2 : Prop := ∀ (N w : ℕ) (A B WA WB : Finset ℕ), 0 < N → w ≤ N → M7.PrefixCompleted.Base N A B WA WB → ∀ E : Finset M5.BinaryPolynomial, M7.PrefixSector.ValidSector N E → M7.ScalarWork.sector N w E A B WA WB ≤ 1024 * N^4 * E.card * M7.ArithmeticLoops.divisorCount N * 2^(M7.ArithmeticLoops.factorCount N + N)
def target_3 : Prop := ∀ (N : ℕ) [NeZero N], M7.ScalarWork.maskPositions N = 4 * Fintype.card ((ZMod N)ˣ) * N^2
