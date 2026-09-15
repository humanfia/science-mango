import M7ScalarWork


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N D k : ℕ) (W : Finset ℕ), 0 < N → D ≤ N → k ≤ N → W.card ≤ N → M7.ScalarWork.term D W k ≤ 128 * N^4
