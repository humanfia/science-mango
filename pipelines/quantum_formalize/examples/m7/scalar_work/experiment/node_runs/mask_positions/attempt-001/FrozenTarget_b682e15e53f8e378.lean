import M7ScalarWork


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], M7.ScalarWork.maskPositions N = 4 * Fintype.card ((ZMod N)ˣ) * N^2
