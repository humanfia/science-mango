import M6ZeroSpan


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (i : ℕ) (m n : M6.Transfer.Memory 0), M6.Transfer.edgeMatrix (M6.ActualTransfer.boundaryWeight 0 N 1 1 (M6.Pinned.free (2*N)) i) m n = (1 : Polynomial ℤ) + Polynomial.X^2
