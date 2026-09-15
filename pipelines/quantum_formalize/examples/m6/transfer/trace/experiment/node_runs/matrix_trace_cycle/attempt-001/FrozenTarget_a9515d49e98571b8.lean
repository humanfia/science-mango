import M6TransferTraceReady


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (S K : Type) [Fintype S] [DecidableEq S] [CommSemiring K] (N : ℕ) [NeZero N] (A : ℕ → Matrix S S K), Matrix.trace (M6.Transfer.matrixProduct A N) = ∑ m : ZMod N → S, ∏ i : ZMod N, A i.val (m i) (m (i+1))
