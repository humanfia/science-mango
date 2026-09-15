import M6TransferTraceReady


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (S K : Type) [Fintype S] [DecidableEq S] [CommSemiring K] (A : Matrix S S K) (N : ℕ), M6.Transfer.matrixProduct (fun _ => A) N = A ^ N
