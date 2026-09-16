import M8WholeResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], M8.WholeResources.setupWork N ≤ 21000*(N+1)^3 ∧ M8.WholeResources.transformWork N ≤ 96*(N+1)^3 ∧ M8.WholeResources.undoWork N ≤ 160*(N+1)^3
