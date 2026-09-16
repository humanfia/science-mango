import M8Exclusion


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (c : M7.Action.Recipe N), 0 < w → M8.PhysicalBridge.Valid w c → M8.PhysicalBridge.signature c ≠ 1 → (∀ g : M7.Action.Record N, M8.Cutoff.limit N < M8.Anchor.span (M7.Action.act g c)) → M8.Solver.run c = M8.Solver.Outcome.unrecognized (M8.PhysicalBridge.signature c)
