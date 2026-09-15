import M7FinalSelector


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → M7.DefaultQuery.valid N q → ∀ x : M7.FinalSelector.Index N w q, M7.GlobalQuery.feasible q (M7.FinalSelector.family N w q) x ↔ M7.FinalSelector.RawFeasible w q (M7.FinalSelector.realize q x)
