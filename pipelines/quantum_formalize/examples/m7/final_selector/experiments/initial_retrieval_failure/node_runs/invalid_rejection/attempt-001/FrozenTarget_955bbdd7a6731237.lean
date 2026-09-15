import M7FinalSelector


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), (¬ M7.DefaultQuery.valid N q) → (∀ x : M7.FinalSelector.Index N w q, M7.FinalSelector.answer q x = Except.error M7.DefaultQuery.QueryError.invalidSignature) ∧ (¬ ∃ c : M7.Action.Recipe N, M7.FinalSelector.RawFeasible w q c)
