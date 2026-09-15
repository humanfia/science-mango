import M7FinalReplay


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), ¬ M7.DefaultQuery.valid N q → ∀ c : M7.FinalReplay.Certificate N w q, M7.FinalReplay.check q c = Except.error M7.DefaultQuery.QueryError.invalidSignature
