import FrozenTarget_78b94e456e6c5535
theorem M7.LabelReplay.trace_recover : QuantumHarnessFrozenTarget := by
    intro N inst c d P xs
    induction xs generalizing P with
    | nil =>
        rfl
    | cons x xs ih =>
        simp only [M7.LabelReplay.trace, M6.Pinned.recover]
        rw [← ih]
        simp [M7.LabelReplay.endpoint, M7.LabelReplay.queryCount, Nat.add_comm]
