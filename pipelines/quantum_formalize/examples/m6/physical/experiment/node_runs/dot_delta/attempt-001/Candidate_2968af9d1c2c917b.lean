import FrozenTarget_2968af9d1c2c917b
theorem M6.Physical.dot_delta : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (a : M6.Physical.Block N) (i : ZMod N), M6.Physical.dot N (M6.Physical.delta N i) a = a i
  intro N _ a i
  classical
  simp [M6.Physical.dot, M6.Physical.delta, ite_mul]
