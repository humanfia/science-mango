import FrozenTarget_37f0fdd18fc4d4b2
theorem M7.CanonicalOuter.realizer_correct : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.Action.act (M7.CanonicalOuter.realizer c) c = M7.CanonicalOuter.canonical c
  intro N _ c
  classical
  unfold M7.CanonicalOuter.realizer M7.CanonicalOuter.canonical M7.CanonicalOuter.candidate M7.CanonicalOuter.normalizePair
  rw [M7.Action.act_compose]
  simp [M7.Action.act, M7.Action.translate, M7.Action.affine, M7.CanonicalBlock.normalize, M7.CanonicalBlock.shift, add_comm]
