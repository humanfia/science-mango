import FrozenTarget_0c18d38d8c85eed6
theorem M7.Action.act_identity : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M7.Action.act (M7.Action.identity N) c = c
  intro N inst c
  rcases c with ⟨s, t⟩
  simp [M7.Action.act, M7.Action.identity, M7.Action.affine]
