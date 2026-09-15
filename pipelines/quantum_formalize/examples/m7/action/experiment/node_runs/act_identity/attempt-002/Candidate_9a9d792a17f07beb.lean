import FrozenTarget_9a9d792a17f07beb
theorem M7.Action.act_identity : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.Action.act (M7.Action.identity N) c = c
  intro N inst c
  have h : M7.Action.affine (1 : (ZMod N)ˣ) (0 : ZMod N) = id := by
    funext i
    simp [M7.Action.affine]
  rcases c with ⟨s, t⟩
  simp [M7.Action.act, M7.Action.identity, h]
