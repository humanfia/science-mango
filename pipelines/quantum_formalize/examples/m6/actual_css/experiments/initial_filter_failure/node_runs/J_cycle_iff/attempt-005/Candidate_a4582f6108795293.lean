import FrozenTarget_a4582f6108795293
theorem M6.ActualCSS.J_cycle_iff : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), ∀ v : M6.Pinned.Vector (2*N), v ∈ M6.Spaces.cycleWords N a b ↔ M6.Flatten.J N v ∈ M6.Character.dualWords (M6.Spaces.B N a b)
  intro N inst a b v
  classical
  have hmem :
      M6.Flatten.J N v ∈ M6.Character.dualWords (M6.Spaces.B N a b) ↔
        ∀ h : M6.Physical.Block N,
          M6.Character.dot (M6.Spaces.boundary N a b h) (M6.Flatten.J N v) = 0 := by
    simp [M6.Character.dualWords, M6.Character.Orthogonal,
      M6.Spaces.B, LinearMap.mem_range]
  rw [M6.Spaces.cycle_words_iff, M6.Flatten.cycle_orthogonal, hmem]
  apply forall_congr'
  intro h
  have hJ :
      M6.Flatten.J N (M6.Spaces.boundary N a b h) =
        M6.Flatten.flatten N (M6.Physical.J N (M6.Physical.boundary N a b h)) := by
    rw [M6.Spaces.boundary_eval]
    simp only [M6.Flatten.J, M6.Flatten.flatten_left]
  have hd := M6.ActualCSS.J_dot N (M6.Spaces.boundary N a b h) (M6.Flatten.J N v)
  simp only [M6.Flatten.J_involution] at hd
  rw [← hJ, hd]
