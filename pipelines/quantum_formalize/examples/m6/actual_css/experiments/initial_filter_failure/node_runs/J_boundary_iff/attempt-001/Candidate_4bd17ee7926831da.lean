import FrozenTarget_4bd17ee7926831da
theorem M6.ActualCSS.J_boundary_iff : QuantumHarnessFrozenTarget := by
  intro N inst a b v
  classical
  have hJ (h : M6.Physical.Block N) :
      M6.Spaces.dualBoundary N a b h =
        M6.Flatten.J N (M6.Flatten.flatten N (M6.Physical.boundary N a b h)) := by
    rw [M6.Spaces.dual_boundary_eval]
    simp only [M6.Flatten.J, M6.Flatten.flatten_left]
  have hmem :
      M6.Flatten.J N v ∈ M6.Character.subspaceWords (M6.Spaces.D N a b) ↔
        ∃ h : M6.Physical.Block N,
          M6.Spaces.dualBoundary N a b h = M6.Flatten.J N v := by
    simp [M6.Character.subspaceWords, M6.Spaces.D, LinearMap.mem_range]
  rw [M6.Spaces.boundary_words_iff, hmem]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h, (hJ h).trans (congrArg (M6.Flatten.J N) hh)⟩
  · rintro ⟨h, hh⟩
    refine ⟨h, ?_⟩
    rw [hJ h] at hh
    have he := congrArg (M6.Flatten.J N) hh
    simpa only [M6.Flatten.J_involution] using he
