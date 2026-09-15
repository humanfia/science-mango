import FrozenTarget_cb5d0310912a074f
theorem M6.Spaces.dual_boundary_card : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), (M6.Character.subspaceWords (M6.Spaces.D N a b)).card = (M6.Spaces.boundaryWords N a b).card
  intro N inst a b
  classical
  have hd (v : M6.Pinned.Vector (2*N)) :
      v ∈ M6.Character.subspaceWords (M6.Spaces.D N a b) ↔
        ∃ h : M6.Physical.Block N,
          M6.Flatten.flatten N (M6.Physical.J N (M6.Physical.boundary N a b h)) = v := by
    simp [M6.Character.subspaceWords, M6.Spaces.D, LinearMap.mem_range,
      M6.Spaces.dual_boundary_eval]
  refine Finset.card_bij (fun v _ => M6.Flatten.J N v) ?_ ?_ ?_
  · intro v hv
    obtain ⟨h, rfl⟩ := (hd v).mp hv
    apply (M6.Spaces.boundary_words_iff N a b _).mpr
    refine ⟨h, ?_⟩
    simp [M6.Flatten.J, M6.Flatten.flatten_left, M6.Physical.J_involution]
  · intro v hv w hw he
    have hh := congrArg (M6.Flatten.J N) he
    simpa only [M6.Flatten.J_involution] using hh
  · intro v hv
    obtain ⟨h, rfl⟩ := (M6.Spaces.boundary_words_iff N a b v).mp hv
    refine ⟨M6.Flatten.flatten N (M6.Physical.J N (M6.Physical.boundary N a b h)), ?_, ?_⟩
    · exact (hd _).mpr ⟨h, rfl⟩
    · simp [M6.Flatten.J, M6.Flatten.flatten_left, M6.Physical.J_involution]
