import M6SpacesReady

theorem M6.Spaces.boundary_eval : ∀ (N : ℕ) [NeZero N] (a b h : M6.Physical.Block N), M6.Spaces.boundary N a b h = M6.Flatten.flatten N (M6.Physical.boundary N a b h) := by
  intro N inst a b h
  rfl

theorem M6.Spaces.dual_boundary_eval : ∀ (N : ℕ) [NeZero N] (a b h : M6.Physical.Block N), M6.Spaces.dualBoundary N a b h = M6.Flatten.flatten N (M6.Physical.J N (M6.Physical.boundary N a b h)) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (a b h : M6.Physical.Block N), M6.Spaces.dualBoundary N a b h = M6.Flatten.flatten N (M6.Physical.J N (M6.Physical.boundary N a b h))
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst a b h
  rfl

theorem M6.Spaces.input_card : ∀ (N : ℕ) [NeZero N], Nat.card (M6.Physical.Block N) = 2^N := by
  intro N inst
  change Nat.card (ZMod N → ZMod 2) = 2 ^ N
  simp [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]

theorem M6.Spaces.boundary_words_iff : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (v : M6.Pinned.Vector (2*N)), v ∈ M6.Spaces.boundaryWords N a b ↔ ∃ h : M6.Physical.Block N, M6.Flatten.flatten N (M6.Physical.boundary N a b h) = v := by
  intro N inst a b v
  classical
  simp [M6.Spaces.boundaryWords, M6.Character.subspaceWords, M6.Spaces.B,
    LinearMap.mem_range, M6.Spaces.boundary_eval]

theorem M6.Spaces.cycle_words_iff : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (v : M6.Pinned.Vector (2*N)), v ∈ M6.Spaces.cycleWords N a b ↔ M6.Physical.syndrome N a b (M6.Flatten.unflatten N v) = 0 := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (v : M6.Pinned.Vector (2*N)), v ∈ M6.Spaces.cycleWords N a b ↔ M6.Physical.syndrome N a b (M6.Flatten.unflatten N v) = 0
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst a b v
  classical
  change v ∈ Finset.filter (M6.Character.Orthogonal (M6.Spaces.dualBoundary N a b).range) Finset.univ ↔ _
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  change (∀ q, q ∈ (M6.Spaces.dualBoundary N a b).range → M6.Character.dot q v = 0) ↔ _
  rw [M6.Flatten.cycle_orthogonal]
  constructor
  · intro hv h
    exact hv _ ⟨h, rfl⟩
  · intro hv q hq
    obtain ⟨h, rfl⟩ := hq
    exact hv h

theorem M6.Spaces.boundaries_are_cycles : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), M6.Spaces.boundaryWords N a b ⊆ M6.Spaces.cycleWords N a b := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), M6.Spaces.boundaryWords N a b ⊆ M6.Spaces.cycleWords N a b
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst a b v hv
  obtain ⟨h, rfl⟩ := (M6.Spaces.boundary_words_iff N a b v).mp hv
  apply (M6.Spaces.cycle_words_iff N a b _).mpr
  rw [M6.Flatten.flatten_left]
  exact M6.Physical.boundary_cycle N a b h

theorem M6.Spaces.dual_boundary_card : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), (M6.Character.subspaceWords (M6.Spaces.D N a b)).card = (M6.Spaces.boundaryWords N a b).card := by
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

theorem M6.Spaces.logical_words_iff : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (v : M6.Pinned.Vector (2*N)), v ∈ M6.Spaces.logicalWords N a b ↔ M6.Physical.syndrome N a b (M6.Flatten.unflatten N v) = 0 ∧ ¬ ∃ h : M6.Physical.Block N, M6.Flatten.flatten N (M6.Physical.boundary N a b h) = v := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (v : M6.Pinned.Vector (2*N)), v ∈ M6.Spaces.logicalWords N a b ↔ M6.Physical.syndrome N a b (M6.Flatten.unflatten N v) = 0 ∧ ¬ ∃ h : M6.Physical.Block N, M6.Flatten.flatten N (M6.Physical.boundary N a b h) = v
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst a b v
  classical
  simp only [M6.Spaces.logicalWords, Finset.mem_sdiff,
    M6.Spaces.cycle_words_iff, M6.Spaces.boundary_words_iff]

theorem M6.Spaces.zero_not_logical : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), (0 : M6.Pinned.Vector (2*N)) ∉ M6.Spaces.logicalWords N a b := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), (0 : M6.Pinned.Vector (2*N)) ∉ M6.Spaces.logicalWords N a b
  intro N inst a b
  classical
  have hz : (0 : M6.Pinned.Vector (2*N)) ∈ M6.Spaces.boundaryWords N a b := by
    simpa [M6.Spaces.boundaryWords, M6.Character.subspaceWords] using
      (M6.Spaces.B N a b).zero_mem
  simpa [M6.Spaces.logicalWords, Finset.mem_sdiff, hz]
#print axioms M6.Spaces.boundary_eval
#print axioms M6.Spaces.boundary_words_iff
#print axioms M6.Spaces.dual_boundary_eval
#print axioms M6.Spaces.cycle_words_iff
#print axioms M6.Spaces.boundaries_are_cycles
#print axioms M6.Spaces.dual_boundary_card
#print axioms M6.Spaces.input_card
#print axioms M6.Spaces.logical_words_iff
#print axioms M6.Spaces.zero_not_logical
