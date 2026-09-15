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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (v : M6.Pinned.Vector (2*N)), v ∈ M6.Spaces.logicalWords N a b ↔ M6.Physical.syndrome N a b (M6.Flatten.unflatten N v) = 0 ∧ ¬ ∃ h : M6.Physical.Block N, M6.Flatten.flatten N (M6.Physical.boundary N a b h) = v
