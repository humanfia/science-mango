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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), (M6.Character.subspaceWords (M6.Spaces.D N a b)).card = (M6.Spaces.boundaryWords N a b).card
