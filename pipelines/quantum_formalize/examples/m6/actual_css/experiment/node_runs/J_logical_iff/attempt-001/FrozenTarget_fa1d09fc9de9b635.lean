import M6ActualCSS
import M6ActualCSSDependencies

theorem M6.ActualCSS.J_boundary_iff : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), ∀ v : M6.Pinned.Vector (2*N), v ∈ M6.Spaces.boundaryWords N a b ↔ M6.Flatten.J N v ∈ M6.Character.subspaceWords (M6.Spaces.D N a b) := by
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

theorem M6.ActualCSS.J_dot : ∀ (N : ℕ) [NeZero N] (v w : M6.Pinned.Vector (2*N)), M6.Character.dot (M6.Flatten.J N v) (M6.Flatten.J N w) = M6.Character.dot v w := by
  change ∀ (N : ℕ) [NeZero N] (v w : M6.Pinned.Vector (2*N)), M6.Character.dot (M6.Flatten.J N v) (M6.Flatten.J N w) = M6.Character.dot v w
  intro N _ v w
  have hrev (a b : M6.Physical.Block N) :
      M6.Physical.dot N (fun i => a (-i)) (fun i => b (-i)) =
        M6.Physical.dot N a b := by
    change (∑ i : ZMod N, a (-i) * b (-i)) = ∑ i : ZMod N, a i * b i
    exact Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ (fun _ => rfl)
  have hJ (z t : M6.Physical.Word N) :
      M6.Physical.pairing N (M6.Physical.J N z) (M6.Physical.J N t) =
        M6.Physical.pairing N z t := by
    change M6.Physical.dot N (fun i => z.2 (-i)) (fun i => t.2 (-i)) +
        M6.Physical.dot N (fun i => z.1 (-i)) (fun i => t.1 (-i)) =
      M6.Physical.dot N z.1 t.1 + M6.Physical.dot N z.2 t.2
    rw [hrev, hrev, add_comm]
  unfold M6.Flatten.J
  rw [M6.Flatten.flatten_dot, hJ]
  exact (by simpa only [M6.Flatten.flatten_right] using
    (M6.Flatten.flatten_dot N (M6.Flatten.unflatten N v)
      (M6.Flatten.unflatten N w)).symm)

theorem M6.ActualCSS.J_cycle_iff : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), ∀ v : M6.Pinned.Vector (2*N), v ∈ M6.Spaces.cycleWords N a b ↔ M6.Flatten.J N v ∈ M6.Character.dualWords (M6.Spaces.B N a b) := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (v : M6.Pinned.Vector (2*N)), v ∈ M6.Spaces.cycleWords N a b ↔ M6.Flatten.J N v ∈ M6.Character.dualWords (M6.Spaces.B N a b)
  intro N inst a b v
  classical
  have hmem :
      M6.Flatten.J N v ∈ M6.Character.dualWords (M6.Spaces.B N a b) ↔
        ∀ h : M6.Physical.Block N,
          M6.Character.dot (M6.Spaces.boundary N a b h) (M6.Flatten.J N v) = 0 := by
    unfold M6.Character.dualWords
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, M6.Character.Orthogonal, M6.Spaces.B, LinearMap.mem_range]
    constructor
    · intro hh h
      exact hh _ ⟨h, rfl⟩
    · intro hh q hq
      rcases hq with ⟨h, rfl⟩
      exact hh h
  have hpair (h : M6.Physical.Block N) :
      M6.Character.dot (M6.Flatten.flatten N (M6.Physical.J N (M6.Physical.boundary N a b h))) v =
        M6.Character.dot (M6.Spaces.boundary N a b h) (M6.Flatten.J N v) := by
    have hJ :
        M6.Flatten.flatten N (M6.Physical.J N (M6.Physical.boundary N a b h)) =
          M6.Flatten.J N (M6.Spaces.boundary N a b h) := by
      rw [M6.Spaces.boundary_eval]
      simp only [M6.Flatten.J, M6.Flatten.flatten_left]
    rw [hJ]
    simpa only [M6.Flatten.J_involution] using
      (M6.ActualCSS.J_dot N (M6.Spaces.boundary N a b h) (M6.Flatten.J N v))
  rw [M6.Spaces.cycle_words_iff, M6.Flatten.cycle_orthogonal, hmem]
  simp only [hpair]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), ∀ v : M6.Pinned.Vector (2*N), v ∈ M6.CSS.logical (M6.Spaces.boundaryWords N a b) (M6.Spaces.cycleWords N a b) ↔ M6.Flatten.J N v ∈ M6.CSS.logical (M6.Character.subspaceWords (M6.Spaces.D N a b)) (M6.Character.dualWords (M6.Spaces.B N a b))
