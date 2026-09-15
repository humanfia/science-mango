import M6RecipeIsometries

theorem M6.RecipeIsometries.exchange_laws : ∀ (N : ℕ) [NeZero N] (a b h : M6.RecipeIsometries.Block N) (z : M6.RecipeIsometries.Word N), M6.Physical.boundary N b a h = M6.RecipeIsometries.exchange N (M6.Physical.boundary N a b h) ∧ M6.Physical.syndrome N b a (M6.RecipeIsometries.exchange N z) = M6.Physical.syndrome N a b z := by
  intro N inst a b h z
  constructor
  · rfl
  · unfold M6.Physical.syndrome M6.RecipeIsometries.exchange
    funext i
    exact add_comm _ _

theorem M6.RecipeIsometries.exchange_weight : ∀ (N : ℕ) [NeZero N] (z : M6.RecipeIsometries.Word N), M6.Physical.wordWeight N (M6.RecipeIsometries.exchange N z) = M6.Physical.wordWeight N z := by
  intro N inst z
  change M6.Physical.weight N z.2 + M6.Physical.weight N z.1 = M6.Physical.weight N z.1 + M6.Physical.weight N z.2
  exact Nat.add_comm _ _

theorem M6.RecipeIsometries.lift_transport : ∀ (N : ℕ) [NeZero N] (a b a1 b1 : M6.RecipeIsometries.Block N) (P : M6.RecipeIsometries.Word N → M6.RecipeIsometries.Word N) (H : M6.RecipeIsometries.Block N → M6.RecipeIsometries.Block N), Function.Bijective P → Function.Surjective H → (∀ h, M6.Physical.boundary N a1 b1 (H h) = P (M6.Physical.boundary N a b h)) → (∀ z, M6.Physical.syndrome N a1 b1 (P z) = 0 ↔ M6.Physical.syndrome N a b z = 0) → (∀ z, M6.Physical.wordWeight N (P z) = M6.Physical.wordWeight N z) → Function.Bijective (M6.RecipeIsometries.lift N P) ∧ ∀ v : M6.Pinned.Vector (2*N), ((M6.RecipeIsometries.lift N P) v ∈ M6.Spaces.boundaryWords N (a1) (b1) ↔ v ∈ M6.Spaces.boundaryWords N a b) ∧ ((M6.RecipeIsometries.lift N P) v ∈ M6.Spaces.cycleWords N (a1) (b1) ↔ v ∈ M6.Spaces.cycleWords N a b) ∧ M6.Pinned.weight ((M6.RecipeIsometries.lift N P) v) = M6.Pinned.weight v := by
  intro N inst a b a1 b1 P H hP hH hB hC hW
  have hf : Function.Injective (M6.Flatten.flatten N) := by
    intro x y h
    have h' := congrArg (M6.Flatten.unflatten N) h
    simpa only [M6.Flatten.flatten_left] using h'
  have hu : Function.Injective (M6.Flatten.unflatten N) := by
    intro x y h
    have h' := congrArg (M6.Flatten.flatten N) h
    simpa only [M6.Flatten.flatten_right] using h'
  constructor
  · constructor
    · intro x y h
      apply hu
      apply hP.1
      apply hf
      exact h
    · intro v
      obtain ⟨z, hz⟩ := hP.2 (M6.Flatten.unflatten N v)
      refine ⟨M6.Flatten.flatten N z, ?_⟩
      simp only [M6.RecipeIsometries.lift, M6.Flatten.flatten_left, hz,
        M6.Flatten.flatten_right]
  · intro v
    constructor
    · rw [M6.Spaces.boundary_words_iff, M6.Spaces.boundary_words_iff]
      constructor
      · rintro ⟨k, hk⟩
        obtain ⟨h, rfl⟩ := hH k
        rw [hB h] at hk
        change M6.Flatten.flatten N (P (M6.Physical.boundary N a b h)) =
          M6.Flatten.flatten N (P (M6.Flatten.unflatten N v)) at hk
        have he := hP.1 (hf hk)
        refine ⟨h, ?_⟩
        exact (congrArg (M6.Flatten.flatten N) he).trans
          (M6.Flatten.flatten_right N v)
      · rintro ⟨h, hh⟩
        have he : M6.Physical.boundary N a b h = M6.Flatten.unflatten N v := by
          have he' := congrArg (M6.Flatten.unflatten N) hh
          simpa only [M6.Flatten.flatten_left] using he'
        refine ⟨H h, ?_⟩
        rw [hB h, he]
        rfl
    · constructor
      · simp only [M6.Spaces.cycle_words_iff, M6.RecipeIsometries.lift,
          M6.Flatten.flatten_left]
        exact hC (M6.Flatten.unflatten N v)
      · change M6.Pinned.weight
          (M6.Flatten.flatten N (P (M6.Flatten.unflatten N v))) =
          M6.Pinned.weight v
        rw [M6.Flatten.flatten_weight, hW]
        calc
          M6.Physical.wordWeight N (M6.Flatten.unflatten N v) =
              M6.Pinned.weight (M6.Flatten.flatten N (M6.Flatten.unflatten N v)) :=
            (M6.Flatten.flatten_weight N (M6.Flatten.unflatten N v)).symm
          _ = M6.Pinned.weight v := by rw [M6.Flatten.flatten_right]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.RecipeIsometries.Block N), Function.Bijective (M6.RecipeIsometries.blockExchange N) ∧ ∀ v : M6.Pinned.Vector (2*N), ((M6.RecipeIsometries.blockExchange N) v ∈ M6.Spaces.boundaryWords N (b) (a) ↔ v ∈ M6.Spaces.boundaryWords N a b) ∧ ((M6.RecipeIsometries.blockExchange N) v ∈ M6.Spaces.cycleWords N (b) (a) ↔ v ∈ M6.Spaces.cycleWords N a b) ∧ M6.Pinned.weight ((M6.RecipeIsometries.blockExchange N) v) = M6.Pinned.weight v
