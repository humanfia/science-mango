import M6RecipeIsometries

theorem M6.RecipeIsometries.conv_multiply : ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (a h : M6.RecipeIsometries.Block N), M6.Physical.conv N (M6.RecipeIsometries.multiply N u a) (M6.RecipeIsometries.multiply N u h) = M6.RecipeIsometries.multiply N u (M6.Physical.conv N a h) := by
  intro N _ u a h
  classical
  funext i
  change (∑ j : ZMod N, a ((↑(u⁻¹) : ZMod N) * j) * h ((↑(u⁻¹) : ZMod N) * (i - j))) =
    ∑ k : ZMod N, a k * h ((↑(u⁻¹) : ZMod N) * i - k)
  calc
    _ = ∑ k : ZMod N, a ((↑(u⁻¹) : ZMod N) * ((↑u : ZMod N) * k)) *
        h ((↑(u⁻¹) : ZMod N) * (i - (↑u : ZMod N) * k)) :=
      (Equiv.sum_comp u.mulLeft (fun j : ZMod N =>
        a ((↑(u⁻¹) : ZMod N) * j) * h ((↑(u⁻¹) : ZMod N) * (i - j)))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [mul_sub, ← mul_assoc]

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

theorem M6.RecipeIsometries.multiply_laws : ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (a : M6.RecipeIsometries.Block N), M6.RecipeIsometries.multiply N 1 a = a ∧ M6.RecipeIsometries.multiply N (u⁻¹) (M6.RecipeIsometries.multiply N u a) = a ∧ (M6.RecipeIsometries.multiply N u a = 0 ↔ a = 0) := by
  intro N inst u a
  have hinv : M6.RecipeIsometries.multiply N (u⁻¹) (M6.RecipeIsometries.multiply N u a) = a := by
    funext i
    simp [M6.RecipeIsometries.multiply, ← mul_assoc]
  refine ⟨?_, hinv, ?_⟩
  · funext i
    simp [M6.RecipeIsometries.multiply]
  · constructor
    · intro h
      calc
        a = M6.RecipeIsometries.multiply N (u⁻¹) (M6.RecipeIsometries.multiply N u a) := hinv.symm
        _ = M6.RecipeIsometries.multiply N (u⁻¹) 0 := congrArg (M6.RecipeIsometries.multiply N (u⁻¹)) h
        _ = 0 := rfl
    · intro h
      subst a
      rfl

theorem M6.RecipeIsometries.permutation_weight : ∀ (N : ℕ) [NeZero N] (e : Equiv.Perm (ZMod N)) (a : M6.RecipeIsometries.Block N), M6.Physical.weight N (fun i => a (e i)) = M6.Physical.weight N a := by
  change ∀ (N : ℕ) [NeZero N] (e : Equiv.Perm (ZMod N)) (a : M6.RecipeIsometries.Block N), M6.Physical.weight N (fun i => a (e i)) = M6.Physical.weight N a
  intro N _ e a
  classical
  unfold M6.Physical.weight
  apply Finset.card_bij (fun i _ => e i)
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
  · intro i hi j hj hij
    exact e.injective hij
  · intro j hj
    refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
    simpa using hj

theorem M6.RecipeIsometries.multiplied_boundary : ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (a b h : M6.RecipeIsometries.Block N), M6.Physical.boundary N (M6.RecipeIsometries.multiply N u a) (M6.RecipeIsometries.multiply N u b) (M6.RecipeIsometries.multiply N u h) = M6.RecipeIsometries.multiplyWord N u (M6.Physical.boundary N a b h) := by
  intro N _ u a b h
  simp only [M6.Physical.boundary, M6.RecipeIsometries.multiplyWord,
    M6.RecipeIsometries.conv_multiply]

theorem M6.RecipeIsometries.multiplied_syndrome : ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (a b : M6.RecipeIsometries.Block N) (z : M6.RecipeIsometries.Word N), M6.Physical.syndrome N (M6.RecipeIsometries.multiply N u a) (M6.RecipeIsometries.multiply N u b) (M6.RecipeIsometries.multiplyWord N u z) = M6.RecipeIsometries.multiply N u (M6.Physical.syndrome N a b z) := by
  intro N _ u a b z
  unfold M6.Physical.syndrome M6.RecipeIsometries.multiplyWord
  dsimp only
  rw [M6.RecipeIsometries.conv_multiply, M6.RecipeIsometries.conv_multiply]
  rfl

theorem M6.RecipeIsometries.multiplied_weight : ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (z : M6.RecipeIsometries.Word N), M6.Physical.wordWeight N (M6.RecipeIsometries.multiplyWord N u z) = M6.Physical.wordWeight N z := by
  change ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (z : M6.RecipeIsometries.Word N), M6.Physical.wordWeight N (M6.RecipeIsometries.multiplyWord N u z) = M6.Physical.wordWeight N z
  intro N _ u z
  exact congrArg₂ Nat.add
    (M6.RecipeIsometries.permutation_weight N (u⁻¹).mulLeft z.1)
    (M6.RecipeIsometries.permutation_weight N (u⁻¹).mulLeft z.2)
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.RecipeIsometries.Block N) (u : (ZMod N)ˣ), Function.Bijective (M6.RecipeIsometries.multiplier N u) ∧ ∀ v : M6.Pinned.Vector (2*N), ((M6.RecipeIsometries.multiplier N u) v ∈ M6.Spaces.boundaryWords N (M6.RecipeIsometries.multiply N u a) (M6.RecipeIsometries.multiply N u b) ↔ v ∈ M6.Spaces.boundaryWords N a b) ∧ ((M6.RecipeIsometries.multiplier N u) v ∈ M6.Spaces.cycleWords N (M6.RecipeIsometries.multiply N u a) (M6.RecipeIsometries.multiply N u b) ↔ v ∈ M6.Spaces.cycleWords N a b) ∧ M6.Pinned.weight ((M6.RecipeIsometries.multiplier N u) v) = M6.Pinned.weight v
