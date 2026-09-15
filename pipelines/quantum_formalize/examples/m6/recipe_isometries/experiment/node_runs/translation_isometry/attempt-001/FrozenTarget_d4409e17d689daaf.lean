import M6RecipeIsometries

theorem M6.RecipeIsometries.conv_shift : ∀ (N : ℕ) [NeZero N] (r s : ZMod N) (a h : M6.RecipeIsometries.Block N), M6.Physical.conv N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s h) = M6.RecipeIsometries.shift N (r+s) (M6.Physical.conv N a h) := by
  intro N inst r s a h
  classical
  funext i
  change Finset.sum Finset.univ (fun k : ZMod N => a (k - r) * h (i - k - s)) =
    Finset.sum Finset.univ (fun k : ZMod N => a k * h (i - (r + s) - k))
  refine (Equiv.sum_comp (Equiv.addRight r)
    (fun k : ZMod N => a (k - r) * h (i - k - s))).symm.trans ?_
  change Finset.sum Finset.univ (fun k : ZMod N => a (k + r - r) * h (i - (k + r) - s)) = _
  apply Finset.sum_congr rfl
  intro k hk
  have hi : i - (k + r) - s = i - (r + s) - k := by ring
  simp only [add_sub_cancel_right, hi]

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

theorem M6.RecipeIsometries.shift_laws : ∀ (N : ℕ) [NeZero N] (r : ZMod N) (a : M6.RecipeIsometries.Block N), M6.RecipeIsometries.shift N 0 a = a ∧ M6.RecipeIsometries.shift N (-r) (M6.RecipeIsometries.shift N r a) = a ∧ (M6.RecipeIsometries.shift N r a = 0 ↔ a = 0) := by
  intro N inst r a
  have hinv (b : M6.RecipeIsometries.Block N) :
      M6.RecipeIsometries.shift N (-r) (M6.RecipeIsometries.shift N r b) = b := by
    funext i
    simp [M6.RecipeIsometries.shift, sub_eq_add_neg, add_assoc]
  refine ⟨?_, hinv a, ?_⟩
  · funext i
    simp [M6.RecipeIsometries.shift]
  · constructor
    · intro h
      calc
        a = M6.RecipeIsometries.shift N (-r) (M6.RecipeIsometries.shift N r a) := (hinv a).symm
        _ = M6.RecipeIsometries.shift N (-r) 0 := congrArg (M6.RecipeIsometries.shift N (-r)) h
        _ = 0 := rfl
    · intro h
      subst a
      rfl

theorem M6.RecipeIsometries.translated_boundary : ∀ (N : ℕ) [NeZero N] (r s : ZMod N) (a b h : M6.RecipeIsometries.Block N), M6.Physical.boundary N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s b) h = M6.RecipeIsometries.translateWord N r s (M6.Physical.boundary N a b h) := by
  intro N inst r s a b h
  have ha := M6.RecipeIsometries.conv_shift N r 0 a h
  have hb := M6.RecipeIsometries.conv_shift N s 0 b h
  simp only [(M6.RecipeIsometries.shift_laws N 0 h).1, add_zero] at ha hb
  simp only [M6.Physical.boundary, M6.RecipeIsometries.translateWord, ha, hb]

theorem M6.RecipeIsometries.translated_syndrome : ∀ (N : ℕ) [NeZero N] (r s : ZMod N) (a b : M6.RecipeIsometries.Block N) (z : M6.RecipeIsometries.Word N), M6.Physical.syndrome N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s b) (M6.RecipeIsometries.translateWord N r s z) = M6.RecipeIsometries.shift N (r+s) (M6.Physical.syndrome N a b z) := by
  intro N inst r s a b z
  change M6.Physical.conv N (M6.RecipeIsometries.shift N s b) (M6.RecipeIsometries.shift N r z.1) + M6.Physical.conv N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s z.2) = M6.RecipeIsometries.shift N (r + s) (M6.Physical.conv N b z.1 + M6.Physical.conv N a z.2)
  rw [M6.RecipeIsometries.conv_shift, M6.RecipeIsometries.conv_shift, add_comm s r]
  rfl

theorem M6.RecipeIsometries.translated_weight : ∀ (N : ℕ) [NeZero N] (r s : ZMod N) (z : M6.RecipeIsometries.Word N), M6.Physical.wordWeight N (M6.RecipeIsometries.translateWord N r s z) = M6.Physical.wordWeight N z := by
  intro N _ r s z
  change M6.Physical.weight N (M6.RecipeIsometries.shift N r z.1) + M6.Physical.weight N (M6.RecipeIsometries.shift N s z.2) = M6.Physical.weight N z.1 + M6.Physical.weight N z.2
  have h (t : ZMod N) (a : M6.RecipeIsometries.Block N) : M6.Physical.weight N (M6.RecipeIsometries.shift N t a) = M6.Physical.weight N a := by
    have hf : M6.RecipeIsometries.shift N t a = fun i => a ((Equiv.addRight (-t)) i) := by
      funext i
      exact congrArg a (sub_eq_add_neg i t)
    rw [hf]
    exact M6.RecipeIsometries.permutation_weight N (Equiv.addRight (-t)) a
  exact congrArg₂ (fun a b : ℕ => a + b) (h r z.1) (h s z.2)
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.RecipeIsometries.Block N) (r s : ZMod N), Function.Bijective (M6.RecipeIsometries.translate N r s) ∧ ∀ v : M6.Pinned.Vector (2*N), ((M6.RecipeIsometries.translate N r s) v ∈ M6.Spaces.boundaryWords N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s b) ↔ v ∈ M6.Spaces.boundaryWords N a b) ∧ ((M6.RecipeIsometries.translate N r s) v ∈ M6.Spaces.cycleWords N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s b) ↔ v ∈ M6.Spaces.cycleWords N a b) ∧ M6.Pinned.weight ((M6.RecipeIsometries.translate N r s) v) = M6.Pinned.weight v
