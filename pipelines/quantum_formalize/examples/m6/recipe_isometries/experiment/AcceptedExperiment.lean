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

theorem M6.RecipeIsometries.exchange_isometry : ∀ (N : ℕ) [NeZero N] (a b : M6.RecipeIsometries.Block N), Function.Bijective (M6.RecipeIsometries.blockExchange N) ∧ ∀ v : M6.Pinned.Vector (2*N), ((M6.RecipeIsometries.blockExchange N) v ∈ M6.Spaces.boundaryWords N (b) (a) ↔ v ∈ M6.Spaces.boundaryWords N a b) ∧ ((M6.RecipeIsometries.blockExchange N) v ∈ M6.Spaces.cycleWords N (b) (a) ↔ v ∈ M6.Spaces.cycleWords N a b) ∧ M6.Pinned.weight ((M6.RecipeIsometries.blockExchange N) v) = M6.Pinned.weight v := by
  intro N inst a b
  have hinv : ∀ z : M6.RecipeIsometries.Word N,
      M6.RecipeIsometries.exchange N (M6.RecipeIsometries.exchange N z) = z := by
    intro z
    cases z
    rfl
  refine M6.RecipeIsometries.lift_transport N a b b a
    (M6.RecipeIsometries.exchange N) (fun h => h) ?_ ?_ ?_ ?_ ?_
  · constructor
    · intro x y h
      have he := congrArg (M6.RecipeIsometries.exchange N) h
      simpa only [hinv] using he
    · intro z
      exact ⟨M6.RecipeIsometries.exchange N z, hinv z⟩
  · intro h
    exact ⟨h, rfl⟩
  · intro h
    exact (M6.RecipeIsometries.exchange_laws N a b h (0 : M6.RecipeIsometries.Word N)).1
  · intro z
    rw [(M6.RecipeIsometries.exchange_laws N a b a z).2]
  · exact M6.RecipeIsometries.exchange_weight N

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

theorem M6.RecipeIsometries.multiplier_isometry : ∀ (N : ℕ) [NeZero N] (a b : M6.RecipeIsometries.Block N) (u : (ZMod N)ˣ), Function.Bijective (M6.RecipeIsometries.multiplier N u) ∧ ∀ v : M6.Pinned.Vector (2*N), ((M6.RecipeIsometries.multiplier N u) v ∈ M6.Spaces.boundaryWords N (M6.RecipeIsometries.multiply N u a) (M6.RecipeIsometries.multiply N u b) ↔ v ∈ M6.Spaces.boundaryWords N a b) ∧ ((M6.RecipeIsometries.multiplier N u) v ∈ M6.Spaces.cycleWords N (M6.RecipeIsometries.multiply N u a) (M6.RecipeIsometries.multiply N u b) ↔ v ∈ M6.Spaces.cycleWords N a b) ∧ M6.Pinned.weight ((M6.RecipeIsometries.multiplier N u) v) = M6.Pinned.weight v := by
  intro N inst a b u
  have hInv (t : (ZMod N)ˣ) (z : M6.RecipeIsometries.Word N) :
      M6.RecipeIsometries.multiplyWord N t⁻¹
        (M6.RecipeIsometries.multiplyWord N t z) = z := by
    apply Prod.ext
    · exact (M6.RecipeIsometries.multiply_laws N t z.1).2.1
    · exact (M6.RecipeIsometries.multiply_laws N t z.2).2.1
  refine M6.RecipeIsometries.lift_transport N a b
    (M6.RecipeIsometries.multiply N u a)
    (M6.RecipeIsometries.multiply N u b)
    (M6.RecipeIsometries.multiplyWord N u)
    (M6.RecipeIsometries.multiply N u) ?_ ?_ ?_ ?_ ?_
  · constructor
    · intro x y h
      calc
        x = M6.RecipeIsometries.multiplyWord N u⁻¹
            (M6.RecipeIsometries.multiplyWord N u x) := (hInv u x).symm
        _ = M6.RecipeIsometries.multiplyWord N u⁻¹
            (M6.RecipeIsometries.multiplyWord N u y) :=
          congrArg (M6.RecipeIsometries.multiplyWord N u⁻¹) h
        _ = y := hInv u y
    · intro z
      refine ⟨M6.RecipeIsometries.multiplyWord N u⁻¹ z, ?_⟩
      simpa only [inv_inv] using hInv u⁻¹ z
  · intro h
    refine ⟨M6.RecipeIsometries.multiply N u⁻¹ h, ?_⟩
    simpa only [inv_inv] using
      (M6.RecipeIsometries.multiply_laws N u⁻¹ h).2.1
  · exact M6.RecipeIsometries.multiplied_boundary N u a b
  · intro z
    rw [M6.RecipeIsometries.multiplied_syndrome]
    exact (M6.RecipeIsometries.multiply_laws N u
      (M6.Physical.syndrome N a b z)).2.2
  · exact M6.RecipeIsometries.multiplied_weight N u

theorem M6.RecipeIsometries.translation_isometry : ∀ (N : ℕ) [NeZero N] (a b : M6.RecipeIsometries.Block N) (r s : ZMod N), Function.Bijective (M6.RecipeIsometries.translate N r s) ∧ ∀ v : M6.Pinned.Vector (2*N), ((M6.RecipeIsometries.translate N r s) v ∈ M6.Spaces.boundaryWords N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s b) ↔ v ∈ M6.Spaces.boundaryWords N a b) ∧ ((M6.RecipeIsometries.translate N r s) v ∈ M6.Spaces.cycleWords N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s b) ↔ v ∈ M6.Spaces.cycleWords N a b) ∧ M6.Pinned.weight ((M6.RecipeIsometries.translate N r s) v) = M6.Pinned.weight v := by
  intro N inst a b r s
  have hinv (t u : ZMod N) (z : M6.RecipeIsometries.Word N) :
      M6.RecipeIsometries.translateWord N (-t) (-u)
        (M6.RecipeIsometries.translateWord N t u z) = z := by
    apply Prod.ext
    · exact (M6.RecipeIsometries.shift_laws N t z.1).2.1
    · exact (M6.RecipeIsometries.shift_laws N u z.2).2.1
  refine M6.RecipeIsometries.lift_transport N a b
    (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s b)
    (M6.RecipeIsometries.translateWord N r s) (fun h => h) ?_ ?_ ?_ ?_ ?_
  · constructor
    · intro x y h
      have he := congrArg (M6.RecipeIsometries.translateWord N (-r) (-s)) h
      simpa only [hinv] using he
    · intro z
      refine ⟨M6.RecipeIsometries.translateWord N (-r) (-s) z, ?_⟩
      simpa only [neg_neg] using hinv (-r) (-s) z
  · intro h
    exact ⟨h, rfl⟩
  · intro h
    exact M6.RecipeIsometries.translated_boundary N r s a b h
  · intro z
    rw [M6.RecipeIsometries.translated_syndrome]
    exact (M6.RecipeIsometries.shift_laws N (r + s)
      (M6.Physical.syndrome N a b z)).2.2
  · exact M6.RecipeIsometries.translated_weight N r s
#print axioms M6.RecipeIsometries.conv_multiply
#print axioms M6.RecipeIsometries.conv_shift
#print axioms M6.RecipeIsometries.exchange_laws
#print axioms M6.RecipeIsometries.exchange_weight
#print axioms M6.RecipeIsometries.lift_transport
#print axioms M6.RecipeIsometries.exchange_isometry
#print axioms M6.RecipeIsometries.multiplied_boundary
#print axioms M6.RecipeIsometries.multiplied_syndrome
#print axioms M6.RecipeIsometries.multiply_laws
#print axioms M6.RecipeIsometries.permutation_weight
#print axioms M6.RecipeIsometries.multiplied_weight
#print axioms M6.RecipeIsometries.multiplier_isometry
#print axioms M6.RecipeIsometries.shift_laws
#print axioms M6.RecipeIsometries.translated_boundary
#print axioms M6.RecipeIsometries.translated_syndrome
#print axioms M6.RecipeIsometries.translated_weight
#print axioms M6.RecipeIsometries.translation_isometry
