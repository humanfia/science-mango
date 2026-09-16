import M8MixedNonproduct

theorem M8.MixedNonproduct.mixed_obstruction : ∀ (N : ℕ) [NeZero N], 7 ≤ N → (M7.Supports.indicator (M8.MixedFamily.left N),M7.Supports.indicator (M8.MixedFamily.right N)) ∈ M8.MixedNonproduct.Cycles (M8.MixedFamily.recipe N) ∧ (0,0) ∈ M8.MixedNonproduct.Cycles (M8.MixedFamily.recipe N) ∧ (M7.Supports.indicator (M8.MixedFamily.left N),0) ∉ M8.MixedNonproduct.Cycles (M8.MixedFamily.recipe N) := by
  classical
  intro N inst hN
  have hsmall (k : ℕ) (hk : 0 < k) (hk' : k ≤ 4) : (k : ZMod N) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    have hkN : k < N := by omega
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt hkN] at hv
    omega
  have h1 : (1 : ZMod N) ≠ 0 := by simpa using hsmall 1 (by omega) (by omega)
  have h2 : (2 : ZMod N) ≠ 0 := by simpa using hsmall 2 (by omega) (by omega)
  have h3 : (3 : ZMod N) ≠ 0 := by simpa using hsmall 3 (by omega) (by omega)
  have hn12 : (-1 : ZMod N) ≠ 2 := by
    intro h
    have he := congrArg (fun x : ZMod N => x + 1) h
    norm_num at he
    exact h3 he.symm
  have hn21 : (-2 : ZMod N) ≠ 1 := by
    intro h
    have he := congrArg (fun x : ZMod N => x + 2) h
    norm_num at he
    exact h3 he.symm
  have hp : ∀ j : ZMod N, j ≠ 0 →
      M7.Supports.indicator (M8.MixedFamily.left N) j *
        M7.Supports.indicator (M8.MixedFamily.right N) (-j) = 0 := by
    intro j hj
    by_cases hj1 : j = 1
    · subst j
      simp [M7.Supports.indicator, M8.MixedFamily.left, M8.MixedFamily.right, hn12, h1]
    · simp [M7.Supports.indicator, M8.MixedFamily.left, hj, hj1]
  have hq : ∀ j : ZMod N, j ≠ 0 →
      M7.Supports.indicator (M8.MixedFamily.right N) j *
        M7.Supports.indicator (M8.MixedFamily.left N) (-j) = 0 := by
    intro j hj
    by_cases hj2 : j = 2
    · subst j
      simp [M7.Supports.indicator, M8.MixedFamily.left, M8.MixedFamily.right, hn21, h2]
    · simp [M7.Supports.indicator, M8.MixedFamily.right, hj, hj2]
  have hs : (∑ j : ZMod N, M7.Supports.indicator (M8.MixedFamily.left N) j *
      M7.Supports.indicator (M8.MixedFamily.right N) (-j)) = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp [M7.Supports.indicator, M8.MixedFamily.left, M8.MixedFamily.right]
    · intro j _ hj
      exact hp j hj
    · simp
  have ht : (∑ j : ZMod N, M7.Supports.indicator (M8.MixedFamily.right N) j *
      M7.Supports.indicator (M8.MixedFamily.left N) (-j)) = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp [M7.Supports.indicator, M8.MixedFamily.left, M8.MixedFamily.right]
    · intro j _ hj
      exact hq j hj
    · simp
  refine ⟨?_, ?_, ?_⟩
  · change M6.Physical.syndrome N
        (M7.Supports.indicator (M8.MixedFamily.left N))
        (M7.Supports.indicator (M8.MixedFamily.right N))
        (M7.Supports.indicator (M8.MixedFamily.left N),
         M7.Supports.indicator (M8.MixedFamily.right N)) = 0
    unfold M6.Physical.syndrome
    rw [M6.Physical.conv_comm N (M7.Supports.indicator (M8.MixedFamily.left N))
      (M7.Supports.indicator (M8.MixedFamily.right N))]
    ext i
    have hc : ∀ x : ZMod 2, x + x = 0 := by decide
    exact hc _
  · change M6.Physical.syndrome N
        (M7.Supports.indicator (M8.MixedFamily.left N))
        (M7.Supports.indicator (M8.MixedFamily.right N)) (0, 0) = 0
    ext i
    simp [M6.Physical.syndrome, M6.Physical.conv]
  · intro hz
    change M6.Physical.syndrome N
        (M7.Supports.indicator (M8.MixedFamily.left N))
        (M7.Supports.indicator (M8.MixedFamily.right N))
        (M7.Supports.indicator (M8.MixedFamily.left N), 0) = 0 at hz
    have he := congrArg (fun f => f 0) hz
    simpa [M6.Physical.syndrome, M6.Physical.conv, hs, ht] using he

theorem M8.MixedNonproduct.product_rectangular : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M8.MixedNonproduct.Product c ↔ ∀ z ∈ M8.MixedNonproduct.Cycles c, ∀ t ∈ M8.MixedNonproduct.Cycles c, (z.1,t.2) ∈ M8.MixedNonproduct.Cycles c := by
  intro N inst c
  unfold M8.MixedNonproduct.Product
  constructor
  · rintro ⟨U, V, h⟩ z hz t ht
    rw [h] at hz ht ⊢
    exact ⟨hz.1, ht.2⟩
  · intro h
    refine ⟨{x | ∃ y, (x, y) ∈ M8.MixedNonproduct.Cycles c},
      {y | ∃ x, (x, y) ∈ M8.MixedNonproduct.Cycles c}, ?_⟩
    apply Set.ext
    intro z
    change z ∈ M8.MixedNonproduct.Cycles c ↔
      (∃ y, (z.1, y) ∈ M8.MixedNonproduct.Cycles c) ∧
      (∃ x, (x, z.2) ∈ M8.MixedNonproduct.Cycles c)
    constructor
    · intro hz
      exact ⟨⟨z.2, hz⟩, ⟨z.1, hz⟩⟩
    · rintro ⟨⟨y, hy⟩, ⟨x, hx⟩⟩
      exact h (z.1, y) hy (x, z.2) hx

theorem M8.MixedNonproduct.word_action : ∀ (N : ℕ) [NeZero N], ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N), Function.Bijective (M8.MixedNonproduct.wordAction g) ∧ ∀ z : M6.Physical.Word N, M8.MixedNonproduct.wordAction g z ∈ M8.MixedNonproduct.Cycles (M7.Action.act g c) ↔ z ∈ M8.MixedNonproduct.Cycles c := by
  classical
  intro N _ g c
  have hi := M7.Transport.action_isometry N g c
  have hf : Function.Injective (M6.Flatten.flatten N) := by
    first
    | exact Function.LeftInverse.injective (M6.Flatten.flatten_left N)
    | exact Function.LeftInverse.injective (M6.Flatten.flatten_right N)
  have hw : ∀ z : M6.Physical.Word N,
      M6.Flatten.flatten N (M8.MixedNonproduct.wordAction g z) =
        M7.Transport.Xmap g (M6.Flatten.flatten N z) := by
    intro z
    cases he : g.exchange <;>
      simp [M8.MixedNonproduct.wordAction, M7.Transport.Xmap,
        M6.RecipeIsometries.translate, M6.RecipeIsometries.multiplier,
        M6.RecipeIsometries.blockExchange, M6.RecipeIsometries.lift,
        M6.Flatten.flatten_left, M6.Flatten.flatten_right, he]
  constructor
  · have hinj : Function.Injective (M8.MixedNonproduct.wordAction g) := by
      intro x y h
      apply hf
      apply hi.1.1
      rw [← hw x, ← hw y, h]
    exact ⟨hinj, Finite.surjective_of_injective hinj⟩
  · intro z
    have hc := (hi.2 (M6.Flatten.flatten N z)).2.1
    rw [← hw z] at hc
    simpa [M7.Transport.CX, M8.MixedNonproduct.Cycles,
      M6.Spaces.cycle_words_iff, M6.Flatten.flatten_left,
      M6.Flatten.flatten_right] using hc

theorem M8.MixedNonproduct.product_action : ∀ (N : ℕ) [NeZero N], ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N), M8.MixedNonproduct.Product (M7.Action.act g c) ↔ M8.MixedNonproduct.Product c := by
  classical
  intro N inst g c
  have forward : ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N),
      M8.MixedNonproduct.Product c → M8.MixedNonproduct.Product (M7.Action.act g c) := by
    intro g c hc
    have hr := (M8.MixedNonproduct.product_rectangular N c).mp hc
    obtain ⟨hb, hw⟩ := M8.MixedNonproduct.word_action N g c
    apply (M8.MixedNonproduct.product_rectangular N (M7.Action.act g c)).mpr
    intro z hz t ht
    obtain ⟨x, rfl⟩ := hb.2 z
    obtain ⟨y, rfl⟩ := hb.2 t
    have hx := (hw x).mp hz
    have hy := (hw y).mp ht
    cases he : g.exchange
    · have hcross : M8.MixedNonproduct.wordAction g (x.1, y.2) =
          ((M8.MixedNonproduct.wordAction g x).1,
           (M8.MixedNonproduct.wordAction g y).2) := by
        simp [M8.MixedNonproduct.wordAction, he,
          M6.RecipeIsometries.translateWord, M6.RecipeIsometries.multiplyWord,
          M6.RecipeIsometries.exchange]
      rw [← hcross]
      exact (hw (x.1, y.2)).mpr (hr x hx y hy)
    · have hcross : M8.MixedNonproduct.wordAction g (y.1, x.2) =
          ((M8.MixedNonproduct.wordAction g x).1,
           (M8.MixedNonproduct.wordAction g y).2) := by
        simp [M8.MixedNonproduct.wordAction, he,
          M6.RecipeIsometries.translateWord, M6.RecipeIsometries.multiplyWord,
          M6.RecipeIsometries.exchange]
      rw [← hcross]
      exact (hw (y.1, x.2)).mpr (hr y hy x hx)
  constructor
  · intro h
    have hi := forward (M7.Action.inverse g) (M7.Action.act g c) h
    rw [M7.Action.act_inverse N g c] at hi
    exact hi
  · exact forward g c

theorem M8.MixedNonproduct.orbit_nonproduct : ∀ (N : ℕ) [NeZero N], 7 ≤ N → ∀ g : M7.Action.Record N, ¬ M8.MixedNonproduct.Product (M7.Action.act g (M8.MixedFamily.recipe N)) := by
  intro N inst hN g hprod
  have hp := (M8.MixedNonproduct.product_action N g (M8.MixedFamily.recipe N)).mp hprod
  have hr := (M8.MixedNonproduct.product_rectangular N (M8.MixedFamily.recipe N)).mp hp
  obtain ⟨hab, hzero, hnot⟩ := M8.MixedNonproduct.mixed_obstruction N hN
  exact hnot (hr _ hab _ hzero)
#print axioms M8.MixedNonproduct.mixed_obstruction
#print axioms M8.MixedNonproduct.product_rectangular
#print axioms M8.MixedNonproduct.word_action
#print axioms M8.MixedNonproduct.product_action
#print axioms M8.MixedNonproduct.orbit_nonproduct
