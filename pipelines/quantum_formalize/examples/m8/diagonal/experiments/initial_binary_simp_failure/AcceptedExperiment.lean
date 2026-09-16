import M8Diagonal

theorem M8.Diagonal.conv_delta : ∀ (N : ℕ) [NeZero N], ∀ (p : M6.Physical.Block N) (j i : ZMod N), M6.Physical.conv N p (M6.Physical.delta N j) i = p (i-j) := by
  intro N inst p j i
  classical
  unfold M6.Physical.conv M6.Physical.delta
  rw [Finset.sum_eq_single (i - j)]
  · simp
  · intro r hr hne
    have h : i - r ≠ j := by
      intro heq
      apply hne
      calc
        r = i - (i - r) := (sub_sub_cancel i r).symm
        _ = i - j := congrArg (fun x => i - x) heq
    simp [h, Ne.symm h]
  · simp

theorem M8.Diagonal.delta_weight : ∀ (N : ℕ) [NeZero N], ∀ j : ZMod N, M6.Physical.weight N (M6.Physical.delta N j) = 1 := by
  intro N inst j
  classical
  change (Finset.univ.filter (fun i : ZMod N => M6.Physical.delta N j i ≠ 0)).card = 1
  have h : Finset.univ.filter (fun i : ZMod N => M6.Physical.delta N j i ≠ 0) = {j} := by
    ext i
    by_cases hij : i = j
    · subst i
      simp [M6.Physical.delta]
    · simp [M6.Physical.delta, hij, Ne.symm hij]
  rw [h]
  simp

theorem M8.Diagonal.weight_zero : ∀ (N : ℕ) [NeZero N], ∀ a : M6.Physical.Block N, M6.Physical.weight N a = 0 ↔ a = 0 := by
  classical
  intro N inst a
  change (Finset.univ.filter (fun i : ZMod N => a i ≠ 0)).card = 0 ↔ a = 0
  constructor
  · intro h
    have hempty := Finset.card_eq_zero.mp h
    funext i
    change a i = 0
    by_contra hi
    have hmem : i ∈ Finset.univ.filter (fun j : ZMod N => a j ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    simp [hempty] at hmem
  · rintro rfl
    simp

theorem M8.Diagonal.diagonal_witness : ∀ (N : ℕ) [NeZero N], ∀ p : M6.Physical.Block N, M8.Diagonal.DeltaNotImage N p → (M6.Flatten.flatten N (M6.Physical.delta N 0, M6.Physical.delta N 0) ∈ M6.Spaces.logicalWords N p p ∧ M6.Pinned.weight (M6.Flatten.flatten N (M6.Physical.delta N 0, M6.Physical.delta N 0)) = 2) := by
  intro N inst p hp
  classical
  constructor
  · apply (M6.Spaces.logical_words_iff N p p _).2
    constructor
    · rw [M6.Flatten.flatten_left]
      funext i
      change M6.Physical.conv N p (M6.Physical.delta N 0) i + M6.Physical.conv N p (M6.Physical.delta N 0) i = 0
      have htwo : ∀ x : ZMod 2, x + x = 0 := by decide
      exact htwo _
    · rintro ⟨h, he⟩
      apply hp
      refine ⟨h, ?_⟩
      have hh := congrArg (fun v => (M6.Flatten.unflatten N v).1) he
      simpa only [M6.Flatten.flatten_left, M6.Physical.boundary] using hh
  · rw [M6.Flatten.flatten_weight]
    norm_num [M6.Physical.wordWeight, M8.Diagonal.delta_weight]
#print axioms M8.Diagonal.conv_delta
#print axioms M8.Diagonal.delta_weight
#print axioms M8.Diagonal.diagonal_witness
#print axioms M8.Diagonal.weight_zero
