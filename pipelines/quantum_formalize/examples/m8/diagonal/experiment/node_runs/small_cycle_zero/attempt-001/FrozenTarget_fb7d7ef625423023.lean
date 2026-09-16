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

theorem M8.Diagonal.weight_one : ∀ (N : ℕ) [NeZero N], ∀ a : M6.Physical.Block N, M6.Physical.weight N a = 1 ↔ ∃ j : ZMod N, a = M6.Physical.delta N j := by
  change ∀ (N : ℕ) [NeZero N], ∀ a : M6.Physical.Block N, M6.Physical.weight N a = 1 ↔ ∃ j : ZMod N, a = M6.Physical.delta N j
  intro N inst a
  classical
  have bit_one : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by
    intro x
    fin_cases x
    · intro hx
      exact (hx rfl).elim
    · intro _
      rfl
  constructor
  · intro h
    change (Finset.univ.filter (fun i : ZMod N => a i ≠ 0)).card = 1 at h
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h
    have hs : ∀ i : ZMod N, a i ≠ 0 ↔ i = j := by
      intro i
      have hm := congrArg (fun s : Finset (ZMod N) => i ∈ s) hj
      simpa using hm
    refine ⟨j, ?_⟩
    funext i
    by_cases hij : i = j
    · subst i
      have hone : a j = 1 := bit_one (a j) ((hs j).mpr rfl)
      simpa [M6.Physical.delta] using hone
    · have hzero : a i = 0 := by
        by_contra hn
        exact hij ((hs i).mp hn)
      simp [M6.Physical.delta, hij, hzero]
  · rintro ⟨j, rfl⟩
    change (Finset.univ.filter (fun i : ZMod N => M6.Physical.delta N j i ≠ 0)).card = 1
    apply Finset.card_eq_one.mpr
    refine ⟨j, ?_⟩
    ext i
    by_cases hij : i = j
    · subst i
      simp [M6.Physical.delta]
    · simp [M6.Physical.delta, hij]

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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (p : M6.Physical.Block N) (z : M6.Physical.Word N), p ≠ 0 → M6.Physical.syndrome N p p z = 0 → M6.Physical.wordWeight N z < 2 → z = 0
