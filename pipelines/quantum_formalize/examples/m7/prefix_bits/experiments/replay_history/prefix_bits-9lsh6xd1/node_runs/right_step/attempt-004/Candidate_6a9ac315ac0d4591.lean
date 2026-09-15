import FrozenTarget_6a9ac315ac0d4591
theorem M7.PrefixBits.right_step : QuantumHarnessFrozenTarget := by
  by
    classical
    intro N hN p bit hlo hhi
    change p.length < 2 * (N - 1) at hhi
    dsimp only
    have hs (o : ℕ) (q : List Bool) (k : ℕ) :
        k + 1 ∈ M7.PrefixBits.selected N o q ↔
          k < N - 1 ∧ o + k < q.length ∧ q.getD (o + k) false = true := by
      simp [M7.PrefixBits.selected, Finset.mem_image]
    have hw (o : ℕ) (q : List Bool) (k : ℕ) :
        k + 1 ∈ M7.PrefixBits.undecided N o q ↔
          k < N - 1 ∧ q.length ≤ o + k := by
      simp [M7.PrefixBits.undecided, Finset.mem_image]
    have hlast : (p ++ [bit]).getD p.length false = bit := by
      rw [List.getD_append_right p [bit] false p.length (by omega)]
      simp
    have hb (k : ℕ) :
        (k < N - 1 ∧ N - 1 + k < p.length + 1 ∧
          (p ++ [bit]).getD (N - 1 + k) false = true) ↔
        ((bit = true ∧ k + 1 = p.length - (N - 1) + 1) ∨
          (k < N - 1 ∧ N - 1 + k < p.length ∧
            p.getD (N - 1 + k) false = true)) := by
      by_cases ht : N - 1 + k < p.length
      · rw [List.getD_append p [bit] false (N - 1 + k) ht]
        omega
      · by_cases he : N - 1 + k = p.length
        · rw [he, hlast]
          cases bit <;> simp only [Bool.false_eq_true, Bool.true_eq_true] <;> omega
        · omega
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change p.length - (N - 1) + 1 ∈ M7.PrefixBits.undecided N (N - 1) p
      apply (hw (N - 1) p (p.length - (N - 1))).2
      omega
    · apply Finset.ext
      intro x
      cases x with
      | zero => simp [M7.PrefixBits.A, M7.PrefixBits.selected]
      | succ k =>
        change k + 1 ∈ M7.PrefixBits.selected N 0 (p ++ [bit]) ↔
          k + 1 ∈ M7.PrefixBits.selected N 0 p
        rw [hs, hs]
        simp only [Nat.zero_add, List.length_append, List.length_singleton]
        by_cases hk : k < N - 1
        · have ht : k < p.length := by omega
          have ht' : k < p.length + 1 := by omega
          rw [List.getD_append p [bit] false k ht]
          simp only [hk, ht, ht', true_and]
        · simp only [hk, false_and]
    · apply Finset.ext
      intro x
      cases x with
      | zero =>
        cases bit <;> simp [M7.PrefixBits.B, M7.PrefixBits.selected]
      | succ k =>
        change k + 1 ∈ M7.PrefixBits.selected N (N - 1) (p ++ [bit]) ↔
          k + 1 ∈ (if bit then insert (p.length - (N - 1) + 1)
            (M7.PrefixBits.selected N (N - 1) p)
          else M7.PrefixBits.selected N (N - 1) p)
        rw [hs]
        simp only [List.length_append, List.length_singleton]
        rw [hb]
        cases bit <;> simp [hs]
    · apply Finset.ext
      intro x
      cases x with
      | zero => simp [M7.PrefixBits.WA, M7.PrefixBits.undecided]
      | succ k =>
        change k + 1 ∈ M7.PrefixBits.undecided N 0 (p ++ [bit]) ↔
          k + 1 ∈ M7.PrefixBits.undecided N 0 p
        rw [hw, hw]
        simp only [Nat.zero_add, List.length_append, List.length_singleton]
        omega
    · apply Finset.ext
      intro x
      cases x with
      | zero => simp [M7.PrefixBits.WB, M7.PrefixBits.undecided]
      | succ k =>
        change k + 1 ∈ M7.PrefixBits.undecided N (N - 1) (p ++ [bit]) ↔
          k + 1 ∈ (M7.PrefixBits.undecided N (N - 1) p).erase
            (p.length - (N - 1) + 1)
        rw [Finset.mem_erase, hw, hw]
        simp only [List.length_append, List.length_singleton]
        omega
