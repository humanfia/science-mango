import FrozenTarget_77102b34978cbd22
theorem M7.PrefixBits.left_step : QuantumHarnessFrozenTarget := by
  by
    classical
    unfold QuantumHarnessFrozenTarget
    intro N hN p bit hp
    dsimp only
    have hs (o : ℕ) (q : List Bool) (k : ℕ) :
        k + 1 ∈ M7.PrefixBits.selected N o q ↔
          k < N - 1 ∧ o + k < q.length ∧ q.getD (o + k) false = true := by
      simp [M7.PrefixBits.selected, Finset.mem_image]
    have hu (o : ℕ) (q : List Bool) (k : ℕ) :
        k + 1 ∈ M7.PrefixBits.undecided N o q ↔
          k < N - 1 ∧ q.length ≤ o + k := by
      simp [M7.PrefixBits.undecided, Finset.mem_image]
    have hend : (p ++ [bit]).getD p.length false = bit := by
      rw [List.getD_append_right p [bit] false p.length (Nat.le_refl _)]
      simp
    have hstep (k : ℕ) :
        (k < N - 1 ∧ k < (p ++ [bit]).length ∧
          (p ++ [bit]).getD k false = true) ↔
        (k = p.length ∧ bit = true) ∨
          (k < N - 1 ∧ k < p.length ∧ p.getD k false = true) := by
      by_cases hk : k < p.length
      · have hne : k ≠ p.length := by omega
        have hka : k < (p ++ [bit]).length := by
          simp only [List.length_append, List.length_singleton]
          omega
        rw [List.getD_append p [bit] false k hk]
        simp [hk, hne, hka]
      · by_cases he : k = p.length
        · subst k
          simp [hp, hend]
        · have hka : ¬ k < (p ++ [bit]).length := by
            simp only [List.length_append, List.length_singleton]
            omega
          simp [hk, he, hka]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change p.length + 1 ∈ M7.PrefixBits.undecided N 0 p
      exact (hu 0 p p.length).mpr ⟨hp, by omega⟩
    · cases bit <;> apply Finset.ext <;> intro x <;> cases x with
      | zero =>
          simp [M7.PrefixBits.A, M7.PrefixBits.selected, Finset.mem_image]
      | succ k =>
          simp [M7.PrefixBits.A, Nat.succ_eq_add_one, hs, hstep,
            eq_comm, or_comm]
    · apply Finset.ext
      intro x
      cases x with
      | zero =>
          simp [M7.PrefixBits.B, M7.PrefixBits.selected, Finset.mem_image]
      | succ k =>
          have hbefore : ¬ N - 1 + k < p.length := by omega
          have hafter : ¬ N - 1 + k < (p ++ [bit]).length := by
            simp only [List.length_append, List.length_singleton]
            omega
          simp [M7.PrefixBits.B, Nat.succ_eq_add_one, hs, hbefore, hafter]
    · apply Finset.ext
      intro x
      cases x with
      | zero =>
          simp [M7.PrefixBits.WA, M7.PrefixBits.undecided, Finset.mem_image]
      | succ k =>
          simp only [M7.PrefixBits.WA, Nat.succ_eq_add_one, Finset.mem_erase,
            hu, Nat.zero_add, List.length_append, List.length_singleton]
          omega
    · apply Finset.ext
      intro x
      cases x with
      | zero =>
          simp [M7.PrefixBits.WB, M7.PrefixBits.undecided, Finset.mem_image]
      | succ k =>
          simp only [M7.PrefixBits.WB, Nat.succ_eq_add_one, hu,
            List.length_append, List.length_singleton]
          omega
