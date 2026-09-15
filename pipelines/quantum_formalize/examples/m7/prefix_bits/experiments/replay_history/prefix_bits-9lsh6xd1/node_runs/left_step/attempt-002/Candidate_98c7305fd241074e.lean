import FrozenTarget_98c7305fd241074e
theorem M7.PrefixBits.left_step : QuantumHarnessFrozenTarget := by
  intro N hN p bit hp
  classical
   dsimp only
  have hs (offset : ℕ) (q : List Bool) (k : ℕ) :
      k + 1 ∈ M7.PrefixBits.selected N offset q ↔
        k < N - 1 ∧ offset + k < q.length ∧ q.getD (offset + k) false = true := by
    simp [M7.PrefixBits.selected, Finset.mem_image]
  have hu (offset : ℕ) (q : List Bool) (k : ℕ) :
      k + 1 ∈ M7.PrefixBits.undecided N offset q ↔
        k < N - 1 ∧ q.length ≤ offset + k := by
    simp [M7.PrefixBits.undecided, Finset.mem_image]
  have hg (k : ℕ) :
      (k < p.length + 1 ∧ (p ++ [bit]).getD k false = true) ↔
        (k < p.length ∧ p.getD k false = true) ∨ (k = p.length ∧ bit = true) := by
    by_cases hk : k < p.length
    · rw [List.getD_append p [bit] false k hk]
      have hne : k ≠ p.length := by omega
      have hlt : k < p.length + 1 := by omega
      simp [hk, hne, hlt]
    · by_cases he : k = p.length
      · subst k
        rw [List.getD_append_right p [bit] false p.length (by omega)]
        simp
      · have hlt : ¬k < p.length + 1 := by omega
        simp [hk, he, hlt]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change p.length + 1 ∈ M7.PrefixBits.undecided N 0 p
    exact (hu 0 p p.length).2 ⟨hp, by omega⟩
  · cases bit <;> ext x <;> cases x with
    | zero => simp [M7.PrefixBits.A, M7.PrefixBits.selected]
    | succ k =>
        simp [M7.PrefixBits.A, Nat.succ_eq_add_one, hs,
          List.length_append, hg] <;> omega
  · ext x
    cases x with
    | zero => simp [M7.PrefixBits.B, M7.PrefixBits.selected]
    | succ k =>
        simp only [M7.PrefixBits.B, Nat.succ_eq_add_one, hs,
          List.length_append, List.length_singleton]
        omega
  · ext x
    cases x with
    | zero =>
        simp [M7.PrefixBits.WA, M7.PrefixBits.undecided, Finset.mem_image]
    | succ k =>
        simp only [M7.PrefixBits.WA, Nat.succ_eq_add_one, Finset.mem_erase,
          hu, List.length_append, List.length_singleton]
        omega
  · ext x
    cases x with
    | zero =>
        simp [M7.PrefixBits.WB, M7.PrefixBits.undecided, Finset.mem_image]
    | succ k =>
        simp only [M7.PrefixBits.WB, Nat.succ_eq_add_one, hu,
          List.length_append, List.length_singleton]
        omega
