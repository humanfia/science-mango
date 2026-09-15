import FrozenTarget_f69ef01da26b3c6b
theorem M7.PrefixBits.right_step : QuantumHarnessFrozenTarget := by
  by
    classical
    intro N hN p bit hlo hhi
    change p.length < 2 * (N - 1) at hhi
    dsimp only
    have hs : ∀ (offset : ℕ) (q : List Bool) (k : ℕ),
        k + 1 ∈ M7.PrefixBits.selected N offset q ↔
          k < N - 1 ∧ offset + k < q.length ∧ q.getD (offset + k) false = true := by
      intro offset q k
      simp [M7.PrefixBits.selected, Finset.mem_image]
    have hu : ∀ (offset : ℕ) (q : List Bool) (k : ℕ),
        k + 1 ∈ M7.PrefixBits.undecided N offset q ↔
          k < N - 1 ∧ q.length ≤ offset + k := by
      intro offset q k
      simp [M7.PrefixBits.undecided, Finset.mem_image]
    have hget : ∀ (q : List Bool) (i : ℕ), i < q.length →
        (q ++ [bit]).getD i false = q.getD i false := by
      intro q i hi
      exact List.getD_append q [bit] false i hi
    have hend : ∀ (q : List Bool), (q ++ [bit]).getD q.length false = bit := by
      intro q
      rw [List.getD_append_right q [bit] false q.length (Nat.le_refl _)]
      simp
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change p.length - (N - 1) + 1 ∈ M7.PrefixBits.undecided N (N - 1) p
      rw [hu]
      constructor <;> omega
    · apply Finset.ext
      intro x
      cases x with
      | zero => simp [M7.PrefixBits.A, M7.PrefixBits.selected]
      | succ k =>
        change k + 1 ∈ M7.PrefixBits.A N (p ++ [bit]) ↔ k + 1 ∈ M7.PrefixBits.A N p
        by_cases hk : k < N - 1
        · have hp : k < p.length := by omega
          have hp' : k < p.length + 1 := by omega
          simp [M7.PrefixBits.A, hs, hk, hp, hp', hget p k hp]
        · simp [M7.PrefixBits.A, hs, hk]
    · apply Finset.ext
      intro x
      cases x with
      | zero =>
        cases bit <;> simp [M7.PrefixBits.B, M7.PrefixBits.selected]
      | succ k =>
        change k + 1 ∈ M7.PrefixBits.B N (p ++ [bit]) ↔
          k + 1 ∈ (if bit then insert (p.length - (N - 1) + 1) (M7.PrefixBits.B N p) else M7.PrefixBits.B N p)
        by_cases hi : N - 1 + k < p.length
        · have hi' : N - 1 + k < p.length + 1 := by omega
          have hne : k ≠ p.length - (N - 1) := by omega
          cases bit <;>
            simp [M7.PrefixBits.B, hs, hi, hi', hne, hget p (N - 1 + k) hi]
        · by_cases he : N - 1 + k = p.length
          · have hk : k < N - 1 := by omega
            have hj : k = p.length - (N - 1) := by omega
            cases bit <;> simp [M7.PrefixBits.B, hs, he, hk, hj, hend]
          · have hi' : ¬ N - 1 + k < p.length + 1 := by omega
            have hne : k ≠ p.length - (N - 1) := by omega
            cases bit <;> simp [M7.PrefixBits.B, hs, hi, hi', hne]
    · apply Finset.ext
      intro x
      cases x with
      | zero => simp [M7.PrefixBits.WA, M7.PrefixBits.undecided]
      | succ k =>
        change k + 1 ∈ M7.PrefixBits.WA N (p ++ [bit]) ↔ k + 1 ∈ M7.PrefixBits.WA N p
        simp only [M7.PrefixBits.WA, hu, List.length_append, List.length_singleton, zero_add]
        omega
    · apply Finset.ext
      intro x
      cases x with
      | zero => simp [M7.PrefixBits.WB, M7.PrefixBits.undecided]
      | succ k =>
        change k + 1 ∈ M7.PrefixBits.WB N (p ++ [bit]) ↔
          k + 1 ∈ (M7.PrefixBits.WB N p).erase (p.length - (N - 1) + 1)
        simp only [Finset.mem_erase, M7.PrefixBits.WB, hu, List.length_append, List.length_singleton]
        omega
