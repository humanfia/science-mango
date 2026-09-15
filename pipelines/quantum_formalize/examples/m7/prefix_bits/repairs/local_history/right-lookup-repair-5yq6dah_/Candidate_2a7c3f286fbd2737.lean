import FrozenTarget_2a7c3f286fbd2737
theorem M7.PrefixBits.right_step : QuantumHarnessFrozenTarget := by
    classical
    unfold QuantumHarnessFrozenTarget
    intro N hN p bit hlo hhi
    dsimp only
    unfold M7.PrefixBits.depth at hhi
    have lookup : ∀ (q : List Bool) (i : ℕ),
        (q ++ [bit]).getD i false =
          if i < q.length then q.getD i false else if i = q.length then bit else false := by
      intro q
      induction q with
      | nil =>
          intro i
          cases i <;> simp [List.getD]
      | cons a q ih =>
          intro i
          cases i with
          | zero => simp [List.getD]
          | succ i => simpa [List.getD] using ih i
    have ms : ∀ (o : ℕ) (q : List Bool) (k : ℕ),
        k + 1 ∈ M7.PrefixBits.selected N o q ↔
          k < N - 1 ∧ o + k < q.length ∧ q.getD (o + k) false = true := by
      intro o q k
      simp [M7.PrefixBits.selected, Finset.mem_image]
    have mu : ∀ (o : ℕ) (q : List Bool) (k : ℕ),
        k + 1 ∈ M7.PrefixBits.undecided N o q ↔
          k < N - 1 ∧ q.length ≤ o + k := by
      intro o q k
      simp [M7.PrefixBits.undecided, Finset.mem_image]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [M7.PrefixBits.WB, mu]
      constructor <;> omega
    · apply Finset.ext
      intro x
      cases x with
      | zero => simp [M7.PrefixBits.A, M7.PrefixBits.selected]
      | succ k =>
          change (k + 1 ∈ M7.PrefixBits.selected N 0 (p ++ [bit])) ↔
            (k + 1 ∈ M7.PrefixBits.selected N 0 p)
          rw [ms, ms]
          by_cases hk : k < N - 1
          · have hp : k < p.length := by omega
            have hp' : k < (p ++ [bit]).length := by
              simp only [List.length_append, List.length_singleton]
              omega
            simp only [Nat.zero_add, lookup, if_pos hp]
            have hle : k ≤ p.length := by omega
            simp [hk, hp, hle]
          · simp [hk]
    · apply Finset.ext
      intro x
      cases x with
      | zero =>
          cases bit <;> simp [M7.PrefixBits.B, M7.PrefixBits.selected]
      | succ k =>
          change (k + 1 ∈ M7.PrefixBits.B N (p ++ [bit])) ↔
            (k + 1 ∈ if bit then insert (p.length - (N - 1) + 1) (M7.PrefixBits.B N p)
              else M7.PrefixBits.B N p)
          by_cases hb : N - 1 + k < p.length
          · have hn : N - 1 + k < (p ++ [bit]).length := by
              simp only [List.length_append, List.length_singleton]
              omega
            have hj : k + 1 ≠ p.length - (N - 1) + 1 := by omega
            have hle : N - 1 + k ≤ p.length := by omega
            have hne : k ≠ p.length - (N - 1) := by omega
            cases bit <;>
              simp only [M7.PrefixBits.B, Bool.false_eq_true, if_false, if_true,
                Finset.mem_insert, ms, lookup, if_pos hb] <;>
              simp [hb, hle, hne]
          · by_cases he : N - 1 + k = p.length
            · have hk : k < N - 1 := by omega
              have hj : k + 1 = p.length - (N - 1) + 1 := by omega
              have hn : N - 1 + k < (p ++ [bit]).length := by
                simp only [List.length_append, List.length_singleton]
                omega
              cases bit <;>
                simp only [Bool.false_eq_true, if_false, if_true,
                  M7.PrefixBits.B, Finset.mem_insert, ms] <;>
                simp only [lookup] <;>
                simp [hb, he, hk, hj, hn]
            · have hn : ¬ N - 1 + k < (p ++ [bit]).length := by
                simp only [List.length_append, List.length_singleton]
                omega
              have hj : k + 1 ≠ p.length - (N - 1) + 1 := by omega
              have hne : k ≠ p.length - (N - 1) := by omega
              cases bit <;>
                simp only [M7.PrefixBits.B, Bool.false_eq_true, if_false, if_true,
                  Finset.mem_insert, ms, lookup, if_neg hb, if_neg he] <;>
                simp [hb, hne]
    · apply Finset.ext
      intro x
      cases x with
      | zero => simp [M7.PrefixBits.WA, M7.PrefixBits.undecided]
      | succ k =>
          change (k + 1 ∈ M7.PrefixBits.undecided N 0 (p ++ [bit])) ↔
            (k + 1 ∈ M7.PrefixBits.undecided N 0 p)
          simp only [mu, Nat.zero_add, List.length_append, List.length_singleton]
          omega
    · apply Finset.ext
      intro x
      cases x with
      | zero => simp [M7.PrefixBits.WB, M7.PrefixBits.undecided]
      | succ k =>
          change (k + 1 ∈ M7.PrefixBits.undecided N (N - 1) (p ++ [bit])) ↔
            (k + 1 ∈ (M7.PrefixBits.undecided N (N - 1) p).erase
              (p.length - (N - 1) + 1))
          simp only [Finset.mem_erase, mu, List.length_append, List.length_singleton]
          omega
