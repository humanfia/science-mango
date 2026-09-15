import FrozenTarget_1c86ad759d43abc4
theorem M7.PrefixBits.left_step : QuantumHarnessFrozenTarget := by
  by
    classical
    intro N hN p bit hp
    dsimp only
    have hs : ∀ (o : ℕ) (q : List Bool) (k : ℕ),
        k + 1 ∈ M7.PrefixBits.selected N o q ↔
          k < N - 1 ∧ o + k < q.length ∧ q.getD (o + k) false = true := by
      intro o q k
      simp [M7.PrefixBits.selected, Finset.mem_image]
    have hu : ∀ (o : ℕ) (q : List Bool) (k : ℕ),
        k + 1 ∈ M7.PrefixBits.undecided N o q ↔
          k < N - 1 ∧ q.length ≤ o + k := by
      intro o q k
      simp [M7.PrefixBits.undecided, Finset.mem_image]
    have hget : ∀ (q : List Bool) (b : Bool) (k : ℕ),
        k < q.length → (q ++ [b]).getD k false = q.getD k false := by
      intro q
      induction q with
      | nil =>
          intro b k hk
          simp at hk
      | cons a q ih =>
          intro b k hk
          cases k with
          | zero => simp [List.getD]
          | succ k =>
              have hk' : k < q.length := by simpa using hk
              simpa [List.getD] using ih b k hk'
    have hend : ∀ (q : List Bool) (b : Bool),
        (q ++ [b]).getD q.length false = b := by
      intro q
      induction q with
      | nil => intro b; simp [List.getD]
      | cons a q ih => intro b; simpa [List.getD] using ih b
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [M7.PrefixBits.WA, hu] using hp
    · apply Finset.ext
      intro x
      cases x with
      | zero =>
          cases bit <;>
            simp [M7.PrefixBits.A, M7.PrefixBits.selected, Finset.mem_image]
      | succ k =>
          change (k + 1 ∈ M7.PrefixBits.A N (p ++ [bit])) ↔
            k + 1 ∈ (if bit then insert (p.length + 1) (M7.PrefixBits.A N p)
              else M7.PrefixBits.A N p)
          by_cases hk : k < p.length
          · have hg := hget p bit k hk
            cases bit <;> simp [M7.PrefixBits.A, hs, hk, hg] <;> omega
          · by_cases he : k = p.length
            · subst k
              cases bit <;> simp [M7.PrefixBits.A, hs, hend, hp]
            · have hn : ¬ k < (p ++ [bit]).length := by
                simp only [List.length_append, List.length_singleton]
                omega
              cases bit <;> simp [M7.PrefixBits.A, hs, hk, hn] <;> omega
    · apply Finset.ext
      intro x
      cases x with
      | zero =>
          simp [M7.PrefixBits.B, M7.PrefixBits.selected, Finset.mem_image]
      | succ k =>
          have h₁ : ¬ N - 1 + k < p.length := by omega
          have h₂ : ¬ N - 1 + k < (p ++ [bit]).length := by
            simp only [List.length_append, List.length_singleton]
            omega
          change (k + 1 ∈ M7.PrefixBits.B N (p ++ [bit])) ↔
            k + 1 ∈ M7.PrefixBits.B N p
          simp [M7.PrefixBits.B, hs, h₁, h₂]
    · apply Finset.ext
      intro x
      cases x with
      | zero =>
          simp [M7.PrefixBits.WA, M7.PrefixBits.undecided, Finset.mem_image]
      | succ k =>
          change (k + 1 ∈ M7.PrefixBits.WA N (p ++ [bit])) ↔
            k + 1 ∈ (M7.PrefixBits.WA N p).erase (p.length + 1)
          simp [M7.PrefixBits.WA, hu, Finset.mem_erase]
          omega
    · apply Finset.ext
      intro x
      cases x with
      | zero =>
          simp [M7.PrefixBits.WB, M7.PrefixBits.undecided, Finset.mem_image]
      | succ k =>
          change (k + 1 ∈ M7.PrefixBits.WB N (p ++ [bit])) ↔
            k + 1 ∈ M7.PrefixBits.WB N p
          simp [M7.PrefixBits.WB, hu]
          omega
