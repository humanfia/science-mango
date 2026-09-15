import FrozenTarget_33b76e1b4d30aacb
theorem M7.PrefixBits.left_step : QuantumHarnessFrozenTarget := by
  by
    classical
    unfold QuantumHarnessFrozenTarget
    intro N hN p bit hp
    dsimp only
    have hget : ∀ (q : List Bool) (b : Bool) (i : ℕ), i < q.length →
        (q ++ [b]).getD i false = q.getD i false := by
      intro q
      induction q with
      | nil =>
          intro b i hi
          simp at hi
      | cons a q ih =>
          intro b i hi
          cases i with
          | zero => rfl
          | succ i =>
              exact ih b i (by simpa using hi)
    have hlast : ∀ (q : List Bool) (b : Bool),
        (q ++ [b]).getD q.length false = b := by
      intro q b
      induction q with
      | nil => rfl
      | cons a q ih =>
          change (q ++ [b]).getD q.length false = b
          exact ih
    have hs : ∀ (offset : ℕ) (q : List Bool) (k : ℕ),
        k + 1 ∈ M7.PrefixBits.selected N offset q ↔
          k < N - 1 ∧ offset + k < q.length ∧
            q.getD (offset + k) false = true := by
      intro offset q k
      simp [M7.PrefixBits.selected, Finset.mem_image]
    have hu : ∀ (offset : ℕ) (q : List Bool) (k : ℕ),
        k + 1 ∈ M7.PrefixBits.undecided N offset q ↔
          k < N - 1 ∧ q.length ≤ offset + k := by
      intro offset q k
      simp [M7.PrefixBits.undecided, Finset.mem_image]
    have hstep : ∀ k : ℕ,
        (k < p.length + 1 ∧ (p ++ [bit]).getD k false = true) ↔
          (k < p.length ∧ p.getD k false = true) ∨
            (k = p.length ∧ bit = true) := by
      intro k
      rcases lt_trichotomy k p.length with hk | hk | hk
      · have hk' : k < p.length + 1 := by omega
        have hne : k ≠ p.length := by omega
        simp [hk, hk', hne, hget p bit k hk]
      · subst k
        simp [hlast]
      · have hnot : ¬ k < p.length := by omega
        have hnot' : ¬ k < p.length + 1 := by omega
        have hne : k ≠ p.length := by omega
        simp [hnot, hnot', hne]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [M7.PrefixBits.WA, hu] using hp
    · apply Finset.ext
      intro x
      cases x with
      | zero =>
          cases bit <;>
            simp [M7.PrefixBits.A, M7.PrefixBits.selected]
      | succ k =>
          change k + 1 ∈ M7.PrefixBits.A N (p ++ [bit]) ↔
            k + 1 ∈ (if bit then insert (p.length + 1) (M7.PrefixBits.A N p)
                      else M7.PrefixBits.A N p)
          cases bit <;>
            simp [M7.PrefixBits.A, hs, hstep] <;> omega
    · apply Finset.ext
      intro x
      cases x with
      | zero => simp [M7.PrefixBits.B, M7.PrefixBits.selected]
      | succ k =>
          have h₁ : ¬ N - 1 + k < p.length := by omega
          have h₂ : ¬ N - 1 + k < p.length + 1 := by omega
          change k + 1 ∈ M7.PrefixBits.B N (p ++ [bit]) ↔
            k + 1 ∈ M7.PrefixBits.B N p
          simp [M7.PrefixBits.B, hs, h₁, h₂]
    · apply Finset.ext
      intro x
      cases x with
      | zero =>
          simp [M7.PrefixBits.WA, M7.PrefixBits.undecided]
      | succ k =>
          change k + 1 ∈ M7.PrefixBits.WA N (p ++ [bit]) ↔
            k + 1 ∈ (M7.PrefixBits.WA N p).erase (p.length + 1)
          simp [M7.PrefixBits.WA, hu]
          omega
    · apply Finset.ext
      intro x
      cases x with
      | zero => simp [M7.PrefixBits.WB, M7.PrefixBits.undecided]
      | succ k =>
          change k + 1 ∈ M7.PrefixBits.WB N (p ++ [bit]) ↔
            k + 1 ∈ M7.PrefixBits.WB N p
          simp [M7.PrefixBits.WB, hu]
          omega
