import FrozenTarget_06829853bcbf8d10
theorem M7.PrefixBits.right_step : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N hN p bit hlo hhi
  dsimp only
  simp only [M7.PrefixBits.depth] at hhi
  have hget : ∀ (q : List Bool) (i : ℕ),
      (q ++ [bit]).getD i false =
        if i < q.length then q.getD i false else if i = q.length then bit else false := by
    intro q
    induction q with
    | nil => intro i; cases i <;> simp [List.getD]
    | cons a q ih =>
      intro i
      cases i with
      | zero => simp [List.getD]
      | succ i => simpa [List.getD] using ih i
  have hs : ∀ (o : ℕ) (q : List Bool) (k : ℕ),
      k + 1 ∈ M7.PrefixBits.selected N o q ↔
        k < N - 1 ∧ o + k < q.length ∧ q.getD (o + k) false = true := by
    intro o q k
    simp [M7.PrefixBits.selected, Finset.mem_image]
  have hw : ∀ (o : ℕ) (q : List Bool) (k : ℕ),
      k + 1 ∈ M7.PrefixBits.undecided N o q ↔
        k < N - 1 ∧ q.length ≤ o + k := by
    intro o q k
    simp [M7.PrefixBits.undecided, Finset.mem_image]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change p.length - (N - 1) + 1 ∈ M7.PrefixBits.undecided N (N - 1) p
    rw [hw]
    omega
  · apply Finset.ext
    intro x
    cases x with
    | zero => simp [M7.PrefixBits.A, M7.PrefixBits.selected]
    | succ k =>
      simp only [Nat.succ_eq_add_one, M7.PrefixBits.A, hs]
      by_cases hk : k < N - 1
      · have hkp : k < p.length := by omega
        simp [hk, hget, hkp]
      · simp [hk]
  · apply Finset.ext
    intro x
    cases x with
    | zero =>
      cases bit <;> simp [M7.PrefixBits.B, M7.PrefixBits.selected]
    | succ k =>
      simp only [Nat.succ_eq_add_one]
      have hk : k + 1 = p.length - (N - 1) + 1 ↔ N - 1 + k = p.length := by omega
      cases bit <;>
        by_cases hlt : N - 1 + k < p.length <;>
        by_cases heq : N - 1 + k = p.length <;>
        simp [M7.PrefixBits.B, hs, hget, hlt, heq, hk] <;> omega
  · apply Finset.ext
    intro x
    cases x with
    | zero => simp [M7.PrefixBits.WA, M7.PrefixBits.undecided]
    | succ k =>
      simp only [Nat.succ_eq_add_one, M7.PrefixBits.WA, hw,
        List.length_append, List.length_singleton, Nat.zero_add]
      omega
  · apply Finset.ext
    intro x
    cases x with
    | zero => simp [M7.PrefixBits.WB, M7.PrefixBits.undecided]
    | succ k =>
      simp only [Nat.succ_eq_add_one, M7.PrefixBits.WB,
        Finset.mem_erase, hw, List.length_append, List.length_singleton]
      omega
