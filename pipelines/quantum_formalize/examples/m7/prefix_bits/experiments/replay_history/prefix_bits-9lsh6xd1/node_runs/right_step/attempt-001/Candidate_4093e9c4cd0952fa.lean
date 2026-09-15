import FrozenTarget_4093e9c4cd0952fa
theorem M7.PrefixBits.right_step : QuantumHarnessFrozenTarget := by
  intro N hN p bit hlo hhi
  dsimp only
  unfold M7.PrefixBits.depth at hhi
  have hget : ∀ (q : List Bool) (i : ℕ), i < q.length →
      (q ++ [bit]).getD i false = q.getD i false := by
    intro q
    induction q with
    | nil => simp
    | cons a q ih =>
      intro i hi
      cases i with
      | zero => rfl
      | succ i => exact ih i (by simpa using hi)
  have hend : ∀ q : List Bool, (q ++ [bit]).getD q.length false = bit := by
    intro q
    induction q with
    | nil => rfl
    | cons a q ih => exact ih
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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [M7.PrefixBits.WB, hu]
    constructor <;> omega
  · apply Finset.ext
    intro x
    cases x with
    | zero => simp [M7.PrefixBits.A, M7.PrefixBits.selected]
    | succ k =>
      change (k + 1 ∈ M7.PrefixBits.selected N 0 (p ++ [bit])) ↔
        (k + 1 ∈ M7.PrefixBits.selected N 0 p)
      rw [hs, hs]
      by_cases hk : k < N - 1
      · have hp : k < p.length := by omega
        have hp' : k < p.length + 1 := by omega
        simp [hk, hp, hp', hget p k hp]
      · simp [hk]
  · apply Finset.ext
    intro x
    cases x with
    | zero =>
      cases bit <;> simp [M7.PrefixBits.B, M7.PrefixBits.selected]
    | succ k =>
      change (k + 1 ∈ M7.PrefixBits.B N (p ++ [bit])) ↔
        (k + 1 ∈ (if bit then insert (p.length - (N - 1) + 1)
          (M7.PrefixBits.B N p) else M7.PrefixBits.B N p))
      by_cases hi : N - 1 + k < p.length
      · have hi' : N - 1 + k < p.length + 1 := by omega
        have hne : k + 1 ≠ p.length - (N - 1) + 1 := by omega
        cases bit <;>
          simp [M7.PrefixBits.B, hs, hi, hi', hne, hget p (N - 1 + k) hi]
      · by_cases he : N - 1 + k = p.length
        · have hk : k < N - 1 := by omega
          cases bit <;>
            simp [M7.PrefixBits.B, hs, hi, he, hk, hend] <;> omega
        · have hi' : ¬ N - 1 + k < p.length + 1 := by omega
          have hne : k + 1 ≠ p.length - (N - 1) + 1 := by omega
          cases bit <;> simp [M7.PrefixBits.B, hs, hi, hi', hne]
  · apply Finset.ext
    intro x
    cases x with
    | zero => simp [M7.PrefixBits.WA, M7.PrefixBits.undecided]
    | succ k =>
      change (k + 1 ∈ M7.PrefixBits.undecided N 0 (p ++ [bit])) ↔
        (k + 1 ∈ M7.PrefixBits.undecided N 0 p)
      simp only [hu, List.length_append, List.length_singleton, Nat.zero_add]
      omega
  · apply Finset.ext
    intro x
    cases x with
    | zero => simp [M7.PrefixBits.WB, M7.PrefixBits.undecided]
    | succ k =>
      change (k + 1 ∈ M7.PrefixBits.undecided N (N - 1) (p ++ [bit])) ↔
        (k + 1 ∈ (M7.PrefixBits.undecided N (N - 1) p).erase
          (p.length - (N - 1) + 1))
      simp only [Finset.mem_erase, hu, List.length_append, List.length_singleton]
      omega
