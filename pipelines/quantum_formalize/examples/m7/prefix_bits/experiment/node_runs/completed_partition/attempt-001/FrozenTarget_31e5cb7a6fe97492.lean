import M7PrefixBits

theorem M7.PrefixBits.base : ∀ (N : ℕ), 0 < N → ∀ p : List Bool, M7.PrefixCompleted.Base N (M7.PrefixBits.A N p) (M7.PrefixBits.B N p) (M7.PrefixBits.WA N p) (M7.PrefixBits.WB N p) := by
  change ∀ (N : ℕ), 0 < N → ∀ p : List Bool, M7.PrefixCompleted.Base N (M7.PrefixBits.A N p) (M7.PrefixBits.B N p) (M7.PrefixBits.WA N p) (M7.PrefixBits.WB N p)
  intro N hN p
  classical
  have hs (o : ℕ) : M7.PrefixBits.selected N o p ⊆ Finset.range N := by
    intro x hx
    simp only [M7.PrefixBits.selected, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hx
    apply Finset.mem_range.mpr
    rcases hx with rfl | ⟨j, ⟨hj, _⟩, rfl⟩
    · exact hN
    · omega
  have hu (o : ℕ) : M7.PrefixBits.undecided N o p ⊆ Finset.range N := by
    intro x hx
    simp only [M7.PrefixBits.undecided, Finset.mem_image,
      Finset.mem_filter, Finset.mem_range] at hx
    rcases hx with ⟨j, ⟨hj, _⟩, rfl⟩
    apply Finset.mem_range.mpr
    omega
  have hz (o : ℕ) : 0 ∈ M7.PrefixBits.selected N o p := by
    simp [M7.PrefixBits.selected]
  have hd (o : ℕ) : Disjoint (M7.PrefixBits.selected N o p) (M7.PrefixBits.undecided N o p) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [M7.PrefixBits.selected, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hx
    simp only [M7.PrefixBits.undecided, Finset.mem_image,
      Finset.mem_filter, Finset.mem_range] at hy
    rcases hy with ⟨k, ⟨hk, hku⟩, hke⟩
    rcases hx with hx | ⟨j, ⟨hj, hjd, hjb⟩, hje⟩
    · omega
    · omega
  have hs0 := hs 0
  have hs1 := hs (N - 1)
  have hu0 := hu 0
  have hu1 := hu (N - 1)
  have hz0 := hz 0
  have hz1 := hz (N - 1)
  have hd0 := hd 0
  have hd1 := hd (N - 1)
  unfold M7.PrefixCompleted.Base
  simp only [M7.PrefixBits.A, M7.PrefixBits.B, M7.PrefixBits.WA, M7.PrefixBits.WB]
  aesop

theorem M7.PrefixBits.left_step : ∀ (N : ℕ), 0 < N → ∀ (p : List Bool) (bit : Bool), p.length < N-1 → let j := p.length+1; j ∈ M7.PrefixBits.WA N p ∧ M7.PrefixBits.A N (p ++ [bit]) = (if bit then insert j (M7.PrefixBits.A N p) else M7.PrefixBits.A N p) ∧ M7.PrefixBits.B N (p ++ [bit]) = M7.PrefixBits.B N p ∧ M7.PrefixBits.WA N (p ++ [bit]) = (M7.PrefixBits.WA N p).erase j ∧ M7.PrefixBits.WB N (p ++ [bit]) = M7.PrefixBits.WB N p := by
  intro N hN p bit hp
  dsimp only
  classical
  have hg : ∀ (q : List Bool) (k : ℕ),
      (q ++ [bit]).getD k false =
        if k < q.length then q.getD k false else if k = q.length then bit else false := by
    intro q
    induction q with
    | nil =>
        intro k
        cases k <;> simp [List.getD]
    | cons a q ih =>
        intro k
        cases k with
        | zero => simp [List.getD]
        | succ k => simpa [List.getD] using ih k
  have hs : ∀ (q : List Bool) (off k : ℕ),
      k + 1 ∈ M7.PrefixBits.selected N off q ↔
        k < N - 1 ∧ off + k < q.length ∧ q.getD (off + k) false = true := by
    intros q off k
    simp [M7.PrefixBits.selected, Finset.mem_image]
  have hu : ∀ (q : List Bool) (off k : ℕ),
      k + 1 ∈ M7.PrefixBits.undecided N off q ↔
        k < N - 1 ∧ q.length ≤ off + k := by
    intros q off k
    simp [M7.PrefixBits.undecided, Finset.mem_image]
  have hs0 : ∀ (q : List Bool) (off : ℕ),
      0 ∈ M7.PrefixBits.selected N off q := by
    intros q off
    simp [M7.PrefixBits.selected]
  have hu0 : ∀ (q : List Bool) (off : ℕ),
      0 ∉ M7.PrefixBits.undecided N off q := by
    intros q off
    simp [M7.PrefixBits.undecided, Finset.mem_image]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [M7.PrefixBits.WA, hu] using hp
  · apply Finset.ext
    intro x
    cases x with
    | zero => cases bit <;> simp [M7.PrefixBits.A, hs0]
    | succ k =>
        change (k + 1 ∈ M7.PrefixBits.A N (p ++ [bit])) ↔ _
        by_cases hk : k < p.length
        · have he : k ≠ p.length := by omega
          have he' : k + 1 ≠ p.length + 1 := by omega
          have hl : k < p.length + 1 := by omega
          cases bit <;>
            simp [M7.PrefixBits.A, hs, hg, hk, he, he', hl]
        · by_cases he : k = p.length
          · subst k
            cases bit <;> simp [M7.PrefixBits.A, hs, hg, hp]
          · have he' : k + 1 ≠ p.length + 1 := by omega
            have hl : ¬ k < p.length + 1 := by omega
            cases bit <;>
              simp [M7.PrefixBits.A, hs, hg, hk, he, he', hl]
  · apply Finset.ext
    intro x
    cases x with
    | zero => simp [M7.PrefixBits.B, hs0]
    | succ k =>
        change (k + 1 ∈ M7.PrefixBits.B N (p ++ [bit])) ↔ _
        have h0 : ¬ N - 1 + k < p.length := by omega
        have h1 : ¬ N - 1 + k < p.length + 1 := by omega
        simp [M7.PrefixBits.B, hs, h0, h1]
  · apply Finset.ext
    intro x
    cases x with
    | zero => simp [M7.PrefixBits.WA, hu0]
    | succ k =>
        change (k + 1 ∈ M7.PrefixBits.WA N (p ++ [bit])) ↔ _
        simp only [M7.PrefixBits.WA, Finset.mem_erase, hu,
          List.length_append, List.length_singleton, zero_add]
        omega
  · apply Finset.ext
    intro x
    cases x with
    | zero => simp [M7.PrefixBits.WB, hu0]
    | succ k =>
        change (k + 1 ∈ M7.PrefixBits.WB N (p ++ [bit])) ↔ _
        simp only [M7.PrefixBits.WB, hu, List.length_append, List.length_singleton]
        omega

theorem M7.PrefixBits.right_step : ∀ (N : ℕ), 0 < N → ∀ (p : List Bool) (bit : Bool), N-1 ≤ p.length → p.length < M7.PrefixBits.depth N → let j := p.length-(N-1)+1; j ∈ M7.PrefixBits.WB N p ∧ M7.PrefixBits.A N (p ++ [bit]) = M7.PrefixBits.A N p ∧ M7.PrefixBits.B N (p ++ [bit]) = (if bit then insert j (M7.PrefixBits.B N p) else M7.PrefixBits.B N p) ∧ M7.PrefixBits.WA N (p ++ [bit]) = M7.PrefixBits.WA N p ∧ M7.PrefixBits.WB N (p ++ [bit]) = (M7.PrefixBits.WB N p).erase j := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ), 0 < N → ∀ (p : List Bool) (bit : Bool), N-1 ≤ p.length → p.length < M7.PrefixBits.depth N → let j := p.length-(N-1)+1; j ∈ M7.PrefixBits.WB N p ∧ M7.PrefixBits.A N (p ++ [bit]) = M7.PrefixBits.A N p ∧ M7.PrefixBits.B N (p ++ [bit]) = (if bit then insert j (M7.PrefixBits.B N p) else M7.PrefixBits.B N p) ∧ M7.PrefixBits.WA N (p ++ [bit]) = M7.PrefixBits.WA N p ∧ M7.PrefixBits.WB N (p ++ [bit]) = (M7.PrefixBits.WB N p).erase j
  )
  change QuantumHarnessFrozenTarget
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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (w : ℕ) (E : Finset M5.BinaryPolynomial) (p : List Bool), p.length < M7.PrefixBits.depth N → M7.PrefixBits.completed N w E p = M7.PrefixBits.completed N w E (p ++ [false]) ∪ M7.PrefixBits.completed N w E (p ++ [true]) ∧ Disjoint (M7.PrefixBits.completed N w E (p ++ [false])) (M7.PrefixBits.completed N w E (p ++ [true]))
