import M7StreamingIndices

theorem M7.StreamingIndices.cursor_interval : ∀ (n : ℕ) (p : Fin n → Bool) (i fuel : ℕ), M7.StreamingIndices.allFinFrom n p i fuel = true ↔ ∀ j : Fin n, i ≤ j.val → j.val < i + fuel → p j = true := by
  change ∀ (n : ℕ) (p : Fin n → Bool) (i fuel : ℕ), M7.StreamingIndices.allFinFrom n p i fuel = true ↔ ∀ j : Fin n, i ≤ j.val → j.val < i + fuel → p j = true
  intro n p i fuel
  induction fuel generalizing i with
  | zero =>
      constructor
      · intro _ j hlo hhi
        omega
      · intro _
        rfl
  | succ fuel ih =>
      by_cases hi : i < n
      · by_cases hp : p ⟨i, hi⟩ = true
        · have hstep : M7.StreamingIndices.allFinFrom n p i (fuel + 1) = M7.StreamingIndices.allFinFrom n p (i + 1) fuel := by
            simp [M7.StreamingIndices.allFinFrom, hi, hp]
          rw [hstep, ih]
          constructor
          · intro h j hlo hhi
            by_cases hj : j.val = i
            · have heq : j = ⟨i, hi⟩ := Fin.ext hj
              simpa only [heq] using hp
            · exact h j (by omega) (by omega)
          · intro h j hlo hhi
            exact h j (by omega) (by omega)
        · constructor
          · intro h
            simp [M7.StreamingIndices.allFinFrom, hi, hp] at h
          · intro h
            exfalso
            apply hp
            exact h ⟨i, hi⟩ (by simp) (by dsimp; omega)
      · constructor
        · intro _ j hlo _
          have hj := j.isLt
          omega
        · intro _
          simp [M7.StreamingIndices.allFinFrom, hi]

theorem M7.StreamingIndices.record_surjective : ∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, ∃ (u : Fin (Fintype.card ((ZMod N)ˣ))) (e : Fin 2) (s t : Fin N), M7.StreamingIndices.decodeRecord N u e s t = g := by
  classical
  intro N inst g
  rcases g with ⟨v, b, s, t⟩
  cases b
  · refine ⟨Fintype.equivFin ((ZMod N)ˣ) v, 0, ⟨s.val, ZMod.val_lt s⟩, ⟨t.val, ZMod.val_lt t⟩, ?_⟩
    simp [M7.StreamingIndices.decodeRecord, ZMod.natCast_zmod_val]
  · refine ⟨Fintype.equivFin ((ZMod N)ˣ) v, 1, ⟨s.val, ZMod.val_lt s⟩, ⟨t.val, ZMod.val_lt t⟩, ?_⟩
    simp [M7.StreamingIndices.decodeRecord, ZMod.natCast_zmod_val]

theorem M7.StreamingIndices.all_fin : ∀ (n : ℕ) (p : Fin n → Bool), M7.StreamingIndices.allFin n p = true ↔ ∀ j : Fin n, p j = true := by
  change ∀ (n : ℕ) (p : Fin n → Bool), M7.StreamingIndices.allFin n p = true ↔ ∀ j : Fin n, p j = true
  intro n p
  unfold M7.StreamingIndices.allFin
  rw [M7.StreamingIndices.cursor_interval]
  constructor
  · intro h j
    exact h j (Nat.zero_le _) (by simpa only [Nat.zero_add] using j.isLt)
  · intro h j _ _
    exact h j

theorem M7.StreamingIndices.all_records : ∀ (N : ℕ) [NeZero N], ∀ p : M7.Action.Record N → Bool, M7.StreamingIndices.allRecords N p = true ↔ ∀ g : M7.Action.Record N, p g = true := by
  change ∀ (N : ℕ) [NeZero N], ∀ p : M7.Action.Record N → Bool, M7.StreamingIndices.allRecords N p = true ↔ ∀ g : M7.Action.Record N, p g = true
  intro N inst p
  unfold M7.StreamingIndices.allRecords
  simp only [M7.StreamingIndices.all_fin]
  constructor
  · intro h g
    rcases M7.StreamingIndices.record_surjective N g with ⟨u, e, s, t, hg⟩
    rw [← hg]
    exact h u e s t
  · intro h u e s t
    exact h (M7.StreamingIndices.decodeRecord N u e s t)

theorem M7.StreamingIndices.all_indices : ∀ (H N : ℕ) [NeZero N], ∀ p : M7.GlobalQuery.Index H N → Bool, M7.StreamingIndices.allIndices H N p = true ↔ ∀ x : M7.GlobalQuery.Index H N, p x = true := by
  change ∀ (H N : ℕ) [NeZero N], ∀ p : M7.GlobalQuery.Index H N → Bool, M7.StreamingIndices.allIndices H N p = true ↔ ∀ x : M7.GlobalQuery.Index H N, p x = true
  intro H N inst p
  unfold M7.StreamingIndices.allIndices
  simp only [M7.StreamingIndices.all_fin, M7.StreamingIndices.all_records]
  constructor
  · intro h x
    rcases x with ⟨i, g⟩
    exact h i g
  · intro h i g
    exact h (i, g)

theorem M7.StreamingIndices.stream_winners : ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (x : M7.GlobalQuery.Index H N), M7.StreamingIndices.streamWin q bases x = true ↔ x ∈ M7.GlobalQuery.winners q bases := by
  change ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (x : M7.GlobalQuery.Index H N), M7.StreamingIndices.streamWin q bases x = true ↔ x ∈ M7.GlobalQuery.winners q bases
  classical
  intro H N inst q bases x
  unfold M7.StreamingIndices.streamWin
  simp only [Bool.and_eq_true, M7.StreamingIndices.all_indices, decide_eq_true_eq]
  exact ((M7.GlobalQuery.winners_exact H N q bases).1 x).symm
#print axioms M7.StreamingIndices.cursor_interval
#print axioms M7.StreamingIndices.all_fin
#print axioms M7.StreamingIndices.record_surjective
#print axioms M7.StreamingIndices.all_records
#print axioms M7.StreamingIndices.all_indices
#print axioms M7.StreamingIndices.stream_winners
