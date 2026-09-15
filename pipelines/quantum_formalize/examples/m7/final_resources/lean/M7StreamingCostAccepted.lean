import M7StreamingCost

theorem M7.StreamingCost.cursor_bound : ∀ (n : ℕ) (p : Fin n → M7.StreamingCost.Eval) (i fuel a b : ℕ), (∀ j, (p j).outer ≤ a ∧ (p j).inner ≤ b) → (M7.StreamingCost.allFinFrom n p i fuel).outer ≤ fuel*a ∧ (M7.StreamingCost.allFinFrom n p i fuel).inner ≤ fuel*b := by
  intro n p i fuel a b hp
  induction fuel generalizing i with
  | zero =>
      simp [M7.StreamingCost.allFinFrom]
  | succ fuel ih =>
      by_cases h : i < n
      · have hc := hp ⟨i, h⟩
        have hr := ih (i + 1)
        simp only [M7.StreamingCost.allFinFrom, dif_pos h]
        split <;> (try dsimp only) <;>
          simp only [Nat.succ_mul] <;> omega
      · simp [M7.StreamingCost.allFinFrom, h]

theorem M7.StreamingCost.cursor_projection : ∀ (n : ℕ) (p : Fin n → M7.StreamingCost.Eval) (i fuel : ℕ), (M7.StreamingCost.allFinFrom n p i fuel).result = M7.StreamingIndices.allFinFrom n (fun j => (p j).result) i fuel := by
  change ∀ (n : ℕ) (p : Fin n → M7.StreamingCost.Eval) (i fuel : ℕ), (M7.StreamingCost.allFinFrom n p i fuel).result = M7.StreamingIndices.allFinFrom n (fun j => (p j).result) i fuel
  intro n p i fuel
  induction fuel generalizing i with
  | zero => rfl
  | succ fuel ih =>
      by_cases h : i < n
      · cases hb : (p ⟨i, h⟩).result <;>
          simp [M7.StreamingCost.allFinFrom, M7.StreamingIndices.allFinFrom, h, hb, ih]
      · simp [M7.StreamingCost.allFinFrom, M7.StreamingIndices.allFinFrom, h]

theorem M7.StreamingCost.record_cardinality : ∀ (N : ℕ) [NeZero N], M7.StreamingCost.recordCount N = Fintype.card (M7.Action.Record N) ∧ M7.StreamingCost.recordCount N = 2 * Nat.totient N * N^2 := by
  intro N inst
  have h := Fintype.card_congr (show M7.Action.Record N ≃ _ from
    { toFun := fun g => (g.unit, g.exchange, g.leftShift, g.rightShift)
      invFun := fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
      left_inv := by intro g; cases g; rfl
      right_inv := by intro p; rcases p with ⟨u, e, s, t⟩; rfl })
  constructor
  · rw [h]
    simp [M7.StreamingCost.recordCount, ZMod.card_units_eq_totient,
      pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  · simp [M7.StreamingCost.recordCount, ZMod.card_units_eq_totient,
      pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem M7.StreamingCost.record_bound : ∀ (N : ℕ) [NeZero N], ∀ (p : M7.Action.Record N → M7.StreamingCost.Eval) (a b : ℕ), (∀ g, (p g).outer ≤ a ∧ (p g).inner ≤ b) → (M7.StreamingCost.allRecords N p).outer ≤ M7.StreamingCost.recordCount N*a ∧ (M7.StreamingCost.allRecords N p).inner ≤ M7.StreamingCost.recordCount N*b := by
  intro N inst p a b hp
  have hb : ∀ (n : ℕ) (q : Fin n → M7.StreamingCost.Eval) (c d : ℕ),
      (∀ j, (q j).outer ≤ c ∧ (q j).inner ≤ d) →
      (M7.StreamingCost.allFin n q).outer ≤ n * c ∧
      (M7.StreamingCost.allFin n q).inner ≤ n * d := by
    intro n q c d hq
    simpa only [M7.StreamingCost.allFin] using
      M7.StreamingCost.cursor_bound n q 0 n c d hq
  have h :
      (M7.StreamingCost.allRecords N p).outer ≤
        Fintype.card ((ZMod N)ˣ) * (2 * (N * (N * a))) ∧
      (M7.StreamingCost.allRecords N p).inner ≤
        Fintype.card ((ZMod N)ˣ) * (2 * (N * (N * b))) := by
    unfold M7.StreamingCost.allRecords
    apply hb
    intro u
    apply hb
    intro e
    apply hb
    intro s
    apply hb
    intro t
    exact hp _
  simpa only [M7.StreamingCost.recordCount, pow_two, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm] using h

theorem M7.StreamingCost.record_projection : ∀ (N : ℕ) [NeZero N], ∀ p : M7.Action.Record N → M7.StreamingCost.Eval, (M7.StreamingCost.allRecords N p).result = M7.StreamingIndices.allRecords N (fun g => (p g).result) := by
  change ∀ (N : ℕ) [NeZero N], ∀ p : M7.Action.Record N → M7.StreamingCost.Eval, (M7.StreamingCost.allRecords N p).result = M7.StreamingIndices.allRecords N (fun g => (p g).result)
  intro N inst p
  simp only [M7.StreamingCost.allRecords, M7.StreamingIndices.allRecords, M7.StreamingCost.allFin, M7.StreamingIndices.allFin, M7.StreamingCost.cursor_projection]

theorem M7.StreamingCost.index_bound : ∀ (H N : ℕ) [NeZero N], ∀ (p : M7.GlobalQuery.Index H N → M7.StreamingCost.Eval) (a b : ℕ), (∀ x, (p x).outer ≤ a ∧ (p x).inner ≤ b) → (M7.StreamingCost.allIndices H N p).outer ≤ (H * M7.StreamingCost.recordCount N)*a ∧ (M7.StreamingCost.allIndices H N p).inner ≤ (H * M7.StreamingCost.recordCount N)*b := by
  intro H N inst p a b hp
  have h :
      (M7.StreamingCost.allIndices H N p).outer ≤ H * (M7.StreamingCost.recordCount N * a) ∧
      (M7.StreamingCost.allIndices H N p).inner ≤ H * (M7.StreamingCost.recordCount N * b) := by
    unfold M7.StreamingCost.allIndices M7.StreamingCost.allFin
    apply M7.StreamingCost.cursor_bound
    intro i
    apply M7.StreamingCost.record_bound
    intro g
    exact hp _
  simpa only [Nat.mul_assoc] using h

theorem M7.StreamingCost.index_projection : ∀ (H N : ℕ) [NeZero N], ∀ p : M7.GlobalQuery.Index H N → M7.StreamingCost.Eval, (M7.StreamingCost.allIndices H N p).result = M7.StreamingIndices.allIndices H N (fun x => (p x).result) := by
  change ∀ (H N : ℕ) [NeZero N], ∀ p : M7.GlobalQuery.Index H N → M7.StreamingCost.Eval, (M7.StreamingCost.allIndices H N p).result = M7.StreamingIndices.allIndices H N (fun x => (p x).result)
  intro H N inst p
  simp only [M7.StreamingCost.allIndices, M7.StreamingIndices.allIndices, M7.StreamingCost.allFin, M7.StreamingIndices.allFin, M7.StreamingCost.cursor_projection, M7.StreamingCost.record_projection]

theorem M7.StreamingCost.stream_projection_bound : ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), ∀ x : M7.GlobalQuery.Index H N, (M7.StreamingCost.streamWin q bases x).result = M7.StreamingIndices.streamWin q bases x ∧ (M7.StreamingCost.streamWin q bases x).outer = 0 ∧ (M7.StreamingCost.streamWin q bases x).inner ≤ (H * M7.StreamingCost.recordCount N) := by
  change ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), ∀ x : M7.GlobalQuery.Index H N, (M7.StreamingCost.streamWin q bases x).result = M7.StreamingIndices.streamWin q bases x ∧ (M7.StreamingCost.streamWin q bases x).outer = 0 ∧ (M7.StreamingCost.streamWin q bases x).inner ≤ H * M7.StreamingCost.recordCount N
  intro H N inst q bases x
  classical
  have hb : ∀ p : M7.GlobalQuery.Index H N → M7.StreamingCost.Eval,
      (∀ y, (p y).outer ≤ 0 ∧ (p y).inner ≤ 1) →
      (M7.StreamingCost.allIndices H N p).outer = 0 ∧
      (M7.StreamingCost.allIndices H N p).inner ≤ H * M7.StreamingCost.recordCount N := by
    intro p hp
    have h := M7.StreamingCost.index_bound H N p 0 1 hp
    simpa only [Nat.mul_zero, Nat.mul_one, Nat.le_zero] using h
  by_cases hx : M7.GlobalQuery.feasible q bases x
  · simp only [M7.StreamingCost.streamWin, M7.StreamingIndices.streamWin, hx, ↓reduceIte]
    constructor
    · rw [M7.StreamingCost.index_projection]
      rfl
    · apply hb
      intro y
      dsimp only
      first | omega | (split_ifs <;> simp)
  · simp [M7.StreamingCost.streamWin, M7.StreamingIndices.streamWin, hx]

theorem M7.StreamingCost.scan_bound : ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), (M7.StreamingCost.scanWins q bases).outer ≤ (H * M7.StreamingCost.recordCount N) ∧ (M7.StreamingCost.scanWins q bases).inner ≤ (H * M7.StreamingCost.recordCount N)^2 := by
  change ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), (M7.StreamingCost.scanWins q bases).outer ≤ H * M7.StreamingCost.recordCount N ∧ (M7.StreamingCost.scanWins q bases).inner ≤ (H * M7.StreamingCost.recordCount N)^2
  intro H N inst q bases
  have hb : ∀ p : M7.GlobalQuery.Index H N → M7.StreamingCost.Eval,
      (∀ x, (p x).outer ≤ 1 ∧ (p x).inner ≤ H * M7.StreamingCost.recordCount N) →
      (M7.StreamingCost.allIndices H N p).outer ≤ H * M7.StreamingCost.recordCount N ∧
      (M7.StreamingCost.allIndices H N p).inner ≤ (H * M7.StreamingCost.recordCount N)^2 := by
    intro p hp
    simpa only [Nat.mul_one, pow_two] using
      M7.StreamingCost.index_bound H N p 1 (H * M7.StreamingCost.recordCount N) hp
  unfold M7.StreamingCost.scanWins
  apply hb
  intro x
  dsimp only
  exact ⟨Nat.le_refl 1, (M7.StreamingCost.stream_projection_bound H N q bases x).2.2⟩
#print axioms M7.StreamingCost.cursor_bound
#print axioms M7.StreamingCost.cursor_projection
#print axioms M7.StreamingCost.record_bound
#print axioms M7.StreamingCost.index_bound
#print axioms M7.StreamingCost.record_cardinality
#print axioms M7.StreamingCost.record_projection
#print axioms M7.StreamingCost.index_projection
#print axioms M7.StreamingCost.stream_projection_bound
#print axioms M7.StreamingCost.scan_bound
