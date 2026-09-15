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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (H N : ℕ) [NeZero N], ∀ (p : M7.GlobalQuery.Index H N → M7.StreamingCost.Eval) (a b : ℕ), (∀ x, (p x).outer ≤ a ∧ (p x).inner ≤ b) → (M7.StreamingCost.allIndices H N p).outer ≤ (H * M7.StreamingCost.recordCount N)*a ∧ (M7.StreamingCost.allIndices H N p).inner ≤ (H * M7.StreamingCost.recordCount N)*b
