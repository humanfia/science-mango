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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (p : M7.Action.Record N → M7.StreamingCost.Eval) (a b : ℕ), (∀ g, (p g).outer ≤ a ∧ (p g).inner ≤ b) → (M7.StreamingCost.allRecords N p).outer ≤ M7.StreamingCost.recordCount N*a ∧ (M7.StreamingCost.allRecords N p).inner ≤ M7.StreamingCost.recordCount N*b
