import M7StreamingCost

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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ p : M7.Action.Record N → M7.StreamingCost.Eval, (M7.StreamingCost.allRecords N p).result = M7.StreamingIndices.allRecords N (fun g => (p g).result)
