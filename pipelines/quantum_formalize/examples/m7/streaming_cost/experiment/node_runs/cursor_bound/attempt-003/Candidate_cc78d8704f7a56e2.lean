import FrozenTarget_cc78d8704f7a56e2
theorem M7.StreamingCost.cursor_bound : QuantumHarnessFrozenTarget := by
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
