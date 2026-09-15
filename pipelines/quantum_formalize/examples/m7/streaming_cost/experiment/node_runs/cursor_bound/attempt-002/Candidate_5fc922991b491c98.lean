import FrozenTarget_5fc922991b491c98
theorem M7.StreamingCost.cursor_bound : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro n p i fuel a b hp
  induction fuel generalizing i with
  | zero =>
      simp [M7.StreamingCost.allFinFrom]
  | succ fuel ih =>
      by_cases h : i < n
      · have hcur := hp ⟨i, h⟩
        have htail := ih (i + 1)
        simp only [M7.StreamingCost.allFinFrom, dif_pos h, Nat.succ_mul]
        split <;> dsimp <;> constructor <;> omega
      · simp [M7.StreamingCost.allFinFrom, h]
