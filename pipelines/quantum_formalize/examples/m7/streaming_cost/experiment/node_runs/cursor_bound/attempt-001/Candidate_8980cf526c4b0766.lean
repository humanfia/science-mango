import FrozenTarget_8980cf526c4b0766
theorem M7.StreamingCost.cursor_bound : QuantumHarnessFrozenTarget := by
  intro n p i fuel a b hp
  induction fuel generalizing i with
  | zero =>
      simp [M7.StreamingCost.allFinFrom]
  | succ fuel ih =>
      by_cases hi : i < n
      · have hcurrent := hp ⟨i, hi⟩
        have hrest := ih (i + 1)
        simp only [M7.StreamingCost.allFinFrom, hi, dite_true, Nat.succ_mul]
        split <;> simp_all <;> omega
      · simp [M7.StreamingCost.allFinFrom, hi]
