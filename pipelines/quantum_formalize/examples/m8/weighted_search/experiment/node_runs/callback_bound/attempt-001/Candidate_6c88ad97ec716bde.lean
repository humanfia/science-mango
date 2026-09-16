import FrozenTarget_6c88ad97ec716bde
theorem M8.WeightedSearch.callback_bound : QuantumHarnessFrozenTarget := by
  intro n α test start fuel C hC
  induction fuel generalizing start with
  | zero =>
      simp [M8.WeightedSearch.walk]
  | succ fuel ih =>
      by_cases h : start < n
      · cases e : (test ⟨start, h⟩).1 with
        | none =>
            simpa [M8.WeightedSearch.walk, h, e, Nat.add_mul, Nat.add_comm] using
              (Nat.add_le_add (hC ⟨start, h⟩) (ih (start + 1)))
        | some a =>
            simpa [M8.WeightedSearch.walk, h, e] using (hC ⟨start, h⟩)
      · simp [M8.WeightedSearch.walk, h]
