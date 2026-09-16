import FrozenTarget_f4597a807b04baa5
theorem M8.FiniteSearch.exhaustion_calls : QuantumHarnessFrozenTarget := by
  intro n α test start fuel
  induction fuel generalizing start with
  | zero =>
      intro hbound hnone
      rfl
  | succ fuel ih =>
      intro hbound hnone
      have hs : start < n := by omega
      cases ht : test ⟨start, hs⟩ with
      | none =>
          simp only [M8.FiniteSearch.walk, dif_pos hs, ht] at hnone ⊢
          have hbound' : start + 1 + fuel ≤ n := by omega
          exact congrArg (fun k : ℕ => k + 1) (ih (start + 1) hbound' hnone)
      | some a =>
          simp [M8.FiniteSearch.walk, hs, ht] at hnone
