import FrozenTarget_4f438a7ca4833845
theorem M8.WeightedSearch.projection : QuantumHarnessFrozenTarget := by
    change ∀ (n : ℕ) (α : Type) (test : Fin n → Option α × ℕ) (start fuel : ℕ), _
    intro n α test start fuel
    induction fuel generalizing start with
    | zero =>
        rfl
    | succ fuel ih =>
        by_cases h : start < n
        · cases e : (test ⟨start, h⟩).1 with
          | none =>
              simpa only [M8.WeightedSearch.walk, M8.FiniteSearch.walk, dif_pos h, e, Prod.fst, Prod.snd] using
                congrArg (fun r : Option (Fin n × α) × ℕ => (r.1, r.2 + 1)) (ih (start + 1))
          | some a =>
              simp [M8.WeightedSearch.walk, M8.FiniteSearch.walk, h, e]
        · simp [M8.WeightedSearch.walk, M8.FiniteSearch.walk, h]
