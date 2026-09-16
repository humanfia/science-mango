import FrozenTarget_4b890f336fc81708
theorem M8.FiniteSearch.successful_calls : QuantumHarnessFrozenTarget := by
  change ∀ (n : ℕ) (α : Type) (test : Fin n → Option α) (start fuel : ℕ) (i : Fin n) (a : α), (M8.FiniteSearch.walk test start fuel).1 = some (i, a) → (M8.FiniteSearch.walk test start fuel).2 = i.val - start + 1
  intro n α test
  have aux : ∀ (fuel start : ℕ) (i : Fin n) (a : α),
      (M8.FiniteSearch.walk test start fuel).1 = some (i, a) →
      start ≤ i.val ∧ (M8.FiniteSearch.walk test start fuel).2 = i.val - start + 1 := by
    intro fuel
    induction fuel with
    | zero =>
        intro start i a hs
        simp [M8.FiniteSearch.walk] at hs
    | succ fuel ih =>
        intro start i a hs
        by_cases h : start < n
        · cases ht : test ⟨start, h⟩ with
          | none =>
              have hs' : (M8.FiniteSearch.walk test (start + 1) fuel).1 = some (i, a) := by
                simpa only [M8.FiniteSearch.walk, dif_pos h, ht] using hs
              obtain ⟨hle, hcount⟩ := ih (start + 1) i a hs'
              simp only [M8.FiniteSearch.walk, dif_pos h, ht]
              dsimp only
              constructor <;> omega
          | some b =>
              have hs' : some ((⟨start, h⟩ : Fin n), b) = some (i, a) := by
                simpa only [M8.FiniteSearch.walk, dif_pos h, ht] using hs
              have hp := Option.some.inj hs'
              have hi := congrArg (fun p : Fin n × α => p.1.val) hp
              dsimp only at hi
              simp only [M8.FiniteSearch.walk, dif_pos h, ht]
              dsimp only
              constructor <;> omega
        · simp [M8.FiniteSearch.walk, h] at hs
  intro start fuel i a hs
  exact (aux fuel start i a hs).2
