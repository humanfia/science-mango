import FrozenTarget_deed9ec4264501fd
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
              simp only [M8.FiniteSearch.walk, dif_pos h, ht] at hs ⊢
              rcases ih (start + 1) i a hs with ⟨hlo, hcount⟩
              constructor <;> omega
          | some b =>
              simp only [M8.FiniteSearch.walk, dif_pos h, ht] at hs ⊢
              have hi : start = i.val :=
                congrArg (fun p : Fin n × α => p.1.val) (Option.some.inj hs)
              constructor <;> omega
        · simp [M8.FiniteSearch.walk, h] at hs
  intro start fuel i a hs
  exact (aux fuel start i a hs).2
