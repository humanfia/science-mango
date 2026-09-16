import M8WeightedSearch

theorem M8.WeightedSearch.callback_bound : ∀ (n : ℕ) (α : Type) (test : Fin n → Option α × ℕ) (start fuel : ℕ), ∀ C : ℕ, (∀ i, (test i).2 ≤ C) → (M8.WeightedSearch.walk test start fuel).work ≤ (M8.WeightedSearch.walk test start fuel).calls*C := by
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

theorem M8.WeightedSearch.projection : ∀ (n : ℕ) (α : Type) (test : Fin n → Option α × ℕ) (start fuel : ℕ), ((M8.WeightedSearch.walk test start fuel).selected, (M8.WeightedSearch.walk test start fuel).calls) = M8.FiniteSearch.walk (fun i => (test i).1) start fuel := by
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

theorem M8.WeightedSearch.find_projection : ∀ (n : ℕ) (α : Type) (test : Fin n → Option α × ℕ), ((M8.WeightedSearch.find test).selected,(M8.WeightedSearch.find test).calls) = M8.FiniteSearch.find (fun i => (test i).1) := by
  change ∀ (n : ℕ) (α : Type) (test : Fin n → Option α × ℕ), _
  intro n α test
  simpa only [M8.WeightedSearch.find, M8.FiniteSearch.find] using
    M8.WeightedSearch.projection n α test 0 n

theorem M8.WeightedSearch.find_callback_bound : ∀ (n : ℕ) (α : Type) (test : Fin n → Option α × ℕ) (C : ℕ), (∀ i, (test i).2 ≤ C) → (M8.WeightedSearch.find test).work ≤ n*C := by
  change ∀ (n : ℕ) (α : Type) (test : Fin n → Option α × ℕ) (C : ℕ), (∀ i, (test i).2 ≤ C) → (M8.WeightedSearch.find test).work ≤ n * C
  intro n α test C hC
  have hcalls : (M8.WeightedSearch.find test).calls ≤ n := by
    calc
      (M8.WeightedSearch.find test).calls = (M8.FiniteSearch.find (fun i => (test i).1)).2 :=
        congrArg Prod.snd (M8.WeightedSearch.find_projection n α test)
      _ ≤ n := M8.FiniteSearch.find_bound n α (fun i => (test i).1)
  exact le_trans (M8.WeightedSearch.callback_bound n α test 0 n C hC)
    (Nat.mul_le_mul_right C hcalls)
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (n : ℕ) (α : Type) (test : Fin n → Option α × ℕ) (C overhead : ℕ), (∀ i, (test i).2 ≤ C) → (M8.WeightedSearch.find test).calls*overhead + (M8.WeightedSearch.find test).work ≤ n*(overhead+C)
