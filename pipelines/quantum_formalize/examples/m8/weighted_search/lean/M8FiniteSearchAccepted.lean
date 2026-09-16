import M8FiniteSearch

theorem M8.FiniteSearch.calls_bound : ∀ (n : ℕ) (α : Type) (test : Fin n → Option α) (start fuel : ℕ), (M8.FiniteSearch.walk test start fuel).2 ≤ fuel := by
  change ∀ (n : ℕ) (α : Type) (test : Fin n → Option α) (start fuel : ℕ), (M8.FiniteSearch.walk test start fuel).2 ≤ fuel
  intro n α test start fuel
  induction fuel generalizing start with
  | zero => simp [M8.FiniteSearch.walk]
  | succ fuel ih =>
      by_cases h : start < n
      · cases ht : test ⟨start, h⟩ with
        | none =>
            simpa [M8.FiniteSearch.walk, h, ht] using
              Nat.add_le_add_right (ih (start + 1)) 1
        | some a =>
            simp [M8.FiniteSearch.walk, h, ht]
      · simp [M8.FiniteSearch.walk, h]

theorem M8.FiniteSearch.exhaustion_calls : ∀ (n : ℕ) (α : Type) (test : Fin n → Option α) (start fuel : ℕ), start+fuel ≤ n → (M8.FiniteSearch.walk test start fuel).1 = none → (M8.FiniteSearch.walk test start fuel).2 = fuel := by
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

theorem M8.FiniteSearch.none_iff : ∀ (n : ℕ) (α : Type) (test : Fin n → Option α) (start fuel : ℕ), ((M8.FiniteSearch.walk test start fuel).1 = none ↔ ∀ i : Fin n, start ≤ i.val → i.val < start+fuel → test i = none) := by
  change ∀ (n : ℕ) (α : Type) (test : Fin n → Option α) (start fuel : ℕ), (M8.FiniteSearch.walk test start fuel).1 = none ↔ ∀ i : Fin n, start ≤ i.val → i.val < start + fuel → test i = none
  intro n α test start fuel
  induction fuel generalizing start with
  | zero =>
      constructor
      · intro _ i hlo hhi
        omega
      · intro _
        rfl
  | succ fuel ih =>
      by_cases hs : start < n
      · cases ht : test ⟨start, hs⟩ with
        | none =>
            simp only [M8.FiniteSearch.walk, dif_pos hs, ht, Prod.fst]
            rw [ih]
            constructor
            · intro hall i hlo hhi
              by_cases heq : i.val = start
              · have hi : i = ⟨start, hs⟩ := Fin.ext heq
                simpa only [hi] using ht
              · exact hall i (by omega) (by omega)
            · intro hall i hlo hhi
              exact hall i (by omega) (by omega)
        | some a =>
            constructor
            · intro hw
              have hf : False := by
                simpa [M8.FiniteSearch.walk, hs, ht] using hw
              exact hf.elim
            · intro hall
              have hn : test ⟨start, hs⟩ = none :=
                hall ⟨start, hs⟩ (by simp) (by dsimp; omega)
              simp [ht] at hn
      · constructor
        · intro _ i hlo _
          have hi := i.isLt
          omega
        · intro _
          simp [M8.FiniteSearch.walk, hs]

theorem M8.FiniteSearch.some_iff : ∀ (n : ℕ) (α : Type) (test : Fin n → Option α) (start fuel : ℕ), ∀ (i : Fin n) (a : α), (M8.FiniteSearch.walk test start fuel).1 = some (i,a) ↔ M8.FiniteSearch.First test start fuel i a := by
  change ∀ (n : ℕ) (α : Type) (test : Fin n → Option α) (start fuel : ℕ) (i : Fin n) (a : α), (M8.FiniteSearch.walk test start fuel).1 = some (i, a) ↔ M8.FiniteSearch.First test start fuel i a
  intro n α test start fuel
  induction fuel generalizing start with
  | zero =>
      intro i a
      change (none : Option (Fin n × α)) = some (i, a) ↔ M8.FiniteSearch.First test start 0 i a
      constructor
      · intro he
        cases he
      · intro hf
        rcases hf with ⟨hl, hu, ht, hall⟩
        omega
  | succ fuel ih =>
      intro i a
      by_cases h : start < n
      · cases ht : test ⟨start, h⟩ with
        | none =>
            simp only [M8.FiniteSearch.walk, dif_pos h, ht]
            rw [ih]
            unfold M8.FiniteSearch.First
            constructor
            · rintro ⟨hl, hu, hv, hall⟩
              refine ⟨by omega, by omega, hv, ?_⟩
              intro j hj hji
              by_cases he : j.val = start
              · have ej : j = ⟨start, h⟩ := Fin.ext he
                rw [ej]
                exact ht
              · exact hall j (by omega) hji
            · rintro ⟨hl, hu, hv, hall⟩
              have hne : i.val ≠ start := by
                intro he
                have ei : i = ⟨start, h⟩ := Fin.ext he
                rw [ei, ht] at hv
                cases hv
              refine ⟨by omega, by omega, hv, ?_⟩
              intro j hj hji
              exact hall j (by omega) hji
        | some b =>
            simp only [M8.FiniteSearch.walk, dif_pos h, ht]
            change some ((⟨start, h⟩ : Fin n), b) = some (i, a) ↔ M8.FiniteSearch.First test start (fuel + 1) i a
            constructor
            · intro he
              have hp := Option.some.inj he
              have hi : (⟨start, h⟩ : Fin n) = i := congrArg Prod.fst hp
              have ha : b = a := congrArg Prod.snd hp
              subst i
              subst a
              unfold M8.FiniteSearch.First
              dsimp only
              refine ⟨le_rfl, by omega, ht, ?_⟩
              intro j hj hji
              omega
            · intro hf
              rcases hf with ⟨hl, hu, hv, hall⟩
              have hi : i = ⟨start, h⟩ := by
                apply Fin.ext
                change i.val = start
                by_contra hne
                have hlt : start < i.val := by omega
                have hn := hall ⟨start, h⟩ (by simp) (by simpa only using hlt)
                rw [ht] at hn
                cases hn
              subst i
              rw [ht] at hv
              have ha : b = a := Option.some.inj hv
              cases ha
              rfl
      · rw [M8.FiniteSearch.walk, dif_neg h]
        change (none : Option (Fin n × α)) = some (i, a) ↔ M8.FiniteSearch.First test start (fuel + 1) i a
        constructor
        · intro he
          cases he
        · intro hf
          rcases hf with ⟨hl, hu, hv, hall⟩
          have hi := i.isLt
          omega

theorem M8.FiniteSearch.successful_calls : ∀ (n : ℕ) (α : Type) (test : Fin n → Option α) (start fuel : ℕ), ∀ (i : Fin n) (a : α), (M8.FiniteSearch.walk test start fuel).1 = some (i,a) → (M8.FiniteSearch.walk test start fuel).2 = i.val-start+1 := by
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

theorem M8.FiniteSearch.find_bound : ∀ (n : ℕ) (α : Type) (test : Fin n → Option α), (M8.FiniteSearch.find test).2 ≤ n := by
  change ∀ (n : ℕ) (α : Type) (test : Fin n → Option α), (M8.FiniteSearch.find test).2 ≤ n
  intro n α test
  exact M8.FiniteSearch.calls_bound n α test 0 n

theorem M8.FiniteSearch.find_none : ∀ (n : ℕ) (α : Type) (test : Fin n → Option α), (M8.FiniteSearch.find test).1 = none ↔ ∀ i, test i = none := by
  change ∀ (n : ℕ) (α : Type) (test : Fin n → Option α), (M8.FiniteSearch.walk test 0 n).1 = none ↔ ∀ i, test i = none
  intro n α test
  rw [M8.FiniteSearch.none_iff n α test 0 n]
  constructor
  · intro h i
    exact h i (Nat.zero_le _) (by simpa using i.isLt)
  · intro h i _ _
    exact h i

theorem M8.FiniteSearch.find_some : ∀ (n : ℕ) (α : Type) (test : Fin n → Option α) (i : Fin n) (a : α), (M8.FiniteSearch.find test).1 = some (i,a) ↔ test i = some a ∧ ∀ j : Fin n, j.val < i.val → test j = none := by
  change ∀ (n : ℕ) (α : Type) (test : Fin n → Option α) (i : Fin n) (a : α), (M8.FiniteSearch.find test).1 = some (i, a) ↔ test i = some a ∧ ∀ j : Fin n, j.val < i.val → test j = none
  intro n α test i a
  change (M8.FiniteSearch.walk test 0 n).1 = some (i, a) ↔ _
  rw [M8.FiniteSearch.some_iff n α test 0 n i a]
  unfold M8.FiniteSearch.First
  constructor
  · rintro ⟨hl, hu, ht, hall⟩
    exact ⟨ht, fun j hj => hall j (Nat.zero_le _) hj⟩
  · rintro ⟨ht, hall⟩
    refine ⟨Nat.zero_le _, ?_, ht, ?_⟩
    · simpa only [Nat.zero_add] using i.isLt
    · intro j hj hji
      exact hall j hji
#print axioms M8.FiniteSearch.calls_bound
#print axioms M8.FiniteSearch.exhaustion_calls
#print axioms M8.FiniteSearch.find_bound
#print axioms M8.FiniteSearch.none_iff
#print axioms M8.FiniteSearch.find_none
#print axioms M8.FiniteSearch.some_iff
#print axioms M8.FiniteSearch.find_some
#print axioms M8.FiniteSearch.successful_calls
