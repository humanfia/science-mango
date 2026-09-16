import FrozenTarget_648e83d7042e902b
theorem M8.FiniteSearch.some_iff : QuantumHarnessFrozenTarget := by
  change ∀ (n : ℕ) (α : Type) (test : Fin n → Option α) (start fuel : ℕ) (i : Fin n) (a : α), (M8.FiniteSearch.walk test start fuel).1 = some (i, a) ↔ M8.FiniteSearch.First test start fuel i a
  intro n α test start fuel
  induction fuel generalizing start with
  | zero =>
      intro i a
      constructor
      · intro h
        cases h
      · intro h
        rcases h with ⟨hl, hu, hv, hp⟩
        omega
  | succ fuel ih =>
      intro i a
      by_cases hs : start < n
      · cases ht : test ⟨start, hs⟩ with
        | none =>
            simp only [M8.FiniteSearch.walk, dif_pos hs, ht]
            rw [ih]
            unfold M8.FiniteSearch.First
            constructor
            · rintro ⟨hl, hu, hv, hp⟩
              refine ⟨by omega, by omega, hv, ?_⟩
              intro j hj hji
              by_cases he : j.val = start
              · have hj' : j = ⟨start, hs⟩ := Fin.ext he
                rw [hj']
                exact ht
              · exact hp j (by omega) hji
            · rintro ⟨hl, hu, hv, hp⟩
              have hne : i.val ≠ start := by
                intro he
                have hi' : i = ⟨start, hs⟩ := Fin.ext he
                rw [hi', ht] at hv
                cases hv
              refine ⟨by omega, by omega, hv, ?_⟩
              intro j hj hji
              exact hp j (by omega) hji
        | some b =>
            simp only [M8.FiniteSearch.walk, dif_pos hs, ht]
            constructor
            · intro h
              have hp := Option.some.inj h
              rcases Prod.mk.inj hp with ⟨hi, ha⟩
              subst i
              subst a
              refine ⟨le_rfl, by omega, ht, ?_⟩
              intro j hj hji
              omega
            · intro h
              rcases h with ⟨hl, hu, hv, hp⟩
              have he : i.val = start := by
                by_contra hne
                have hlt : start < i.val := by omega
                have hn := hp ⟨start, hs⟩ (by simp) hlt
                rw [ht] at hn
                cases hn
              have hi : i = ⟨start, hs⟩ := Fin.ext he
              subst i
              have ha : b = a := Option.some.inj (ht.symm.trans hv)
              subst a
              rfl
      · simp only [M8.FiniteSearch.walk, dif_neg hs]
        constructor
        · intro h
          cases h
        · intro h
          rcases h with ⟨hl, hu, hv, hp⟩
          have hi := i.isLt
          omega
