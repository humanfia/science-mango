import FrozenTarget_b365b536d05c6e93
theorem M7.ObjectiveComparison.lex_interval : QuantumHarnessFrozenTarget := by
  change ∀ (m : ℕ) (a b : Fin m → ℤ) (i fuel : ℕ), (M7.ObjectiveComparison.lexFrom a b i fuel).1 = true ↔ ∃ j : Fin m, (i ≤ j.val ∧ j.val < i + fuel) ∧ (∀ k : Fin m, i ≤ k.val → k < j → a k = b k) ∧ a j < b j
  intro m a b i fuel
  induction fuel generalizing i with
  | zero =>
      constructor
      · intro h
        simp [M7.ObjectiveComparison.lexFrom] at h
      · rintro ⟨j, hj, _⟩
        omega
  | succ fuel ih =>
      by_cases hi : i < m
      · by_cases hlt : a ⟨i, hi⟩ < b ⟨i, hi⟩
        · constructor
          · intro _
            refine ⟨⟨i, hi⟩, ⟨le_rfl, by omega⟩, ?_, hlt⟩
            intro k hk hki
            have hki' : k.val < i := hki
            omega
          · intro _
            simp [M7.ObjectiveComparison.lexFrom, hi, hlt]
        · by_cases hgt : b ⟨i, hi⟩ < a ⟨i, hi⟩
          · constructor
            · intro h
              simp [M7.ObjectiveComparison.lexFrom, hi, hlt, hgt] at h
            · rintro ⟨j, ⟨hij, hjbound⟩, hp, hjlt⟩
              exfalso
              by_cases he : j.val = i
              · have hji : j = ⟨i, hi⟩ := Fin.ext he
                subst j
                exact (not_lt_of_gt hgt) hjlt
              · have hij' : (⟨i, hi⟩ : Fin m) < j := by
                  change i < j.val
                  omega
                have hab := hp ⟨i, hi⟩ (Nat.le_refl i) hij'
                exact (ne_of_lt hgt) hab.symm
          · have hab : a ⟨i, hi⟩ = b ⟨i, hi⟩ := le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
            have step : (M7.ObjectiveComparison.lexFrom a b i (Nat.succ fuel)).1 = (M7.ObjectiveComparison.lexFrom a b (i + 1) fuel).1 := by
              simp [M7.ObjectiveComparison.lexFrom, hi, hlt, hgt]
            rw [step, ih]
            constructor
            · rintro ⟨j, ⟨hij, hjbound⟩, hp, hjlt⟩
              refine ⟨j, ⟨by omega, by omega⟩, ?_, hjlt⟩
              intro k hik hkj
              by_cases he : k.val = i
              · have hki : k = ⟨i, hi⟩ := Fin.ext he
                subst k
                exact hab
              · exact hp k (by omega) hkj
            · rintro ⟨j, ⟨hij, hjbound⟩, hp, hjlt⟩
              have hij' : i + 1 ≤ j.val := by
                by_cases he : j.val = i
                · have hji : j = ⟨i, hi⟩ := Fin.ext he
                  subst j
                  exact False.elim ((ne_of_lt hjlt) hab)
                · omega
              refine ⟨j, ⟨hij', by omega⟩, ?_, hjlt⟩
              intro k hik hkj
              exact hp k (by omega) hkj
      · constructor
        · intro h
          simp [M7.ObjectiveComparison.lexFrom, hi] at h
        · rintro ⟨j, ⟨hij, _⟩, _⟩
          have hjm := j.isLt
          omega
