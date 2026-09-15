import FrozenTarget_fb54807a6d29ff81
theorem M7.ObjectiveComparison.lex_interval : QuantumHarnessFrozenTarget := by
  change ∀ (m : ℕ) (a b : Fin m → ℤ) (i fuel : ℕ), (M7.ObjectiveComparison.lexFrom a b i fuel).1 = true ↔ ∃ j : Fin m, (i ≤ j.val ∧ j.val < i + fuel) ∧ (∀ k : Fin m, i ≤ k.val → k < j → a k = b k) ∧ a j < b j
  intro m a b i fuel
  induction fuel generalizing i with
  | zero =>
      constructor
      · intro h
        have : False := by simpa [M7.ObjectiveComparison.lexFrom] using h
        contradiction
      · rintro ⟨j, hj, hp, hab⟩
        omega
  | succ fuel ih =>
      by_cases hi : i < m
      · by_cases hlt : a ⟨i, hi⟩ < b ⟨i, hi⟩
        · have hrun : (M7.ObjectiveComparison.lexFrom a b i (fuel + 1)).1 = true := by
            simp [M7.ObjectiveComparison.lexFrom, hi, hlt]
          constructor
          · intro _
            refine ⟨⟨i, hi⟩, ⟨by simp, by simp; omega⟩, ?_, hlt⟩
            intro k hk hki
            have : k.val < i := hki
            omega
          · intro _
            exact hrun
        · by_cases hgt : b ⟨i, hi⟩ < a ⟨i, hi⟩
          · have hrun : (M7.ObjectiveComparison.lexFrom a b i (fuel + 1)).1 = false := by
              simp [M7.ObjectiveComparison.lexFrom, hi, hlt, hgt]
            constructor
            · intro h
              rw [hrun] at h
              cases h
            · rintro ⟨j, hj, hp, hab⟩
              exfalso
              by_cases hji : j.val = i
              · have hjc : j = ⟨i, hi⟩ := Fin.ext hji
                rw [hjc] at hab
                omega
              · have he := hp ⟨i, hi⟩ (by simp) (by change i < j.val; omega)
                omega
          · have heq : a ⟨i, hi⟩ = b ⟨i, hi⟩ :=
              le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
            have hrun : (M7.ObjectiveComparison.lexFrom a b i (fuel + 1)).1 = (M7.ObjectiveComparison.lexFrom a b (i + 1) fuel).1 := by
              simp [M7.ObjectiveComparison.lexFrom, hi, hlt, hgt]
            rw [hrun, ih (i + 1)]
            constructor
            · rintro ⟨j, hj, hp, hab⟩
              refine ⟨j, ⟨by omega, by omega⟩, ?_, hab⟩
              intro k hk hkj
              by_cases hki : k.val = i
              · have hkc : k = ⟨i, hi⟩ := Fin.ext hki
                simpa only [hkc] using heq
              · exact hp k (by omega) hkj
            · rintro ⟨j, hj, hp, hab⟩
              have hij : i + 1 ≤ j.val := by
                by_contra hn
                have hjc : j = ⟨i, hi⟩ := Fin.ext (by omega)
                rw [hjc] at hab
                omega
              refine ⟨j, ⟨hij, by omega⟩, ?_, hab⟩
              intro k hk hkj
              exact hp k (by omega) hkj
      · have hrun : (M7.ObjectiveComparison.lexFrom a b i (fuel + 1)).1 = false := by
          simp [M7.ObjectiveComparison.lexFrom, hi]
        constructor
        · intro h
          rw [hrun] at h
          cases h
        · rintro ⟨j, hj, hp, hab⟩
          have := j.isLt
          omega
