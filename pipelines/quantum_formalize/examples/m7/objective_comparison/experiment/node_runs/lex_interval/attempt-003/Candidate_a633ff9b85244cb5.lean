import FrozenTarget_a633ff9b85244cb5
theorem M7.ObjectiveComparison.lex_interval : QuantumHarnessFrozenTarget := by
  intro m a b i fuel
  induction fuel generalizing i with
  | zero =>
      constructor
      · intro h
        have hf : False := by simpa [M7.ObjectiveComparison.lexFrom] using h
        exact hf.elim
      · rintro ⟨j, hj, hp, hl⟩
        omega
  | succ fuel ih =>
      by_cases hi : i < m
      · by_cases hab : a ⟨i, hi⟩ < b ⟨i, hi⟩
        · constructor
          · intro h
            refine ⟨⟨i, hi⟩, ?_, ?_, hab⟩
            · change i ≤ i ∧ i < i + (fuel + 1)
              omega
            · intro k hk hkj
              have hk' : k.val < i := hkj
              omega
          · intro h
            simp [M7.ObjectiveComparison.lexFrom, hi, hab]
        · by_cases hba : b ⟨i, hi⟩ < a ⟨i, hi⟩
          · constructor
            · intro h
              have hf : False := by
                simpa [M7.ObjectiveComparison.lexFrom, hi, hab, hba] using h
              exact hf.elim
            · rintro ⟨j, hj, hp, hl⟩
              exfalso
              by_cases hji : j.val = i
              · have he : j = ⟨i, hi⟩ := Fin.ext hji
                have hl' : a ⟨i, hi⟩ < b ⟨i, hi⟩ := by simpa [he] using hl
                omega
              · have hij : (⟨i, hi⟩ : Fin m) < j := by
                  change i < j.val
                  omega
                have he := hp ⟨i, hi⟩ (Nat.le_refl i) hij
                omega
          · have heq : a ⟨i, hi⟩ = b ⟨i, hi⟩ := by omega
            have hs : (M7.ObjectiveComparison.lexFrom a b i (fuel + 1)).1 =
                (M7.ObjectiveComparison.lexFrom a b (i + 1) fuel).1 := by
              simp [M7.ObjectiveComparison.lexFrom, hi, hab, hba]
            rw [hs, ih]
            constructor
            · rintro ⟨j, hj, hp, hl⟩
              refine ⟨j, ?_, ?_, hl⟩
              · omega
              · intro k hk hkj
                by_cases hki : k.val = i
                · have he : k = ⟨i, hi⟩ := Fin.ext hki
                  simpa [he] using heq
                · exact hp k (by omega) hkj
            · rintro ⟨j, hj, hp, hl⟩
              have hji : j.val ≠ i := by
                intro hji
                have he : j = ⟨i, hi⟩ := Fin.ext hji
                have hl' : a ⟨i, hi⟩ < b ⟨i, hi⟩ := by simpa [he] using hl
                omega
              refine ⟨j, ?_, ?_, hl⟩
              · omega
              · intro k hk hkj
                exact hp k (by omega) hkj
      · constructor
        · intro h
          have hf : False := by
            simpa [M7.ObjectiveComparison.lexFrom, hi] using h
          exact hf.elim
        · rintro ⟨j, hj, hp, hl⟩
          have hjm := j.isLt
          omega
