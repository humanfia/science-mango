import M7ObjectiveComparison

theorem M7.ObjectiveComparison.lex_interval : ∀ (m : ℕ) (a b : Fin m → ℤ) (i fuel : ℕ), (M7.ObjectiveComparison.lexFrom a b i fuel).1 = true ↔ ∃ j : Fin m, (i ≤ j.val ∧ j.val < i+fuel) ∧ (∀ k : Fin m, i ≤ k.val → k < j → a k = b k) ∧ a j < b j := by
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

theorem M7.ObjectiveComparison.pareto_interval : ∀ (m : ℕ) (a b : Fin m → ℤ) (i fuel : ℕ) (seen : Bool), (M7.ObjectiveComparison.paretoFrom a b i fuel seen).1 = true ↔ (∀ j : Fin m, i ≤ j.val ∧ j.val < i+fuel → a j ≤ b j) ∧ (seen = true ∨ ∃ j : Fin m, (i ≤ j.val ∧ j.val < i+fuel) ∧ a j < b j) := by
  change ∀ (m : ℕ) (a b : Fin m → ℤ) (i fuel : ℕ) (seen : Bool), _
  intro m a b i fuel seen
  induction fuel generalizing i seen with
  | zero =>
      have hempty : ∀ j : Fin m, ¬ (i ≤ j.val ∧ j.val < i + 0) := by
        intro j
        omega
      simp [M7.ObjectiveComparison.paretoFrom, hempty]
  | succ fuel ih =>
      by_cases hi : i < m
      · let k : Fin m := ⟨i, hi⟩
        have hk : k.val = i := rfl
        have hall :
            (∀ j : Fin m, i ≤ j.val ∧ j.val < i + Nat.succ fuel → a j ≤ b j) ↔
            a k ≤ b k ∧
              (∀ j : Fin m, i + 1 ≤ j.val ∧ j.val < (i + 1) + fuel → a j ≤ b j) := by
          constructor
          · intro h
            constructor
            · exact h k (by omega)
            · intro j hj
              exact h j (by omega)
          · rintro ⟨hhead, htail⟩ j hj
            by_cases heq : j.val = i
            · have hjk : j = k := Fin.ext (by omega)
              simpa [hjk] using hhead
            · exact htail j (by omega)
        have hex :
            (∃ j : Fin m, (i ≤ j.val ∧ j.val < i + Nat.succ fuel) ∧ a j < b j) ↔
            a k < b k ∨
              (∃ j : Fin m, (i + 1 ≤ j.val ∧ j.val < (i + 1) + fuel) ∧ a j < b j) := by
          constructor
          · rintro ⟨j, hj, hstrict⟩
            by_cases heq : j.val = i
            · left
              have hjk : j = k := Fin.ext (by omega)
              simpa [hjk] using hstrict
            · exact Or.inr ⟨j, by omega, hstrict⟩
          · intro h
            rcases h with hhead | ⟨j, hj, hstrict⟩
            · exact ⟨k, by omega, hhead⟩
            · exact ⟨j, by omega, hstrict⟩
        rw [hall, hex]
        by_cases hle : a k ≤ b k
        · simp [M7.ObjectiveComparison.paretoFrom, hi, k, hle, ih, or_assoc] at *
        · simp [M7.ObjectiveComparison.paretoFrom, hi, k, hle] at *
      · have hempty : ∀ j : Fin m, ¬ (i ≤ j.val ∧ j.val < i + Nat.succ fuel) := by
          intro j hj
          have hjm := j.isLt
          omega
        simp [M7.ObjectiveComparison.paretoFrom, hi, hempty]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (mode : M7.Selection.Mode) (a b : Fin m → ℤ), (M7.ObjectiveComparison.compare mode a b).1 = true ↔ M7.Selection.better mode a b
