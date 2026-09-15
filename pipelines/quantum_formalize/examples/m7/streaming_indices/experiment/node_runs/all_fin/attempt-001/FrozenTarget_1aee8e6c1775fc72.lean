import M7StreamingIndices

theorem M7.StreamingIndices.cursor_interval : ∀ (n : ℕ) (p : Fin n → Bool) (i fuel : ℕ), M7.StreamingIndices.allFinFrom n p i fuel = true ↔ ∀ j : Fin n, i ≤ j.val → j.val < i + fuel → p j = true := by
  change ∀ (n : ℕ) (p : Fin n → Bool) (i fuel : ℕ), M7.StreamingIndices.allFinFrom n p i fuel = true ↔ ∀ j : Fin n, i ≤ j.val → j.val < i + fuel → p j = true
  intro n p i fuel
  induction fuel generalizing i with
  | zero =>
      constructor
      · intro _ j hlo hhi
        omega
      · intro _
        rfl
  | succ fuel ih =>
      by_cases hi : i < n
      · by_cases hp : p ⟨i, hi⟩ = true
        · have hstep : M7.StreamingIndices.allFinFrom n p i (fuel + 1) = M7.StreamingIndices.allFinFrom n p (i + 1) fuel := by
            simp [M7.StreamingIndices.allFinFrom, hi, hp]
          rw [hstep, ih]
          constructor
          · intro h j hlo hhi
            by_cases hj : j.val = i
            · have heq : j = ⟨i, hi⟩ := Fin.ext hj
              simpa only [heq] using hp
            · exact h j (by omega) (by omega)
          · intro h j hlo hhi
            exact h j (by omega) (by omega)
        · constructor
          · intro h
            simp [M7.StreamingIndices.allFinFrom, hi, hp] at h
          · intro h
            exfalso
            apply hp
            exact h ⟨i, hi⟩ (by simp) (by dsimp; omega)
      · constructor
        · intro _ j hlo _
          have hj := j.isLt
          omega
        · intro _
          simp [M7.StreamingIndices.allFinFrom, hi]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (n : ℕ) (p : Fin n → Bool), M7.StreamingIndices.allFin n p = true ↔ ∀ j : Fin n, p j = true
