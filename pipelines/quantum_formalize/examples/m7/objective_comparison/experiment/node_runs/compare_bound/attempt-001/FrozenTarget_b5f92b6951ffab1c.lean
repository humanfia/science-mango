import M7ObjectiveComparison

theorem M7.ObjectiveComparison.lex_comparisons : ∀ (m : ℕ) (a b : Fin m → ℤ) (i fuel : ℕ), (M7.ObjectiveComparison.lexFrom a b i fuel).2 ≤ 2*fuel := by
  change ∀ (m : ℕ) (a b : Fin m → ℤ) (i fuel : ℕ), (M7.ObjectiveComparison.lexFrom a b i fuel).2 ≤ 2 * fuel
  intro m a b i fuel
  induction fuel generalizing i with
  | zero => simp [M7.ObjectiveComparison.lexFrom]
  | succ fuel ih =>
      have h := ih (i + 1)
      simp only [M7.ObjectiveComparison.lexFrom]
      repeat' split
      all_goals
        dsimp only at *
        omega

theorem M7.ObjectiveComparison.pareto_comparisons : ∀ (m : ℕ) (a b : Fin m → ℤ) (i fuel : ℕ) (seen : Bool), (M7.ObjectiveComparison.paretoFrom a b i fuel seen).2 ≤ 2*fuel := by
  change ∀ (m : ℕ) (a b : Fin m → ℤ) (i fuel : ℕ) (seen : Bool), (M7.ObjectiveComparison.paretoFrom a b i fuel seen).2 ≤ 2 * fuel
  intro m a b i fuel seen
  induction fuel generalizing i seen with
  | zero => simp [M7.ObjectiveComparison.paretoFrom]
  | succ fuel ih =>
      simp only [M7.ObjectiveComparison.paretoFrom]
      split
      next h =>
        split
        next hab =>
          have hrec := ih (i + 1) (seen || decide (a ⟨i, h⟩ < b ⟨i, h⟩))
          simp only [Prod.snd]
          omega
        next hab =>
          simp only [Prod.snd]
          omega
      next h =>
        simp only [Prod.snd]
        omega
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (mode : M7.Selection.Mode) (a b : Fin m → ℤ), (M7.ObjectiveComparison.compare mode a b).2 ≤ 2*m ∧ (M7.ObjectiveComparison.compare mode a b).2 ≤ 2*(m+1)
