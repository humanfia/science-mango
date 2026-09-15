import FrozenTarget_3e937b48aa346175
theorem M7.ObjectiveComparison.lex_comparisons : QuantumHarnessFrozenTarget := by
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
