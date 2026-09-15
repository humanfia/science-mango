import FrozenTarget_941a83987400ac36
theorem M7.ObjectiveComparison.pareto_comparisons : QuantumHarnessFrozenTarget := by
  change ∀ (m : ℕ) (a b : Fin m → ℤ) (i fuel : ℕ) (seen : Bool), (M7.ObjectiveComparison.paretoFrom a b i fuel seen).2 ≤ 2 * fuel
  intro m a b i fuel seen
  induction fuel generalizing i seen with
  | zero => simp [M7.ObjectiveComparison.paretoFrom]
  | succ fuel ih =>
      have ht := ih (i + 1) true
      have hf := ih (i + 1) false
      cases seen <;> simp only [M7.ObjectiveComparison.paretoFrom]
      all_goals repeat' first | progress dsimp only | split
      all_goals simp_all <;> omega
