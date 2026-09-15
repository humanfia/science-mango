import FrozenTarget_784dccfc582fb9f1
theorem M7.ObjectiveComparison.pareto_comparisons : QuantumHarnessFrozenTarget := by
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
