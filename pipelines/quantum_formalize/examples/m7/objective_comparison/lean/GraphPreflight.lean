import M7ObjectiveComparison

noncomputable def M7.ObjectiveComparisonTarget.pareto_interval : Prop :=
  ∀ (m : ℕ) (a b : Fin m → ℤ) (i fuel : ℕ) (seen : Bool), (M7.ObjectiveComparison.paretoFrom a b i fuel seen).1 = true ↔ (∀ j : Fin m, i ≤ j.val ∧ j.val < i+fuel → a j ≤ b j) ∧ (seen = true ∨ ∃ j : Fin m, (i ≤ j.val ∧ j.val < i+fuel) ∧ a j < b j)

noncomputable def M7.ObjectiveComparisonTarget.lex_interval : Prop :=
  ∀ (m : ℕ) (a b : Fin m → ℤ) (i fuel : ℕ), (M7.ObjectiveComparison.lexFrom a b i fuel).1 = true ↔ ∃ j : Fin m, (i ≤ j.val ∧ j.val < i+fuel) ∧ (∀ k : Fin m, i ≤ k.val → k < j → a k = b k) ∧ a j < b j

noncomputable def M7.ObjectiveComparisonTarget.pareto_comparisons : Prop :=
  ∀ (m : ℕ) (a b : Fin m → ℤ) (i fuel : ℕ) (seen : Bool), (M7.ObjectiveComparison.paretoFrom a b i fuel seen).2 ≤ 2*fuel

noncomputable def M7.ObjectiveComparisonTarget.lex_comparisons : Prop :=
  ∀ (m : ℕ) (a b : Fin m → ℤ) (i fuel : ℕ), (M7.ObjectiveComparison.lexFrom a b i fuel).2 ≤ 2*fuel

noncomputable def M7.ObjectiveComparisonTarget.compare_exact : Prop :=
  ∀ (m : ℕ) (mode : M7.Selection.Mode) (a b : Fin m → ℤ), (M7.ObjectiveComparison.compare mode a b).1 = true ↔ M7.Selection.better mode a b

noncomputable def M7.ObjectiveComparisonTarget.compare_bound : Prop :=
  ∀ (m : ℕ) (mode : M7.Selection.Mode) (a b : Fin m → ℤ), (M7.ObjectiveComparison.compare mode a b).2 ≤ 2*m ∧ (M7.ObjectiveComparison.compare mode a b).2 ≤ 2*(m+1)

