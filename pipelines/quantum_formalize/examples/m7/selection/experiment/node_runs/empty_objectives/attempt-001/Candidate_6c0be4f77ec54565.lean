import FrozenTarget_6c0be4f77ec54565
theorem M7.Selection.empty_objectives : QuantumHarnessFrozenTarget := by
  classical
  intro α T feasible objective mode
  have hempty (P : Fin 0 → Prop) : (∃ i, P i) ↔ False := by
    constructor
    · rintro ⟨i, _⟩
      exact Fin.elim0 i
    · exact False.elim
  have hbetter (a b : Fin 0 → ℤ) : ¬ M7.Selection.better mode a b := by
    cases mode <;>
      simp [M7.Selection.better, M7.Selection.pareto, M7.Selection.lex, hempty]
  apply Finset.ext
  intro x
  simp [M7.Selection.select, M7.Selection.winners, M7.Selection.win,
    M7.Selection.feasibleSet, hbetter]
