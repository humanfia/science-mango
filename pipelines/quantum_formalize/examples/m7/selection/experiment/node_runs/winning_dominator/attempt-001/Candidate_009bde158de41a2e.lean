import FrozenTarget_009bde158de41a2e
theorem M7.Selection.winning_dominator : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (α : Type) (T : Finset α) (feasible : α → Prop) (R : α → α → Prop), (∀ x, ¬ R x x) → (∀ x y z, R x y → R y z → R x z) → ∀ x ∈ T, feasible x → ∃ y ∈ M7.Selection.winners T feasible R, y = x ∨ R y x
  intro α T feasible R hir htr x hx hfx
  have hxF : x ∈ M7.Selection.feasibleSet T feasible := by
    simpa [M7.Selection.feasibleSet] using And.intro hx hfx
  obtain ⟨y, hy, hmin, hyx⟩ := M7.Selection.finite_extreme α (M7.Selection.feasibleSet T feasible) R hir htr x hxF
  refine ⟨y, ?_, hyx⟩
  apply (M7.Selection.win_membership α T feasible R y).mpr
  simp only [M7.Selection.feasibleSet, Finset.mem_filter] at hy hmin
  simp only [M7.Selection.win, M7.Selection.feasibleSet, Finset.mem_filter]
  aesop
