import FrozenTarget_2824cb6cf990b1ab
theorem M7.Selection.selector_strict_dominator : QuantumHarnessFrozenTarget := by
  change ∀ (α : Type) (m : ℕ) (T : Finset α) (feasible : α → Prop) (objective : α → Fin m → ℤ) (mode : M7.Selection.Mode), ∀ x ∈ T, feasible x → x ∉ M7.Selection.select T feasible objective mode → ∃ y ∈ M7.Selection.select T feasible objective mode, M7.Selection.better mode (objective y) (objective x)
  intro α m T feasible objective mode x hx hfx hn
  exact M7.Selection.nonwinner_strict_dominator α T feasible
    (fun y z => M7.Selection.better mode (objective y) (objective z))
    (fun y => (M7.Selection.better_laws m mode).1 (objective y))
    (fun y z w => (M7.Selection.better_laws m mode).2 (objective y) (objective z) (objective w))
    x hx hfx hn
