import M7Selection

noncomputable def M7.SelectionTarget.win_membership : Prop :=
  ∀ (α : Type) (T : Finset α) (feasible : α → Prop) (R : α → α → Prop) (x : α), x ∈ M7.Selection.winners T feasible R ↔ M7.Selection.win T feasible R x

#check M7.SelectionTarget.win_membership

noncomputable def M7.SelectionTarget.win_sound_complete : Prop :=
  ∀ (α : Type) (T : Finset α) (feasible : α → Prop) (R : α → α → Prop) (x : α), x ∈ M7.Selection.winners T feasible R ↔ x ∈ T ∧ feasible x ∧ ∀ y ∈ T, feasible y → ¬ R y x

#check M7.SelectionTarget.win_sound_complete

noncomputable def M7.SelectionTarget.finite_extreme : Prop :=
  ∀ (α : Type) (T : Finset α) (R : α → α → Prop), (∀ x, ¬ R x x) → (∀ x y z, R x y → R y z → R x z) → ∀ x ∈ T, ∃ y ∈ T, (∀ z ∈ T, ¬ R z y) ∧ (y = x ∨ R y x)

#check M7.SelectionTarget.finite_extreme

noncomputable def M7.SelectionTarget.winning_dominator : Prop :=
  ∀ (α : Type) (T : Finset α) (feasible : α → Prop) (R : α → α → Prop), (∀ x, ¬ R x x) → (∀ x y z, R x y → R y z → R x z) → ∀ x ∈ T, feasible x → ∃ y ∈ M7.Selection.winners T feasible R, y = x ∨ R y x

#check M7.SelectionTarget.winning_dominator

noncomputable def M7.SelectionTarget.empty_iff : Prop :=
  ∀ (α : Type) (T : Finset α) (feasible : α → Prop) (R : α → α → Prop), (∀ x, ¬ R x x) → (∀ x y z, R x y → R y z → R x z) → (M7.Selection.winners T feasible R = ∅ ↔ M7.Selection.feasibleSet T feasible = ∅)

#check M7.SelectionTarget.empty_iff

noncomputable def M7.SelectionTarget.nonwinner_strict_dominator : Prop :=
  ∀ (α : Type) (T : Finset α) (feasible : α → Prop) (R : α → α → Prop), (∀ x, ¬ R x x) → (∀ x y z, R x y → R y z → R x z) → ∀ x ∈ T, feasible x → x ∉ M7.Selection.winners T feasible R → ∃ y ∈ M7.Selection.winners T feasible R, R y x

#check M7.SelectionTarget.nonwinner_strict_dominator

noncomputable def M7.SelectionTarget.pareto_laws : Prop :=
  ∀ (m : ℕ), (∀ a : Fin m → ℤ, ¬ M7.Selection.pareto a a) ∧ (∀ a b c : Fin m → ℤ, M7.Selection.pareto a b → M7.Selection.pareto b c → M7.Selection.pareto a c)

#check M7.SelectionTarget.pareto_laws

noncomputable def M7.SelectionTarget.lex_laws : Prop :=
  ∀ (m : ℕ), (∀ a : Fin m → ℤ, ¬ M7.Selection.lex a a) ∧ (∀ a b c : Fin m → ℤ, M7.Selection.lex a b → M7.Selection.lex b c → M7.Selection.lex a c)

#check M7.SelectionTarget.lex_laws

noncomputable def M7.SelectionTarget.better_laws : Prop :=
  ∀ (m : ℕ) (mode : M7.Selection.Mode), (∀ a : Fin m → ℤ, ¬ M7.Selection.better mode a a) ∧ (∀ a b c : Fin m → ℤ, M7.Selection.better mode a b → M7.Selection.better mode b c → M7.Selection.better mode a c)

#check M7.SelectionTarget.better_laws

noncomputable def M7.SelectionTarget.selector_exact : Prop :=
  ∀ (α : Type) (m : ℕ) (T : Finset α) (feasible : α → Prop) (objective : α → Fin m → ℤ) (mode : M7.Selection.Mode), (∀ x, x ∈ M7.Selection.select T feasible objective mode ↔ x ∈ T ∧ feasible x ∧ ∀ y ∈ T, feasible y → ¬ M7.Selection.better mode (objective y) (objective x)) ∧ (M7.Selection.select T feasible objective mode = ∅ ↔ M7.Selection.feasibleSet T feasible = ∅)

#check M7.SelectionTarget.selector_exact

noncomputable def M7.SelectionTarget.selector_strict_dominator : Prop :=
  ∀ (α : Type) (m : ℕ) (T : Finset α) (feasible : α → Prop) (objective : α → Fin m → ℤ) (mode : M7.Selection.Mode), ∀ x ∈ T, feasible x → x ∉ M7.Selection.select T feasible objective mode → ∃ y ∈ M7.Selection.select T feasible objective mode, M7.Selection.better mode (objective y) (objective x)

#check M7.SelectionTarget.selector_strict_dominator

noncomputable def M7.SelectionTarget.empty_objectives : Prop :=
  ∀ (α : Type) (T : Finset α) (feasible : α → Prop) (objective : α → Fin 0 → ℤ) (mode : M7.Selection.Mode), M7.Selection.select T feasible objective mode = M7.Selection.feasibleSet T feasible

#check M7.SelectionTarget.empty_objectives

