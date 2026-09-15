import M7Selection

theorem M7.Selection.finite_extreme : ∀ (α : Type) (T : Finset α) (R : α → α → Prop), (∀ x, ¬ R x x) → (∀ x y z, R x y → R y z → R x z) → ∀ x ∈ T, ∃ y ∈ T, (∀ z ∈ T, ¬ R z y) ∧ (y = x ∨ R y x) := by
  classical
  change ∀ (α : Type) (T : Finset α) (R : α → α → Prop), (∀ x, ¬ R x x) → (∀ x y z, R x y → R y z → R x z) → ∀ x ∈ T, ∃ y ∈ T, (∀ z ∈ T, ¬ R z y) ∧ (y = x ∨ R y x)
  intro α T R hir htr
  induction T using Finset.induction_on with
  | empty =>
      intro x hx
      simp at hx
  | @insert a S ha ih =>
      intro x hx
      rcases Finset.mem_insert.mp hx with hxa | hxS
      · subst x
        by_cases hp : ∃ b ∈ S, R b a
        · obtain ⟨b, hb, hba⟩ := hp
          obtain ⟨y, hy, hmin, hyb⟩ := ih b hb
          have hya : R y a := by
            rcases hyb with heq | hyb
            · subst y
              exact hba
            · exact htr y b a hyb hba
          refine ⟨y, Finset.mem_insert_of_mem hy, ?_, Or.inr hya⟩
          intro z hz hzy
          rcases Finset.mem_insert.mp hz with hza | hzS
          · subst z
            exact hir a (htr a y a hzy hya)
          · exact hmin z hzS hzy
        · refine ⟨a, Finset.mem_insert_self a S, ?_, Or.inl rfl⟩
          intro z hz hza
          rcases Finset.mem_insert.mp hz with heq | hzS
          · subst z
            exact hir a hza
          · exact hp ⟨z, hzS, hza⟩
      · obtain ⟨y, hy, hmin, hyx⟩ := ih x hxS
        by_cases hay : R a y
        · refine ⟨a, Finset.mem_insert_self a S, ?_, ?_⟩
          · intro z hz hza
            rcases Finset.mem_insert.mp hz with heq | hzS
            · subst z
              exact hir a hza
            · exact hmin z hzS (htr z a y hza hay)
          · right
            rcases hyx with heq | hyx
            · subst y
              exact hay
            · exact htr a y x hay hyx
        · refine ⟨y, Finset.mem_insert_of_mem hy, ?_, hyx⟩
          intro z hz hzy
          rcases Finset.mem_insert.mp hz with heq | hzS
          · subst z
            exact hay hzy
          · exact hmin z hzS hzy

theorem M7.Selection.win_membership : ∀ (α : Type) (T : Finset α) (feasible : α → Prop) (R : α → α → Prop) (x : α), x ∈ M7.Selection.winners T feasible R ↔ M7.Selection.win T feasible R x := by
  change ∀ (α : Type) (T : Finset α) (feasible : α → Prop) (R : α → α → Prop) (x : α), x ∈ M7.Selection.winners T feasible R ↔ M7.Selection.win T feasible R x
  intro α T feasible R x
  classical
  simp [M7.Selection.winners, M7.Selection.win, M7.Selection.feasibleSet, and_assoc, and_left_comm, and_comm]

theorem M7.Selection.winning_dominator : ∀ (α : Type) (T : Finset α) (feasible : α → Prop) (R : α → α → Prop), (∀ x, ¬ R x x) → (∀ x y z, R x y → R y z → R x z) → ∀ x ∈ T, feasible x → ∃ y ∈ M7.Selection.winners T feasible R, y = x ∨ R y x := by
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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (α : Type) (T : Finset α) (feasible : α → Prop) (R : α → α → Prop), (∀ x, ¬ R x x) → (∀ x y z, R x y → R y z → R x z) → ∀ x ∈ T, feasible x → x ∉ M7.Selection.winners T feasible R → ∃ y ∈ M7.Selection.winners T feasible R, R y x
