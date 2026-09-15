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

theorem M7.Selection.lex_laws : ∀ (m : ℕ), (∀ a : Fin m → ℤ, ¬ M7.Selection.lex a a) ∧ (∀ a b c : Fin m → ℤ, M7.Selection.lex a b → M7.Selection.lex b c → M7.Selection.lex a c) := by
  change ∀ (m : ℕ), (∀ a : Fin m → ℤ, ¬ M7.Selection.lex a a) ∧ (∀ a b c : Fin m → ℤ, M7.Selection.lex a b → M7.Selection.lex b c → M7.Selection.lex a c)
  intro m
  constructor
  · intro a h
    unfold M7.Selection.lex at h
    rcases h with ⟨i, h₁, h₂⟩
    first
    | exact (lt_irrefl (a i)) h₁
    | exact (lt_irrefl (a i)) h₂
  · intro a b c hab hbc
    unfold M7.Selection.lex at hab hbc ⊢
    rcases hab with ⟨i, hi₁, hi₂⟩
    rcases hbc with ⟨j, hj₁, hj₂⟩
    have hi : a i < b i := by first | exact hi₁ | exact hi₂
    have hj : b j < c j := by first | exact hj₁ | exact hj₂
    have ei : ∀ k : Fin m, k < i → a k = b k := by
      first | exact hi₁ | exact hi₂
    have ej : ∀ k : Fin m, k < j → b k = c k := by
      first | exact hj₁ | exact hj₂
    rcases lt_trichotomy i j with hij | hij | hji
    · have hl : a i < c i := by rw [← ej i hij]; exact hi
      have he : ∀ k : Fin m, k < i → a k = c k := by
        intro k hk
        exact (ei k hk).trans (ej k (lt_trans hk hij))
      refine ⟨i, ?_⟩
      first | exact ⟨hl, he⟩ | exact ⟨he, hl⟩
    · subst j
      have hl : a i < c i := lt_trans hi hj
      have he : ∀ k : Fin m, k < i → a k = c k := by
        intro k hk
        exact (ei k hk).trans (ej k hk)
      refine ⟨i, ?_⟩
      first | exact ⟨hl, he⟩ | exact ⟨he, hl⟩
    · have hl : a j < c j := by rw [ei j hji]; exact hj
      have he : ∀ k : Fin m, k < j → a k = c k := by
        intro k hk
        exact (ei k (lt_trans hk hji)).trans (ej k hk)
      refine ⟨j, ?_⟩
      first | exact ⟨hl, he⟩ | exact ⟨he, hl⟩

theorem M7.Selection.pareto_laws : ∀ (m : ℕ), (∀ a : Fin m → ℤ, ¬ M7.Selection.pareto a a) ∧ (∀ a b c : Fin m → ℤ, M7.Selection.pareto a b → M7.Selection.pareto b c → M7.Selection.pareto a c) := by
  change ∀ (m : ℕ), (∀ a : Fin m → ℤ, ¬ M7.Selection.pareto a a) ∧ (∀ a b c : Fin m → ℤ, M7.Selection.pareto a b → M7.Selection.pareto b c → M7.Selection.pareto a c)
  intro m
  constructor
  · intro a h
    unfold M7.Selection.pareto at h
    rcases h with ⟨_, i, hi⟩
    exact (lt_irrefl (a i)) hi
  · intro a b c hab hbc
    unfold M7.Selection.pareto at *
    rcases hab with ⟨hab, i, hi⟩
    rcases hbc with ⟨hbc, _⟩
    constructor
    · intro j
      have h₁ := hab j
      have h₂ := hbc j
      omega
    · refine ⟨i, ?_⟩
      have h₂ := hbc i
      omega

theorem M7.Selection.win_membership : ∀ (α : Type) (T : Finset α) (feasible : α → Prop) (R : α → α → Prop) (x : α), x ∈ M7.Selection.winners T feasible R ↔ M7.Selection.win T feasible R x := by
  change ∀ (α : Type) (T : Finset α) (feasible : α → Prop) (R : α → α → Prop) (x : α), x ∈ M7.Selection.winners T feasible R ↔ M7.Selection.win T feasible R x
  intro α T feasible R x
  classical
  simp [M7.Selection.winners, M7.Selection.win, M7.Selection.feasibleSet, and_assoc, and_left_comm, and_comm]

theorem M7.Selection.better_laws : ∀ (m : ℕ) (mode : M7.Selection.Mode), (∀ a : Fin m → ℤ, ¬ M7.Selection.better mode a a) ∧ (∀ a b c : Fin m → ℤ, M7.Selection.better mode a b → M7.Selection.better mode b c → M7.Selection.better mode a c) := by
  change ∀ (m : ℕ) (mode : M7.Selection.Mode), (∀ a : Fin m → ℤ, ¬ M7.Selection.better mode a a) ∧ (∀ a b c : Fin m → ℤ, M7.Selection.better mode a b → M7.Selection.better mode b c → M7.Selection.better mode a c)
  intro m mode
  cases mode <;> first
  | exact M7.Selection.pareto_laws m
  | exact M7.Selection.lex_laws m

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

theorem M7.Selection.nonwinner_strict_dominator : ∀ (α : Type) (T : Finset α) (feasible : α → Prop) (R : α → α → Prop), (∀ x, ¬ R x x) → (∀ x y z, R x y → R y z → R x z) → ∀ x ∈ T, feasible x → x ∉ M7.Selection.winners T feasible R → ∃ y ∈ M7.Selection.winners T feasible R, R y x := by
  change ∀ (α : Type) (T : Finset α) (feasible : α → Prop) (R : α → α → Prop), (∀ x, ¬ R x x) → (∀ x y z, R x y → R y z → R x z) → ∀ x ∈ T, feasible x → x ∉ M7.Selection.winners T feasible R → ∃ y ∈ M7.Selection.winners T feasible R, R y x
  intro α T feasible R hir htr x hx hfx hnwin
  obtain ⟨y, hy, hyx⟩ := M7.Selection.winning_dominator α T feasible R hir htr x hx hfx
  rcases hyx with heq | hrel
  · subst y
    exact False.elim (hnwin hy)
  · exact ⟨y, hy, hrel⟩
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (α : Type) (m : ℕ) (T : Finset α) (feasible : α → Prop) (objective : α → Fin m → ℤ) (mode : M7.Selection.Mode), ∀ x ∈ T, feasible x → x ∉ M7.Selection.select T feasible objective mode → ∃ y ∈ M7.Selection.select T feasible objective mode, M7.Selection.better mode (objective y) (objective x)
