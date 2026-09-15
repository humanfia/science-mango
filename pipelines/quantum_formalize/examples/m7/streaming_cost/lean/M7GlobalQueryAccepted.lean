import M7ActualPresentationAccepted
import M7GlobalQuery
import M7SelectionAccepted

theorem M7.GlobalQuery.empty_objectives : ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), q.objectives = [] → M7.GlobalQuery.winners q bases = M7.Selection.feasibleSet Finset.univ (M7.GlobalQuery.feasible q bases) := by
  intro H N inst q bases h
  cases q
  dsimp only at h
  subst_vars
  unfold M7.GlobalQuery.winners
  exact M7.Selection.empty_objectives _ _ _ _ _

theorem M7.GlobalQuery.presentation_sound : ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (x : M7.GlobalQuery.Index H N), M7.GlobalQuery.present q bases x → x ∈ M7.GlobalQuery.winners q bases ∧ ∀ g : M7.Action.Record N, M7.Action.act g (bases x.1) = M7.GlobalQuery.realize bases x → M7.ActualPresentation.encode x.2 ≤ M7.ActualPresentation.encode g := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (x : M7.GlobalQuery.Index H N), M7.GlobalQuery.present q bases x → x ∈ M7.GlobalQuery.winners q bases ∧ ∀ g : M7.Action.Record N, M7.Action.act g (bases x.1) = M7.GlobalQuery.realize bases x → M7.ActualPresentation.encode x.2 ≤ M7.ActualPresentation.encode g
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases x hx
  unfold M7.GlobalQuery.present at hx
  refine ⟨hx.1, ?_⟩
  exact (((M7.ActualPresentation.leastAction_spec N (bases x.1)
    (M7.GlobalQuery.realize bases x)).1 x.2).mp hx.2).2

theorem M7.GlobalQuery.strict_dominator : ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (x : M7.GlobalQuery.Index H N), M7.GlobalQuery.feasible q bases x → x ∉ M7.GlobalQuery.winners q bases → ∃ y ∈ M7.GlobalQuery.winners q bases, M7.Selection.better q.order (M7.GlobalQuery.objective q bases y) (M7.GlobalQuery.objective q bases x) := by
  intro H N inst q bases x hx hn
  classical
  exact M7.Selection.selector_strict_dominator
    (M7.GlobalQuery.Index H N) q.objectives.length Finset.univ
    (M7.GlobalQuery.feasible q bases) (M7.GlobalQuery.objective q bases)
    q.order x (Finset.mem_univ x) hx hn

theorem M7.GlobalQuery.winners_exact : ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), (∀ x : M7.GlobalQuery.Index H N, x ∈ M7.GlobalQuery.winners q bases ↔ M7.GlobalQuery.feasible q bases x ∧ ∀ y : M7.GlobalQuery.Index H N, M7.GlobalQuery.feasible q bases y → ¬ M7.Selection.better q.order (M7.GlobalQuery.objective q bases y) (M7.GlobalQuery.objective q bases x)) ∧ (M7.GlobalQuery.winners q bases = ∅ ↔ ¬ ∃ x : M7.GlobalQuery.Index H N, M7.GlobalQuery.feasible q bases x) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), (∀ x : M7.GlobalQuery.Index H N, x ∈ M7.GlobalQuery.winners q bases ↔ M7.GlobalQuery.feasible q bases x ∧ ∀ y : M7.GlobalQuery.Index H N, M7.GlobalQuery.feasible q bases y → ¬ M7.Selection.better q.order (M7.GlobalQuery.objective q bases y) (M7.GlobalQuery.objective q bases x)) ∧ (M7.GlobalQuery.winners q bases = ∅ ↔ ¬ ∃ x : M7.GlobalQuery.Index H N, M7.GlobalQuery.feasible q bases x)
  )
  change QuantumHarnessFrozenTarget
  classical
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases
  simpa [M7.GlobalQuery.winners, M7.Selection.feasibleSet,
    Finset.filter_eq_empty_iff, not_exists] using
    (M7.Selection.selector_exact (M7.GlobalQuery.Index H N)
      q.objectives.length Finset.univ (M7.GlobalQuery.feasible q bases)
      (M7.GlobalQuery.objective q bases) q.order)

theorem M7.GlobalQuery.winning_classes : ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (i : Fin H), i ∈ M7.GlobalQuery.winningClasses q bases ↔ ∃ g : M7.Action.Record N, (i,g) ∈ M7.GlobalQuery.winners q bases := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (i : Fin H), i ∈ M7.GlobalQuery.winningClasses q bases ↔ ∃ g : M7.Action.Record N, (i,g) ∈ M7.GlobalQuery.winners q bases
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases i
  classical
  unfold M7.GlobalQuery.winningClasses
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨j, g⟩, h, hj⟩
    change j = i at hj
    subst j
    exact ⟨g, h⟩
  · rintro ⟨g, hg⟩
    exact ⟨(i, g), hg, rfl⟩

theorem M7.GlobalQuery.invalid_rejection : ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), (¬ M7.DefaultQuery.valid N q → M7.GlobalQuery.answer q bases = Except.error M7.DefaultQuery.QueryError.invalidSignature ∧ M7.GlobalQuery.winners q bases = ∅) ∧ (M7.DefaultQuery.valid N q → M7.GlobalQuery.answer q bases = Except.ok (M7.GlobalQuery.winners q bases)) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), (¬ M7.DefaultQuery.valid N q → M7.GlobalQuery.answer q bases = Except.error M7.DefaultQuery.QueryError.invalidSignature ∧ M7.GlobalQuery.winners q bases = ∅) ∧ (M7.DefaultQuery.valid N q → M7.GlobalQuery.answer q bases = Except.ok (M7.GlobalQuery.winners q bases))
  )
  change QuantumHarnessFrozenTarget
  classical
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases
  constructor
  · intro hbad
    constructor
    · simp [M7.GlobalQuery.answer, hbad]
    · apply (M7.GlobalQuery.winners_exact H N q bases).2.mpr
      rintro ⟨x, hx⟩
      simpa [M7.GlobalQuery.feasible, M7.DefaultQuery.feasible, hbad] using hx
  · intro hvalid
    simp [M7.GlobalQuery.answer, hvalid]

theorem M7.GlobalQuery.winning_fiber : ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (x y : M7.GlobalQuery.Index H N), x.1 = y.1 → M7.GlobalQuery.realize bases x = M7.GlobalQuery.realize bases y → (x ∈ M7.GlobalQuery.winners q bases ↔ y ∈ M7.GlobalQuery.winners q bases) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (x y : M7.GlobalQuery.Index H N), x.1 = y.1 → M7.GlobalQuery.realize bases x = M7.GlobalQuery.realize bases y → (x ∈ M7.GlobalQuery.winners q bases ↔ y ∈ M7.GlobalQuery.winners q bases)
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases x y hclass himage
  classical
  have hf : M7.GlobalQuery.feasible q bases x = M7.GlobalQuery.feasible q bases y := by
    simp only [M7.GlobalQuery.feasible, hclass, himage]
  have ho : M7.GlobalQuery.objective q bases x = M7.GlobalQuery.objective q bases y := by
    simp only [M7.GlobalQuery.objective, himage]
  rw [(M7.GlobalQuery.winners_exact H N q bases).1 x,
    (M7.GlobalQuery.winners_exact H N q bases).1 y, hf, ho]

theorem M7.GlobalQuery.same_class_presentation : ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (x : M7.GlobalQuery.Index H N), x ∈ M7.GlobalQuery.winners q bases → ∃! g : M7.Action.Record N, M7.GlobalQuery.present q bases (x.1,g) ∧ M7.Action.act g (bases x.1) = M7.GlobalQuery.realize bases x := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (x : M7.GlobalQuery.Index H N), x ∈ M7.GlobalQuery.winners q bases → ∃! g : M7.Action.Record N, M7.GlobalQuery.present q bases (x.1,g) ∧ M7.Action.act g (bases x.1) = M7.GlobalQuery.realize bases x
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases x hx
  classical
  have hs := M7.ActualPresentation.leastAction_spec N (bases x.1) (M7.GlobalQuery.realize bases x)
  cases he : M7.ActualPresentation.leastAction (bases x.1) (M7.GlobalQuery.realize bases x) with
  | none =>
      exact False.elim ((hs.2.mp he) ⟨x.2, rfl⟩)
  | some g =>
      have hg := ((hs.1 g).mp he).1
      have hw : (x.1, g) ∈ M7.GlobalQuery.winners q bases :=
        (M7.GlobalQuery.winning_fiber H N q bases x (x.1, g) rfl hg.symm).mp hx
      refine ⟨g, ⟨?_, hg⟩, ?_⟩
      · change (x.1, g) ∈ M7.GlobalQuery.winners q bases ∧
          M7.ActualPresentation.leastAction (bases x.1) (M7.Action.act g (bases x.1)) = some g
        refine ⟨hw, ?_⟩
        rw [hg]
        exact he
      · intro h hh
        have hhleast : M7.ActualPresentation.leastAction (bases x.1)
            (M7.Action.act h (bases x.1)) = some h := hh.1.2
        rw [hh.2] at hhleast
        exact Option.some.inj (hhleast.symm.trans he)

theorem M7.GlobalQuery.physical_presentation : ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), M7.GlobalQuery.separated bases → ∀ x ∈ M7.GlobalQuery.winners q bases, ∃! y : M7.GlobalQuery.Index H N, M7.GlobalQuery.present q bases y ∧ M7.GlobalQuery.realize bases y = M7.GlobalQuery.realize bases x := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), M7.GlobalQuery.separated bases → ∀ x ∈ M7.GlobalQuery.winners q bases, ∃! y : M7.GlobalQuery.Index H N, M7.GlobalQuery.present q bases y ∧ M7.GlobalQuery.realize bases y = M7.GlobalQuery.realize bases x
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases hsep x hx
  classical
  rcases M7.GlobalQuery.same_class_presentation H N q bases x hx with ⟨g, hg, huniq⟩
  refine ⟨(x.1, g), hg, ?_⟩
  intro y hy
  have hclass : y.1 = x.1 := by
    unfold M7.GlobalQuery.separated at hsep
    first
    | exact hsep y x hy.2
    | exact hsep y.1 x.1 y.2 x.2 hy.2
    | exact hsep y.1 y.2 x.1 x.2 hy.2
  rcases y with ⟨j, h⟩
  change j = x.1 at hclass
  subst j
  exact congrArg (fun a : M7.Action.Record N => (x.1, a)) (huniq h hy)
#print axioms M7.GlobalQuery.empty_objectives
#print axioms M7.GlobalQuery.presentation_sound
#print axioms M7.GlobalQuery.strict_dominator
#print axioms M7.GlobalQuery.winners_exact
#print axioms M7.GlobalQuery.invalid_rejection
#print axioms M7.GlobalQuery.winning_classes
#print axioms M7.GlobalQuery.winning_fiber
#print axioms M7.GlobalQuery.same_class_presentation
#print axioms M7.GlobalQuery.physical_presentation
