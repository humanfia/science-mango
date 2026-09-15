import M7ActualPresentationAccepted
import M7GlobalQuery
import M7SelectionAccepted

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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), M7.GlobalQuery.separated bases → ∀ x ∈ M7.GlobalQuery.winners q bases, ∃! y : M7.GlobalQuery.Index H N, M7.GlobalQuery.present q bases y ∧ M7.GlobalQuery.realize bases y = M7.GlobalQuery.realize bases x
