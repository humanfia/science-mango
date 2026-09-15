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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (x : M7.GlobalQuery.Index H N), x ∈ M7.GlobalQuery.winners q bases → ∃! g : M7.Action.Record N, M7.GlobalQuery.present q bases (x.1,g) ∧ M7.Action.act g (bases x.1) = M7.GlobalQuery.realize bases x
