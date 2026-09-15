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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N), (¬ M7.DefaultQuery.valid N q → M7.GlobalQuery.answer q bases = Except.error M7.DefaultQuery.QueryError.invalidSignature ∧ M7.GlobalQuery.winners q bases = ∅) ∧ (M7.DefaultQuery.valid N q → M7.GlobalQuery.answer q bases = Except.ok (M7.GlobalQuery.winners q bases))
